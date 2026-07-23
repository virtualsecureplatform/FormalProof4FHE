/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AuxiliaryInputCircularSearch
import FormalProof4FHE.TFHE.KeySwitchRecovery

/-!
# Completing Scalar TFHE Search with the Real Key-Switch Key

The native auxiliary-input CircLWE search experiment asks for both the scalar key and the binary
ring key.  Under the checked centered-binomial KSK decoding margin, this is no harder than
recovering the scalar key: the retained real KSK deterministically completes every correct scalar
candidate to the unique ring key.

This module formalizes the completion solver and proves exact equality of its paired-key success
game with the corresponding scalar-only success game.  The result removes ring-key randomization
from the remaining search-to-decision obligation; constructing the scalar decision-to-search
solver and its quantitative advantage bound remains separate.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery

/-- A public solver for only the scalar component of the native auxiliary-input search secret. -/
abbrev ScalarSolver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Challenge q degree ringRank tgswLevels lweDimension →
    Auxiliary q degree ringRank lweDimension keySwitchLevels →
      ProbComp (BinarySecret lweDimension)

/-- Verify only scalar-key recovery in the same native real BRK+KSK experiment. -/
noncomputable def scalarGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : ScalarSolver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp Bool := do
  let secrets ←
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleChallenge secrets
  let auxiliary ←
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  let recovered ← solver challenge auxiliary
  return decide (recovered = secrets.1)

/-- Complete a scalar-search solver to a paired-search solver by decrypting the retained KSK with
the candidate scalar key. -/
noncomputable def completeScalarSolver
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (solver : ScalarSolver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    Solver q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun challenge keySwitchKey ↦
    (fun candidate ↦ Native.KeySwitchRecovery.completeCandidate
      keySwitchGadget level keySwitchKey candidate) <$> solver challenge keySwitchKey

/-- **Exact scalar-to-paired search completion.**

For centered-binomial KSK errors and a separated gadget level, the completed solver wins the
native exact paired-key search game with exactly the probability that its underlying solver
recovers the scalar key. -/
theorem game_completeScalarSolver_eq_scalarGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (solver : ScalarSolver q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    Search.game ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget
        (completeScalarSolver keySwitchGadget level solver) =
      scalarGame ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget solver := by
  classical
  simp only [Search.game, Search.problem,
    LWE.AuxiliaryInput.Search.game, LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    AuxiliaryInput.problem, scalarGame, completeScalarSolver,
    map_eq_bind_pure_comp]
  apply bind_congr
  rintro ⟨lweSecret, ringSecret⟩
  apply bind_congr
  intro challenge
  apply OracleComp.bind_congr_of_forall_mem_support
  intro keySwitchKey hkey
  simp only [bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  intro candidate
  congr 1
  have hiff :=
    Native.KeySwitchRecovery.completeCandidate_eq_iff_of_mem_support_generate_centeredBinomial
      keySwitchGadget level ringSecret lweSecret candidate hkey hmargin
  by_cases hcandidate : candidate = lweSecret
  · subst candidate
    have hcomplete :
        Native.KeySwitchRecovery.completeCandidate keySwitchGadget level keySwitchKey lweSecret =
          (lweSecret, ringSecret) := hiff.mpr rfl
    simp [hcomplete]
  · have hcomplete :
        Native.KeySwitchRecovery.completeCandidate keySwitchGadget level keySwitchKey candidate ≠
          (lweSecret, ringSecret) := fun heq ↦ hcandidate (hiff.mp heq)
    simp [hcandidate, hcomplete]

/-- The exact paired success probability of the completed solver is the scalar-only recovery
probability. -/
theorem successProbability_completeScalarSolver_eq
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (solver : ScalarSolver q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    Search.successProbability ringErrorSampler
        (CenteredBinomial.scalarSampler q keySwitchEta) tgswGadget keySwitchGadget
        (completeScalarSolver keySwitchGadget level solver) =
      Pr[= true |
        scalarGame ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget solver] := by
  unfold Search.successProbability LWE.AuxiliaryInput.Search.successProbability
  change Pr[= true |
      Search.game ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget
        (completeScalarSolver keySwitchGadget level solver)] = _
  rw [game_completeScalarSolver_eq_scalarGame ringErrorSampler tgswGadget
    keySwitchGadget level solver hmargin]

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery
