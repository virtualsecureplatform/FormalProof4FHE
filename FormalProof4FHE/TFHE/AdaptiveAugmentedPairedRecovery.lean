/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptivePublicAuxiliaryInputCircular
import FormalProof4FHE.TFHE.KeySwitchRecovery

/-!
# Paired-Key Completion for Augmented Adaptive CircLWE Search

The augmented public CircLWE source carries `(BRK, KSK, input tape)`.  A scalar-key recovery
algorithm may use all three public components.  This module proves that the retained real KSK
still completes a correct scalar candidate to the full native scalar/ring key pair with no loss,
even when the bounded input tape is present.

This is the paired-recovery backend needed by an augmented search-to-decision reduction.  The
remaining front end is the candidate-dependent shifted evaluator; tape transport itself is exact
in `AdaptivePublicAuxiliaryInputCircular`.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

open Native

variable
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

abbrev Secret (lweDimension ringRank degree : ℕ) :=
  Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
    lweDimension ringRank degree

abbrev Challenge
    (q degree ringRank tgswLevels lweDimension : ℕ) :=
  Native.BootstrappingKey q degree ringRank tgswLevels lweDimension

abbrev Auxiliary
    (q ringRank degree lweDimension keySwitchLevels queryCount : ℕ) :=
  KeySwitchFirstFiniteView.CircularBatchAuxiliary
    q ringRank degree lweDimension keySwitchLevels queryCount

abbrev ScalarSolver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  Challenge q degree ringRank tgswLevels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
      ProbComp (BinarySecret lweDimension)

abbrev Solver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  LWE.AuxiliaryInput.Search.Solver
    (Secret lweDimension ringRank degree)
    (Challenge q degree ringRank tgswLevels lweDimension)
    (Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)

/-- Exact paired-secret search associated with the real branch of the augmented public problem. -/
noncomputable def problem
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    LWE.AuxiliaryInput.Search.Problem
      (Secret lweDimension ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) :=
  LWE.AuxiliaryInput.Search.exactRecoveryProblem
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget)

/-- Verify only scalar-key recovery in the same augmented real experiment. -/
noncomputable def scalarGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : ScalarSolver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) : ProbComp Bool := do
  let secrets ←
    (problem (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (problem (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget).sampleChallenge secrets
  let auxiliary ←
    (problem (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  let recovered ← solver challenge auxiliary
  return decide (recovered = secrets.1)

/-- Complete a scalar solver using the KSK component while retaining the input tape for the
scalar recovery computation. -/
noncomputable def completeScalarSolver
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (solver : ScalarSolver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) :
    Solver q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  fun challenge auxiliary ↦
    (fun candidate ↦ Native.KeySwitchRecovery.completeCandidate
      keySwitchGadget level auxiliary.1 candidate) <$> solver challenge auxiliary

/-- **Exact augmented scalar-to-paired completion.**

For centered-binomial KSK errors satisfying the decoding margin, the bounded input tape does not
alter completion: paired-key recovery succeeds exactly when the scalar solver succeeds. -/
theorem game_completeScalarSolver_eq_scalarGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (solver : ScalarSolver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    LWE.AuxiliaryInput.Search.game
        (problem (queryCount := queryCount) ringErrorSampler
          (CenteredBinomial.scalarSampler q keySwitchEta) inputErrorSampler
          tgswGadget keySwitchGadget)
        (completeScalarSolver keySwitchGadget level solver) =
      scalarGame ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
        inputErrorSampler tgswGadget keySwitchGadget solver := by
  classical
  simp only [LWE.AuxiliaryInput.Search.game, problem,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    KeySwitchFirstFiniteView.augmentedCircularProblem, scalarGame,
    completeScalarSolver, map_eq_bind_pure_comp]
  apply bind_congr
  rintro ⟨lweSecret, ringSecret⟩
  apply bind_congr
  intro challenge
  simp only [bind_assoc]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro keySwitchKey hkey
  apply bind_congr
  intro tape
  simp only [pure_bind, Function.comp_apply]
  apply bind_congr
  intro candidate
  congr 1
  have hiff :=
    Native.KeySwitchRecovery.completeCandidate_eq_iff_of_mem_support_generate_centeredBinomial
      keySwitchGadget level ringSecret lweSecret candidate hkey hmargin
  by_cases hcandidate : candidate = lweSecret
  · subst candidate
    have hcomplete :
        Native.KeySwitchRecovery.completeCandidate keySwitchGadget level
          keySwitchKey lweSecret = (lweSecret, ringSecret) := hiff.mpr rfl
    simp [hcomplete]
  · have hcomplete :
        Native.KeySwitchRecovery.completeCandidate keySwitchGadget level
          keySwitchKey candidate ≠ (lweSecret, ringSecret) :=
      fun heq ↦ hcandidate (hiff.mp heq)
    simp [hcandidate, hcomplete]

/-- The exact paired-search success probability of the completed solver is the scalar-only
success probability. -/
theorem successProbability_completeScalarSolver_eq
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (solver : ScalarSolver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    LWE.AuxiliaryInput.Search.successProbability
        (problem (queryCount := queryCount) ringErrorSampler
          (CenteredBinomial.scalarSampler q keySwitchEta) inputErrorSampler
          tgswGadget keySwitchGadget)
        (completeScalarSolver keySwitchGadget level solver) =
      Pr[= true |
        scalarGame ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
          inputErrorSampler tgswGadget keySwitchGadget solver] := by
  unfold LWE.AuxiliaryInput.Search.successProbability
  rw [game_completeScalarSolver_eq_scalarGame ringErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget level solver hmargin]

/-! ## Cross-distribution reduction adapters -/

/-- A paired-secret cross reduction from a narrow centered-binomial augmented search view to a
possibly wider augmented public CircLWE decision view. -/
abbrev PairedSecretReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
      ringEta keySwitchEta : ℕ)
    [NeZero q]
    (inputErrorSampler : ProbComp (ZMod q))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :=
  LWE.AuxiliaryInput.SearchToDecision.CrossReduction
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) targetRingErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (problem (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount)
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      inputErrorSampler tgswGadget keySwitchGadget)

/-- Scalar-only augmented reduction certificate.  Candidate testing may inspect the BRK, KSK,
and complete bounded input tape. -/
structure ScalarSecretReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
      ringEta keySwitchEta : ℕ)
    [NeZero q]
    (inputErrorSampler : ProbComp (ZMod q))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toScalarSolver :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) →
    ScalarSolver q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
  loss :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le : ∀ distinguisher,
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (KeySwitchFirstFiniteView.augmentedCircularProblem
          (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler
          targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
        distinguisher ≤
      (Pr[= true |
        scalarGame
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          inputErrorSampler tgswGadget keySwitchGadget
          (toScalarSolver distinguisher)]).toReal +
        loss distinguisher

namespace ScalarSecretReduction

/-- Centered-binomial KSK decoding turns an augmented scalar reduction into a checked paired-key
cross reduction without changing either its success probability or loss. -/
noncomputable def toPairedSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
      ringEta keySwitchEta : ℕ}
    [NeZero q]
    {inputErrorSampler : ProbComp (ZMod q)}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : ScalarSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount ringEta keySwitchEta inputErrorSampler
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    PairedSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringEta keySwitchEta inputErrorSampler targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget where
  toSolver := fun distinguisher ↦
    completeScalarSolver keySwitchGadget level
      (reduction.toScalarSolver distinguisher)
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  advantage_le := by
    intro distinguisher
    have h := reduction.advantage_le distinguisher
    rw [← successProbability_completeScalarSolver_eq
      (RLWE.CenteredBinomial.sampler q degree ringEta) inputErrorSampler
      tgswGadget keySwitchGadget level (reduction.toScalarSolver distinguisher)
      hmargin] at h
    exact h

/-- Narrow augmented paired-search hardness transfers to widened public augmented CircLWE through
any checked scalar candidate reduction and the exact KSK completion adapter. -/
theorem publicHardAgainst_of_search
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
      ringEta keySwitchEta : ℕ}
    [NeZero q]
    (inputErrorSampler : ProbComp (ZMod q))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reduction : ScalarSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount ringEta keySwitchEta inputErrorSampler
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (decisionAllowed : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) → Prop)
    (solverAllowed : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : LWE.AuxiliaryInput.SearchToDecision.RealSearchHardAgainst
      (problem (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount)
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        inputErrorSampler tgswGadget keySwitchGadget)
      solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed ((reduction.toPairedSecretReduction level hmargin).toSolver
        distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      (reduction.toPairedSecretReduction level hmargin).loss distinguisher ≤ lossBound) :
    LWE.AuxiliaryInput.SearchToDecision.PublicHardAgainst
      (KeySwitchFirstFiniteView.augmentedCircularProblem
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) targetRingErrorSampler
        targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
      decisionAllowed (searchBound + lossBound) :=
  LWE.AuxiliaryInput.SearchToDecision.publicHardAgainst_of_crossReduction
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) targetRingErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (problem (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount)
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      inputErrorSampler tgswGadget keySwitchGadget)
    (reduction.toPairedSecretReduction level hmargin)
    decisionAllowed solverAllowed searchBound lossBound hSearch hClosed hLoss

end ScalarSecretReduction

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery
