/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveBRKCircLWE
import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveCircularLWE

set_option autoImplicit false

/-!
# Search Equivalence for the Two Full-Target-Message Circular Games

The BRK-first formulation exposes

`(BRK, (extension, target tape))`,

whereas the direct FHE formulation exposes

`(target tape, (BRK, extension))`.

Their decision endpoints differ, but their honest exact-recovery experiments use the same nested
secret and the same three public objects.  This file proves that the real search distributions
are exactly equal after the public reassociation.  The BRK is additionally changed from the
explicit monomial generator to the honest native generator using the already checked exact
fixed-secret distribution equality.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveBRKCircLWE.SearchEquiv

noncomputable section

/-- The BRK-first complete public search view. -/
abbrev BootstrapFirstView
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  Challenge q degree sourceRank suffixRank tgswLevels ×
    Auxiliary q degree sourceRank suffixRank tgswLevels queryCount

/-- The tape-first complete public search view. -/
abbrev TapeFirstView
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  AdaptiveCircularLWE.Challenge q (degree + 1) sourceRank suffixRank queryCount ×
    AdaptiveCircularLWE.Auxiliary q (degree + 1) sourceRank suffixRank tgswLevels

/-- Public reassociation between the two complete-view layouts. -/
def viewEquiv
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :
    TapeFirstView q degree sourceRank suffixRank tgswLevels queryCount ≃
      BootstrapFirstView q degree sourceRank suffixRank tgswLevels queryCount where
  toFun := fun view ↦ (view.2.1, (view.2.2, view.1))
  invFun := fun view ↦ (view.2.2, (view.1, view.2.1))
  left_inv := by intro view; rfl
  right_inv := by intro view; rfl

/-- Fixed-secret honest view of the explicit monomial BRK-first problem. -/
def sampleBootstrapFirstMonomialView
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (secret : Secret sourceRank suffixRank degree) :
    ProbComp (BootstrapFirstView q degree sourceRank suffixRank tgswLevels queryCount) := do
  let challenge ←
    (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler gadget).sampleReal secret
  let auxiliary ←
    (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler gadget).sampleAuxiliary secret
  return (challenge, auxiliary)

/-- Fixed-secret honest view of the direct tape-first problem. -/
def sampleTapeFirstRealView
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (secret : Secret sourceRank suffixRank degree) :
    ProbComp (TapeFirstView q degree sourceRank suffixRank tgswLevels queryCount) := do
  let challenge ←
    (AdaptiveCircularLWE.problem q (degree + 1) sourceRank suffixRank tgswLevels queryCount
      errorSampler errorSampler (AdaptiveReduction.extractedErrorSampler errorSampler)
      gadget).sampleReal secret
  let auxiliary ←
    (AdaptiveCircularLWE.problem q (degree + 1) sourceRank suffixRank tgswLevels queryCount
      errorSampler errorSampler (AdaptiveReduction.extractedErrorSampler errorSampler)
      gadget).sampleAuxiliary secret
  return (challenge, auxiliary)

/-- For every fixed nested key, the two complete honest public views have identical laws after
the public tuple reassociation. -/
theorem sampleBootstrapFirstMonomialView_evalDist_eq_tapeFirst
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (secret : Secret sourceRank suffixRank degree) :
    evalDist
        (sampleBootstrapFirstMonomialView q degree sourceRank suffixRank tgswLevels
          queryCount errorSampler gadget secret) =
      evalDist
        (viewEquiv q degree sourceRank suffixRank tgswLevels queryCount <$>
          sampleTapeFirstRealView q degree sourceRank suffixRank tgswLevels queryCount
            errorSampler gadget secret) := by
  let MonomialBootstrap :=
    PrefixCircLWE.generateMonomialSourceBootstrappingKey q (degree + 1) sourceRank
      suffixRank tgswLevels errorSampler gadget secret.1 secret.2
  let HonestBootstrap :=
    generateSourceBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels
      errorSampler gadget secret.1 secret.2
  let Extension :=
    generateRingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
      errorSampler gadget secret.1 secret.2
  let Tape :=
    TLWE.batchEncrypt
      (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
      (AdaptiveReduction.extractedErrorSampler errorSampler)
      (embedBinarySecret (targetMessages secret.1 secret.2)) 0
  let Finish := fun
      (bootstrappingKey : Challenge q degree sourceRank suffixRank tgswLevels)
      (extensionKey : RingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels)
      (tape : TLWE.BatchCiphertext (ZMod q)
        (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount) ↦
    (pure (bootstrappingKey, (extensionKey, tape)) :
      ProbComp (BootstrapFirstView q degree sourceRank suffixRank tgswLevels queryCount))
  simp only [sampleBootstrapFirstMonomialView, sampleTapeFirstRealView,
    monomialProblem, problem, AdaptiveCircularLWE.problem, viewEquiv,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  change evalDist (MonomialBootstrap >>= fun bootstrappingKey ↦
      Extension >>= fun extensionKey ↦
      Tape >>= fun tape ↦ Finish bootstrappingKey extensionKey tape) =
    evalDist (Tape >>= fun tape ↦
      HonestBootstrap >>= fun bootstrappingKey ↦
      Extension >>= fun extensionKey ↦ Finish bootstrappingKey extensionKey tape)
  calc
    _ = evalDist (HonestBootstrap >>= fun bootstrappingKey ↦
        Extension >>= fun extensionKey ↦
        Tape >>= fun tape ↦ Finish bootstrappingKey extensionKey tape) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (PrefixCircLWE.generateSourceBootstrappingKey_evalDist_eq_monomial
          q (degree + 1) sourceRank suffixRank tgswLevels errorSampler gadget
          secret.1 secret.2).symm
        (fun bootstrappingKey ↦
          Extension >>= fun extensionKey ↦
          Tape >>= fun tape ↦ Finish bootstrappingKey extensionKey tape)
    _ = evalDist (HonestBootstrap >>= fun bootstrappingKey ↦
        Tape >>= fun tape ↦
        Extension >>= fun extensionKey ↦ Finish bootstrappingKey extensionKey tape) := by
      refine evalDist_bind_congr' HonestBootstrap fun bootstrappingKey ↦ ?_
      exact evalDist_bind_bind_swap Extension Tape
        (fun extensionKey tape ↦ Finish bootstrappingKey extensionKey tape)
    _ = _ :=
      evalDist_bind_bind_swap HonestBootstrap Tape
        (fun bootstrappingKey tape ↦
          Extension >>= fun extensionKey ↦ Finish bootstrappingKey extensionKey tape)

/-! ## Public solver transport -/

/-- Reassociate a BRK-first complete-view solver into the tape-first interface. -/
def toTapeFirstSolver
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ}
    (solver : MonomialSolver q degree sourceRank suffixRank tgswLevels queryCount) :
    AdaptiveCircularLWE.Solver q (degree + 1) sourceRank suffixRank tgswLevels
      queryCount :=
  fun tape auxiliary ↦ solver auxiliary.1 (auxiliary.2, tape)

/-- Reassociate a tape-first complete-view solver into the BRK-first interface. -/
def toBootstrapFirstSolver
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ}
    (solver : AdaptiveCircularLWE.Solver q (degree + 1) sourceRank suffixRank
      tgswLevels queryCount) :
    MonomialSolver q degree sourceRank suffixRank tgswLevels queryCount :=
  fun bootstrappingKey auxiliary ↦
    solver auxiliary.2 (bootstrappingKey, auxiliary.1)

@[simp]
theorem toBootstrapFirstSolver_toTapeFirstSolver
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ}
    (solver : MonomialSolver q degree sourceRank suffixRank tgswLevels queryCount) :
    toBootstrapFirstSolver (toTapeFirstSolver solver) = solver := by
  rfl

@[simp]
theorem toTapeFirstSolver_toBootstrapFirstSolver
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ}
    (solver : AdaptiveCircularLWE.Solver q (degree + 1) sourceRank suffixRank
      tgswLevels queryCount) :
    toTapeFirstSolver (toBootstrapFirstSolver solver) = solver := by
  rfl

/-- The exact nested-key recovery games are distributionally identical under solver
reassociation.  In particular, the BRK-first and tape-first circular formulations do not require
separate honest-search assumptions. -/
theorem monomialSearchGame_evalDist_eq_tapeFirstSearchGame
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (solver : MonomialSolver q degree sourceRank suffixRank tgswLevels queryCount) :
    evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.Search.game
          (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
            errorSampler gadget)
          solver) =
      evalDist
        (FormalProof4FHE.LWE.AuxiliaryInput.Search.game
          (AdaptiveCircularLWE.searchProblem q (degree + 1) sourceRank suffixRank
            tgswLevels queryCount errorSampler errorSampler
            (AdaptiveReduction.extractedErrorSampler errorSampler) gadget)
          (toTapeFirstSolver solver)) := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.Search.game monomialSearchProblem
    AdaptiveCircularLWE.searchProblem
    FormalProof4FHE.LWE.AuxiliaryInput.Search.exactRecoveryProblem
  simp only [monomialProblem, problem, AdaptiveCircularLWE.problem]
  refine evalDist_bind_congr'
    (sampleNestedSecret sourceRank suffixRank (degree + 1)) fun secret ↦ ?_
  let Finish := fun
      (view : BootstrapFirstView q degree sourceRank suffixRank tgswLevels queryCount) ↦
    solver view.1 view.2 >>= fun recovered ↦
      pure (decide (recovered = secret))
  calc
    _ = evalDist
        (sampleBootstrapFirstMonomialView q degree sourceRank suffixRank tgswLevels
          queryCount errorSampler gadget secret >>= Finish) := by
      simp [sampleBootstrapFirstMonomialView, monomialProblem, problem, Finish,
        bind_assoc, monad_norm]
    _ = evalDist
        ((viewEquiv q degree sourceRank suffixRank tgswLevels queryCount <$>
            sampleTapeFirstRealView q degree sourceRank suffixRank tgswLevels queryCount
              errorSampler gadget secret) >>= Finish) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (sampleBootstrapFirstMonomialView_evalDist_eq_tapeFirst q degree sourceRank
          suffixRank tgswLevels queryCount errorSampler gadget secret)
        Finish
    _ = _ := by
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      simp [sampleTapeFirstRealView, AdaptiveCircularLWE.problem, Finish,
        toTapeFirstSolver, viewEquiv, bind_assoc, monad_norm]

/-- Exact recovery success probabilities are equal under the public view reassociation. -/
theorem monomialSearchSuccessProbability_eq_tapeFirst
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (solver : MonomialSolver q degree sourceRank suffixRank tgswLevels queryCount) :
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget)
        solver =
      FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (AdaptiveCircularLWE.searchProblem q (degree + 1) sourceRank suffixRank
          tgswLevels queryCount errorSampler errorSampler
          (AdaptiveReduction.extractedErrorSampler errorSampler) gadget)
        (toTapeFirstSolver solver) := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
  exact congrArg (fun distribution ↦ distribution true)
    (monomialSearchGame_evalDist_eq_tapeFirstSearchGame q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler gadget solver)

/-- The reverse success-probability equality, convenient for tape-first recovery solvers already
constructed elsewhere in the development. -/
theorem tapeFirstSearchSuccessProbability_eq_monomial
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (solver : AdaptiveCircularLWE.Solver q (degree + 1) sourceRank suffixRank
      tgswLevels queryCount) :
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (AdaptiveCircularLWE.searchProblem q (degree + 1) sourceRank suffixRank
          tgswLevels queryCount errorSampler errorSampler
          (AdaptiveReduction.extractedErrorSampler errorSampler) gadget)
        solver =
      FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget)
        (toBootstrapFirstSolver solver) := by
  simpa using
    (monomialSearchSuccessProbability_eq_tapeFirst q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler gadget (toBootstrapFirstSolver solver)).symm

/-- Real-valued search hardness is exactly the same for the two layouts, provided the allowed
solver class is transported by the public reassociation. -/
theorem realSearchHardAgainst_monomial_iff_tapeFirst
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (tapeFirstAllowed :
      AdaptiveCircularLWE.Solver q (degree + 1) sourceRank suffixRank tgswLevels
        queryCount → Prop)
    (bound : ℝ) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.RealSearchHardAgainst
        (monomialSearchProblem q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget)
        (fun solver ↦ tapeFirstAllowed (toTapeFirstSolver solver)) bound ↔
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.RealSearchHardAgainst
        (AdaptiveCircularLWE.searchProblem q (degree + 1) sourceRank suffixRank
          tgswLevels queryCount errorSampler errorSampler
          (AdaptiveReduction.extractedErrorSampler errorSampler) gadget)
        tapeFirstAllowed bound := by
  constructor
  · intro hSearch solver hAllowed
    have h := hSearch (toBootstrapFirstSolver solver) (by simpa using hAllowed)
    rw [monomialSearchSuccessProbability_eq_tapeFirst q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler gadget (toBootstrapFirstSolver solver)] at h
    simpa using h
  · intro hSearch solver hAllowed
    have h := hSearch (toTapeFirstSolver solver) hAllowed
    rw [← monomialSearchSuccessProbability_eq_tapeFirst q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler gadget solver] at h
    exact h

/-! ## Final theorem with the common tape-first recovery problem -/

/-- A widened-decision certificate for the monomial BRK problem whose generated solver is measured
directly in the established tape-first exact-recovery experiment.  The public carriers differ by
reassociation, so this small interface states that heterogeneous layout explicitly. -/
structure CrossDecisionToTapeFirstSearchReduction
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionErrorSampler searchErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1)) where
  toSolver : FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount) →
    AdaptiveCircularLWE.Solver q (degree + 1) sourceRank suffixRank tgswLevels
      queryCount
  loss : FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (Auxiliary q degree sourceRank suffixRank tgswLevels queryCount) → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le : ∀ distinguisher,
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (monomialProblem q degree sourceRank suffixRank tgswLevels queryCount
          decisionErrorSampler gadget)
        distinguisher ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (AdaptiveCircularLWE.searchProblem q (degree + 1) sourceRank suffixRank
          tgswLevels queryCount searchErrorSampler searchErrorSampler
          (AdaptiveReduction.extractedErrorSampler searchErrorSampler) gadget)
        (toSolver distinguisher)).toReal + loss distinguisher

namespace CrossDecisionToTapeFirstSearchReduction

/-- Reassociate the solver generated by an ordinary monomial cross-reduction. -/
def ofMonomial
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionErrorSampler searchErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (reduction : MonomialCrossDecisionToSearchReduction q degree sourceRank suffixRank
      tgswLevels queryCount decisionErrorSampler searchErrorSampler gadget) :
    CrossDecisionToTapeFirstSearchReduction q degree sourceRank suffixRank tgswLevels
      queryCount decisionErrorSampler searchErrorSampler gadget where
  toSolver := fun distinguisher ↦ toTapeFirstSolver (reduction.toSolver distinguisher)
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  advantage_le := by
    intro distinguisher
    have h := reduction.advantage_le distinguisher
    rw [monomialSearchSuccessProbability_eq_tapeFirst q degree sourceRank suffixRank
      tgswLevels queryCount searchErrorSampler gadget
      (reduction.toSolver distinguisher)] at h
    exact h

/-- Reassociate a tape-first-search certificate back into the generic monomial cross-reduction
interface. -/
def toMonomial
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionErrorSampler searchErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (reduction : CrossDecisionToTapeFirstSearchReduction q degree sourceRank suffixRank
      tgswLevels queryCount decisionErrorSampler searchErrorSampler gadget) :
    MonomialCrossDecisionToSearchReduction q degree sourceRank suffixRank tgswLevels
      queryCount decisionErrorSampler searchErrorSampler gadget where
  toSolver := fun distinguisher ↦ toBootstrapFirstSolver (reduction.toSolver distinguisher)
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  advantage_le := by
    intro distinguisher
    have h := reduction.advantage_le distinguisher
    rw [tapeFirstSearchSuccessProbability_eq_monomial q degree sourceRank suffixRank
      tgswLevels queryCount searchErrorSampler gadget
      (reduction.toSolver distinguisher)] at h
    exact h

end CrossDecisionToTapeFirstSearchReduction

/-- **Common-search end-to-end adaptive TFHE security.**

The BRK-first monomial decision hop may now target the same tape-first nested-key recovery problem
used by the direct FHE CircLWE development.  Its explicit reduction loss and one ordinary blocked
module-RLWE advantage are the only other terms. -/
theorem abs_signedAdvantage_realAdaptive_le_tapeFirstSearch_add_reductionLoss_add_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionErrorSampler searchErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount)
    (reduction : CrossDecisionToTapeFirstSearchReduction q degree sourceRank suffixRank
      tgswLevels queryCount decisionErrorSampler searchErrorSampler gadget) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
        decisionErrorSampler decisionErrorSampler
        (AdaptiveReduction.extractedErrorSampler decisionErrorSampler)
        gadget decompose encode adversary)| ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (AdaptiveCircularLWE.searchProblem q (degree + 1) sourceRank suffixRank
          tgswLevels queryCount searchErrorSampler searchErrorSampler
          (AdaptiveReduction.extractedErrorSampler searchErrorSampler) gadget)
        (reduction.toSolver
          (adaptiveDistinguisher decompose encode adversary))).toReal +
        reduction.loss (adaptiveDistinguisher decompose encode adversary) +
        LearningWithErrors.advantage
          (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels
            queryCount decisionErrorSampler)
          (jointZeroReduction gadget
            (resampleBootstrapContinuation
              (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))) := by
  exact
    (abs_signedAdvantage_realAdaptive_le_monomialCircularLwe_add_moduleLwe q degree
      sourceRank suffixRank tgswLevels queryCount decisionErrorSampler gadget decompose
      encode adversary hbound).trans
      (add_le_add
        (by
          simpa [monomialCircularLweAdvantage] using
            (reduction.advantage_le
              (adaptiveDistinguisher decompose encode adversary)))
        (le_refl _))

/-- Tape-first nested-key search hardness, a checked heterogeneous search-to-decision
certificate, and ordinary joint module-RLWE hardness compose into adaptive TFHE security. -/
theorem hardAgainst_of_tapeFirstSearch_reduction_and_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decisionErrorSampler searchErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adaptiveAllowed : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels → Prop)
    (solverAllowed : AdaptiveCircularLWE.Solver q (degree + 1) sourceRank suffixRank
      tgswLevels queryCount → Prop)
    (moduleLweAllowed : LearningWithErrors.Adversary
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        decisionErrorSampler) → Prop)
    (searchBound reductionLossBound moduleLweBound : ℝ)
    (reduction : CrossDecisionToTapeFirstSearchReduction q degree sourceRank suffixRank
      tgswLevels queryCount decisionErrorSampler searchErrorSampler gadget)
    (hSolverClosed : ∀ adversary, adaptiveAllowed adversary →
      solverAllowed
        (reduction.toSolver (adaptiveDistinguisher decompose encode adversary)))
    (hLoss : ∀ adversary, adaptiveAllowed adversary →
      reduction.loss (adaptiveDistinguisher decompose encode adversary) ≤
        reductionLossBound)
    (hModuleLweClosed : ∀ adversary, adaptiveAllowed adversary →
      moduleLweAllowed
        (jointZeroReduction gadget
          (resampleBootstrapContinuation
            (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary))))
    (hSearch :
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.RealSearchHardAgainst
        (AdaptiveCircularLWE.searchProblem q (degree + 1) sourceRank suffixRank
          tgswLevels queryCount searchErrorSampler searchErrorSampler
          (AdaptiveReduction.extractedErrorSampler searchErrorSampler) gadget)
        solverAllowed searchBound)
    (hModuleLwe : FormalProof4FHE.LWE.HardAgainst
      (AdaptiveReduction.problem q degree sourceRank suffixRank tgswLevels queryCount
        decisionErrorSampler)
      moduleLweAllowed moduleLweBound) :
    HardAgainst q degree sourceRank suffixRank tgswLevels queryCount
      decisionErrorSampler gadget decompose encode adaptiveAllowed
      (searchBound + reductionLossBound + moduleLweBound) := by
  intro adversary hAllowed hBound
  exact
    (abs_signedAdvantage_realAdaptive_le_tapeFirstSearch_add_reductionLoss_add_moduleLwe
      q degree sourceRank suffixRank tgswLevels queryCount decisionErrorSampler
      searchErrorSampler gadget decompose encode adversary hBound reduction).trans
      (add_le_add
        (add_le_add
          (hSearch
            (reduction.toSolver (adaptiveDistinguisher decompose encode adversary))
            (hSolverClosed adversary hAllowed))
          (hLoss adversary hAllowed))
        (hModuleLwe
          (jointZeroReduction gadget
            (resampleBootstrapContinuation
              (AdaptiveReduction.adaptiveViewContinuation decompose encode adversary)))
          (hModuleLweClosed adversary hAllowed)))

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveBRKCircLWE.SearchEquiv
