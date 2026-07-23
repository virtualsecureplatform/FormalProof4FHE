/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeShiftedResidualBounds

/-!
# Independent-Difference Coins for the Native Shifted Evaluator

The shifted CMux samples a uniformly random true-branch BRK and digitizes its difference from the
public source BRK.  Translation in the finite additive BRK space is a permutation.  Consequently
that difference can be sampled as a fresh uniform BRK independently of the source and the true
branch can be reconstructed by adding the source back.

This reparameterization separates the source-row error retained by the correct branch from the
independent digit/control perturbation.  The only self-correlation left in the complete BRK is the
selected control coordinate, which is the precise normal-form boundary for subsequent work.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree ringRank levels lweDimension : ℕ}

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Reconstruct a true branch by adding an independently sampled difference to the source. -/
noncomputable def addDifference
    (source difference : BootstrappingKey q (degree + 1) ringRank levels lweDimension) :
    BootstrappingKey q (degree + 1) ringRank levels lweDimension :=
  fun coordinate => TGSW.add (difference coordinate) (source coordinate)

/-- Translate a true branch to its componentwise difference from the source BRK. -/
noncomputable def differenceFromSource
    (source trueBranch : BootstrappingKey q (degree + 1) ringRank levels lweDimension) :
    BootstrappingKey q (degree + 1) ringRank levels lweDimension :=
  fun coordinate => TGSW.sub (trueBranch coordinate) (source coordinate)

@[simp]
theorem differenceFromSource_addDifference
    (source difference : BootstrappingKey q (degree + 1) ringRank levels lweDimension) :
    differenceFromSource source (addDifference source difference) = difference := by
  funext coordinate
  apply Prod.ext
  · funext component row
    change (difference coordinate).1 component row +
        (source coordinate).1 component row -
        (source coordinate).1 component row =
      (difference coordinate).1 component row
    exact add_sub_cancel_right _ _
  · funext row
    change (difference coordinate).2 row + (source coordinate).2 row -
        (source coordinate).2 row = (difference coordinate).2 row
    exact add_sub_cancel_right _ _

@[simp]
theorem addDifference_differenceFromSource
    (source trueBranch : BootstrappingKey q (degree + 1) ringRank levels lweDimension) :
    addDifference source (differenceFromSource source trueBranch) = trueBranch := by
  funext coordinate
  apply Prod.ext
  · funext component row
    change (trueBranch coordinate).1 component row -
        (source coordinate).1 component row +
        (source coordinate).1 component row =
      (trueBranch coordinate).1 component row
    exact sub_add_cancel _ _
  · funext row
    change (trueBranch coordinate).2 row - (source coordinate).2 row +
        (source coordinate).2 row = (trueBranch coordinate).2 row
    exact sub_add_cancel _ _

/-- Translation by one fixed source, packaged as an equivalence of complete BRKs. -/
noncomputable def differenceEquiv
    (source : BootstrappingKey q (degree + 1) ringRank levels lweDimension) :
    BootstrappingKey q (degree + 1) ringRank levels lweDimension ≃
      BootstrappingKey q (degree + 1) ringRank levels lweDimension where
  toFun := differenceFromSource source
  invFun := addDifference source
  left_inv := addDifference_differenceFromSource source
  right_inv := differenceFromSource_addDifference source

/-- The difference between a uniform true branch and any fixed source is exactly uniform. -/
theorem differenceFromSource_uniform_evalDist [NeZero q]
    (source : BootstrappingKey q (degree + 1) ringRank levels lweDimension) :
    evalDist (differenceFromSource source <$>
        ($ᵗ BootstrappingKey q (degree + 1) ringRank levels lweDimension)) =
      evalDist ($ᵗ BootstrappingKey q (degree + 1) ringRank levels lweDimension) :=
  evalDist_map_bijective_uniform_cross
    (α := BootstrappingKey q (degree + 1) ringRank levels lweDimension)
    (β := BootstrappingKey q (degree + 1) ringRank levels lweDimension)
    (differenceFromSource source) (differenceEquiv source).bijective

/-- Conversely, adding one fixed source to a uniform independent difference reconstructs an
exactly uniform true branch. -/
theorem addDifference_uniform_evalDist [NeZero q]
    (source : BootstrappingKey q (degree + 1) ringRank levels lweDimension) :
    evalDist (addDifference source <$>
        ($ᵗ BootstrappingKey q (degree + 1) ringRank levels lweDimension)) =
      evalDist ($ᵗ BootstrappingKey q (degree + 1) ringRank levels lweDimension) :=
  evalDist_map_bijective_uniform_cross
    (α := BootstrappingKey q (degree + 1) ringRank levels lweDimension)
    (β := BootstrappingKey q (degree + 1) ringRank levels lweDimension)
    (addDifference source) (differenceEquiv source).symm.bijective

/-- Averaging over any source sampler preserves the exact factorization into the same source and
an independent uniform difference BRK. -/
theorem source_trueBranch_to_independentDifference_evalDist [NeZero q]
    (sourceSampler :
      ProbComp (BootstrappingKey q (degree + 1) ringRank levels lweDimension)) :
    evalDist (do
        let source ← sourceSampler
        let trueBranch ← $ᵗ BootstrappingKey q (degree + 1) ringRank levels lweDimension
        return (source, differenceFromSource source trueBranch)) =
      evalDist (do
        let source ← sourceSampler
        let difference ← $ᵗ BootstrappingKey q (degree + 1) ringRank levels lweDimension
        return (source, difference)) := by
  refine evalDist_bind_congr' sourceSampler fun source => ?_
  simpa only [map_eq_bind_pure_comp, Function.comp_apply, Function.comp_def,
    bind_assoc, pure_bind] using
    (evalDist_map_eq_of_evalDist_eq
      (differenceFromSource_uniform_evalDist source)
      (fun difference => (source, difference)))

/-- Under the independent-difference parametrization, the concrete digitizer sees exactly the
supplied difference row, with no remaining source dependence. -/
theorem differenceDigits_addDifference
    (params : Gadget.Base.Parameters q)
    (source difference :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (coordinate : Fin lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    differenceDigits params (addDifference source difference coordinate)
        (source coordinate) row =
      Gadget.Base.ringExtendedDigits params
        (TLWE.entry (difference coordinate) row) := by
  apply congrArg (Gadget.Base.ringExtendedDigits params)
  apply congrArg₂ TLWE.Ciphertext.mk
  · funext component
    change (difference coordinate).1 component row +
        (source coordinate).1 component row -
        (source coordinate).1 component row =
      (difference coordinate).1 component row
    exact add_sub_cancel_right _ _
  · change (difference coordinate).2 row + (source coordinate).2 row -
        (source coordinate).2 row = (difference coordinate).2 row
    exact add_sub_cancel_right _ _

/-- The additional correct-branch perturbation after retaining the source row error as the base
noise.  Its digit input is the independent uniform difference BRK, while its zero-message control
uses only the selected source coordinate. -/
noncomputable def independentControlResidual
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate : Fin lweDimension)
    (source difference :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :
    Fin lweDimension → Fin (TGSW.rowCount ringRank params.levels) →
      RLWE.Rq q (degree + 1) :=
  fun outputCoordinate row =>
    TGSW.externalProductError secret (Gadget.Base.ringGadget params) proofZero
      (Gadget.Base.ringExtendedDigits params
        (TLWE.entry (difference outputCoordinate) row))
      (candidateControl params (hidden coordinate) (source coordinate))

/-- Under the independent-difference coins, the old complete residual splits exactly into the
retained source-row error and `independentControlResidual`. -/
theorem correctBootstrappingResidual_addDifference_eq_sourceError_add_controlResidual
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source difference :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    correctBootstrappingResidual params secret hidden coordinate source
        (addDifference source difference) outputCoordinate (finProdFinEquiv index) =
      proofAdd
        (TGSW.rowError secret (Gadget.Base.ringGadget params)
          (embedBit (hidden outputCoordinate)) (source outputCoordinate) index)
        (independentControlResidual params secret hidden coordinate source difference
          outputCoordinate (finProdFinEquiv index)) := by
  rw [correctBootstrappingResidual_eq_rowError_add_externalProductError]
  unfold independentControlResidual
  rw [differenceDigits_addDifference]

/-- Worst-case norm budget for only the independent zero-control perturbation, excluding the
retained source-row error. -/
def independentControlResidualBound {q : ℕ} (params : Gadget.Base.Parameters q)
    (ringDegree ringRank eta : ℕ) : ℕ :=
  ((ringRank + 1) * params.levels) *
    ((ringDegree * ringDegree) * ((params.base - 1) * eta))

/-- Centered-binomial support at the selected source coordinate bounds the independent control
perturbation without charging the retained output row a second time. -/
theorem cInfNorm_independentControlResidual_le
    {eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source difference :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (hsource : ∀ index : Fin (ringRank + 1) × Fin params.levels,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params) (embedBit (hidden coordinate))
          (source coordinate) index) ≤ eta) :
    LatticeCrypto.cInfNorm
        (independentControlResidual params secret hidden coordinate source difference
          outputCoordinate row) ≤
      independentControlResidualBound params (degree + 1) ringRank eta := by
  unfold independentControlResidual independentControlResidualBound
  apply NoiseBounds.cInfNorm_externalProductError_ringDigits_le
  exact ShiftedResidualBounds.cInfNorm_candidateControl_correct_le
    params secret hidden coordinate source hsource

/-- Complete-ciphertext correct endpoint with the independent difference exposed explicitly.
Every nonselected source entry is now visibly a retained source ciphertext plus a perturbation
whose gadget digits are sampled independently of the entire source BRK. -/
theorem selectBootstrappingKey_correct_ciphertext_addDifference
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source difference :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :
    selectBootstrappingKey params coordinate (hidden coordinate) source
        (addDifference source difference) outputCoordinate =
      addInternalProduct params (source outputCoordinate)
        (fun row => Gadget.Base.ringExtendedDigits params
          (TLWE.entry (difference outputCoordinate) row))
        (candidateHomogeneousPart params proofZero
          (hidden coordinate) (source coordinate)) := by
  rw [selectBootstrappingKey_correct_ciphertext]
  congr 1
  funext row
  exact differenceDigits_addDifference params source difference outputCoordinate row

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator
