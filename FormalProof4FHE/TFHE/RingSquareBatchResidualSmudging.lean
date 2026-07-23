/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareResidualSmudging

/-!
# Full-Batch Residual Smudging for `RGSW_S(-S)`

This file lifts the one-row compiler residual law to the complete stripped rank-one RGSW
matrix.  Only upper square rows are translated; lower zero rows have zero shift.  Finite-product
hybridization bounds the full ciphertext distance by the sum of the upper-row additive shift
distances.  Hidden shared compiler contexts preserve this bound, which is then connected to the
named genuine-RGSW distribution gap and the final ordinary batch-RLWE reduction.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BatchResidualSmudging

noncomputable section

/-- Put one compiler residual in every upper square row and zero in every lower row. -/
def upperShiftVector {R : Type} [Zero R] {levels : ℕ}
    (shift : Fin levels → R) : Fin (TGSW.rowCount 1 levels) → R :=
  fun row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then shift indexed.2 else 0

@[simp]
theorem upperShiftVector_upper {R : Type} [Zero R] {levels : ℕ}
    (shift : Fin levels → R) (level : Fin levels) :
    upperShiftVector shift (Full.upperRow level) = shift level := by
  simp [upperShiftVector]

@[simp]
theorem upperShiftVector_lower {R : Type} [Zero R] {levels : ℕ}
    (shift : Fin levels → R) (level : Fin levels) :
    upperShiftVector shift (Full.lowerRow level) = 0 := by
  simp [upperShiftVector]

/-- Summing over the complete rank-one row layout counts every upper shift exactly once; all
lower-row terms vanish. -/
theorem sum_addShiftDistance_upperShiftVector_eq
    {R : Type} [AddCommGroup R] {levels : ℕ}
    (errorSampler : ProbComp R) (shift : Fin levels → R) :
    (∑ row : Fin (TGSW.rowCount 1 levels),
      FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
        (upperShiftVector shift row)) =
      ∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler (shift level) := by
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_two]
  have hUpper :
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (upperShiftVector shift (finProdFinEquiv ((0 : Fin 2), level)))) =
        ∑ level : Fin levels,
          FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler (shift level) := by
    apply Finset.sum_congr rfl
    intro level _
    rw [show finProdFinEquiv ((0 : Fin 2), level) = Full.upperRow level by rfl,
      upperShiftVector_upper]
  have hLower :
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (upperShiftVector shift (finProdFinEquiv ((1 : Fin 2), level)))) = 0 := by
    apply Finset.sum_eq_zero
    intro level _
    rw [show finProdFinEquiv ((1 : Fin 2), level) = Full.lowerRow level by rfl,
      upperShiftVector_lower,
      FormalProof4FHE.FiniteProduct.addShiftDistance_zero]
  rw [hUpper, hLower, add_zero]

/-- Independently sample all target errors, then translate only the upper coordinates. -/
def shiftedBatchErrorSampler {R : Type} [Add R] [Zero R] (levels : ℕ)
    (errorSampler : ProbComp R) (shift : Fin levels → R) :
    ProbComp (Fin (TGSW.rowCount 1 levels) → R) :=
  (fun error row ↦ upperShiftVector shift row + error row) <$>
    ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler

/-- A fixed-secret square/zero batch with translated upper-row errors. -/
def fixedSecretShiftedSquareBatchSampler
    {R : Type} [CommRing R] [SampleableType R]
    (levels : ℕ) (secret : Fin 1 → R) (errorSampler : ProbComp R)
    (gadget shift : Fin levels → R) : ProbComp (Full.TargetBatch R levels) := do
  let challenge ← $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R
  let error ← shiftedBatchErrorSampler levels errorSampler shift
  return TLWE.batchAssemble secret challenge (Full.squareMessages secret gadget) error

/-- The corresponding fixed-secret native square/zero batch. -/
def fixedSecretSquareBatchSampler
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secret : Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) : ProbComp (Full.TargetBatch R levels) :=
  TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler secret
    (Full.squareMessages secret gadget)

/-- The full ciphertext distance is at most the sum of the upper-coordinate translation costs. -/
theorem tvDist_fixedSecretShiftedSquareBatchSampler_le_sum
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secret : Fin 1 → R) (errorSampler : ProbComp R)
    (gadget shift : Fin levels → R) :
    tvDist
        (fixedSecretShiftedSquareBatchSampler levels secret errorSampler gadget shift)
        (fixedSecretSquareBatchSampler levels secret errorSampler gadget) ≤
      ∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler (shift level) := by
  unfold fixedSecretShiftedSquareBatchSampler fixedSecretSquareBatchSampler
    TLWE.batchEncrypt
  apply tvDist_bind_left_le_const'
  intro challenge
  let assemble := fun error ↦
    TLWE.batchAssemble secret challenge (Full.squareMessages secret gadget) error
  calc
    tvDist
        (shiftedBatchErrorSampler levels errorSampler shift >>=
          pure ∘ assemble)
        (ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler >>=
          pure ∘ assemble) =
      tvDist
        (assemble <$> shiftedBatchErrorSampler levels errorSampler shift)
        (assemble <$> ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler) := by
          simp [assemble, monad_norm]
    _ ≤ tvDist
        (shiftedBatchErrorSampler levels errorSampler shift)
        (ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler) :=
      tvDist_map_le (m := ProbComp) assemble _ _
    _ ≤ ∑ row : Fin (TGSW.rowCount 1 levels),
          FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
            (upperShiftVector shift row) := by
      unfold shiftedBatchErrorSampler ProbComp.sampleIID
      exact FormalProof4FHE.FiniteProduct.tvDist_add_fin_mOfFn_le_sum
        (TGSW.rowCount 1 levels) errorSampler (upperShiftVector shift)
    _ = ∑ level : Fin levels,
          FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler (shift level) :=
      sum_addShiftDistance_upperShiftVector_eq errorSampler shift

/-- Hidden shared compiler context lifts the same full-batch bound. -/
theorem tvDist_contextualShiftedSquareBatches_le
    {R Context : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (contextSampler : ProbComp Context)
    (secret : Context → Fin 1 → R) (shift : Context → Fin levels → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R) (bound : ℝ)
    (hShift : ∀ context, context ∈ support contextSampler →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (shift context level)) ≤ bound) :
    tvDist
        (contextSampler >>= fun context ↦
          fixedSecretShiftedSquareBatchSampler levels (secret context)
            errorSampler gadget (shift context))
        (contextSampler >>= fun context ↦
          fixedSecretSquareBatchSampler levels (secret context) errorSampler gadget) ≤
      bound := by
  apply tvDist_bind_left_le_const
  intro context hcontext
  exact
    (tvDist_fixedSecretShiftedSquareBatchSampler_le_sum levels
      (secret context) errorSampler gadget (shift context)).trans
      (hShift context hcontext)

/-- Contextual normal forms turn the full native compiler gap into the explicit shift sum. -/
theorem nativeDistributionGap_le_of_contextual_normalForms
    {R Secret Context : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Full.Selectors R levels sourceCount)
    (contextSampler : ProbComp Context)
    (contextSecret : Context → Fin 1 → R)
    (contextShift : Context → Fin levels → R) (bound : ℝ)
    (hNative :
      evalDist
          (Full.nativeSquareBatchSampler levels secretSampler embed errorSampler gadget) =
        evalDist
          (contextSampler >>= fun context ↦
            fixedSecretSquareBatchSampler levels (contextSecret context)
              errorSampler gadget))
    (hCompiled :
      evalDist
          (Full.compiledBatchSampler levels sourceCount secretSampler embed errorSampler
            selectors) =
        evalDist
          (contextSampler >>= fun context ↦
            fixedSecretShiftedSquareBatchSampler levels (contextSecret context)
              errorSampler gadget (contextShift context)))
    (hShift : ∀ context, context ∈ support contextSampler →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (contextShift context level)) ≤ bound) :
    Full.nativeDistributionGap levels sourceCount secretSampler embed errorSampler gadget
      selectors ≤ bound := by
  have hContext := tvDist_contextualShiftedSquareBatches_le levels contextSampler
    contextSecret contextShift errorSampler gadget bound hShift
  unfold Full.nativeDistributionGap tvDist at hContext ⊢
  rw [hNative, hCompiled]
  simpa only [SPMF.tvDist_comm] using hContext

/-- The same bound applies to the genuine stripped `RGSW_S(-S)` distribution gap. -/
theorem actualDistributionGap_le_of_contextual_normalForms
    {R Secret Context : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Full.Selectors R levels sourceCount)
    (contextSampler : ProbComp Context)
    (contextSecret : Context → Fin 1 → R)
    (contextShift : Context → Fin levels → R) (bound : ℝ)
    (hNative :
      evalDist
          (Full.nativeSquareBatchSampler levels secretSampler embed errorSampler gadget) =
        evalDist
          (contextSampler >>= fun context ↦
            fixedSecretSquareBatchSampler levels (contextSecret context)
              errorSampler gadget))
    (hCompiled :
      evalDist
          (Full.compiledBatchSampler levels sourceCount secretSampler embed errorSampler
            selectors) =
        evalDist
          (contextSampler >>= fun context ↦
            fixedSecretShiftedSquareBatchSampler levels (contextSecret context)
              errorSampler gadget (contextShift context)))
    (hShift : ∀ context, context ∈ support contextSampler →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (contextShift context level)) ≤ bound) :
    Full.actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget
      selectors ≤ bound := by
  rw [ActualNormalForm.actualDistributionGap_eq_nativeDistributionGap]
  exact nativeDistributionGap_le_of_contextual_normalForms
    levels sourceCount secretSampler embed errorSampler gadget selectors
    contextSampler contextSecret contextShift bound hNative hCompiled hShift

/-- Standalone circular-RLWE security now has only the explicit residual-shift sum and the
ordinary batch-RLWE advantage. -/
theorem rgswMinusSecretAdvantage_le_contextualSmudging_add_batchLWE
    {R Secret Context : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels)
    (contextSampler : ProbComp Context)
    (contextSecret : Context → Fin 1 → R)
    (contextShift : Context → Fin levels → R) (bound : ℝ)
    (hNative :
      evalDist
          (Full.nativeSquareBatchSampler levels secretSampler embed errorSampler gadget) =
        evalDist
          (contextSampler >>= fun context ↦
            fixedSecretSquareBatchSampler levels (contextSecret context)
              errorSampler gadget))
    (hCompiled :
      evalDist
          (Full.compiledBatchSampler levels sourceCount secretSampler embed errorSampler
            selectors) =
        evalDist
          (contextSampler >>= fun context ↦
            fixedSecretShiftedSquareBatchSampler levels (contextSecret context)
              errorSampler gadget (contextShift context)))
    (hShift : ∀ context, context ∈ support contextSampler →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (contextShift context level)) ≤ bound) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed errorSampler gadget
        distinguisher ≤
      bound +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Full.reduction selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  exact
    (Full.rgswMinusSecretAdvantage_le_actualDistributionGap_add_batchLWE
      levels sourceCount secretSampler embed errorSampler gadget selectors
        distinguisher).trans
      (add_le_add
        (actualDistributionGap_le_of_contextual_normalForms
          levels sourceCount secretSampler embed errorSampler gadget selectors
          contextSampler contextSecret contextShift bound hNative hCompiled hShift)
        le_rfl)

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BatchResidualSmudging
