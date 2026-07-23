/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.TFHE.Basic

/-!
# Conditional Body-Noise Smudging for Native TFHE Rows

The CircLWE search-to-decision construction must add wide noise *after the supplied public view
has been fixed*.  This file proves that native TLWE/TGSW body smudging has exactly the required
conditional form.

For a fixed mask, message, and residual vector `r`, adding an independent wide error vector `e`
to the bodies changes the error from `r` to `r + e`.  Data processing therefore bounds the
ciphertext distance by the translation distance between `r + e` and `e`.  When the wide errors
are sampled independently, the vector cost is at most the sum of the scalar translation costs.
The same statement is then lifted through fresh uniform mask sampling and specialized to the
direct-row presentation of a native TGSW ciphertext.

These theorems are pointwise in `r`; they do not average over a hidden source error.  They accept
any executable finite sampler, including centered-binomial samplers and certified finite
approximations to a modular discrete Gaussian.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.TLWE

/-- Add public noise to the body of one TLWE row, leaving its mask unchanged. -/
def addBodyNoise {R : Type} [Add R] {dimension : ℕ}
    (noise : R) (ciphertext : Ciphertext R dimension) : Ciphertext R dimension :=
  ⟨ciphertext.mask, ciphertext.body + noise⟩

@[simp]
theorem addBodyNoise_mask {R : Type} [Add R] {dimension : ℕ}
    (noise : R) (ciphertext : Ciphertext R dimension) :
    (addBodyNoise noise ciphertext).mask = ciphertext.mask :=
  rfl

@[simp]
theorem addBodyNoise_body {R : Type} [Add R] {dimension : ℕ}
    (noise : R) (ciphertext : Ciphertext R dimension) :
    (addBodyNoise noise ciphertext).body = ciphertext.body + noise :=
  rfl

/-- Body-noise addition translates the TLWE phase by exactly the added noise. -/
@[simp]
theorem phase_addBodyNoise {R : Type} [Ring R] {dimension : ℕ}
    (secret : Fin dimension → R) (noise : R) (ciphertext : Ciphertext R dimension) :
    phase secret (addBodyNoise noise ciphertext) = phase secret ciphertext + noise := by
  simp only [phase, addBodyNoise]
  abel

/-- Adding body noise to an assembled row adds it to the existing residual error. -/
theorem addBodyNoise_assemble {R : Type} [Semiring R] {dimension : ℕ}
    (secret mask : Fin dimension → R) (message residual noise : R) :
    addBodyNoise noise (assemble secret mask message residual) =
      assemble secret mask message (residual + noise) := by
  simp only [addBodyNoise, assemble]
  apply congrArg (fun body ↦ (⟨mask, body⟩ : Ciphertext R dimension))
  ac_rfl

/-- Add a vector of public noises to the bodies of a TLWE batch. -/
def addBatchBodyNoise {R : Type} [Add R] {dimension samples : ℕ}
    (noise : Fin samples → R) (ciphertext : BatchCiphertext R dimension samples) :
    BatchCiphertext R dimension samples :=
  (ciphertext.1, ciphertext.2 + noise)

@[simp]
theorem addBatchBodyNoise_fst {R : Type} [Add R] {dimension samples : ℕ}
    (noise : Fin samples → R) (ciphertext : BatchCiphertext R dimension samples) :
    (addBatchBodyNoise noise ciphertext).1 = ciphertext.1 :=
  rfl

@[simp]
theorem addBatchBodyNoise_snd {R : Type} [Add R] {dimension samples : ℕ}
    (noise : Fin samples → R) (ciphertext : BatchCiphertext R dimension samples) :
    (addBatchBodyNoise noise ciphertext).2 = ciphertext.2 + noise :=
  rfl

/-- Batch body-noise addition translates every TLWE phase coordinate. -/
@[simp]
theorem batchPhase_addBatchBodyNoise {R : Type} [Ring R] {dimension samples : ℕ}
    (secret : Fin dimension → R) (noise : Fin samples → R)
    (ciphertext : BatchCiphertext R dimension samples) :
    batchPhase secret (addBatchBodyNoise noise ciphertext) =
      batchPhase secret ciphertext + noise := by
  funext sample
  simp only [batchPhase, addBatchBodyNoise, Pi.sub_apply, Pi.add_apply]
  abel

/-- Adding body noise to an assembled batch adds it to the fixed residual vector. -/
theorem addBatchBodyNoise_batchAssemble {R : Type} [Semiring R]
    {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message residual noise : Fin samples → R) :
    addBatchBodyNoise noise (batchAssemble secret challenge message residual) =
      batchAssemble secret challenge message (residual + noise) := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [addBatchBodyNoise, batchAssemble, Pi.add_apply]
    ac_rfl

/-- Fixed body-noise addition is a permutation of the complete public batch transcript. -/
theorem addBatchBodyNoise_bijective {R : Type} [AddGroup R]
    {dimension samples : ℕ} (noise : Fin samples → R) :
    Function.Bijective
      (addBatchBodyNoise (dimension := dimension) noise) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨addBatchBodyNoise (-noise), ?_, ?_⟩
  · intro ciphertext
    apply Prod.ext
    · rfl
    · funext sample
      simp [addBatchBodyNoise]
  · intro ciphertext
    apply Prod.ext
    · rfl
    · funext sample
      simp [addBatchBodyNoise]

/-- Consequently, adding any fixed body-noise vector to a uniformly sampled public batch leaves
the complete batch exactly uniform. -/
theorem addBatchBodyNoise_uniform_evalDist {R : Type}
    [AddGroup R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ} (noise : Fin samples → R) :
    evalDist
        (addBatchBodyNoise (dimension := dimension) noise <$>
          ($ᵗ (BatchCiphertext R dimension samples))) =
      evalDist ($ᵗ (BatchCiphertext R dimension samples)) :=
  evalDist_map_bijective_uniform_cross
    (α := BatchCiphertext R dimension samples)
    (β := BatchCiphertext R dimension samples)
    (addBatchBodyNoise (dimension := dimension) noise)
    (addBatchBodyNoise_bijective (dimension := dimension) noise)

/-- Even after mixing over arbitrary independent smudging noise, a fresh uniform batch remains
exactly uniform. -/
theorem smudge_uniformBatch_evalDist {R : Type}
    [AddGroup R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ} (wideNoise : ProbComp (Fin samples → R)) :
    evalDist (do
        let noise ← wideNoise
        let ciphertext ← $ᵗ (BatchCiphertext R dimension samples)
        return addBatchBodyNoise noise ciphertext) =
      evalDist ($ᵗ (BatchCiphertext R dimension samples)) := by
  calc
    _ = evalDist (wideNoise >>= fun _noise ↦
          ($ᵗ (BatchCiphertext R dimension samples))) := by
      refine evalDist_bind_congr' wideNoise fun noise ↦ ?_
      rw [show (do
          let ciphertext ← $ᵗ (BatchCiphertext R dimension samples)
          pure (addBatchBodyNoise noise ciphertext)) =
            addBatchBodyNoise (dimension := dimension) noise <$>
              ($ᵗ (BatchCiphertext R dimension samples)) by
        simp [map_eq_bind_pure_comp]]
      exact addBatchBodyNoise_uniform_evalDist
        (dimension := dimension) noise
    _ = _ := by
      apply evalDist_ext
      intro ciphertext
      rw [probOutput_bind_const]
      simp

/-- Add freshly sampled body noise to a fixed native TLWE batch. -/
def smudgeBatchBodies {R : Type} [Add R] {dimension samples : ℕ}
    (wideNoise : ProbComp (Fin samples → R))
    (ciphertext : BatchCiphertext R dimension samples) :
    ProbComp (BatchCiphertext R dimension samples) :=
  (fun noise ↦ addBatchBodyNoise noise ciphertext) <$> wideNoise

/-- On an assembled batch, executable body smudging is exactly residual-plus-wide noise. -/
theorem smudgeBatchBodies_batchAssemble {R : Type} [Semiring R]
    {dimension samples : ℕ}
    (wideNoise : ProbComp (Fin samples → R))
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message residual : Fin samples → R) :
    smudgeBatchBodies wideNoise (batchAssemble secret challenge message residual) =
      (fun noise ↦ batchAssemble secret challenge message (residual + noise)) <$>
        wideNoise := by
  unfold smudgeBatchBodies
  congr 1
  funext noise
  exact addBatchBodyNoise_batchAssemble secret challenge message residual noise

/-- A fixed-mask residual view obtained by adding wide noise to a fixed residual vector. -/
def fixedMaskResidualView {R : Type} [Semiring R] {dimension samples : ℕ}
    (wideNoise : ProbComp (Fin samples → R))
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message residual : Fin samples → R) :
    ProbComp (BatchCiphertext R dimension samples) :=
  (fun noise ↦ batchAssemble secret challenge message (residual + noise)) <$> wideNoise

/-- The corresponding fixed-mask target view with no pre-existing residual. -/
def fixedMaskWideView {R : Type} [Semiring R] {dimension samples : ℕ}
    (wideNoise : ProbComp (Fin samples → R))
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message : Fin samples → R) :
    ProbComp (BatchCiphertext R dimension samples) :=
  (fun noise ↦ batchAssemble secret challenge message noise) <$> wideNoise

/-- Conditional data processing: once mask, message, and residual have been fixed, ciphertext
distance is no larger than the translation distance of the wide error vector. -/
theorem tvDist_fixedMaskResidualView_wideView_le {R : Type} [Semiring R]
    {dimension samples : ℕ}
    (wideNoise : ProbComp (Fin samples → R))
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message residual : Fin samples → R) :
    tvDist
        (fixedMaskResidualView wideNoise secret challenge message residual)
        (fixedMaskWideView wideNoise secret challenge message) ≤
      tvDist ((fun noise ↦ residual + noise) <$> wideNoise) wideNoise := by
  simpa only [fixedMaskResidualView, fixedMaskWideView, Functor.map_map,
      Function.comp_apply] using
    (tvDist_map_le (m := ProbComp)
      (fun error ↦ batchAssemble secret challenge message error)
      ((fun noise ↦ residual + noise) <$> wideNoise) wideNoise)

/-- For independent scalar wide errors, the conditional batch-smudging cost is at most the sum
of the scalar translation costs of all fixed residual coordinates. -/
theorem tvDist_fixedMaskResidualView_sampleIID_le_sum
    {R : Type} [Finite R] [Semiring R] {dimension samples : ℕ}
    (wideNoise : ProbComp R)
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message residual : Fin samples → R) :
    tvDist
        (fixedMaskResidualView (ProbComp.sampleIID samples wideNoise)
          secret challenge message residual)
        (fixedMaskWideView (ProbComp.sampleIID samples wideNoise)
          secret challenge message) ≤
      ∑ sample, FormalProof4FHE.FiniteProduct.addShiftDistance
        wideNoise (residual sample) :=
  (tvDist_fixedMaskResidualView_wideView_le
      (ProbComp.sampleIID samples wideNoise) secret challenge message residual).trans
    (FormalProof4FHE.FiniteProduct.tvDist_add_fin_mOfFn_le_sum
      samples wideNoise residual)

/-- Fresh-mask TLWE batch sampling with a fixed residual added before the wide error. -/
def batchEncryptWithResidual {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ) (wideNoise : ProbComp R)
    (secret : Fin dimension → R) (message residual : Fin samples → R) :
    ProbComp (BatchCiphertext R dimension samples) := do
  let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
  let noise ← ProbComp.sampleIID samples wideNoise
  return batchAssemble secret challenge message (residual + noise)

/-- The pointwise smudging bound survives fresh uniform mask sampling. -/
theorem tvDist_batchEncryptWithResidual_batchEncrypt_le_sum
    {R : Type} [Fintype R] [DecidableEq R] [Semiring R] [SampleableType R]
    (dimension samples : ℕ) (wideNoise : ProbComp R)
    (secret : Fin dimension → R) (message residual : Fin samples → R) :
    tvDist
        (batchEncryptWithResidual dimension samples wideNoise secret message residual)
        (batchEncrypt dimension samples wideNoise secret message) ≤
      ∑ sample, FormalProof4FHE.FiniteProduct.addShiftDistance
        wideNoise (residual sample) := by
  let challenges : ProbComp (Matrix (Fin dimension) (Fin samples) R) :=
    $ᵗ Matrix (Fin dimension) (Fin samples) R
  let noises : ProbComp (Fin samples → R) :=
    ProbComp.sampleIID samples wideNoise
  let residualFinish := fun challenge ↦
    (fun noise ↦ batchAssemble secret challenge message (residual + noise)) <$> noises
  let wideFinish := fun challenge ↦
    (fun noise ↦ batchAssemble secret challenge message noise) <$> noises
  have hbound : tvDist
      (challenges >>= residualFinish) (challenges >>= wideFinish) ≤
        ∑ sample, FormalProof4FHE.FiniteProduct.addShiftDistance
          wideNoise (residual sample) := by
    apply tvDist_bind_left_le_const'
    intro challenge
    exact tvDist_fixedMaskResidualView_sampleIID_le_sum
      wideNoise secret challenge message residual
  simpa [batchEncryptWithResidual, batchEncrypt, challenges, noises,
      residualFinish, wideFinish, map_eq_bind_pure_comp, monad_norm] using hbound

end FormalProof4FHE.TFHE.TLWE

namespace FormalProof4FHE.TFHE.TGSW

/-- Direct native TGSW rows with a fixed evaluator residual added before fresh wide noise. -/
def directEncryptWithResidual {R : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (wideNoise : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (residual : Fin (rowCount dimension levels) → R) :
    ProbComp (Ciphertext R dimension levels) :=
  TLWE.batchEncryptWithResidual dimension (rowCount dimension levels) wideNoise secret
    (gadgetPhase secret gadget message) residual

/-- Conditional smudging for one direct-row native TGSW ciphertext. -/
theorem tvDist_directEncryptWithResidual_directEncrypt_le_sum
    {R : Type} [Fintype R] [DecidableEq R] [Ring R] [SampleableType R]
    (dimension levels : ℕ) (wideNoise : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (residual : Fin (rowCount dimension levels) → R) :
    tvDist
        (directEncryptWithResidual dimension levels wideNoise secret gadget message residual)
        (TLWE.batchEncrypt dimension (rowCount dimension levels) wideNoise secret
          (gadgetPhase secret gadget message)) ≤
      ∑ row, FormalProof4FHE.FiniteProduct.addShiftDistance
        wideNoise (residual row) :=
  TLWE.tvDist_batchEncryptWithResidual_batchEncrypt_le_sum
    dimension (rowCount dimension levels) wideNoise secret
      (gadgetPhase secret gadget message) residual

end FormalProof4FHE.TFHE.TGSW
