/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleSecretRandomization
import FormalProof4FHE.TFHE.NativeShiftedCandidateEvaluator

set_option autoImplicit false

/-!
# Public Additive Key Shifts for Rank-One Native TGSW

An additive ring-key shift is not by itself a valid transform of a TGSW ciphertext: the mask
gadget rows contain the old secret in their plaintext phase.  In rank one, however, a public row
shear repairs those phases.  For a shift `delta`, the complete public transform is

* ordinary LWE key transport `s ↦ s + delta`; followed by
* the row operation `(row_mask, row_body) ↦ (row_mask - delta * row_body, row_body)`.

The resulting ciphertext has the same TGSW message under `s + delta`.  Its only statistical
defect is the explicit error shear
`(e_mask, e_body) ↦ (e_mask - delta * e_body, e_body)`.

This is the strongest direct analogue of the additive vector-LWE shift used by the PKC 2024
CircLWE framework that preserves native rank-one ring structure.  It does not claim that an
arbitrary binary coefficientwise XOR is an additive ring shift; that identification is valid in
coefficient characteristic two and is false in general.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

noncomputable section

/-! ## Deterministic row shear -/

/-- Error action forced by an additive shift of a rank-one TGSW encryption key. -/
def rankOneAdditiveShiftErrorShear {R : Type} [Ring R] {levels : ℕ}
    (delta : R) (error : Fin (TGSW.rowCount 1 levels) → R) :
    Fin (TGSW.rowCount 1 levels) → R :=
  fun row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then
      error (rankOneMaskRow indexed.2) - delta * error (rankOneBodyRow indexed.2)
    else
      error (rankOneBodyRow indexed.2)

@[simp]
theorem rankOneAdditiveShiftErrorShear_maskRow
    {R : Type} [Ring R] {levels : ℕ} (delta : R)
    (error : Fin (TGSW.rowCount 1 levels) → R) (level : Fin levels) :
    rankOneAdditiveShiftErrorShear delta error (rankOneMaskRow level) =
      error (rankOneMaskRow level) - delta * error (rankOneBodyRow level) := by
  simp [rankOneAdditiveShiftErrorShear, rankOneMaskRow, TGSW.rowIndex]

@[simp]
theorem rankOneAdditiveShiftErrorShear_bodyRow
    {R : Type} [Ring R] {levels : ℕ} (delta : R)
    (error : Fin (TGSW.rowCount 1 levels) → R) (level : Fin levels) :
    rankOneAdditiveShiftErrorShear delta error (rankOneBodyRow level) =
      error (rankOneBodyRow level) := by
  simp [rankOneAdditiveShiftErrorShear, rankOneBodyRow, TGSW.rowIndex]

/-- The inverse error shear is obtained by changing the sign of the public shift. -/
@[simp]
theorem rankOneAdditiveShiftErrorShear_neg
    {R : Type} [Ring R] {levels : ℕ} (delta : R)
    (error : Fin (TGSW.rowCount 1 levels) → R) :
    rankOneAdditiveShiftErrorShear (-delta)
        (rankOneAdditiveShiftErrorShear delta error) = error := by
  classical
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  fin_cases block
  · simp [rankOneAdditiveShiftErrorShear, rankOneMaskRow, rankOneBodyRow,
      TGSW.rowIndex]
  · simp [rankOneAdditiveShiftErrorShear, rankOneBodyRow, TGSW.rowIndex]

/-- The additive key-shift error action is a permutation of the complete row vector. -/
theorem rankOneAdditiveShiftErrorShear_bijective
    {R : Type} [Ring R] {levels : ℕ} (delta : R) :
    Function.Bijective
      (rankOneAdditiveShiftErrorShear delta :
        (Fin (TGSW.rowCount 1 levels) → R) →
          Fin (TGSW.rowCount 1 levels) → R) := by
  apply Function.bijective_iff_has_inverse.mpr
  exact ⟨rankOneAdditiveShiftErrorShear (-delta),
    rankOneAdditiveShiftErrorShear_neg delta,
    by
      intro error
      simpa only [neg_neg] using rankOneAdditiveShiftErrorShear_neg (-delta) error⟩

/-- Challenge-row shear corresponding to the same additive ring-key shift. -/
def rankOneAdditiveShiftChallenge {R : Type} [Ring R] {levels : ℕ}
    (delta : R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R :=
  fun coordinate row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then
      challenge coordinate (rankOneMaskRow indexed.2) -
        delta * challenge coordinate (rankOneBodyRow indexed.2)
    else
      challenge coordinate (rankOneBodyRow indexed.2)

@[simp]
theorem rankOneAdditiveShiftChallenge_neg
    {R : Type} [Ring R] {levels : ℕ} (delta : R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    rankOneAdditiveShiftChallenge (-delta)
        (rankOneAdditiveShiftChallenge delta challenge) = challenge := by
  classical
  funext coordinate row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  fin_cases block
  · simp [rankOneAdditiveShiftChallenge, rankOneMaskRow, rankOneBodyRow,
      TGSW.rowIndex]
  · simp [rankOneAdditiveShiftChallenge, rankOneBodyRow, TGSW.rowIndex]

theorem rankOneAdditiveShiftChallenge_bijective
    {R : Type} [Ring R] {levels : ℕ} (delta : R) :
    Function.Bijective
      (rankOneAdditiveShiftChallenge delta :
        Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R →
          Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) := by
  apply Function.bijective_iff_has_inverse.mpr
  exact ⟨rankOneAdditiveShiftChallenge (-delta),
    rankOneAdditiveShiftChallenge_neg delta,
    by
      intro challenge
      simpa only [neg_neg] using rankOneAdditiveShiftChallenge_neg (-delta) challenge⟩

/-- The row shear preserves the exact uniform TGSW challenge law. -/
theorem rankOneAdditiveShiftChallenge_uniform_evalDist
    {R : Type} [Ring R] [Fintype R] [SampleableType R]
    {levels : ℕ} (delta : R) :
    evalDist (rankOneAdditiveShiftChallenge delta <$>
        ($ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)) =
      evalDist ($ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (β := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (rankOneAdditiveShiftChallenge delta)
    (rankOneAdditiveShiftChallenge_bijective delta)

/-- Shear the two rank-one rows at each gadget level. -/
def rankOneAdditiveShiftRows {R : Type} [Ring R] {levels : ℕ}
    (delta : R) (ciphertext : TGSW.Ciphertext R 1 levels) :
    TGSW.Ciphertext R 1 levels :=
  (rankOneAdditiveShiftChallenge delta ciphertext.1,
    fun row ↦
      let indexed := TGSW.rowIndex row
      if indexed.1 = 0 then
        ciphertext.2 (rankOneMaskRow indexed.2) -
          delta * ciphertext.2 (rankOneBodyRow indexed.2)
      else
        ciphertext.2 (rankOneBodyRow indexed.2))

/-- Row shearing has the expected deterministic effect on an already transported batch. -/
theorem rankOneAdditiveShiftRows_batchAssemble
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (delta : R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (message error : Fin (TGSW.rowCount 1 levels) → R) :
    rankOneAdditiveShiftRows delta
        (TLWE.batchAssemble secret challenge message error) =
      TLWE.batchAssemble secret
        (rankOneAdditiveShiftChallenge delta challenge)
        (fun row ↦
          let indexed := TGSW.rowIndex row
          if indexed.1 = 0 then
            message (rankOneMaskRow indexed.2) -
              delta * message (rankOneBodyRow indexed.2)
          else
            message (rankOneBodyRow indexed.2))
        (rankOneAdditiveShiftErrorShear delta error) := by
  classical
  apply Prod.ext
  · rfl
  · funext row
    by_cases hmask : (TGSW.rowIndex row).1 = 0
    · rw [rankOne_row_eq_maskRow_of_index_eq_zero row hmask]
      simp [rankOneAdditiveShiftRows, rankOneAdditiveShiftChallenge,
        rankOneAdditiveShiftErrorShear, TLWE.batchAssemble,
        Matrix.vecMul, dotProduct]
      ring
    · rw [rankOne_row_eq_bodyRow_of_index_ne_zero row hmask]
      simp [rankOneAdditiveShiftRows, rankOneAdditiveShiftChallenge,
        rankOneAdditiveShiftErrorShear, TLWE.batchAssemble,
        Matrix.vecMul, dotProduct]

/-- After changing `s` to `s + delta`, the row shear converts the old gadget phase into the
gadget phase for the same plaintext under the shifted key. -/
theorem rankOneAdditiveShiftMessage_gadgetPhase
    {R : Type} [CommRing R] {levels : ℕ}
    (secretValue delta message : R) (gadget : Fin levels → R) :
    (fun row : Fin (TGSW.rowCount 1 levels) ↦
      let indexed := TGSW.rowIndex row
      if indexed.1 = 0 then
        TGSW.gadgetPhase (fun _ : Fin 1 ↦ secretValue) gadget message
            (rankOneMaskRow indexed.2) -
          delta * TGSW.gadgetPhase (fun _ : Fin 1 ↦ secretValue) gadget message
            (rankOneBodyRow indexed.2)
      else
        TGSW.gadgetPhase (fun _ : Fin 1 ↦ secretValue) gadget message
          (rankOneBodyRow indexed.2)) =
      TGSW.gadgetPhase (fun _ : Fin 1 ↦ secretValue + delta) gadget message := by
  classical
  funext row
  by_cases hmask : (TGSW.rowIndex row).1 = 0
  · rw [rankOne_row_eq_maskRow_of_index_eq_zero row hmask]
    simp
    ring
  · rw [rankOne_row_eq_bodyRow_of_index_ne_zero row hmask]
    simp

/-- Complete public additive shift of a rank-one native TGSW ciphertext. -/
def additiveShiftTGSW {R : Type} [CommRing R] {levels : ℕ}
    (delta : R) (ciphertext : TGSW.Ciphertext R 1 levels) :
    TGSW.Ciphertext R 1 levels :=
  rankOneAdditiveShiftRows delta
    (additiveTranslateBatch (fun _ ↦ delta) ciphertext)

/-- Exact deterministic normal form of the additive rank-one TGSW key shift. -/
theorem additiveShiftTGSW_batchAssemble
    {R : Type} [CommRing R] {levels : ℕ}
    (secretValue delta message : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (error : Fin (TGSW.rowCount 1 levels) → R) :
    additiveShiftTGSW delta
        (TLWE.batchAssemble (fun _ ↦ secretValue) challenge
          (TGSW.gadgetPhase (fun _ ↦ secretValue) gadget message) error) =
      TLWE.batchAssemble (fun _ ↦ secretValue + delta)
        (rankOneAdditiveShiftChallenge delta challenge)
        (TGSW.gadgetPhase (fun _ ↦ secretValue + delta) gadget message)
        (rankOneAdditiveShiftErrorShear delta error) := by
  unfold additiveShiftTGSW
  rw [additiveTranslateBatch_batchAssemble]
  rw [rankOneAdditiveShiftRows_batchAssemble]
  rw [rankOneAdditiveShiftMessage_gadgetPhase]
  congr 1

/-! ## Distributional laws -/

/-- Exact noise condition for the public additive rank-one TGSW key shift. -/
def RankOneAdditiveShiftNoiseInvariant {R : Type} [Ring R] {levels : ℕ}
    (errorSampler : ProbComp R) (delta : R) : Prop :=
  evalDist (rankOneAdditiveShiftErrorShear delta <$>
      ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler) =
    evalDist (ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler)

/-- Uniform row errors are exactly invariant under every additive key-shift shear. -/
theorem rankOneAdditiveShiftNoiseInvariant_uniform
    {R : Type} [Ring R] [Fintype R] [SampleableType R]
    {levels : ℕ} (delta : R) :
    RankOneAdditiveShiftNoiseInvariant (levels := levels) ($ᵗ R) delta := by
  unfold RankOneAdditiveShiftNoiseInvariant
  calc
    evalDist (rankOneAdditiveShiftErrorShear delta <$>
        ProbComp.sampleIID (TGSW.rowCount 1 levels) ($ᵗ R)) =
      evalDist (rankOneAdditiveShiftErrorShear delta <$>
        ($ᵗ (Fin (TGSW.rowCount 1 levels) → R))) :=
      evalDist_map_eq_of_evalDist_eq
        (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
          (alpha := R) (TGSW.rowCount 1 levels))
        (rankOneAdditiveShiftErrorShear delta)
    _ = evalDist ($ᵗ (Fin (TGSW.rowCount 1 levels) → R)) :=
      evalDist_map_bijective_uniform_cross
        (α := Fin (TGSW.rowCount 1 levels) → R)
        (β := Fin (TGSW.rowCount 1 levels) → R)
        (rankOneAdditiveShiftErrorShear delta)
        (rankOneAdditiveShiftErrorShear_bijective delta)
    _ = evalDist (ProbComp.sampleIID (TGSW.rowCount 1 levels) ($ᵗ R)) :=
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := R) (TGSW.rowCount 1 levels)).symm

/-- Statistical defect of the additive key-shift error shear. -/
noncomputable def rankOneAdditiveShiftNoiseDistance
    {R : Type} [Ring R] {levels : ℕ}
    (errorSampler : ProbComp R) (delta : R) : ℝ :=
  tvDist
    (rankOneAdditiveShiftErrorShear delta <$>
      ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler)
    (ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler)

/-- Exact direct-encryption law under the explicit shear-invariance condition. -/
theorem additiveShiftTGSW_directEncrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secretValue delta message : R)
    (gadget : Fin levels → R)
    (hnoise : RankOneAdditiveShiftNoiseInvariant
      (levels := levels) errorSampler delta) :
    evalDist (additiveShiftTGSW delta <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message) =
      evalDist (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ secretValue + delta) gadget message) := by
  let samples := TGSW.rowCount 1 levels
  let errors := ProbComp.sampleIID samples errorSampler
  let finish := fun (challenge : Matrix (Fin 1) (Fin samples) R)
      (error : Fin samples → R) ↦
        (pure (TLWE.batchAssemble (fun _ ↦ secretValue + delta) challenge
          (TGSW.gadgetPhase (fun _ ↦ secretValue + delta) gadget message)
          error) : ProbComp (TGSW.Ciphertext R 1 levels))
  rw [show TGSW.directEncrypt 1 levels errorSampler
      (fun _ ↦ secretValue) gadget message =
      (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge ↦
        errors >>= fun error ↦
          pure (TLWE.batchAssemble (fun _ ↦ secretValue) challenge
            (TGSW.gadgetPhase (fun _ ↦ secretValue) gadget message) error)) by
    simp [TGSW.directEncrypt, TLWE.batchEncrypt, samples, errors, monad_norm]]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge ↦
        errors >>= fun error ↦
          finish (rankOneAdditiveShiftChallenge delta challenge)
            (rankOneAdditiveShiftErrorShear delta error)) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin 1) (Fin samples) R)
        fun challenge ↦ ?_
      refine evalDist_bind_congr' errors fun error ↦ ?_
      simpa only [samples, finish] using congrArg evalDist
        (congrArg pure (additiveShiftTGSW_batchAssemble
          secretValue delta message gadget challenge error))
    _ = evalDist (((rankOneAdditiveShiftChallenge delta) <$>
          ($ᵗ Matrix (Fin 1) (Fin samples) R)) >>= fun challenge ↦
        (rankOneAdditiveShiftErrorShear delta <$> errors) >>= fun error ↦
          finish challenge error) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      rfl
    _ = evalDist (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge ↦
        (rankOneAdditiveShiftErrorShear delta <$> errors) >>= fun error ↦
          finish challenge error) := by
      rw [evalDist_bind,
        rankOneAdditiveShiftChallenge_uniform_evalDist delta, ← evalDist_bind]
    _ = evalDist (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge ↦
        errors >>= fun error ↦ finish challenge error) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin 1) (Fin samples) R)
        fun _ ↦ ?_
      rw [evalDist_bind, show evalDist
          (rankOneAdditiveShiftErrorShear delta <$> errors) = evalDist errors by
            exact hnoise,
        ← evalDist_bind]
    _ = _ := by
      simp [TGSW.directEncrypt, TLWE.batchEncrypt, samples, errors, finish,
        monad_norm]

/-- Quantitative direct-encryption law.  The public challenge transformation is exact; the
displayed row-error shear is the complete statistical loss. -/
theorem additiveShiftTGSW_directEncrypt_tvDist_le
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secretValue delta message : R)
    (gadget : Fin levels → R) :
    tvDist (additiveShiftTGSW delta <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ secretValue + delta) gadget message) ≤
      rankOneAdditiveShiftNoiseDistance (levels := levels) errorSampler delta := by
  let samples := TGSW.rowCount 1 levels
  let errors := ProbComp.sampleIID samples errorSampler
  let shearedErrors := rankOneAdditiveShiftErrorShear delta <$> errors
  let finish := fun (challenge : Matrix (Fin 1) (Fin samples) R)
      (error : Fin samples → R) ↦
    (pure (TLWE.batchAssemble (fun _ ↦ secretValue + delta) challenge
      (TGSW.gadgetPhase (fun _ ↦ secretValue + delta) gadget message) error) :
      ProbComp (TGSW.Ciphertext R 1 levels))
  let shearedExperiment :=
    ($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge ↦
      shearedErrors >>= fun error ↦ finish challenge error
  let targetExperiment :=
    ($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge ↦
      errors >>= fun error ↦ finish challenge error
  have hsource :
      evalDist (additiveShiftTGSW delta <$>
          TGSW.directEncrypt 1 levels errorSampler
            (fun _ ↦ secretValue) gadget message) =
        evalDist shearedExperiment := by
    rw [show TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ secretValue) gadget message =
        (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge ↦
          errors >>= fun error ↦
            pure (TLWE.batchAssemble (fun _ ↦ secretValue) challenge
              (TGSW.gadgetPhase (fun _ ↦ secretValue) gadget message) error)) by
      simp [TGSW.directEncrypt, TLWE.batchEncrypt, samples, errors, monad_norm]]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    calc
      _ = evalDist (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge ↦
          errors >>= fun error ↦
            finish (rankOneAdditiveShiftChallenge delta challenge)
              (rankOneAdditiveShiftErrorShear delta error)) := by
        refine evalDist_bind_congr' ($ᵗ Matrix (Fin 1) (Fin samples) R)
          fun challenge ↦ ?_
        refine evalDist_bind_congr' errors fun error ↦ ?_
        simpa only [samples, finish] using congrArg evalDist
          (congrArg pure (additiveShiftTGSW_batchAssemble
            secretValue delta message gadget challenge error))
      _ = evalDist ((rankOneAdditiveShiftChallenge delta <$>
            ($ᵗ Matrix (Fin 1) (Fin samples) R)) >>= fun challenge ↦
          shearedErrors >>= fun error ↦ finish challenge error) := by
        unfold shearedErrors
        simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc,
          pure_bind]
        rfl
      _ = evalDist shearedExperiment := by
        unfold shearedExperiment
        rw [evalDist_bind,
          rankOneAdditiveShiftChallenge_uniform_evalDist delta,
          ← evalDist_bind]
  have htarget :
      evalDist (TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue + delta) gadget message) =
        evalDist targetExperiment := by
    simp [TGSW.directEncrypt, TLWE.batchEncrypt, targetExperiment, finish,
      samples, errors, monad_norm]
  have hdistance : tvDist shearedExperiment targetExperiment ≤
      rankOneAdditiveShiftNoiseDistance (levels := levels) errorSampler delta := by
    unfold shearedExperiment targetExperiment
    refine tvDist_bind_left_le_const'
      ($ᵗ Matrix (Fin 1) (Fin samples) R)
      (fun challenge ↦ shearedErrors >>= fun error ↦ finish challenge error)
      (fun challenge ↦ errors >>= fun error ↦ finish challenge error)
      (rankOneAdditiveShiftNoiseDistance
        (levels := levels) errorSampler delta) ?_
    intro challenge
    exact (tvDist_bind_right_le (finish challenge) shearedErrors errors).trans_eq
      (by rfl)
  rw [show tvDist (additiveShiftTGSW delta <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ secretValue + delta) gadget message) =
      tvDist shearedExperiment targetExperiment by
        unfold tvDist
        rw [hsource, htarget]]
  exact hdistance

/-- Exact law for the native structured TGSW sampler. -/
theorem additiveShiftTGSW_encrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secretValue delta message : R)
    (gadget : Fin levels → R)
    (hnoise : RankOneAdditiveShiftNoiseInvariant
      (levels := levels) errorSampler delta) :
    evalDist (additiveShiftTGSW delta <$>
        TGSW.encrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message) =
      evalDist (TGSW.encrypt 1 levels errorSampler
        (fun _ ↦ secretValue + delta) gadget message) := by
  calc
    _ = evalDist (additiveShiftTGSW delta <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message) :=
      evalDist_map_eq_of_evalDist_eq
        (TGSW.encrypt_evalDist_eq_directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
        (additiveShiftTGSW delta)
    _ = evalDist (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ secretValue + delta) gadget message) :=
      additiveShiftTGSW_directEncrypt_evalDist errorSampler secretValue delta
        message gadget hnoise
    _ = _ :=
      (TGSW.encrypt_evalDist_eq_directEncrypt 1 levels errorSampler
        (fun _ ↦ secretValue + delta) gadget message).symm

/-- Quantitative law for the actual structured native TGSW sampler. -/
theorem additiveShiftTGSW_encrypt_tvDist_le
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secretValue delta message : R)
    (gadget : Fin levels → R) :
    tvDist (additiveShiftTGSW delta <$>
        TGSW.encrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.encrypt 1 levels errorSampler
        (fun _ ↦ secretValue + delta) gadget message) ≤
      rankOneAdditiveShiftNoiseDistance (levels := levels) errorSampler delta := by
  have hsource := evalDist_map_eq_of_evalDist_eq
    (TGSW.encrypt_evalDist_eq_directEncrypt 1 levels errorSampler
      (fun _ ↦ secretValue) gadget message)
    (additiveShiftTGSW delta)
  have htarget := TGSW.encrypt_evalDist_eq_directEncrypt
    1 levels errorSampler (fun _ ↦ secretValue + delta) gadget message
  rw [show tvDist (additiveShiftTGSW delta <$>
        TGSW.encrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.encrypt 1 levels errorSampler
        (fun _ ↦ secretValue + delta) gadget message) =
      tvDist (additiveShiftTGSW delta <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ secretValue + delta) gadget message) by
        unfold tvDist
        rw [hsource, htarget]]
  exact additiveShiftTGSW_directEncrypt_tvDist_le
    errorSampler secretValue delta message gadget

/-- Uniform native row errors give an unconditional exact additive TGSW key shift. -/
theorem additiveShiftTGSW_uniformError_encrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (secretValue delta message : R) (gadget : Fin levels → R) :
    evalDist (additiveShiftTGSW delta <$>
        TGSW.encrypt 1 levels ($ᵗ R) (fun _ ↦ secretValue) gadget message) =
      evalDist (TGSW.encrypt 1 levels ($ᵗ R)
        (fun _ ↦ secretValue + delta) gadget message) :=
  additiveShiftTGSW_encrypt_evalDist ($ᵗ R) secretValue delta message gadget
    (rankOneAdditiveShiftNoiseInvariant_uniform delta)

/-! ## Complete bootstrapping-key lift -/

/-- Apply the additive rank-one key shift independently to every BRK entry. -/
def additiveShiftBootstrappingKey
    {q degree levels lweDimension : ℕ}
    (delta : RLWE.Rq q degree)
    (bootstrappingKey : Native.BootstrappingKey q degree 1 levels lweDimension) :
    Native.BootstrappingKey q degree 1 levels lweDimension :=
  fun coordinate ↦ additiveShiftTGSW delta (bootstrappingKey coordinate)

/-- If two rank-one binary ring keys differ by a public additive ring element, the public row
shear transports the complete native BRK exactly, provided its row-error vector is shear
invariant.  The BRK plaintext vector is arbitrary and is retained unchanged. -/
theorem additiveShiftBootstrappingKey_generate_evalDist
    {q degree levels lweDimension : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (sourceRingSecret targetRingSecret : RingBinarySecret 1 degree)
    (delta : RLWE.Rq q degree)
    (hsecret :
      embedRingSecret q targetRingSecret =
        embedRingSecret q sourceRingSecret + fun _ ↦ delta)
    (hnoise : RankOneAdditiveShiftNoiseInvariant
      (levels := levels) errorSampler delta) :
    evalDist (additiveShiftBootstrappingKey delta <$>
        Native.generateBootstrappingKey q degree 1 levels lweDimension
          errorSampler gadget lweSecret sourceRingSecret) =
      evalDist (Native.generateBootstrappingKey q degree 1 levels lweDimension
        errorSampler gadget lweSecret targetRingSecret) := by
  let secretValue := embedRingSecret q sourceRingSecret (0 : Fin 1)
  have hsourceRing :
      embedRingSecret q sourceRingSecret = fun _ ↦ secretValue := by
    funext component
    have hcomponent : component = 0 := Subsingleton.elim _ _
    subst component
    rfl
  have htargetRing :
      embedRingSecret q targetRingSecret = fun _ ↦
        FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofAdd
          secretValue delta := by
    rw [hsecret, hsourceRing]
    funext component
    exact
      (FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofAdd_eq_add
        secretValue delta).symm
  rw [show additiveShiftBootstrappingKey delta =
      (fun bootstrappingKey coordinate ↦
        additiveShiftTGSW delta (bootstrappingKey coordinate)) by rfl]
  simpa only [Native.generateBootstrappingKey] using
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.mOfFn_map_evalDist_congr
      lweDimension
      (fun coordinate ↦
        TGSW.encrypt 1 levels errorSampler
          (embedRingSecret q sourceRingSecret) gadget
          (embedConstantBit q degree (lweSecret coordinate)))
      (fun coordinate ↦
        TGSW.encrypt 1 levels errorSampler
          (embedRingSecret q targetRingSecret) gadget
          (embedConstantBit q degree (lweSecret coordinate)))
      (fun _ ↦ additiveShiftTGSW delta)
      (fun coordinate ↦ by
        rw [hsourceRing, htargetRing]
        exact additiveShiftTGSW_encrypt_evalDist errorSampler secretValue delta
          (embedConstantBit q degree (lweSecret coordinate)) gadget hnoise)

/-- Quantitative complete-BRK law.  Independent entries contribute one explicit additive-shear
distance per BRK plaintext coordinate. -/
theorem additiveShiftBootstrappingKey_generate_tvDist_le
    {q degree levels lweDimension : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (sourceRingSecret targetRingSecret : RingBinarySecret 1 degree)
    (delta : RLWE.Rq q degree)
    (hsecret :
      embedRingSecret q targetRingSecret =
        embedRingSecret q sourceRingSecret + fun _ ↦ delta) :
    tvDist (additiveShiftBootstrappingKey delta <$>
        Native.generateBootstrappingKey q degree 1 levels lweDimension
          errorSampler gadget lweSecret sourceRingSecret)
      (Native.generateBootstrappingKey q degree 1 levels lweDimension
        errorSampler gadget lweSecret targetRingSecret) ≤
      (lweDimension : ℝ) *
        rankOneAdditiveShiftNoiseDistance (levels := levels) errorSampler delta := by
  let secretValue := embedRingSecret q sourceRingSecret (0 : Fin 1)
  have hsourceRing :
      embedRingSecret q sourceRingSecret = fun _ ↦ secretValue := by
    funext component
    have hcomponent : component = 0 := Subsingleton.elim _ _
    subst component
    rfl
  have htargetRing :
      embedRingSecret q targetRingSecret = fun _ ↦
        FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofAdd
          secretValue delta := by
    rw [hsecret, hsourceRing]
    funext component
    exact
      (FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofAdd_eq_add
        secretValue delta).symm
  change tvDist
      ((fun values coordinate ↦ additiveShiftTGSW delta (values coordinate)) <$>
        Fin.mOfFn lweDimension (fun coordinate ↦
          TGSW.encrypt 1 levels errorSampler
            (embedRingSecret q sourceRingSecret) gadget
            (embedConstantBit q degree (lweSecret coordinate))))
      (Fin.mOfFn lweDimension (fun coordinate ↦
        TGSW.encrypt 1 levels errorSampler
          (embedRingSecret q targetRingSecret) gadget
          (embedConstantBit q degree (lweSecret coordinate)))) ≤ _
  rw [FormalProof4FHE.FiniteProduct.map_fin_mOfFn]
  calc
    _ ≤ ∑ coordinate,
        tvDist
          (additiveShiftTGSW delta <$>
            TGSW.encrypt 1 levels errorSampler
              (embedRingSecret q sourceRingSecret) gadget
              (embedConstantBit q degree (lweSecret coordinate)))
          (TGSW.encrypt 1 levels errorSampler
            (embedRingSecret q targetRingSecret) gadget
            (embedConstantBit q degree (lweSecret coordinate))) :=
      FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
        lweDimension _ _
    _ ≤ ∑ _coordinate : Fin lweDimension,
        rankOneAdditiveShiftNoiseDistance
          (levels := levels) errorSampler delta := by
      apply Finset.sum_le_sum
      intro coordinate _
      rw [hsourceRing, htargetRing]
      exact additiveShiftTGSW_encrypt_tvDist_le
        errorSampler secretValue delta
          (embedConstantBit q degree (lweSecret coordinate)) gadget
    _ = (lweDimension : ℝ) *
        rankOneAdditiveShiftNoiseDistance
          (levels := levels) errorSampler delta := by
      simp

/-- At coefficient modulus two, every binary ring-key XOR mask satisfies the additive premise of
the complete BRK transport theorem. -/
theorem additiveShiftBootstrappingKey_masked_zmod_two_evalDist
    {degree levels lweDimension : ℕ}
    (errorSampler : ProbComp (RLWE.Rq 2 degree))
    (gadget : Fin levels → RLWE.Rq 2 degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret mask : RingBinarySecret 1 degree)
    (hnoise : RankOneAdditiveShiftNoiseInvariant (levels := levels) errorSampler
      (embedRingSecret 2 mask 0)) :
    evalDist (additiveShiftBootstrappingKey (embedRingSecret 2 mask 0) <$>
        Native.generateBootstrappingKey 2 degree 1 levels lweDimension
          errorSampler gadget lweSecret ringSecret) =
      evalDist (Native.generateBootstrappingKey 2 degree 1 levels lweDimension
        errorSampler gadget lweSecret (maskedRingSecret ringSecret mask)) := by
  apply additiveShiftBootstrappingKey_generate_evalDist
    errorSampler gadget lweSecret ringSecret (maskedRingSecret ringSecret mask)
      (embedRingSecret 2 mask 0)
  · rw [embedRingSecret_masked_eq_add_of_two_eq_zero
      (ZMod.natCast_self 2)]
    funext component
    have hcomponent : component = 0 := Subsingleton.elim _ _
    subst component
    rfl
  · exact hnoise

/-- With uniform row errors, the characteristic-two arbitrary-XOR BRK transport is exact without
an additional noise hypothesis. -/
theorem additiveShiftBootstrappingKey_masked_zmod_two_uniformError_evalDist
    {degree levels lweDimension : ℕ}
    (gadget : Fin levels → RLWE.Rq 2 degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret mask : RingBinarySecret 1 degree) :
    evalDist (additiveShiftBootstrappingKey (embedRingSecret 2 mask 0) <$>
        Native.generateBootstrappingKey 2 degree 1 levels lweDimension
          ($ᵗ RLWE.Rq 2 degree) gadget lweSecret ringSecret) =
      evalDist (Native.generateBootstrappingKey 2 degree 1 levels lweDimension
        ($ᵗ RLWE.Rq 2 degree) gadget lweSecret
          (maskedRingSecret ringSecret mask)) :=
  additiveShiftBootstrappingKey_masked_zmod_two_evalDist
    ($ᵗ RLWE.Rq 2 degree) gadget lweSecret ringSecret mask
      (rankOneAdditiveShiftNoiseInvariant_uniform (embedRingSecret 2 mask 0))

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
