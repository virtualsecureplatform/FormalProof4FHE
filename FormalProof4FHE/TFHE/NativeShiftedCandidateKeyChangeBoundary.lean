/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeShiftedCandidateEvaluator
import FormalProof4FHE.TFHE.RotationLookup
import FormalProof4FHE.TFHE.CoefficientStructuredLWE

set_option autoImplicit false

/-!
# Encryption-Key Boundary for the Native Shifted-Candidate CMux

The native shifted-candidate evaluator is a same-key CMux.  Its correct branch has an exact
residual normal form under the ring secret used to interpret the source BRK.  A relative-key
randomizer needs a different statement: the output must have the honest narrow residual law under
an XOR-shifted ring secret.

This file makes the difference algebraically explicit.  Reinterpreting one TGSW row under a new
secret adds the dot product of the secret difference with the row's homogeneous public mask.  For
the concrete correct-candidate output, the target-key row error is therefore exactly

`sameKeyResidual + keyChangeDefect`.

Consequently, the existing CMux theorem supplies the desired shifted-key law with the same
residual if and only if this additional defect vanishes, row by row.  This is an exact boundary,
not an impossibility theorem: a future nonlinear evaluator may cancel or statistically smudge the
defect.  It prevents a sequence of same-key candidate selections from being silently treated as
the `RelativeKeyShiftMaterialEvaluator` required by the full nested-key proof.
-/

open Matrix

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateKeyChangeBoundary

open FormalProof4FHE.TFHE

variable {q degree ringRank levels lweDimension : ℕ}

/-! ## Generic TLWE/TGSW key-change identities -/

/-- The phase defect obtained by interpreting one fixed TLWE row under `targetSecret` instead of
`sourceSecret`. -/
def tlweKeyChangeDefect {R : Type} [Ring R] {dimension : ℕ}
    (sourceSecret targetSecret : Fin dimension → R)
    (ciphertext : TLWE.Ciphertext R dimension) : R :=
  dotProduct (sourceSecret - targetSecret) ciphertext.mask

/-- Exact phase change for one fixed public TLWE row. -/
theorem phase_target_eq_phase_source_add_keyChangeDefect
    {R : Type} [CommRing R] {dimension : ℕ}
    (sourceSecret targetSecret : Fin dimension → R)
    (ciphertext : TLWE.Ciphertext R dimension) :
    TLWE.phase targetSecret ciphertext =
      TLWE.phase sourceSecret ciphertext +
        tlweKeyChangeDefect sourceSecret targetSecret ciphertext := by
  classical
  simp only [TLWE.phase, tlweKeyChangeDefect, dotProduct, Pi.sub_apply]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-- The public mask remaining after removing the declared TGSW gadget message. -/
def homogeneousRowMask {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R dimension levels)
    (row : Fin (TGSW.rowCount dimension levels)) : Fin dimension → R :=
  fun coordinate ↦
    (TLWE.entry ciphertext row).mask coordinate -
      TGSW.gadgetMaskShift gadget message coordinate row

/-- The exact extra TGSW row error created by changing the encryption key while retaining the
same complete ciphertext. -/
def tgswKeyChangeDefect {R : Type} [Ring R] {dimension levels : ℕ}
    (sourceSecret targetSecret : Fin dimension → R)
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) : R :=
  dotProduct (sourceSecret - targetSecret)
    (homogeneousRowMask gadget message ciphertext (finProdFinEquiv index))

/-- The structured gadget phase itself obeys the same TLWE key-change identity, with the gadget
mask in place of the ciphertext mask. -/
theorem gadgetPhase_target_eq_gadgetPhase_source_add_defect
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (sourceSecret targetSecret : Fin dimension → R)
    (gadget : Fin levels → R) (message : R)
    (row : Fin (TGSW.rowCount dimension levels)) :
    TGSW.gadgetPhase targetSecret gadget message row =
      TGSW.gadgetPhase sourceSecret gadget message row +
        dotProduct (sourceSecret - targetSecret)
          (fun coordinate ↦ TGSW.gadgetMaskShift gadget message coordinate row) := by
  classical
  simp only [TGSW.gadgetPhase, Pi.sub_apply, Matrix.vecMul, dotProduct,
    Pi.sub_apply]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-- Changing the secret in a TGSW row error adds exactly the homogeneous-mask key-change defect.
The structured gadget mask is subtracted because its secret-dependent phase changes as well. -/
theorem rowError_target_eq_rowError_source_add_keyChangeDefect
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (sourceSecret targetSecret : Fin dimension → R)
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) :
    TGSW.rowError targetSecret gadget message ciphertext index =
      TGSW.rowError sourceSecret gadget message ciphertext index +
        tgswKeyChangeDefect sourceSecret targetSecret gadget message ciphertext index := by
  classical
  unfold TGSW.rowError tgswKeyChangeDefect homogeneousRowMask
  rw [phase_target_eq_phase_source_add_keyChangeDefect
    sourceSecret targetSecret]
  rw [gadgetPhase_target_eq_gadgetPhase_source_add_defect
    sourceSecret targetSecret]
  simp only [tlweKeyChangeDefect, dotProduct, Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- Removing a gadget message from a syntactically structured TGSW ciphertext recovers the mask
of its homogeneous part exactly. -/
@[simp]
theorem homogeneousRowMask_addGadget
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (homogeneous : TGSW.Ciphertext R dimension levels)
    (row : Fin (TGSW.rowCount dimension levels)) :
    homogeneousRowMask gadget message
        (TGSW.addGadget gadget message homogeneous) row =
      (TLWE.entry homogeneous row).mask := by
  funext coordinate
  simp [homogeneousRowMask, TGSW.addGadget, TLWE.entry]

/-! ## Honest-row diagnostic -/

/-- An honestly assembled TLWE row, when interpreted under another secret, carries its original
message and error plus the exact public-mask key-change defect. -/
theorem phase_assemble_at_target
    {R : Type} [CommRing R] {dimension : ℕ}
    (sourceSecret targetSecret mask : Fin dimension → R)
    (message error : R) :
    TLWE.phase targetSecret (TLWE.assemble sourceSecret mask message error) =
      message + error + dotProduct (sourceSecret - targetSecret) mask := by
  calc
    _ = TLWE.phase sourceSecret
          (TLWE.assemble sourceSecret mask message error) +
        tlweKeyChangeDefect sourceSecret targetSecret
          (TLWE.assemble sourceSecret mask message error) :=
      phase_target_eq_phase_source_add_keyChangeDefect
        sourceSecret targetSecret _
    _ = _ := by
      rw [TLWE.phase_assemble]
      rfl

/-- Rank-one diagnostic: if multiplication by the nonzero key difference is a permutation, a
uniform source mask makes the target-key phase uniform, even after adding a fixed narrow error.
Thus merely reinterpreting a fresh source-key row is not a narrow-noise key shift. -/
theorem phase_assemble_rankOne_uniform_at_target_of_mul_bijective
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    (sourceSecret targetSecret message error : R)
    (hmul : Function.Bijective
      (fun mask : R ↦ (sourceSecret - targetSecret) * mask)) :
    evalDist
        ((fun mask : R ↦
          TLWE.phase (fun _ : Fin 1 ↦ targetSecret)
            (TLWE.assemble (fun _ : Fin 1 ↦ sourceSecret)
              (fun _ : Fin 1 ↦ mask) message error)) <$>
          ($ᵗ R)) =
      evalDist ($ᵗ R) := by
  let transform := fun mask : R ↦
    message + error + (sourceSecret - targetSecret) * mask
  have htransform : Function.Bijective transform := by
    constructor
    · intro left right heq
      apply hmul.1
      exact add_left_cancel heq
    · intro output
      obtain ⟨mask, hmask⟩ := hmul.2 (output - (message + error))
      refine ⟨mask, ?_⟩
      dsimp only [transform]
      have hmask' : (sourceSecret - targetSecret) * mask =
          output - (message + error) := hmask
      rw [hmask']
      ring
  have hpointwise : (fun mask : R ↦
      TLWE.phase (fun _ : Fin 1 ↦ targetSecret)
        (TLWE.assemble (fun _ : Fin 1 ↦ sourceSecret)
          (fun _ : Fin 1 ↦ mask) message error)) = transform := by
    funext mask
    rw [phase_assemble_at_target]
    simp [dotProduct, transform]
  rw [hpointwise]
  exact evalDist_map_bijective_uniform_cross
    (α := R) (β := R) transform htransform

/-! ## Complete independent-row diagnostic -/

/-- Target-key phases of a complete rank-one batch assembled under a source key.  Messages and
errors are fixed here so the only sampled input is the independent public mask of each row. -/
def rankOneTargetPhaseVector {R : Type} [Ring R] {samples : ℕ}
    (sourceSecret targetSecret : R)
    (message error mask : Fin samples → R) : Fin samples → R :=
  fun sample ↦
    TLWE.phase (fun _ : Fin 1 ↦ targetSecret)
      (TLWE.assemble (fun _ : Fin 1 ↦ sourceSecret)
        (fun _ : Fin 1 ↦ mask sample) (message sample) (error sample))

/-- Every batch coordinate has the same affine key-change normal form as the single-row
diagnostic. -/
@[simp]
theorem rankOneTargetPhaseVector_apply {R : Type} [CommRing R] {samples : ℕ}
    (sourceSecret targetSecret : R)
    (message error mask : Fin samples → R) (sample : Fin samples) :
    rankOneTargetPhaseVector sourceSecret targetSecret message error mask sample =
      message sample + error sample +
        (sourceSecret - targetSecret) * mask sample := by
  rw [rankOneTargetPhaseVector, phase_assemble_at_target]
  simp [dotProduct]

/-- If multiplication by the key difference is bijective, changing every independent mask into
its target-key phase is a bijection on the complete phase vector, not merely rowwise. -/
theorem rankOneTargetPhaseVector_bijective_of_mul_bijective
    {R : Type} [CommRing R] {samples : ℕ}
    (sourceSecret targetSecret : R)
    (message error : Fin samples → R)
    (hmul : Function.Bijective
      (fun mask : R ↦ (sourceSecret - targetSecret) * mask)) :
    Function.Bijective
      (rankOneTargetPhaseVector sourceSecret targetSecret message error) := by
  let multiply : R ≃ R := Equiv.ofBijective
    (fun mask : R ↦ (sourceSecret - targetSecret) * mask) hmul
  let inverse : (Fin samples → R) → Fin samples → R :=
    fun output sample ↦
      multiply.symm (output sample - (message sample + error sample))
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨inverse, ?_, ?_⟩
  · intro mask
    funext sample
    dsimp only [inverse]
    rw [rankOneTargetPhaseVector_apply]
    have hinside :
        message sample + error sample +
              (sourceSecret - targetSecret) * mask sample -
            (message sample + error sample) = multiply (mask sample) := by
      rw [show multiply (mask sample) =
          (sourceSecret - targetSecret) * mask sample by rfl]
      ring
    rw [hinside, Equiv.symm_apply_apply]
  · intro output
    funext sample
    rw [rankOneTargetPhaseVector_apply]
    change message sample + error sample +
        multiply (multiply.symm
          (output sample - (message sample + error sample))) = output sample
    rw [Equiv.apply_symm_apply]
    ring

/-- Consequently all target-key phases of the independent source-key batch are jointly uniform.
This is stronger than multiplying single-row marginal equalities, and it incurs no union bound. -/
theorem rankOneTargetPhaseVector_uniform_of_mul_bijective
    {R : Type} [CommRing R] [Fintype R] [SampleableType R] {samples : ℕ}
    (sourceSecret targetSecret : R)
    (message error : Fin samples → R)
    (hmul : Function.Bijective
      (fun mask : R ↦ (sourceSecret - targetSecret) * mask)) :
    evalDist
        (rankOneTargetPhaseVector sourceSecret targetSecret message error <$>
          ($ᵗ (Fin samples → R))) =
      evalDist ($ᵗ (Fin samples → R)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Fin samples → R) (β := Fin samples → R)
    (rankOneTargetPhaseVector sourceSecret targetSecret message error)
    (rankOneTargetPhaseVector_bijective_of_mul_bijective
      sourceSecret targetSecret message error hmul)

/-- Retaining both the public masks and their target-key phases produces a graph distribution. -/
def rankOneMaskPhaseView {R : Type} [Ring R] {samples : ℕ}
    (sourceSecret targetSecret : R)
    (message error mask : Fin samples → R) :
    (Fin samples → R) × (Fin samples → R) :=
  (mask, rankOneTargetPhaseVector sourceSecret targetSecret message error mask)

@[simp]
theorem rankOneMaskPhaseView_fst {R : Type} [Ring R] {samples : ℕ}
    (sourceSecret targetSecret : R)
    (message error mask : Fin samples → R) :
    (rankOneMaskPhaseView sourceSecret targetSecret message error mask).1 = mask :=
  rfl

/-- Uniformity of the target phase marginal does **not** make the retained public transcript
uniform.  With at least one row over a nontrivial ring, the mask/phase map is not surjective: its
phase vector is still a deterministic function of its retained mask vector. -/
theorem rankOneMaskPhaseView_not_surjective
    {R : Type} [CommRing R] [Nontrivial R] {samples : ℕ}
    (sample : Fin samples) (sourceSecret targetSecret : R)
    (message error : Fin samples → R) :
    ¬ Function.Surjective
      (rankOneMaskPhaseView sourceSecret targetSecret message error) := by
  let zeroMask : Fin samples → R := 0
  let basePhase := rankOneTargetPhaseVector sourceSecret targetSecret
    message error zeroMask
  let alteredPhase := Function.update basePhase sample (basePhase sample + 1)
  intro hsurjective
  obtain ⟨mask, hmask⟩ := hsurjective (zeroMask, alteredPhase)
  have hmask_eq : mask = zeroMask := congrArg Prod.fst hmask
  have hphase_eq :
      rankOneTargetPhaseVector sourceSecret targetSecret message error mask =
        alteredPhase := congrArg Prod.snd hmask
  subst mask
  have hat := congrFun hphase_eq sample
  have heq : basePhase sample = basePhase sample + 1 := by
    simpa only [alteredPhase, Function.update_self] using hat
  have hzeroOne : (0 : R) = 1 := by
    apply add_left_cancel (a := basePhase sample)
    simpa only [add_zero] using heq
  exact zero_ne_one hzeroOne

/-- Multiplication by every executable signed negacyclic monomial is a permutation. -/
theorem rotationMonomial_mul_bijective
    {q degree : ℕ} [NeZero q]
    (exponent : Fin (2 * (degree + 1))) :
    Function.Bijective
      (fun value : RLWE.Rq q (degree + 1) ↦
        BlindRotation.rotationMonomial q degree exponent * value) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨(fun value ↦
      BlindRotation.rotationMonomial q degree (-exponent) * value), ?_, ?_⟩
  · intro value
    dsimp only
    rw [← mul_assoc, RotationLookup.rotationMonomial_mul]
    simp only [neg_add_cancel, BlindRotation.rotationMonomial_zero, one_mul]
  · intro value
    dsimp only
    rw [← mul_assoc, RotationLookup.rotationMonomial_mul]
    simp only [add_neg_cancel, BlindRotation.rotationMonomial_zero, one_mul]

/-- Concrete signed-monomial specialization.  Moving a rank-one source key by one signed
negacyclic monomial and merely retaining the same uniformly masked row makes its phase under the
new key exactly uniform.  A single binary coefficient flip has precisely such a key difference,
with the sign determined by the old bit. -/
theorem phase_assemble_rankOne_uniform_after_rotationMonomial_keyShift
    {q degree : ℕ} [NeZero q]
    (sourceSecret message error : RLWE.Rq q (degree + 1))
    (exponent : Fin (2 * (degree + 1))) :
    let delta := BlindRotation.rotationMonomial q degree exponent
    evalDist
        ((fun mask : RLWE.Rq q (degree + 1) ↦
          TLWE.phase (fun _ : Fin 1 ↦ sourceSecret - delta)
            (TLWE.assemble (fun _ : Fin 1 ↦ sourceSecret)
              (fun _ : Fin 1 ↦ mask) message error)) <$>
          ($ᵗ RLWE.Rq q (degree + 1))) =
      evalDist ($ᵗ RLWE.Rq q (degree + 1)) := by
  dsimp only
  apply phase_assemble_rankOne_uniform_at_target_of_mul_bijective
  simpa only [sub_sub_cancel] using rotationMonomial_mul_bijective exponent

/-- Flip exactly one coefficient of a binary polynomial secret. -/
def flipBinaryCoefficient {ringDegree : ℕ}
    (secret : BinarySecret ringDegree) (coordinate : Fin ringDegree) :
    BinarySecret ringDegree :=
  Function.update secret coordinate (!secret coordinate)

@[simp]
theorem flipBinaryCoefficient_self {ringDegree : ℕ}
    (secret : BinarySecret ringDegree) (coordinate : Fin ringDegree) :
    flipBinaryCoefficient secret coordinate coordinate = !secret coordinate := by
  simp [flipBinaryCoefficient]

/-- Signed-monomial exponent of `sourceSecret - flippedSecret`: positive when the old bit is one
and negative when the old bit is zero. -/
def binaryCoefficientFlipDifferenceExponent {degree : ℕ}
    (bit : Bool) (coordinate : Fin (degree + 1)) : Fin (2 * (degree + 1)) :=
  if bit then
    ⟨coordinate.val, by omega⟩
  else
    ⟨coordinate.val + (degree + 1), by omega⟩

/-- The embedded difference made by one binary coefficient flip is literally the corresponding
executable signed negacyclic monomial. -/
theorem embedBinaryPolynomial_sub_flipBinaryCoefficient
    {q degree : ℕ} [NeZero q]
    (secret : BinarySecret (degree + 1))
    (coordinate : Fin (degree + 1)) :
    embedBinaryPolynomial q (degree + 1) secret -
        embedBinaryPolynomial q (degree + 1)
          (flipBinaryCoefficient secret coordinate) =
      BlindRotation.rotationMonomial q degree
        (binaryCoefficientFlipDifferenceExponent (secret coordinate) coordinate) := by
  let coefficients := Native.CoefficientStructuredLWE.coefficientEquiv q (degree + 1)
  apply coefficients.injective
  funext input
  rw [show coefficients
        (embedBinaryPolynomial q (degree + 1) secret -
          embedBinaryPolynomial q (degree + 1)
            (flipBinaryCoefficient secret coordinate)) =
      coefficients (embedBinaryPolynomial q (degree + 1) secret) -
        coefficients (embedBinaryPolynomial q (degree + 1)
          (flipBinaryCoefficient secret coordinate)) by
    exact (Native.CoefficientStructuredLWE.coefficientAddEquiv
      q (degree + 1)).map_sub _ _]
  rw [Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial]
  rw [Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial]
  change Native.CoefficientStructuredLWE.binaryCoefficients q secret input -
      Native.CoefficientStructuredLWE.binaryCoefficients q
        (flipBinaryCoefficient secret coordinate) input =
    LatticeCrypto.Poly.toPi
      (BlindRotation.rotationMonomial q degree
        (binaryCoefficientFlipDifferenceExponent (secret coordinate) coordinate)) input
  rw [BlindRotation.rotationMonomial_coefficient]
  by_cases hinput : input = coordinate
  · subst input
    have hcoordinate : coordinate.val ≤ degree := by omega
    have hnegative : ¬coordinate.val + (degree + 1) ≤ degree := by omega
    cases hbit : secret coordinate
    · simp [Native.CoefficientStructuredLWE.binaryCoefficients,
        flipBinaryCoefficient, binaryCoefficientFlipDifferenceExponent,
        hbit, hnegative, embedBit]
    · simp [Native.CoefficientStructuredLWE.binaryCoefficients,
        flipBinaryCoefficient, binaryCoefficientFlipDifferenceExponent,
        hbit, hcoordinate, embedBit]
  · have hval : input.val ≠ coordinate.val := by
      intro heq
      apply hinput
      exact Fin.ext heq
    have hcoordinate : coordinate.val ≤ degree := by omega
    have hnegative : ¬coordinate.val + (degree + 1) ≤ degree := by omega
    cases hbit : secret coordinate
    · simp [Native.CoefficientStructuredLWE.binaryCoefficients,
        flipBinaryCoefficient, binaryCoefficientFlipDifferenceExponent,
        hbit, hinput, hval, hnegative, embedBit]
    · simp [Native.CoefficientStructuredLWE.binaryCoefficients,
        flipBinaryCoefficient, binaryCoefficientFlipDifferenceExponent,
        hbit, hinput, hval, hcoordinate, embedBit]

/-- Direct binary-key specialization of the diagnostic.  If a fresh source-key TLWE row is kept
unchanged while one coefficient of its rank-one binary ring key is flipped, its phase under the
flipped key is exactly uniform. -/
theorem phase_assemble_rankOne_uniform_after_binaryCoefficientFlip
    {q degree : ℕ} [NeZero q]
    (secret : BinarySecret (degree + 1))
    (coordinate : Fin (degree + 1))
    (message error : RLWE.Rq q (degree + 1)) :
    let sourceSecret := embedBinaryPolynomial q (degree + 1) secret
    let targetSecret := embedBinaryPolynomial q (degree + 1)
      (flipBinaryCoefficient secret coordinate)
    evalDist
        ((fun mask : RLWE.Rq q (degree + 1) ↦
          TLWE.phase (fun _ : Fin 1 ↦ targetSecret)
            (TLWE.assemble (fun _ : Fin 1 ↦ sourceSecret)
              (fun _ : Fin 1 ↦ mask) message error)) <$>
          ($ᵗ RLWE.Rq q (degree + 1))) =
      evalDist ($ᵗ RLWE.Rq q (degree + 1)) := by
  dsimp only
  apply phase_assemble_rankOne_uniform_at_target_of_mul_bijective
  rw [embedBinaryPolynomial_sub_flipBinaryCoefficient]
  exact rotationMonomial_mul_bijective
    (binaryCoefficientFlipDifferenceExponent (secret coordinate) coordinate)

/-- Complete independent-row version of the binary coefficient-flip result.  Every target phase
is jointly uniform, while `rankOneMaskPhaseView_not_surjective` shows why this alone is not a
public-ciphertext simulation. -/
theorem rankOneTargetPhaseVector_uniform_after_binaryCoefficientFlip
    {q degree samples : ℕ} [NeZero q]
    (secret : BinarySecret (degree + 1))
    (coordinate : Fin (degree + 1))
    (message error : Fin samples → RLWE.Rq q (degree + 1)) :
    let sourceSecret := embedBinaryPolynomial q (degree + 1) secret
    let targetSecret := embedBinaryPolynomial q (degree + 1)
      (flipBinaryCoefficient secret coordinate)
    evalDist
        (rankOneTargetPhaseVector sourceSecret targetSecret message error <$>
          ($ᵗ (Fin samples → RLWE.Rq q (degree + 1)))) =
      evalDist ($ᵗ (Fin samples → RLWE.Rq q (degree + 1))) := by
  dsimp only
  apply rankOneTargetPhaseVector_uniform_of_mul_bijective
  rw [embedBinaryPolynomial_sub_flipBinaryCoefficient]
  exact rotationMonomial_mul_bijective
    (binaryCoefficientFlipDifferenceExponent (secret coordinate) coordinate)

/-! ## Concrete correct-candidate BRK boundary -/

/-- Under the source ring key, the concrete correct-candidate CMux row error is exactly the
already exposed computed residual. -/
theorem rowError_selectBootstrappingKey_correct
    (params : Gadget.Base.Parameters q)
    (sourceRingSecret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TGSW.rowError sourceRingSecret (Gadget.Base.ringGadget params)
        (embedBit (hidden outputCoordinate))
        (ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
          (hidden coordinate) source trueBranch outputCoordinate) index =
      ShiftedCandidateEvaluator.correctBootstrappingResidual params sourceRingSecret
        hidden coordinate source trueBranch outputCoordinate (finProdFinEquiv index) := by
  unfold TGSW.rowError
  rw [ShiftedCandidateEvaluator.phase_entry_selectBootstrappingKey_correctResidual
    params sourceRingSecret hidden coordinate outputCoordinate source trueBranch]
  simp only [TGSW.cmuxMessage, zero_mul, add_zero,
    ShiftedCandidateEvaluator.proofAdd_eq_add]
  abel

/-- **Exact missing term for a shifted ring key.**  The same concrete correct-candidate output,
when checked under `targetRingSecret`, has its source-key computed residual plus the complete
homogeneous-mask key-change defect. -/
theorem rowError_selectBootstrappingKey_correct_at_target
    (params : Gadget.Base.Parameters q)
    (sourceRingSecret targetRingSecret :
      Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TGSW.rowError targetRingSecret (Gadget.Base.ringGadget params)
        (embedBit (hidden outputCoordinate))
        (ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
          (hidden coordinate) source trueBranch outputCoordinate) index =
      ShiftedCandidateEvaluator.correctBootstrappingResidual params sourceRingSecret
          hidden coordinate source trueBranch outputCoordinate (finProdFinEquiv index) +
        tgswKeyChangeDefect sourceRingSecret targetRingSecret
          (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
          (ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
            (hidden coordinate) source trueBranch outputCoordinate) index := by
  rw [rowError_target_eq_rowError_source_add_keyChangeDefect
    sourceRingSecret targetRingSecret]
  rw [rowError_selectBootstrappingKey_correct params sourceRingSecret hidden
    coordinate outputCoordinate source trueBranch]

/-- The existing same-key CMux residual is also the target-key residual exactly when the new
key-change defect is zero.  This is the rowwise compatibility condition that a whole-material
relative-key evaluator must additionally establish. -/
theorem rowError_selectBootstrappingKey_correct_at_target_iff
    (params : Gadget.Base.Parameters q)
    (sourceRingSecret targetRingSecret :
      Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TGSW.rowError targetRingSecret (Gadget.Base.ringGadget params)
          (embedBit (hidden outputCoordinate))
          (ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
            (hidden coordinate) source trueBranch outputCoordinate) index =
        ShiftedCandidateEvaluator.correctBootstrappingResidual params sourceRingSecret
          hidden coordinate source trueBranch outputCoordinate (finProdFinEquiv index) ↔
      tgswKeyChangeDefect sourceRingSecret targetRingSecret
          (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
          (ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
            (hidden coordinate) source trueBranch outputCoordinate) index = 0 := by
  rw [rowError_selectBootstrappingKey_correct_at_target params sourceRingSecret
    targetRingSecret hidden coordinate outputCoordinate source trueBranch]
  constructor
  · intro heq
    apply add_left_cancel (a :=
      ShiftedCandidateEvaluator.correctBootstrappingResidual params sourceRingSecret
        hidden coordinate source trueBranch outputCoordinate (finProdFinEquiv index))
    calc
      _ = ShiftedCandidateEvaluator.correctBootstrappingResidual params sourceRingSecret
          hidden coordinate source trueBranch outputCoordinate
            (finProdFinEquiv index) := heq
      _ = _ := (add_zero _).symm
  · intro hzero
    calc
      _ = ShiftedCandidateEvaluator.correctBootstrappingResidual params sourceRingSecret
            hidden coordinate source trueBranch outputCoordinate
              (finProdFinEquiv index) + 0 := by rw [hzero]
      _ = _ := add_zero _

/-- Whole-BRK predicate recording precisely the extra condition needed to reinterpret the
correct-candidate output under a different ring key without changing its residual vector. -/
def CorrectOutputKeyChangeCompatible
    (params : Gadget.Base.Parameters q)
    (sourceRingSecret targetRingSecret :
      Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) : Prop :=
  ∀ outputCoordinate index,
    tgswKeyChangeDefect sourceRingSecret targetRingSecret
      (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
      (ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
        (hidden coordinate) source trueBranch outputCoordinate) index = 0

/-- Whole-BRK form of the exact compatibility boundary. -/
theorem correctOutputKeyChangeCompatible_iff
    (params : Gadget.Base.Parameters q)
    (sourceRingSecret targetRingSecret :
      Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :
    CorrectOutputKeyChangeCompatible params sourceRingSecret targetRingSecret hidden
        coordinate source trueBranch ↔
      ∀ outputCoordinate index,
        TGSW.rowError targetRingSecret (Gadget.Base.ringGadget params)
            (embedBit (hidden outputCoordinate))
            (ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
              (hidden coordinate) source trueBranch outputCoordinate) index =
          ShiftedCandidateEvaluator.correctBootstrappingResidual params sourceRingSecret
            hidden coordinate source trueBranch outputCoordinate
              (finProdFinEquiv index) := by
  constructor
  · intro hcompatible outputCoordinate index
    exact (rowError_selectBootstrappingKey_correct_at_target_iff params
      sourceRingSecret targetRingSecret hidden coordinate outputCoordinate
      source trueBranch index).2 (hcompatible outputCoordinate index)
  · intro hrows outputCoordinate index
    exact (rowError_selectBootstrappingKey_correct_at_target_iff params
      sourceRingSecret targetRingSecret hidden coordinate outputCoordinate
      source trueBranch index).1 (hrows outputCoordinate index)

/-! ## Sequential-composition boundary -/

/-- One correct-candidate coordinate selection together with its caller-supplied true branch. -/
abbrev CorrectSelectionStep
    (q ringDegree ringRank levels lweDimension : ℕ) :=
  Fin lweDimension ×
    BootstrappingKey q ringDegree ringRank levels lweDimension

/-- Apply one coordinate step using the declared hidden bit as the candidate. -/
noncomputable def applyCorrectSelectionStep
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension)
    (source : BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (step : CorrectSelectionStep q (degree + 1) ringRank params.levels lweDimension) :
    BootstrappingKey q (degree + 1) ringRank params.levels lweDimension :=
  ShiftedCandidateEvaluator.selectBootstrappingKey params step.1
    (hidden step.1) source step.2

/-- Execute any finite sequence of correct-candidate native CMux calls. -/
noncomputable def applyCorrectSelectionSequence
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension)
    (source : BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (steps : List
      (CorrectSelectionStep q (degree + 1) ringRank params.levels lweDimension)) :
    BootstrappingKey q (degree + 1) ringRank params.levels lweDimension :=
  steps.foldl (applyCorrectSelectionStep params hidden) source

@[simp]
theorem applyCorrectSelectionSequence_nil
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension)
    (source : BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :
    applyCorrectSelectionSequence params hidden source [] = source := by
  rfl

@[simp]
theorem applyCorrectSelectionSequence_cons
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension)
    (source : BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (step : CorrectSelectionStep q (degree + 1) ringRank params.levels lweDimension)
    (steps : List
      (CorrectSelectionStep q (degree + 1) ringRank params.levels lweDimension)) :
    applyCorrectSelectionSequence params hidden source (step :: steps) =
      applyCorrectSelectionSequence params hidden
        (applyCorrectSelectionStep params hidden source step) steps := by
  rfl

/-- No finite sequence removes the encryption-key reinterpretation term automatically: for its
final public ciphertext, changing from the source to the target ring secret still adds exactly
the same homogeneous-mask defect.  The sequence may alter that mask, but a separate theorem must
show that the resulting defect vanishes or is statistically absorbable. -/
theorem rowError_applyCorrectSelectionSequence_at_target
    (params : Gadget.Base.Parameters q)
    (sourceRingSecret targetRingSecret :
      Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (source : BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (steps : List
      (CorrectSelectionStep q (degree + 1) ringRank params.levels lweDimension))
    (outputCoordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TGSW.rowError targetRingSecret (Gadget.Base.ringGadget params)
        (embedBit (hidden outputCoordinate))
        (applyCorrectSelectionSequence params hidden source steps outputCoordinate) index =
      TGSW.rowError sourceRingSecret (Gadget.Base.ringGadget params)
          (embedBit (hidden outputCoordinate))
          (applyCorrectSelectionSequence params hidden source steps outputCoordinate) index +
        tgswKeyChangeDefect sourceRingSecret targetRingSecret
          (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
          (applyCorrectSelectionSequence params hidden source steps outputCoordinate) index :=
  rowError_target_eq_rowError_source_add_keyChangeDefect
    sourceRingSecret targetRingSecret _ _ _ _

/-- Sequence form of the necessary-and-sufficient condition: the final row has the same residual
under the shifted key exactly when its final key-change defect is zero. -/
theorem rowError_applyCorrectSelectionSequence_at_target_iff
    (params : Gadget.Base.Parameters q)
    (sourceRingSecret targetRingSecret :
      Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (source : BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (steps : List
      (CorrectSelectionStep q (degree + 1) ringRank params.levels lweDimension))
    (outputCoordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TGSW.rowError targetRingSecret (Gadget.Base.ringGadget params)
          (embedBit (hidden outputCoordinate))
          (applyCorrectSelectionSequence params hidden source steps outputCoordinate) index =
        TGSW.rowError sourceRingSecret (Gadget.Base.ringGadget params)
          (embedBit (hidden outputCoordinate))
          (applyCorrectSelectionSequence params hidden source steps outputCoordinate) index ↔
      tgswKeyChangeDefect sourceRingSecret targetRingSecret
          (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
          (applyCorrectSelectionSequence params hidden source steps outputCoordinate) index = 0 := by
  rw [rowError_applyCorrectSelectionSequence_at_target params sourceRingSecret
    targetRingSecret hidden source steps outputCoordinate index]
  constructor
  · intro heq
    apply add_left_cancel (a :=
      TGSW.rowError sourceRingSecret (Gadget.Base.ringGadget params)
        (embedBit (hidden outputCoordinate))
        (applyCorrectSelectionSequence params hidden source steps outputCoordinate) index)
    calc
      _ = TGSW.rowError sourceRingSecret (Gadget.Base.ringGadget params)
          (embedBit (hidden outputCoordinate))
          (applyCorrectSelectionSequence params hidden source steps outputCoordinate) index := heq
      _ = _ := (add_zero _).symm
  · intro hzero
    calc
      _ = TGSW.rowError sourceRingSecret (Gadget.Base.ringGadget params)
            (embedBit (hidden outputCoordinate))
            (applyCorrectSelectionSequence params hidden source steps outputCoordinate) index +
          0 := by rw [hzero]
      _ = _ := add_zero _

end FormalProof4FHE.TFHE.Native.ShiftedCandidateKeyChangeBoundary
