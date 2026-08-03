/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RGSWCoefficientCircularSecurity
import FormalProof4FHE.TFHE.ScalarSecretRandomization

/-!
# Native TRGSW public-linear barrier and spectral boundary

This module formalizes the finite mathematical content of
`sketch/native_trgsw_barrier_and_spectral_boundary.tex`.

There are two distinct parts.

* The native nonce-row obstruction is unconditional algebra.  A displayed nonce mask creates a
  prefix/suffix product and, with two prefix coordinates, a nonzero mixed Boolean derivative.
  Consequently the desired row-local public-linear source form does not exist under either of the
  nondegeneracy conditions stated in the note.  Honest private phase cancellation remains exact.
* Exact public TRGSW bit normalization and the diagonal Walsh decomposition are also
  unconditional.  The final native-security bound is proved from explicit low-degree
  affine-source and high-degree channel-tail hypotheses.  In particular, this file does not turn
  the note's unresolved complete-view spectral-decay premise into an axiom or a proved fact.

The ring identities below are stated over a commutative ring.  They therefore apply directly to
the finite quotient rings used by the native TFHE development, without assuming that those rings
are integral domains.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWBarrierAndSpectralBoundary

noncomputable section

/-! ## Exact public-contribution algebra -/

/-- The canonical embedding of a Boolean value into a ring. -/
def bitScalar {R : Type} [Zero R] [One R] (bit : Bool) : R :=
  if bit then 1 else 0

@[simp] theorem bitScalar_false {R : Type} [Zero R] [One R] :
    bitScalar (R := R) false = 0 := rfl

@[simp] theorem bitScalar_true {R : Type} [Zero R] [One R] :
    bitScalar (R := R) true = 1 := rfl

@[simp]
theorem bitScalar_sq {R : Type} [Ring R] (bit : Bool) :
    bitScalar (R := R) bit ^ 2 = bitScalar bit := by
  cases bit <;> simp

/-- Public additive embedding of a binary prefix through a displayed basis. -/
def prefixEmbedding {R Index : Type} [CommRing R] [Fintype Index]
    (basis : Index → R) (prefixBits : Index → Bool) : R :=
  ∑ coordinate, bitScalar (prefixBits coordinate) * basis coordinate

/-- Native body row after splitting the secret into prefix and suffix pieces. -/
def bodyRow {R Index : Type} [CommRing R] [Fintype Index]
    (displayedMask : R) (basis : Index → R) (control : Index)
    (gadget suffix error : R) (prefixBits : Index → Bool) : R :=
  displayedMask * (prefixEmbedding basis prefixBits + suffix) + error +
    gadget * bitScalar (prefixBits control)

/-- The complete prefix-dependent contribution of a body row is public and affine. -/
def bodyPrefixContribution {R Index : Type} [CommRing R] [Fintype Index]
    (displayedMask : R) (basis : Index → R) (control : Index)
    (gadget : R) (prefixBits : Index → Bool) : R :=
  displayedMask * prefixEmbedding basis prefixBits + gadget * bitScalar (prefixBits control)

/-- Public coefficient of one prefix bit in a native body row. -/
def bodyCoefficient {R Index : Type} [CommRing R] [DecidableEq Index]
    (displayedMask : R) (basis : Index → R) (control : Index)
    (gadget : R) (coordinate : Index) : R :=
  displayedMask * basis coordinate + if coordinate = control then gadget else 0

/-- The public body contribution is literally a linear combination of the prefix bits. -/
theorem bodyPrefixContribution_eq_sum {R Index : Type}
    [CommRing R] [Fintype Index] [DecidableEq Index]
    (displayedMask : R) (basis : Index → R) (control : Index)
    (gadget : R) (prefixBits : Index → Bool) :
    bodyPrefixContribution displayedMask basis control gadget prefixBits =
      ∑ coordinate, bodyCoefficient displayedMask basis control gadget coordinate *
        bitScalar (prefixBits coordinate) := by
  classical
  unfold bodyPrefixContribution bodyCoefficient prefixEmbedding
  rw [Finset.mul_sum]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro coordinate _
    ring
  · simp

/-- Equation (2.1) of the note: native body rows have the required public-linear split. -/
theorem bodyRow_publicLinear {R Index : Type} [CommRing R] [Fintype Index]
    (displayedMask : R) (basis : Index → R) (control : Index)
    (gadget suffix error : R) (prefixBits : Index → Bool) :
    bodyRow displayedMask basis control gadget suffix error prefixBits =
      displayedMask * suffix + error +
        bodyPrefixContribution displayedMask basis control gadget prefixBits := by
  simp only [bodyRow, bodyPrefixContribution]
  ring

/-- Native nonce row, expressed using the displayed mask rather than the hidden raw mask. -/
def nonceRow {R Index : Type} [CommRing R] [Fintype Index]
    (displayedMask : R) (basis : Index → R) (control : Index)
    (gadget suffix error : R) (prefixBits : Index → Bool) : R :=
  (displayedMask - gadget * bitScalar (prefixBits control)) *
      (prefixEmbedding basis prefixBits + suffix) + error

/-- Exact degree-two nonce-row decomposition.  The final two terms are respectively the
prefix/suffix product and the prefix/prefix product. -/
theorem nonceRow_degreeTwo {R Index : Type} [CommRing R] [Fintype Index]
    (displayedMask : R) (basis : Index → R) (control : Index)
    (gadget suffix error : R) (prefixBits : Index → Bool) :
    nonceRow displayedMask basis control gadget suffix error prefixBits =
      displayedMask * suffix + displayedMask * prefixEmbedding basis prefixBits + error -
        gadget * bitScalar (prefixBits control) * suffix -
        gadget * bitScalar (prefixBits control) * prefixEmbedding basis prefixBits := by
  simp only [nonceRow]
  ring

/-- Fully expanded Boolean-polynomial nonce form.  The last sum contains all prefix cross terms,
including the control-bit square that reduces to a linear term by `bitScalar_sq`. -/
theorem nonceRow_booleanPolynomial
    {R Index : Type} [CommRing R] [Fintype Index]
    (displayedMask : R) (basis : Index → R) (control : Index)
    (gadget suffix error : R) (prefixBits : Index → Bool) :
    nonceRow displayedMask basis control gadget suffix error prefixBits =
      displayedMask * suffix + error +
        (∑ coordinate,
          displayedMask * basis coordinate * bitScalar (prefixBits coordinate)) -
        gadget * bitScalar (prefixBits control) * suffix -
        ∑ coordinate,
          gadget * basis coordinate * bitScalar (prefixBits control) *
            bitScalar (prefixBits coordinate) := by
  rw [nonceRow_degreeTwo]
  unfold prefixEmbedding
  rw [Finset.mul_sum, Finset.mul_sum]
  have hlinear :
      (∑ coordinate,
          displayedMask * (bitScalar (prefixBits coordinate) * basis coordinate)) =
        ∑ coordinate,
          displayedMask * basis coordinate * bitScalar (prefixBits coordinate) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  have hquadratic :
      (∑ coordinate,
          gadget * bitScalar (prefixBits control) *
            (bitScalar (prefixBits coordinate) * basis coordinate)) =
        ∑ coordinate,
          gadget * basis coordinate * bitScalar (prefixBits control) *
            bitScalar (prefixBits coordinate) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  rw [hlinear]
  rw [hquadratic]
  ring

/-- One-coordinate restriction used to expose the prefix/suffix obstruction. -/
def nonceOne {R Suffix : Type} [CommRing R]
    (displayedMask gadget basisValue : R) (suffixEmbedding : Suffix → R)
    (control : Bool) (suffix : Suffix) : R :=
  (displayedMask - gadget * bitScalar control) *
    (bitScalar control * basisValue + suffixEmbedding suffix)

/-- If the suffix changes in a direction on which the gadget acts nontrivially, a nonce row
cannot be separated into a suffix-only term plus a public affine control-bit term. -/
theorem no_separable_nonce_of_suffix_variation
    {R Suffix : Type} [CommRing R]
    (displayedMask gadget basisValue : R) (suffixEmbedding : Suffix → R)
    (suffixZero suffixOne : Suffix)
    (hnonzero : gadget *
      (suffixEmbedding suffixOne - suffixEmbedding suffixZero) ≠ 0) :
    ¬ ∃ (suffixPart : Suffix → R) (linearPart : R),
        ∀ (control : Bool) (suffix : Suffix),
          nonceOne displayedMask gadget basisValue suffixEmbedding control suffix =
            suffixPart suffix + bitScalar control * linearPart := by
  rintro ⟨suffixPart, linearPart, hform⟩
  have hfalseZero := hform false suffixZero
  have hfalseOne := hform false suffixOne
  have htrueZero := hform true suffixZero
  have htrueOne := hform true suffixOne
  simp only [nonceOne, bitScalar_false, bitScalar_true, mul_zero, sub_zero, zero_mul,
    zero_add, mul_one, one_mul] at hfalseZero hfalseOne htrueZero htrueOne
  apply hnonzero
  linear_combination hfalseOne - hfalseZero - htrueOne + htrueZero

/-- Two-coordinate restriction of a native nonce row. -/
def nonceTwo {R : Type} [CommRing R]
    (displayedMask gadget controlBasis otherBasis suffix : R)
    (control other : Bool) : R :=
  (displayedMask - gadget * bitScalar control) *
    (bitScalar control * controlBasis + bitScalar other * otherBasis + suffix)

/-- Mixed Boolean derivative of a two-bit function. -/
def mixedBooleanDerivative {R : Type} [AddGroup R] (function : Bool → Bool → R) : R :=
  function true true - function true false - function false true + function false false

/-- The native nonce mixed derivative is exactly the cross-product coefficient `-h E_j`. -/
theorem mixedBooleanDerivative_nonceTwo {R : Type} [CommRing R]
    (displayedMask gadget controlBasis otherBasis suffix : R) :
    mixedBooleanDerivative
        (nonceTwo displayedMask gadget controlBasis otherBasis suffix) =
      -gadget * otherBasis := by
  simp [mixedBooleanDerivative, nonceTwo]
  ring

/-- Every public affine function of two Boolean coordinates has zero mixed derivative. -/
theorem mixedBooleanDerivative_affineTwo {R : Type} [CommRing R]
    (constant controlCoefficient otherCoefficient : R) :
    mixedBooleanDerivative (fun control other =>
      constant + bitScalar control * controlCoefficient +
        bitScalar other * otherCoefficient) = 0 := by
  simp [mixedBooleanDerivative]

/-- Nonzero cross embedding rules out every exact affine representation on the four-point binary
support. -/
theorem no_affine_nonce_of_cross_embedding
    {R : Type} [CommRing R]
    (displayedMask gadget controlBasis otherBasis suffix : R)
    (hnonzero : gadget * otherBasis ≠ 0) :
    ¬ ∃ constant controlCoefficient otherCoefficient : R,
        ∀ control other : Bool,
          nonceTwo displayedMask gadget controlBasis otherBasis suffix control other =
            constant + bitScalar control * controlCoefficient +
              bitScalar other * otherCoefficient := by
  rintro ⟨constant, controlCoefficient, otherCoefficient, hform⟩
  have hfunctions :
      nonceTwo displayedMask gadget controlBasis otherBasis suffix =
        fun control other => constant + bitScalar control * controlCoefficient +
          bitScalar other * otherCoefficient := by
    funext control other
    exact hform control other
  have hderivative := congrArg mixedBooleanDerivative hfunctions
  rw [mixedBooleanDerivative_nonceTwo, mixedBooleanDerivative_affineTwo] at hderivative
  apply hnonzero
  have : -(gadget * otherBasis) = 0 := by
    simpa only [neg_mul] using hderivative
  exact neg_eq_zero.mp this

/-- Standard coefficient embeddings are units.  Hence multiplying one by a nonzero gadget cannot
erase the mixed derivative, even when the quotient ring has zero divisors. -/
theorem no_affine_nonce_of_unit_cross_embedding
    {R : Type} [CommRing R]
    (displayedMask gadget controlBasis otherBasis suffix : R)
    (hgadget : gadget ≠ 0) (hunit : IsUnit otherBasis) :
    ¬ ∃ constant controlCoefficient otherCoefficient : R,
        ∀ control other : Bool,
          nonceTwo displayedMask gadget controlBasis otherBasis suffix control other =
            constant + bitScalar control * controlCoefficient +
              bitScalar other * otherCoefficient := by
  apply no_affine_nonce_of_cross_embedding
  intro hproduct
  apply hgadget
  apply hunit.mul_right_cancel
  simpa using hproduct

/-- Replacing the displayed suffix mask by any public value cannot serve both possible control
bits when the suffix variation is nondegenerate. -/
theorem no_public_alternative_suffixMask
    {R Suffix : Type} [CommRing R]
    (displayedMask gadget basisValue : R) (suffixEmbedding : Suffix → R)
    (suffixZero suffixOne : Suffix)
    (hnonzero : gadget *
      (suffixEmbedding suffixOne - suffixEmbedding suffixZero) ≠ 0) :
    ¬ ∃ (alternativeMask : R) (remainder : Bool → R),
        ∀ (control : Bool) (suffix : Suffix),
          nonceOne displayedMask gadget basisValue suffixEmbedding control suffix =
            alternativeMask * suffixEmbedding suffix + remainder control := by
  rintro ⟨alternativeMask, remainder, hform⟩
  have hfalseZero := hform false suffixZero
  have hfalseOne := hform false suffixOne
  have htrueZero := hform true suffixZero
  have htrueOne := hform true suffixOne
  simp only [nonceOne, bitScalar_false, bitScalar_true, mul_zero, sub_zero, zero_mul,
    zero_add, mul_one, one_mul] at hfalseZero hfalseOne htrueZero htrueOne
  apply hnonzero
  linear_combination hfalseOne - hfalseZero - htrueOne + htrueZero

/-! ### The displayed nonce mask is a one-time pad -/

/-- Translation by the message gadget as an explicit additive equivalence. -/
def displayedMaskEquiv {R : Type} [AddGroup R] (shift : R) : R ≃ R where
  toFun := fun rawMask => rawMask + shift
  invFun := fun displayedMask => displayedMask - shift
  left_inv := by intro rawMask; simp
  right_inv := by intro displayedMask; simp

/-- For either fixed control bit, adding the gadget to a uniform raw mask leaves the displayed
mask exactly uniform. -/
theorem displayedNonceMask_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    (gadget : R) (control : Bool) :
    evalDist ((fun rawMask : R =>
        rawMask + gadget * bitScalar (R := R) control) <$> ($ᵗ R)) =
      evalDist ($ᵗ R) :=
  evalDist_map_bijective_uniform_cross
    (α := R) (β := R)
    (displayedMaskEquiv (gadget * bitScalar (R := R) control))
      (displayedMaskEquiv (gadget * bitScalar (R := R) control)).bijective

/-- Retaining the control bit makes the independence statement explicit: the joint law is a
uniform control followed by a fresh uniform displayed mask. -/
theorem controlAndDisplayedNonceMask_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    (gadget : R) :
    evalDist (($ᵗ Bool) >>= fun control =>
      (fun rawMask : R =>
        (control, rawMask + gadget * bitScalar (R := R) control)) <$> ($ᵗ R)) =
    evalDist (($ᵗ Bool) >>= fun control =>
      (fun displayedMask => (control, displayedMask)) <$> ($ᵗ R)) := by
  refine evalDist_bind_congr' ($ᵗ Bool) fun control => ?_
  calc
    evalDist ((fun rawMask : R =>
        (control, rawMask + gadget * bitScalar (R := R) control)) <$>
        ($ᵗ R)) =
      evalDist ((fun displayedMask => (control, displayedMask)) <$>
        ((fun rawMask : R =>
          rawMask + gadget * bitScalar (R := R) control) <$> ($ᵗ R))) := by
      simp [Functor.map_map]
    _ = evalDist ((fun displayedMask => (control, displayedMask)) <$> ($ᵗ R)) :=
      evalDist_map_eq_of_evalDist_eq
        (displayedNonceMask_uniform_evalDist gadget control) _

/-- Uniform-input success probability of an estimator that sees only the displayed nonce mask
and attempts to reconstruct the raw zero-encryption mask. -/
def rawMaskRecoverySuccess
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (gadget : R) (estimator : R → R) : ℝ :=
  (∑ displayedMask : R, ∑ control : Bool,
      if estimator displayedMask =
          displayedMask - gadget * bitScalar (R := R) control
      then 1 else 0) /
    (2 * Fintype.card R)

/-- The displayed mask one-time-pads the raw mask: for a uniform control bit and a nonzero
gadget, no estimator depending only on the displayed mask recovers the raw mask with probability
greater than one half. -/
theorem rawMaskRecoverySuccess_le_half
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (gadget : R) (hgadget : gadget ≠ 0) (estimator : R → R) :
    rawMaskRecoverySuccess gadget estimator ≤ (1 : ℝ) / 2 := by
  have hpointwise : ∀ displayedMask : R,
      (∑ control : Bool,
        if estimator displayedMask =
            displayedMask - gadget * bitScalar (R := R) control
        then (1 : ℝ) else 0) ≤ 1 := by
    intro displayedMask
    rw [Fintype.sum_bool]
    simp only [bitScalar_false, bitScalar_true, mul_zero, mul_one, sub_zero]
    have hmask : displayedMask ≠ displayedMask - gadget := by
      intro hmask
      apply hgadget
      exact add_eq_left.mp (eq_sub_iff_add_eq.mp hmask)
    by_cases hfalse : estimator displayedMask = displayedMask
    · have htrue : estimator displayedMask ≠ displayedMask - gadget := by
        intro htrue
        apply hgadget
        calc
          gadget = displayedMask - (displayedMask - gadget) := by ring
          _ = displayedMask - estimator displayedMask := by rw [htrue]
          _ = 0 := by rw [hfalse]; simp
      simp [hfalse, hmask]
    · by_cases htrue : estimator displayedMask = displayedMask - gadget
      · simp [htrue, hgadget]
      · simp [hfalse, htrue]
  have hsum :
      (∑ displayedMask : R, ∑ control : Bool,
        if estimator displayedMask =
            displayedMask - gadget * bitScalar (R := R) control
        then (1 : ℝ) else 0) ≤ (Fintype.card R : ℝ) := by
    calc
      _ ≤ ∑ _displayedMask : R, (1 : ℝ) :=
        Finset.sum_le_sum fun displayedMask _ => hpointwise displayedMask
      _ = (Fintype.card R : ℝ) := by simp
  have hcard : (0 : ℝ) < Fintype.card R := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card R)
  unfold rawMaskRecoverySuccess
  calc
    _ ≤ (Fintype.card R : ℝ) / (2 * Fintype.card R) :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ = (1 : ℝ) / 2 := by
      field_simp

/-! ## Private cancellation and conditional bridge composition -/

/-- Honest generation cancels the private message phase exactly, but this identity does not make
that phase publicly computable. -/
theorem privatePhaseCancellation {R : Type} [Ring R]
    (publicInnerProduct messagePhase error freshError : R) :
    publicInnerProduct + (messagePhase + error) - messagePhase + freshError =
      publicInnerProduct + error + freshError := by
  abel

/-- Four-experiment triangle inequality underlying native-to-aligned composition. -/
theorem fourExperimentBridge
    (nativeReal alignedReal alignedZero nativeZero
      epsilonReal alignedBound epsilonZero : ℝ)
    (hreal : |nativeReal - alignedReal| ≤ epsilonReal)
    (haligned : |alignedReal - alignedZero| ≤ alignedBound)
    (hzero : |alignedZero - nativeZero| ≤ epsilonZero) :
    |nativeReal - nativeZero| ≤ epsilonReal + alignedBound + epsilonZero := by
  calc
    |nativeReal - nativeZero| =
        |(nativeReal - alignedReal) + (alignedReal - alignedZero) +
          (alignedZero - nativeZero)| := by ring_nf
    _ ≤ |nativeReal - alignedReal| + |alignedReal - alignedZero| +
        |alignedZero - nativeZero| := by
      exact (abs_add_three _ _ _)
    _ ≤ epsilonReal + alignedBound + epsilonZero := by linarith

/-- The concrete loss stated in the note once the aligned source theorem contributes
`2 epsilonRLWE + 4 epsilonLWE`. -/
theorem nativeToAlignedBridge
    (nativeReal alignedReal alignedZero nativeZero
      epsilonReal epsilonRLWE epsilonLWE epsilonZero : ℝ)
    (hreal : |nativeReal - alignedReal| ≤ epsilonReal)
    (haligned : |alignedReal - alignedZero| ≤ 2 * epsilonRLWE + 4 * epsilonLWE)
    (hzero : |alignedZero - nativeZero| ≤ epsilonZero) :
    |nativeReal - nativeZero| ≤
      epsilonReal + 2 * epsilonRLWE + 4 * epsilonLWE + epsilonZero := by
  have h := fourExperimentBridge nativeReal alignedReal alignedZero nativeZero
    epsilonReal (2 * epsilonRLWE + 4 * epsilonLWE) epsilonZero hreal haligned hzero
  linarith

/-! ## Exact public normalization of a complete native TGSW ciphertext -/

/-- Native bit normalization is already supplied by the complete TGSW encryption semantics.
This theorem exposes it at the boundary used by the spectral argument: it transforms the whole
ciphertext, including both mask and body gadget blocks. -/
theorem nativeBitNormalization {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension levels : ℕ} (errorSampler : ProbComp R)
    (hsymmetric : Native.ScalarSecretRandomization.NegationSymmetric errorSampler)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (bit mask : Bool) :
    evalDist (Native.ScalarSecretRandomization.toggleTGSW gadget mask <$>
        TGSW.encrypt dimension levels errorSampler secret gadget (embedBit bit)) =
      evalDist (TGSW.encrypt dimension levels errorSampler secret gadget
        (embedBit (LWE.MultiKeyAffine.maskedBit bit mask))) :=
  Native.ScalarSecretRandomization.toggleTGSW_encrypt_evalDist
    errorSampler hsymmetric secret gadget bit mask

/-- Pointwise normalization of a complete independently generated BRK family under one fixed
ring key.  Each entire TGSW component is transported; no raw nonce mask is recovered. -/
theorem nativeBRKNormalization {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension levels length : ℕ} (errorSampler : ProbComp R)
    (hsymmetric : Native.ScalarSecretRandomization.NegationSymmetric errorSampler)
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (message mask : Fin length → Bool) :
    evalDist
        ((fun ciphertexts coordinate =>
            Native.ScalarSecretRandomization.toggleTGSW gadget (mask coordinate)
              (ciphertexts coordinate)) <$>
          Fin.mOfFn length (fun coordinate =>
            TGSW.encrypt dimension levels errorSampler secret gadget
              (embedBit (message coordinate)))) =
      evalDist
        (Fin.mOfFn length (fun coordinate =>
          TGSW.encrypt dimension levels errorSampler secret gadget
            (embedBit (LWE.MultiKeyAffine.maskedBit
              (message coordinate) (mask coordinate))))) := by
  apply Native.ScalarSecretRandomization.mOfFn_map_evalDist_congr
  intro coordinate
  exact nativeBitNormalization errorSampler hsymmetric secret gadget
    (message coordinate) (mask coordinate)

/-! ## Diagonal Walsh--Fourier decomposition -/

/-- A binary word indexed by the prefix coordinates.  Frequencies are represented by indicator
words, which is definitionally equivalent to indexing them by finite subsets. -/
abbrev BitVector (Index : Type) := Index → Bool

/-- The zero Walsh frequency (the empty subset). -/
def zeroFrequency {Index : Type} : BitVector Index := fun _ => false

/-- Finite support represented by a binary frequency word. -/
def frequencySupport {Index : Type} [Fintype Index]
    (frequency : BitVector Index) : Finset Index :=
  Finset.univ.filter fun coordinate => frequency coordinate = true

/-- Cardinality of the subset represented by a frequency word. -/
def supportSize {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) : ℕ :=
  (frequencySupport frequency).card

/-- Indicator word of a finite subset. -/
def frequencyOfFinset {Index : Type} [DecidableEq Index]
    (support : Finset Index) : BitVector Index :=
  fun coordinate => decide (coordinate ∈ support)

/-- Binary frequencies and finite subsets are exactly equivalent. -/
def frequencyFinsetEquiv (Index : Type) [Fintype Index] [DecidableEq Index] :
    BitVector Index ≃ Finset Index where
  toFun := frequencySupport
  invFun := frequencyOfFinset
  left_inv := by
    intro frequency
    funext coordinate
    cases hfrequency : frequency coordinate <;>
      simp [frequencySupport, frequencyOfFinset, hfrequency]
  right_inv := by
    intro support
    ext coordinate
    simp [frequencySupport, frequencyOfFinset]

@[simp]
theorem frequencySupport_zeroFrequency
    {Index : Type} [Fintype Index] [DecidableEq Index] :
    frequencySupport (zeroFrequency : BitVector Index) = ∅ := by
  simp [frequencySupport, zeroFrequency]

theorem frequencySupport_eq_empty_iff
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) :
    frequencySupport frequency = ∅ ↔ frequency = zeroFrequency := by
  constructor
  · intro hempty
    have hsupport :
        (frequencyFinsetEquiv Index) frequency =
          (frequencyFinsetEquiv Index) (zeroFrequency : BitVector Index) := by
      change frequencySupport frequency =
        frequencySupport (zeroFrequency : BitVector Index)
      simpa using hempty
    exact (frequencyFinsetEquiv Index).injective hsupport
  · rintro rfl
    exact frequencySupport_zeroFrequency

/-- The real sign `(-1)^bit`. -/
def bitSign (bit : Bool) : ℝ := if bit then -1 else 1

/-- Walsh character indexed by a binary frequency word. -/
def walsh {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency word : BitVector Index) : ℝ :=
  ∏ coordinate, if frequency coordinate then bitSign (word coordinate) else 1

/-- Real cardinality of the binary cube. -/
def cubeSize (Index : Type) [Fintype Index] [DecidableEq Index] : ℝ :=
  (2 : ℝ) ^ Fintype.card Index

@[simp]
theorem walsh_zeroFrequency {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : BitVector Index) : walsh zeroFrequency word = 1 := by
  simp [walsh, zeroFrequency]

/-- The Boolean Walsh pairing is symmetric in frequency and input. -/
theorem walsh_comm {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency word : BitVector Index) : walsh frequency word = walsh word frequency := by
  classical
  unfold walsh
  apply Finset.prod_congr rfl
  intro coordinate _
  cases frequency coordinate <;> cases word coordinate <;> simp [bitSign]

/-- Pointwise multiplication law for a Walsh character and xor. -/
theorem walsh_maskedBit {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency left right : BitVector Index) :
    walsh frequency (fun coordinate =>
      LWE.MultiKeyAffine.maskedBit (left coordinate) (right coordinate)) =
      walsh frequency left * walsh frequency right := by
  classical
  rw [walsh, walsh, walsh, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro coordinate _
  cases frequency coordinate <;> cases left coordinate <;> cases right coordinate <;>
    simp [bitSign, LWE.MultiKeyAffine.maskedBit]

/-- Xor by a fixed binary word is an involutive permutation of the cube. -/
def xorEquiv {Index : Type} (left : BitVector Index) :
    BitVector Index ≃ BitVector Index where
  toFun := fun right coordinate =>
    LWE.MultiKeyAffine.maskedBit (left coordinate) (right coordinate)
  invFun := fun right coordinate =>
    LWE.MultiKeyAffine.maskedBit (left coordinate) (right coordinate)
  left_inv := by
    intro right
    funext coordinate
    exact LWE.MultiKeyAffine.maskedBit_involutive (left coordinate) (right coordinate)
  right_inv := by
    intro right
    funext coordinate
    exact LWE.MultiKeyAffine.maskedBit_involutive (left coordinate) (right coordinate)

/-- Walsh orthogonality on a finite binary cube. -/
theorem walsh_orthogonality {Index : Type} [Fintype Index] [DecidableEq Index]
    (first second : BitVector Index) :
    (∑ word : BitVector Index, walsh first word * walsh second word) =
      if first = second then cubeSize Index else 0 := by
  classical
  calc
    (∑ word : BitVector Index, walsh first word * walsh second word) =
        ∑ word : BitVector Index,
          ∏ coordinate,
            ((if first coordinate then bitSign (word coordinate) else 1) *
              (if second coordinate then bitSign (word coordinate) else 1)) := by
      apply Finset.sum_congr rfl
      intro word _
      rw [walsh, walsh, ← Finset.prod_mul_distrib]
    _ = ∏ coordinate,
          ∑ bit : Bool,
            ((if first coordinate then bitSign bit else 1) *
              (if second coordinate then bitSign bit else 1)) := by
      exact (Fintype.prod_sum fun coordinate bit =>
        ((if first coordinate then bitSign bit else 1) *
          (if second coordinate then bitSign bit else 1))).symm
    _ = if first = second then cubeSize Index else 0 := by
      by_cases hequal : first = second
      · subst second
        rw [if_pos rfl]
        unfold cubeSize
        calc
          (∏ coordinate,
              ∑ bit : Bool,
                ((if first coordinate then bitSign bit else 1) *
                  (if first coordinate then bitSign bit else 1))) =
              ∏ _coordinate : Index, (2 : ℝ) := by
            apply Finset.prod_congr rfl
            intro coordinate _
            cases first coordinate <;> norm_num [bitSign]
          _ = 2 ^ Fintype.card Index := by simp
      · rw [if_neg hequal]
        have hdifferent : ∃ coordinate, first coordinate ≠ second coordinate := by
          by_contra hall
          push Not at hall
          exact hequal (funext hall)
        obtain ⟨coordinate, hcoordinate⟩ := hdifferent
        apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
        cases hfirst : first coordinate <;> cases hsecond : second coordinate <;>
          simp_all [bitSign]

/-- Dual Walsh completeness. -/
theorem walsh_completeness {Index : Type} [Fintype Index] [DecidableEq Index]
    (first second : BitVector Index) :
    (∑ frequency : BitVector Index,
        walsh frequency first * walsh frequency second) =
      if first = second then cubeSize Index else 0 := by
  classical
  calc
    (∑ frequency : BitVector Index,
        walsh frequency first * walsh frequency second) =
      ∑ frequency : BitVector Index,
        walsh first frequency * walsh second frequency := by
      apply Finset.sum_congr rfl
      intro frequency _
      rw [walsh_comm frequency first, walsh_comm frequency second]
    _ = if first = second then cubeSize Index else 0 :=
      walsh_orthogonality first second

theorem cubeSize_pos (Index : Type) [Fintype Index] [DecidableEq Index] :
    0 < cubeSize Index := by
  unfold cubeSize
  positivity

theorem cubeSize_ne_zero (Index : Type) [Fintype Index] [DecidableEq Index] :
    cubeSize Index ≠ 0 :=
  ne_of_gt (cubeSize_pos Index)

/-- Normalized two-variable Walsh coefficient. -/
def fourierCoefficient {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ)
    (secretFrequency messageFrequency : BitVector Index) : ℝ :=
  (∑ secret : BitVector Index, ∑ message : BitVector Index,
      function secret message * walsh secretFrequency secret *
        walsh messageFrequency message) / cubeSize Index ^ 2

/-- Signed correlation computed by the public xor-normalization orbit filter. -/
def orbitFilteredCorrelation {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ)
    (frequency : BitVector Index) : ℝ :=
  (∑ secret : BitVector Index, ∑ mask : BitVector Index,
      walsh frequency mask * function secret (xorEquiv secret mask)) /
    cubeSize Index ^ 2

/-- Fourier filtering: the signed orbit-filter gap is exactly one diagonal coefficient. -/
theorem orbitFilteredCorrelation_eq_fourierCoefficient
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ)
    (frequency : BitVector Index) :
    orbitFilteredCorrelation function frequency =
      fourierCoefficient function frequency frequency := by
  classical
  unfold orbitFilteredCorrelation fourierCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro secret _
  calc
    (∑ mask : BitVector Index,
        walsh frequency mask * function secret (xorEquiv secret mask)) =
      ∑ message : BitVector Index,
        walsh frequency (xorEquiv secret message) *
          function secret (xorEquiv secret (xorEquiv secret message)) := by
      exact ((xorEquiv secret).sum_comp (fun mask =>
        walsh frequency mask * function secret (xorEquiv secret mask))).symm
    _ = ∑ message : BitVector Index,
        function secret message * walsh frequency secret * walsh frequency message := by
      apply Finset.sum_congr rfl
      intro message _
      rw [show xorEquiv secret (xorEquiv secret message) = message by
        exact (xorEquiv secret).left_inv message]
      rw [show walsh frequency (xorEquiv secret message) =
          walsh frequency secret * walsh frequency message by
        exact walsh_maskedBit frequency secret message]
      ring

/-- Absolute orbit-filtering advantage is the absolute diagonal coefficient. -/
theorem abs_orbitFilteredCorrelation_eq
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ)
    (frequency : BitVector Index) :
    |orbitFilteredCorrelation function frequency| =
      |fourierCoefficient function frequency frequency| := by
  rw [orbitFilteredCorrelation_eq_fourierCoefficient]

/-- Mean on the secret/message diagonal. -/
def diagonalMean {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ) : ℝ :=
  (∑ secret : BitVector Index, function secret secret) / cubeSize Index

/-- Mean under independent uniform secret and message. -/
def independentMean {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ) : ℝ :=
  (∑ secret : BitVector Index, ∑ message : BitVector Index,
      function secret message) / cubeSize Index ^ 2

/-- Unnormalized diagonal Walsh identity. -/
theorem sum_diagonalFourierNumerator {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ) :
    (∑ frequency : BitVector Index,
      ∑ secret : BitVector Index, ∑ message : BitVector Index,
        function secret message * walsh frequency secret * walsh frequency message) =
      cubeSize Index * ∑ secret : BitVector Index, function secret secret := by
  classical
  calc
    (∑ frequency : BitVector Index,
      ∑ secret : BitVector Index, ∑ message : BitVector Index,
        function secret message * walsh frequency secret * walsh frequency message) =
        ∑ secret : BitVector Index, ∑ message : BitVector Index,
          ∑ frequency : BitVector Index,
            function secret message * walsh frequency secret * walsh frequency message := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro secret _
      rw [Finset.sum_comm]
    _ = ∑ secret : BitVector Index, ∑ message : BitVector Index,
          function secret message *
            (∑ frequency : BitVector Index,
              walsh frequency secret * walsh frequency message) := by
      apply Finset.sum_congr rfl
      intro secret _
      apply Finset.sum_congr rfl
      intro message _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frequency _
      ring
    _ = ∑ secret : BitVector Index, ∑ message : BitVector Index,
          function secret message *
            (if secret = message then cubeSize Index else 0) := by
      simp_rw [walsh_completeness]
    _ = ∑ secret : BitVector Index,
          function secret secret * cubeSize Index := by
      simp
    _ = cubeSize Index * ∑ secret : BitVector Index, function secret secret := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro secret _
      ring

/-- Sum of all diagonal Fourier coefficients is the diagonal mean. -/
theorem sum_diagonalFourierCoefficient {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ) :
    (∑ frequency : BitVector Index,
      fourierCoefficient function frequency frequency) = diagonalMean function := by
  classical
  unfold fourierCoefficient diagonalMean
  rw [← Finset.sum_div, sum_diagonalFourierNumerator]
  field_simp [cubeSize_ne_zero Index]

/-- The empty/empty coefficient is exactly the independent mean. -/
theorem fourierCoefficient_zero_zero {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ) :
    fourierCoefficient function zeroFrequency zeroFrequency = independentMean function := by
  simp [fourierCoefficient, independentMean]

/-- The paper's exact diagonal Fourier identity. -/
theorem diagonalFourierIdentity {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ) :
    diagonalMean function - independentMean function =
      ∑ frequency ∈ (Finset.univ.erase (zeroFrequency : BitVector Index)),
        fourierCoefficient function frequency frequency := by
  classical
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (BitVector Index)))
    (f := fun frequency => fourierCoefficient function frequency frequency)
    (Finset.mem_univ (zeroFrequency : BitVector Index))
  rw [sum_diagonalFourierCoefficient, fourierCoefficient_zero_zero] at hsplit
  linarith

/-- Absolute real/random gap is bounded by the total nonzero diagonal Fourier mass. -/
theorem diagonalGap_le_sum_abs_fourier {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ) :
    |diagonalMean function - independentMean function| ≤
      ∑ frequency ∈ (Finset.univ.erase (zeroFrequency : BitVector Index)),
        |fourierCoefficient function frequency frequency| := by
  rw [diagonalFourierIdentity]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ### Low/high diagonal split -/

def nonzeroFrequencies (Index : Type) [Fintype Index] [DecidableEq Index] :
    Finset (BitVector Index) :=
  Finset.univ.erase zeroFrequency

def lowFrequencies (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    Finset (BitVector Index) :=
  (nonzeroFrequencies Index).filter fun frequency => supportSize frequency ≤ degree

def highFrequencies (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    Finset (BitVector Index) :=
  (nonzeroFrequencies Index).filter fun frequency => degree < supportSize frequency

def lowFrequencyCount (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) : ℕ :=
  (lowFrequencies Index degree).card

/-- The corresponding family of nonempty subsets of size at most `degree`. -/
def lowSubsetFamily (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) : Finset (Finset Index) :=
  Finset.univ.filter fun support => support.Nonempty ∧ support.card ≤ degree

/-- The indicator-word count is exactly the subset-family count. -/
theorem lowFrequencyCount_eq_lowSubsetFamily_card
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    lowFrequencyCount Index degree = (lowSubsetFamily Index degree).card := by
  classical
  unfold lowFrequencyCount
  apply Finset.card_bij
      (fun frequency _ => frequencySupport frequency)
  · intro frequency hfrequency
    rcases Finset.mem_filter.mp hfrequency with ⟨hnonzero, hsize⟩
    have hfrequency_ne : frequency ≠ (zeroFrequency : BitVector Index) :=
      (Finset.mem_erase.mp hnonzero).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact Finset.nonempty_iff_ne_empty.mpr fun hempty =>
        hfrequency_ne ((frequencySupport_eq_empty_iff frequency).mp hempty)
    · exact hsize
  · intro first _ second _ hequal
    exact (frequencyFinsetEquiv Index).injective hequal
  · intro support hsupport
    rcases Finset.mem_filter.mp hsupport with ⟨_, hnonempty, hcard⟩
    let frequency := (frequencyFinsetEquiv Index).symm support
    have hfrequencySupport : frequencySupport frequency = support :=
      (frequencyFinsetEquiv Index).apply_symm_apply support
    have hfrequency_ne : frequency ≠ (zeroFrequency : BitVector Index) := by
      intro hzero
      rw [hzero, frequencySupport_zeroFrequency] at hfrequencySupport
      exact hnonempty.ne_empty hfrequencySupport.symm
    refine ⟨frequency, ?_, hfrequencySupport⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨hfrequency_ne, Finset.mem_univ _⟩, ?_⟩
    unfold supportSize
    rw [hfrequencySupport]
    exact hcard

/-- The paper's binomial expression `sum_{k=1}^degree choose(card Index,k)`. -/
def binomialLowFrequencyCount (Index : Type) [Fintype Index] (degree : ℕ) : ℕ :=
  ∑ cardinality ∈ Finset.Icc 1 degree,
    Nat.choose (Fintype.card Index) cardinality

/-- Exact enumeration of the bounded nonempty subset family. -/
theorem lowSubsetFamily_card_eq_binomialLowFrequencyCount
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    (lowSubsetFamily Index degree).card =
      binomialLowFrequencyCount Index degree := by
  classical
  have hmaps :
      ((lowSubsetFamily Index degree : Finset (Finset Index)) : Set (Finset Index)).MapsTo
        Finset.card (Finset.Icc 1 degree) := by
    intro support hsupport
    rcases Finset.mem_filter.mp hsupport with ⟨_, hnonempty, hcard⟩
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr hnonempty, hcard⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  unfold binomialLowFrequencyCount
  apply Finset.sum_congr rfl
  intro cardinality hcardinality
  have hpowerset :
      ((Finset.univ : Finset Index).powersetCard cardinality).card =
        Nat.choose (Fintype.card Index) cardinality := by
    simp
  rw [← hpowerset]
  congr 1
  ext support
  rcases Finset.mem_Icc.mp hcardinality with ⟨hpositive, hdegree⟩
  simp only [lowSubsetFamily, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_powersetCard, Finset.subset_univ]
  constructor
  · rintro ⟨_, hequal⟩
    exact hequal
  · intro hequal
    have hsupportPositive : 0 < support.card := by omega
    exact ⟨⟨Finset.card_pos.mp hsupportPositive, by omega⟩, hequal⟩

/-- Consequently the low-frequency multiplier is exactly the binomial count in the note. -/
theorem lowFrequencyCount_eq_binomialLowFrequencyCount
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    lowFrequencyCount Index degree = binomialLowFrequencyCount Index degree := by
  rw [lowFrequencyCount_eq_lowSubsetFamily_card,
    lowSubsetFamily_card_eq_binomialLowFrequencyCount]

/-- Low and high degrees partition all nonzero frequencies. -/
theorem sum_nonzero_eq_sum_low_add_sum_high
    {Index : Type} [Fintype Index] [DecidableEq Index] (degree : ℕ)
    (coefficient : BitVector Index → ℝ) :
    (∑ frequency ∈ nonzeroFrequencies Index, coefficient frequency) =
      (∑ frequency ∈ lowFrequencies Index degree, coefficient frequency) +
        ∑ frequency ∈ highFrequencies Index degree, coefficient frequency := by
  classical
  simpa [lowFrequencies, highFrequencies, not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (nonzeroFrequencies Index)
      (fun frequency => supportSize frequency ≤ degree) coefficient).symm

/-- Uniformly bounded low-degree coefficients cost exactly the number of low frequencies. -/
theorem abs_sum_low_le_count_mul
    {Index : Type} [Fintype Index] [DecidableEq Index] (degree : ℕ)
    (coefficient : BitVector Index → ℝ) (bound : ℝ)
    (hbound : ∀ frequency ∈ lowFrequencies Index degree,
      |coefficient frequency| ≤ bound) :
    |∑ frequency ∈ lowFrequencies Index degree, coefficient frequency| ≤
      lowFrequencyCount Index degree * bound := by
  calc
    |∑ frequency ∈ lowFrequencies Index degree, coefficient frequency| ≤
        ∑ frequency ∈ lowFrequencies Index degree, |coefficient frequency| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _frequency ∈ lowFrequencies Index degree, bound := by
      exact Finset.sum_le_sum fun frequency hfrequency => hbound frequency hfrequency
    _ = lowFrequencyCount Index degree * bound := by
      simp [lowFrequencyCount]

/-- Exact high-degree absolute tail of a two-variable function. -/
def diagonalTail {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ) (degree : ℕ) : ℝ :=
  ∑ frequency ∈ highFrequencies Index degree,
    |fourierCoefficient function frequency frequency|

/-- Finite low/high Fourier bridge before inserting a cryptographic source bound. -/
theorem diagonalGap_le_lowCount_mul_add_tail
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ) (degree : ℕ) (bound : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient function frequency frequency| ≤ bound) :
    |diagonalMean function - independentMean function| ≤
      lowFrequencyCount Index degree * bound + diagonalTail function degree := by
  rw [diagonalFourierIdentity]
  rw [show (Finset.univ.erase (zeroFrequency : BitVector Index)) =
      nonzeroFrequencies Index by rfl]
  rw [sum_nonzero_eq_sum_low_add_sum_high]
  calc
    |(∑ frequency ∈ lowFrequencies Index degree,
          fourierCoefficient function frequency frequency) +
        ∑ frequency ∈ highFrequencies Index degree,
          fourierCoefficient function frequency frequency| ≤
      |∑ frequency ∈ lowFrequencies Index degree,
          fourierCoefficient function frequency frequency| +
        |∑ frequency ∈ highFrequencies Index degree,
          fourierCoefficient function frequency frequency| := abs_add_le _ _
    _ ≤ lowFrequencyCount Index degree * bound + diagonalTail function degree := by
      gcongr
      · exact abs_sum_low_le_count_mul degree _ bound hlow
      · exact Finset.abs_sum_le_sum_abs _ _

/-! ## Finite leakage removal and the bounded-degree bridge -/

/-- The generic finite-carrier squared-bias theorem used by the note.  This is an exported
specialization of the already proved complete-game leakage-removal theorem; no independence of
rows or coordinates is assumed. -/
theorem finiteRangeLeakageRemoval
    {Secret Leakage : Type} [Fintype Secret]
    [Fintype Leakage] [Nonempty Leakage] [SampleableType Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) :
    RGSWCoefficientCircularSecurity.leakedAdvantage
        secretSampler leakage real ideal ≤
      Real.sqrt (2 * Fintype.card Leakage *
        RGSWCoefficientCircularSecurity.leakageRemovalAdvantage
          secretSampler ($ᵗ Leakage) real ideal) :=
  RGSWCoefficientCircularSecurity.leakedAdvantage_le_sqrt_two_mul_card_mul_removal
    secretSampler leakage real ideal

/-- Convenient bounded-support consequence: leakage with at most `2^degree` values incurs the
paper's factor `sqrt (2^(degree+1) delta)`. -/
theorem finiteRangeLeakageRemoval_binaryBound
    {Secret Leakage : Type} [Fintype Secret]
    [Fintype Leakage] [Nonempty Leakage] [SampleableType Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) (degree : ℕ) (delta : ℝ)
    (hcard : Fintype.card Leakage ≤ 2 ^ degree)
    (hremoval :
      RGSWCoefficientCircularSecurity.leakageRemovalAdvantage
        secretSampler ($ᵗ Leakage) real ideal ≤ delta) :
    RGSWCoefficientCircularSecurity.leakedAdvantage
        secretSampler leakage real ideal ≤
      Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) := by
  let removal := RGSWCoefficientCircularSecurity.leakageRemovalAdvantage
    secretSampler ($ᵗ Leakage) real ideal
  have hremoval_nonneg : 0 ≤ removal := by
    unfold removal RGSWCoefficientCircularSecurity.leakageRemovalAdvantage
      ProbComp.boolDistAdvantage
    exact abs_nonneg _
  have hdelta_nonneg : 0 ≤ delta := hremoval_nonneg.trans hremoval
  have hcard_real : (Fintype.card Leakage : ℝ) ≤ (2 : ℝ) ^ degree := by
    exact_mod_cast hcard
  have hradicand :
      2 * (Fintype.card Leakage : ℝ) * removal ≤
        (2 : ℝ) ^ (degree + 1) * delta := by
    calc
      2 * (Fintype.card Leakage : ℝ) * removal ≤
          2 * (2 : ℝ) ^ degree * delta := by
        gcongr
      _ = (2 : ℝ) ^ (degree + 1) * delta := by
        rw [pow_succ]
        ring
  exact (finiteRangeLeakageRemoval secretSampler leakage real ideal).trans
    (Real.sqrt_le_sqrt hradicand)

/-- The bounded-degree native real/random bridge.  The low-degree hypothesis is exactly what a
complete affine-source reduction plus `finiteRangeLeakageRemoval_binaryBound` must establish;
the tail hypothesis is kept separate. -/
theorem boundedDegreeNativeBridge
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (delta tailBound : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient function frequency frequency| ≤
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta))
    (htail : diagonalTail function degree ≤ tailBound) :
    |diagonalMean function - independentMean function| ≤
      lowFrequencyCount Index degree *
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) + tailBound := by
  exact (diagonalGap_le_lowCount_mul_add_tail function degree _ hlow).trans
    (add_le_add_right htail _)

/-- Addition of a random-message/zero-message endpoint gives the complete conditional native
bound. -/
theorem boundedDegreeNativeBridge_withEndpoint
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (delta tailBound randomZeroBound randomZeroAdvantage : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient function frequency frequency| ≤
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta))
    (htail : diagonalTail function degree ≤ tailBound)
    (hendpoint : randomZeroAdvantage ≤ randomZeroBound) :
    |diagonalMean function - independentMean function| + randomZeroAdvantage ≤
      lowFrequencyCount Index degree *
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) +
          tailBound + randomZeroBound := by
  have hbridge := boundedDegreeNativeBridge function degree delta tailBound hlow htail
  linarith

/-! ## Complete-view posterior spectral certificate -/

/-- Posterior diagonal-parity energy `E[g(V)^2]` on a finite complete view. -/
def posteriorSpectralEnergy {View : Type} [Fintype View]
    (viewMass posteriorParity : View → ℝ) : ℝ :=
  ∑ view, viewMass view * posteriorParity view ^ 2

/-- Posterior diagonal-parity radius `theta`. -/
def posteriorSpectralRadius {View : Type} [Fintype View]
    (viewMass posteriorParity : View → ℝ) : ℝ :=
  Real.sqrt (posteriorSpectralEnergy viewMass posteriorParity)

/-- Totalized posterior obtained from a parity numerator and the view mass. -/
def posteriorFromNumerator {View : Type}
    (viewMass parityNumerator : View → ℝ) (view : View) : ℝ :=
  if viewMass view = 0 then 0 else parityNumerator view / viewMass view

/-- Exact finite form of the posterior energy.  Empty fibers contribute zero, as in conditional
expectation on a finite channel. -/
theorem posteriorSpectralEnergy_eq_sum_div
    {View : Type} [Fintype View]
    (viewMass parityNumerator : View → ℝ) :
    posteriorSpectralEnergy viewMass
        (posteriorFromNumerator viewMass parityNumerator) =
      ∑ view, if viewMass view = 0 then 0
        else parityNumerator view ^ 2 / viewMass view := by
  classical
  unfold posteriorSpectralEnergy posteriorFromNumerator
  apply Finset.sum_congr rfl
  intro view _
  by_cases hzero : viewMass view = 0
  · simp [hzero]
  · simp only [hzero, if_false]
    field_simp

/-- Distinguisher-independent finite channel spectral bound.  The `view` type is the complete
joint BRK/KSK/auxiliary transcript, so this estimate retains all correlations. -/
theorem channelSpectralBound
    {View : Type} [Fintype View]
    (viewMass posteriorParity response : View → ℝ)
    (hmass : ∀ view, 0 ≤ viewMass view)
    (hmass_one : ∑ view, viewMass view = 1)
    (hresponse : ∀ view, |response view| ≤ 1) :
    |∑ view, viewMass view * response view * posteriorParity view| ≤
      posteriorSpectralRadius viewMass posteriorParity := by
  classical
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun view : View => Real.sqrt (viewMass view) * response view)
    (fun view : View => Real.sqrt (viewMass view) * posteriorParity view)
  have hleft :
      (∑ view,
        (Real.sqrt (viewMass view) * response view) *
          (Real.sqrt (viewMass view) * posteriorParity view)) =
        ∑ view, viewMass view * response view * posteriorParity view := by
    apply Finset.sum_congr rfl
    intro view _
    calc
      (Real.sqrt (viewMass view) * response view) *
          (Real.sqrt (viewMass view) * posteriorParity view) =
        Real.sqrt (viewMass view) ^ 2 * response view * posteriorParity view := by ring
      _ = viewMass view * response view * posteriorParity view := by
        rw [Real.sq_sqrt (hmass view)]
  have hfirst :
      (∑ view, (Real.sqrt (viewMass view) * response view) ^ 2) ≤ 1 := by
    calc
      (∑ view, (Real.sqrt (viewMass view) * response view) ^ 2) ≤
          ∑ view, viewMass view := by
        apply Finset.sum_le_sum
        intro view _
        calc
          (Real.sqrt (viewMass view) * response view) ^ 2 =
              viewMass view * response view ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (hmass view)]
          _ ≤ viewMass view * 1 := by
            exact mul_le_mul_of_nonneg_left
              ((sq_le_one_iff_abs_le_one (response view)).2 (hresponse view)) (hmass view)
          _ = viewMass view := mul_one _
      _ = 1 := hmass_one
  have hsecond :
      (∑ view, (Real.sqrt (viewMass view) * posteriorParity view) ^ 2) =
        posteriorSpectralEnergy viewMass posteriorParity := by
    unfold posteriorSpectralEnergy
    apply Finset.sum_congr rfl
    intro view _
    rw [mul_pow, Real.sq_sqrt (hmass view)]
  have henergy_nonneg :
      0 ≤ posteriorSpectralEnergy viewMass posteriorParity := by
    unfold posteriorSpectralEnergy
    exact Finset.sum_nonneg fun view _ =>
      mul_nonneg (hmass view) (sq_nonneg (posteriorParity view))
  apply Real.abs_le_sqrt
  rw [← hleft]
  calc
    (∑ view,
        (Real.sqrt (viewMass view) * response view) *
          (Real.sqrt (viewMass view) * posteriorParity view)) ^ 2 ≤
      (∑ view, (Real.sqrt (viewMass view) * response view) ^ 2) *
        ∑ view, (Real.sqrt (viewMass view) * posteriorParity view) ^ 2 := hcauchy
    _ ≤ 1 * posteriorSpectralEnergy viewMass posteriorParity := by
      rw [hsecond]
      exact mul_le_mul_of_nonneg_right hfirst henergy_nonneg
    _ = posteriorSpectralEnergy viewMass posteriorParity := one_mul _

/-! ### Exact finite complete-channel specialization -/

/-- Complete finite channel mass `W(view | secret,message)`. -/
abbrev CompleteChannel (Index View : Type) :=
  View → BitVector Index → BitVector Index → ℝ

/-- Uniform-input marginal mass of a complete public view. -/
def completeChannelViewMass
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View) (view : View) : ℝ :=
  (∑ secret : BitVector Index, ∑ message : BitVector Index,
      channel view secret message) / cubeSize Index ^ 2

/-- Uniform-input diagonal-parity numerator at a complete view. -/
def completeChannelParityNumerator
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View) (frequency : BitVector Index)
    (view : View) : ℝ :=
  (∑ secret : BitVector Index, ∑ message : BitVector Index,
      walsh frequency secret * walsh frequency message *
        channel view secret message) / cubeSize Index ^ 2

/-- Posterior diagonal parity on the complete view. -/
def completeChannelPosteriorParity
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View) (frequency : BitVector Index) : View → ℝ :=
  posteriorFromNumerator (completeChannelViewMass channel)
    (completeChannelParityNumerator channel frequency)

/-- Acceptance function induced by a response on the complete finite view. -/
def completeChannelResponse
    {Index View : Type} [Fintype View]
    (channel : CompleteChannel Index View) (response : View → ℝ)
    (secret message : BitVector Index) : ℝ :=
  ∑ view, channel view secret message * response view

@[simp]
theorem abs_walsh {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency word : BitVector Index) : |walsh frequency word| = 1 := by
  classical
  rw [walsh, Finset.abs_prod]
  calc
    (∏ coordinate,
        |if frequency coordinate then bitSign (word coordinate) else 1|) =
      ∏ _coordinate : Index, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro coordinate _
        cases frequency coordinate <;> cases word coordinate <;> norm_num [bitSign]
    _ = 1 := by simp

theorem completeChannelViewMass_nonneg
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (view : View) : 0 ≤ completeChannelViewMass channel view := by
  unfold completeChannelViewMass
  exact div_nonneg
    (Finset.sum_nonneg fun secret _ =>
      Finset.sum_nonneg fun message _ => hchannel view secret message)
    (sq_nonneg (cubeSize Index))

/-- A normalized conditional channel induces a normalized uniform-input view marginal. -/
theorem sum_completeChannelViewMass_eq_one
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hnormalized : ∀ secret message, ∑ view, channel view secret message = 1) :
    ∑ view, completeChannelViewMass channel view = 1 := by
  classical
  unfold completeChannelViewMass
  rw [← Finset.sum_div]
  have hreorder :
      (∑ view : View, ∑ secret : BitVector Index, ∑ message : BitVector Index,
          channel view secret message) =
        ∑ secret : BitVector Index, ∑ message : BitVector Index,
          ∑ view : View, channel view secret message := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro secret _
    rw [Finset.sum_comm]
  rw [hreorder]
  simp_rw [hnormalized]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcardCube : (Fintype.card (BitVector Index) : ℝ) = cubeSize Index := by
    simp [cubeSize]
  rw [hcardCube]
  field_simp [cubeSize_ne_zero Index]

/-- The parity numerator has absolute value at most its view mass. -/
theorem abs_completeChannelParityNumerator_le_viewMass
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (frequency : BitVector Index) (view : View) :
    |completeChannelParityNumerator channel frequency view| ≤
      completeChannelViewMass channel view := by
  classical
  have hraw :
      |∑ secret : BitVector Index, ∑ message : BitVector Index,
          walsh frequency secret * walsh frequency message *
            channel view secret message| ≤
        ∑ secret : BitVector Index, ∑ message : BitVector Index,
          channel view secret message := by
    calc
      |∑ secret : BitVector Index, ∑ message : BitVector Index,
          walsh frequency secret * walsh frequency message *
            channel view secret message| ≤
        ∑ secret : BitVector Index,
          |∑ message : BitVector Index,
            walsh frequency secret * walsh frequency message *
              channel view secret message| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ secret : BitVector Index, ∑ message : BitVector Index,
          |walsh frequency secret * walsh frequency message *
            channel view secret message| := by
        exact Finset.sum_le_sum fun secret _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ secret : BitVector Index, ∑ message : BitVector Index,
          channel view secret message := by
        apply Finset.sum_congr rfl
        intro secret _
        apply Finset.sum_congr rfl
        intro message _
        rw [abs_mul, abs_mul, abs_walsh, abs_walsh, one_mul, one_mul,
          abs_of_nonneg (hchannel view secret message)]
  unfold completeChannelParityNumerator completeChannelViewMass
  rw [abs_div, abs_of_nonneg (sq_nonneg (cubeSize Index))]
  exact div_le_div_of_nonneg_right hraw (sq_nonneg (cubeSize Index))

/-- Empty view fibers have zero parity numerator. -/
theorem completeChannelParityNumerator_eq_zero_of_viewMass_eq_zero
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (frequency : BitVector Index) (view : View)
    (hzero : completeChannelViewMass channel view = 0) :
    completeChannelParityNumerator channel frequency view = 0 := by
  have hbound := abs_completeChannelParityNumerator_le_viewMass
    channel hchannel frequency view
  rw [hzero] at hbound
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

/-- Numerator equals marginal mass times the totalized posterior on every view. -/
theorem completeChannelViewMass_mul_posterior_eq_numerator
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (frequency : BitVector Index) (view : View) :
    completeChannelViewMass channel view *
        completeChannelPosteriorParity channel frequency view =
      completeChannelParityNumerator channel frequency view := by
  unfold completeChannelPosteriorParity posteriorFromNumerator
  by_cases hzero : completeChannelViewMass channel view = 0
  · simp [hzero, completeChannelParityNumerator_eq_zero_of_viewMass_eq_zero
      channel hchannel frequency view hzero]
  · simp only [hzero, if_false]
    field_simp

/-- Exact finite posterior formula from the note, with zero-mass views totalized to zero. -/
theorem completeChannelPosteriorEnergy_formula
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View) (frequency : BitVector Index) :
    posteriorSpectralEnergy (completeChannelViewMass channel)
        (completeChannelPosteriorParity channel frequency) =
      ∑ view, if completeChannelViewMass channel view = 0 then 0 else
        completeChannelParityNumerator channel frequency view ^ 2 /
          completeChannelViewMass channel view :=
  posteriorSpectralEnergy_eq_sum_div _ _

/-- The Fourier coefficient of any complete-view response is its posterior-parity correlation. -/
theorem fourierCoefficient_completeChannelResponse
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (response : View → ℝ) (frequency : BitVector Index) :
    fourierCoefficient (completeChannelResponse channel response)
        frequency frequency =
      ∑ view, completeChannelParityNumerator channel frequency view * response view := by
  classical
  unfold fourierCoefficient completeChannelResponse completeChannelParityNumerator
  calc
    (∑ secret : BitVector Index, ∑ message : BitVector Index,
        (∑ view : View, channel view secret message * response view) *
          walsh frequency secret * walsh frequency message) / cubeSize Index ^ 2 =
      (∑ view : View, (∑ secret : BitVector Index, ∑ message : BitVector Index,
        walsh frequency secret * walsh frequency message *
          channel view secret message) * response view) / cubeSize Index ^ 2 := by
      congr 1
      calc
        (∑ secret : BitVector Index, ∑ message : BitVector Index,
          (∑ view : View, channel view secret message * response view) *
            walsh frequency secret * walsh frequency message) =
          ∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
            (walsh frequency secret * walsh frequency message *
              channel view secret message) * response view := by
          apply Finset.sum_congr rfl
          intro secret _
          apply Finset.sum_congr rfl
          intro message _
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro view _
          ring
        _ = ∑ secret : BitVector Index, ∑ view : View, ∑ message : BitVector Index,
            (walsh frequency secret * walsh frequency message *
              channel view secret message) * response view := by
          apply Finset.sum_congr rfl
          intro secret _
          rw [Finset.sum_comm]
        _ = ∑ view : View, ∑ secret : BitVector Index, ∑ message : BitVector Index,
            (walsh frequency secret * walsh frequency message *
              channel view secret message) * response view := by
          rw [Finset.sum_comm]
        _ = ∑ view : View, (∑ secret : BitVector Index, ∑ message : BitVector Index,
            walsh frequency secret * walsh frequency message *
              channel view secret message) * response view := by
          apply Finset.sum_congr rfl
          intro view _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro secret _
          rw [Finset.sum_mul]
    _ = ∑ view : View,
        ((∑ secret : BitVector Index, ∑ message : BitVector Index,
          walsh frequency secret * walsh frequency message *
            channel view secret message) / cubeSize Index ^ 2) * response view := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro view _
      field_simp [cubeSize_ne_zero Index]
    _ = ∑ view : View, completeChannelParityNumerator channel frequency view *
        response view := by rfl

/-- Complete finite-channel version of the sketch's spectral certificate. -/
theorem completeChannel_fourier_le_posteriorSpectralRadius
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (hnormalized : ∀ secret message, ∑ view, channel view secret message = 1)
    (response : View → ℝ) (hresponse : ∀ view, |response view| ≤ 1)
    (frequency : BitVector Index) :
    |fourierCoefficient (completeChannelResponse channel response)
        frequency frequency| ≤
      posteriorSpectralRadius (completeChannelViewMass channel)
        (completeChannelPosteriorParity channel frequency) := by
  calc
    |fourierCoefficient (completeChannelResponse channel response)
        frequency frequency| =
      |∑ view, completeChannelParityNumerator channel frequency view * response view| := by
        rw [fourierCoefficient_completeChannelResponse]
    _ = |∑ view, completeChannelViewMass channel view * response view *
        completeChannelPosteriorParity channel frequency view| := by
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro view _
      rw [← completeChannelViewMass_mul_posterior_eq_numerator
        channel hchannel frequency view]
      ring
    _ ≤ posteriorSpectralRadius (completeChannelViewMass channel)
        (completeChannelPosteriorParity channel frequency) :=
      channelSpectralBound _ _ _
        (completeChannelViewMass_nonneg channel hchannel)
        (sum_completeChannelViewMass_eq_one channel hnormalized) hresponse

/-! ## Black-box normalization boundary -/

/-- A one-bit point oracle, sufficient to witness the black-box separation. -/
abbrev OneBitPointOracle := Bool → Bool

def oneBitPointOracle (center : Bool) : OneBitPointOracle :=
  fun query => decide (query = center)

/-- Public xor action on a point oracle, implemented by precomposition. -/
def shiftOneBitPointOracle (mask : Bool) (oracle : OneBitPointOracle) :
    OneBitPointOracle :=
  fun query => oracle (LWE.MultiKeyAffine.maskedBit query mask)

/-- Point oracles obey the same public xor-shift normalization law. -/
theorem shiftOneBitPointOracle_point (center mask : Bool) :
    shiftOneBitPointOracle mask (oneBitPointOracle center) =
      oneBitPointOracle (LWE.MultiKeyAffine.maskedBit center mask) := by
  funext query
  cases center <;> cases mask <;> cases query <;>
    decide

/-- In the circular experiment the oracle center is always zero, independently of the secret. -/
theorem oneBitPointOracle_circular_constant (secret : Bool) :
    oneBitPointOracle (LWE.MultiKeyAffine.maskedBit secret secret) =
      oneBitPointOracle false := by
  cases secret <;> rfl

/-- Acceptance of the distinguisher that queries the point oracle at zero. -/
def oneBitZeroQueryAcceptance (secret message : Bool) : ℝ :=
  if oneBitPointOracle (LWE.MultiKeyAffine.maskedBit secret message) false then 1 else 0

def oneBitPointRealAcceptance : ℝ :=
  (∑ secret : Bool, oneBitZeroQueryAcceptance secret secret) / 2

def oneBitPointRandomAcceptance : ℝ :=
  (∑ secret : Bool, ∑ message : Bool,
    oneBitZeroQueryAcceptance secret message) / 4

/-- Public normalization and a large circular gap coexist with a secret-independent real view. -/
theorem oneBitPoint_real_random_gap :
    oneBitPointRealAcceptance - oneBitPointRandomAcceptance = 1 / 2 := by
  unfold oneBitPointRealAcceptance oneBitPointRandomAcceptance
  simp only [Fintype.sum_bool]
  norm_num [oneBitZeroQueryAcceptance, oneBitPointOracle,
    LWE.MultiKeyAffine.maskedBit]

/-- Every predictor given the circular real point-oracle view succeeds on a uniform one-bit secret
with probability exactly one half. -/
theorem oneBitPoint_predictor_success (predictor : OneBitPointOracle → Bool) :
    (∑ secret : Bool,
      if predictor
          (oneBitPointOracle (LWE.MultiKeyAffine.maskedBit secret secret)) = secret
        then (1 : ℝ) else 0) / 2 = 1 / 2 := by
  have hfalse := oneBitPointOracle_circular_constant false
  have htrue := oneBitPointOracle_circular_constant true
  simp only [Fintype.sum_bool]
  rw [hfalse, htrue]
  cases hprediction : predictor (oneBitPointOracle false) <;>
    norm_num [hprediction]

/-- The diagonal spectral-decay property is deliberately a predicate, not an axiom. -/
def NativeDiagonalSpectralDecay
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (spectralRadius : BitVector Index → ℝ) (degree : ℕ) (bound : ℝ) : Prop :=
  (∑ frequency ∈ highFrequencies Index degree, spectralRadius frequency) ≤ bound

/-- The exact remaining conditional theorem.  Low degrees are discharged by the affine-source
premise, while the complete-view radii control every high diagonal coefficient. -/
theorem conditionalNativeCircularSecurity
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ)
    (spectralRadius : BitVector Index → ℝ)
    (degree : ℕ) (delta spectralBound randomZeroBound randomZeroAdvantage : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient function frequency frequency| ≤
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta))
    (hchannel : ∀ frequency ∈ highFrequencies Index degree,
      |fourierCoefficient function frequency frequency| ≤ spectralRadius frequency)
    (hdecay : NativeDiagonalSpectralDecay spectralRadius degree spectralBound)
    (hendpoint : randomZeroAdvantage ≤ randomZeroBound) :
    |diagonalMean function - independentMean function| + randomZeroAdvantage ≤
      lowFrequencyCount Index degree *
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) +
          spectralBound + randomZeroBound := by
  have htail : diagonalTail function degree ≤ spectralBound := by
    calc
      diagonalTail function degree ≤
          ∑ frequency ∈ highFrequencies Index degree, spectralRadius frequency := by
        unfold diagonalTail
        exact Finset.sum_le_sum fun frequency hfrequency =>
          hchannel frequency hfrequency
      _ ≤ spectralBound := hdecay
  exact boundedDegreeNativeBridge_withEndpoint function degree delta spectralBound
    randomZeroBound randomZeroAdvantage hlow htail hendpoint

/-- The same theorem with the low-frequency multiplier written in the paper's binomial form. -/
theorem conditionalNativeCircularSecurity_binomial
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (function : BitVector Index → BitVector Index → ℝ)
    (spectralRadius : BitVector Index → ℝ)
    (degree : ℕ) (delta spectralBound randomZeroBound randomZeroAdvantage : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient function frequency frequency| ≤
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta))
    (hchannel : ∀ frequency ∈ highFrequencies Index degree,
      |fourierCoefficient function frequency frequency| ≤ spectralRadius frequency)
    (hdecay : NativeDiagonalSpectralDecay spectralRadius degree spectralBound)
    (hendpoint : randomZeroAdvantage ≤ randomZeroBound) :
    |diagonalMean function - independentMean function| + randomZeroAdvantage ≤
      binomialLowFrequencyCount Index degree *
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) +
          spectralBound + randomZeroBound := by
  simpa only [lowFrequencyCount_eq_binomialLowFrequencyCount] using
    conditionalNativeCircularSecurity function spectralRadius degree delta spectralBound
      randomZeroBound randomZeroAdvantage hlow hchannel hdecay hendpoint

/-- Complete-channel specialization of the final conditional theorem.  The high-degree
coefficient certificate is derived internally from the exact posterior radii; only their summed
decay, the low-degree affine-source bound, and the random/zero endpoint remain premises. -/
theorem completeChannel_conditionalNativeCircularSecurity
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel_nonneg : ∀ view secret message, 0 ≤ channel view secret message)
    (hchannel_normalized : ∀ secret message,
      ∑ view, channel view secret message = 1)
    (response : View → ℝ) (hresponse : ∀ view, |response view| ≤ 1)
    (degree : ℕ) (delta spectralBound randomZeroBound randomZeroAdvantage : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient (completeChannelResponse channel response)
          frequency frequency| ≤
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta))
    (hdecay : NativeDiagonalSpectralDecay
      (fun frequency =>
        posteriorSpectralRadius (completeChannelViewMass channel)
          (completeChannelPosteriorParity channel frequency))
      degree spectralBound)
    (hendpoint : randomZeroAdvantage ≤ randomZeroBound) :
    |diagonalMean (completeChannelResponse channel response) -
        independentMean (completeChannelResponse channel response)| +
      randomZeroAdvantage ≤
        binomialLowFrequencyCount Index degree *
          Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) +
            spectralBound + randomZeroBound := by
  apply conditionalNativeCircularSecurity_binomial
    (completeChannelResponse channel response)
    (fun frequency =>
      posteriorSpectralRadius (completeChannelViewMass channel)
        (completeChannelPosteriorParity channel frequency))
    degree delta spectralBound randomZeroBound randomZeroAdvantage hlow
  · intro frequency _
    exact completeChannel_fourier_le_posteriorSpectralRadius channel
      hchannel_nonneg hchannel_normalized response hresponse frequency
  · exact hdecay
  · exact hendpoint

end

end FormalProof4FHE.TFHE.NativeTRGSWBarrierAndSpectralBoundary
