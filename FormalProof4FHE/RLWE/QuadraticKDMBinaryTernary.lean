/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.IntervalMaskedQuadratic
import FormalProof4FHE.RLWE.QuadraticKDM
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fin.Rev

/-!
# Binary and Ternary Conditional Quadratic KDM Security

This module formalizes `rlwe_quadratic_kdm_binary_ternary_extension.tex`.

For an exact coefficientwise binary or centered-ternary secret, an independent centered interval
mask `Z`, and public hint `T = S-Z`, the corrected HNF source rows are

`b0 = X-S`, `d j = c j * X + g j * Z^2 + E j`.

The public map

`A j = c j - 2*g j*T`, `B j = d j - c j*b0 - g j*T^2`

is proved to produce exactly `B j = A j*S + g j*S^2 + E j`.  Its random branch is an explicitly
inverted permutation, so it maps exactly to joint uniformity.  The final theorem composes this
compiler with a checked split search-to-decision certificate and a zero-message small-secret RLWE
bound.  As in the source document, the conclusion is conditional on the general-distribution HNF
search theorem and its concrete boundedness, entropy, sample-count, automorphism, and lattice
hypotheses; ordinary decisional RLWE alone is not claimed to imply the result.

The module also checks:

* the exact interval-hint support and average conditional guessing probability;
* the equivalent base-two average conditional min-entropy formula;
* signed-permutation bijections for centered ternary secrets and masks;
* the affine complement correction for binary secrets;
* the real-source affine-equivariance identity and random-payload permutation;
* the source-error norm distinction and the complementary weighted hinted-RLWE algebra.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.QuadraticKDMBinaryTernary

noncomputable section

/-! ## Centered interval encoding -/

/-- Shift an interval encoding by a public ring element.  The mask value changes from `Z` to
`Z-center`, while the decoded hint changes from `S-Z` to `S-(Z-center)`. -/
def shiftMaskEncoding
    {R Secret Mask Hint : Type} [CommRing R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint) (center : R) :
    IntervalMaskedQuadratic.Encoding R Secret Mask Hint where
  secretValue := encoding.secretValue
  maskValue := fun mask ↦ encoding.maskValue mask - center
  hint := encoding.hint
  hintValue := fun hint ↦ encoding.hintValue hint + center
  hintValue_hint := by
    intro secret mask
    rw [encoding.hintValue_hint]
    ring
  hintSecret_injective := encoding.hintSecret_injective

@[simp]
theorem shiftMaskEncoding_secretValue
    {R Secret Mask Hint : Type} [CommRing R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint) (center : R) (secret : Secret) :
    (shiftMaskEncoding encoding center).secretValue secret = encoding.secretValue secret := rfl

@[simp]
theorem shiftMaskEncoding_maskValue
    {R Secret Mask Hint : Type} [CommRing R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint) (center : R) (mask : Mask) :
    (shiftMaskEncoding encoding center).maskValue mask = encoding.maskValue mask - center := rfl

@[simp]
theorem shiftMaskEncoding_hintValue
    {R Secret Mask Hint : Type} [CommRing R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint) (center : R) (hint : Hint) :
    (shiftMaskEncoding encoding center).hintValue hint = encoding.hintValue hint + center := rfl

instance centeredIntervalSizeNeZero (radius : ℕ) : NeZero (2 * radius + 1) :=
  ⟨by omega⟩

/- Use the same bundled algebra dictionary selected by `IntervalMaskedQuadratic` for the
executable negacyclic carrier. -/
local instance centeredRqCommRing (q degree : ℕ) : CommRing (RLWE.Rq q degree) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree

local instance centeredRqSub (q degree : ℕ) : Sub (RLWE.Rq q degree) :=
  (centeredRqCommRing q degree).toAddGroupWithOne.toAddGroup.toSub

/-- Constant coefficient polynomial used to recenter `{0,...,2r}` to `{-r,...,r}`. -/
def radiusPolynomial (q degree radius : ℕ) : RLWE.Rq q degree :=
  IntervalMaskedQuadratic.natCoefficientPolynomial q degree fun _ ↦ radius

/-- Generic centered interval encoding with alphabet digits `{0,...,L-1}` and secret offset.
Its mask coefficients represent `z-r` for `z : Fin (2r+1)`. -/
def centeredIntervalEncoding
    (q degree L radius offset : ℕ) [NeZero L] :
    IntervalMaskedQuadratic.Encoding (RLWE.Rq q degree) (IntervalMaskedQuadratic.DigitSecret L degree)
      (IntervalMaskedQuadratic.IntervalMask (2 * radius + 1) degree)
      (IntervalMaskedQuadratic.IntervalHint L (2 * radius + 1) degree) :=
  shiftMaskEncoding
    (IntervalMaskedQuadratic.intervalEncoding q degree L (2 * radius + 1) offset)
    (radiusPolynomial q degree radius)

/-- Exact coefficientwise binary centered-interval encoding. -/
def binaryCenteredEncoding (q degree radius : ℕ) :
    IntervalMaskedQuadratic.Encoding (RLWE.Rq q degree) (IntervalMaskedQuadratic.BinarySecret degree)
      (IntervalMaskedQuadratic.IntervalMask (2 * radius + 1) degree)
      (IntervalMaskedQuadratic.IntervalHint 2 (2 * radius + 1) degree) :=
  centeredIntervalEncoding q degree 2 radius 0

/-- Exact coefficientwise centered-ternary centered-interval encoding. -/
def ternaryCenteredEncoding (q degree radius : ℕ) :
    IntervalMaskedQuadratic.Encoding (RLWE.Rq q degree) (IntervalMaskedQuadratic.TernarySecret degree)
      (IntervalMaskedQuadratic.IntervalMask (2 * radius + 1) degree)
      (IntervalMaskedQuadratic.IntervalHint 3 (2 * radius + 1) degree) :=
  centeredIntervalEncoding q degree 3 radius 1

/-! ## Exact finite-alphabet fibers and residual entropy -/

/-- A scalar secret in a canonical preimage of an interval hint. -/
def intervalHintSectionSecret (L M : ℕ) [NeZero L] [NeZero M]
    (hint : Fin (M + L - 1)) : Fin L :=
  if h : hint.val < M then
    ⟨0, Nat.pos_of_neZero L⟩
  else
    ⟨hint.val - (M - 1), by
      have hHint := hint.isLt
      have hL : 0 < L := Nat.pos_of_neZero L
      have hM : 0 < M := Nat.pos_of_neZero M
      omega⟩

/-- The matching scalar mask in the canonical preimage of an interval hint. -/
def intervalHintSectionMask (L M : ℕ) [NeZero L] [NeZero M]
    (hint : Fin (M + L - 1)) : Fin M :=
  if h : hint.val < M then
    ⟨M - 1 - hint.val, by
      have hM : 0 < M := Nat.pos_of_neZero M
      omega⟩
  else
    ⟨0, Nat.pos_of_neZero M⟩

/-- The scalar section really maps back to the selected hint. -/
theorem intervalHintSection_code
    (L M : ℕ) [NeZero L] [NeZero M] (hint : Fin (M + L - 1)) :
    (intervalHintSectionSecret L M hint).val +
        (M - 1 - (intervalHintSectionMask L M hint).val) = hint.val := by
  by_cases h : hint.val < M
  · simp [intervalHintSectionSecret, intervalHintSectionMask, h]
    have hM : 0 < M := Nat.pos_of_neZero M
    omega
  · simp [intervalHintSectionSecret, intervalHintSectionMask, h]
    have hM : 0 < M := Nat.pos_of_neZero M
    omega

/-- Every vector interval hint has an explicit secret/mask preimage. -/
theorem intervalHintCode_surjective
    (L M degree : ℕ) [NeZero L] [NeZero M] :
    Function.Surjective (fun value :
      IntervalMaskedQuadratic.DigitSecret L degree ×
        IntervalMaskedQuadratic.IntervalMask M degree ↦
      IntervalMaskedQuadratic.intervalHintCode L M degree value.1 value.2) := by
  intro hint
  let secret : IntervalMaskedQuadratic.DigitSecret L degree :=
    fun coefficient ↦ intervalHintSectionSecret L M (hint coefficient)
  let mask : IntervalMaskedQuadratic.IntervalMask M degree :=
    fun coefficient ↦ intervalHintSectionMask L M (hint coefficient)
  refine ⟨(secret, mask), ?_⟩
  funext coefficient
  apply Fin.ext
  exact intervalHintSection_code L M (hint coefficient)

/-- For fixed hint and secret, at most one interval mask is compatible. -/
theorem intervalHintCode_mask_unique
    (L M degree : ℕ) [NeZero L] [NeZero M]
    (secret : IntervalMaskedQuadratic.DigitSecret L degree)
    {leftMask rightMask : IntervalMaskedQuadratic.IntervalMask M degree}
    (hCode : IntervalMaskedQuadratic.intervalHintCode L M degree secret leftMask =
      IntervalMaskedQuadratic.intervalHintCode L M degree secret rightMask) :
    leftMask = rightMask := by
  have hInput : (secret, leftMask) = (secret, rightMask) :=
    IntervalMaskedQuadratic.intervalHintCode_secret_injective L M degree
      (show
      (IntervalMaskedQuadratic.intervalHintCode L M degree secret leftMask, secret) =
        (IntervalMaskedQuadratic.intervalHintCode L M degree secret rightMask, secret) by
        rw [hCode])
  exact congrArg Prod.snd hInput

/-- The actual support of the interval hint under uniform secret/mask pairs. -/
def intervalHintSupport
    (L M degree : ℕ) [NeZero L] [NeZero M] :
    Finset (IntervalMaskedQuadratic.IntervalHint L M degree) :=
  Finset.univ.image fun value :
      IntervalMaskedQuadratic.DigitSecret L degree × IntervalMaskedQuadratic.IntervalMask M degree ↦
    IntervalMaskedQuadratic.intervalHintCode L M degree value.1 value.2

/-- The hint support is the entire product alphabet of size `(M+L-1)^degree`. -/
theorem intervalHintSupport_eq_univ
    (L M degree : ℕ) [NeZero L] [NeZero M] :
    intervalHintSupport L M degree = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro hint
  obtain ⟨⟨secret, mask⟩, hCode⟩ := intervalHintCode_surjective L M degree hint
  exact Finset.mem_image.mpr ⟨(secret, mask), Finset.mem_univ _, hCode⟩

/-- Finite average conditional guessing probability.  The uniqueness theorem above identifies
this support-size ratio with `E_t max_s Pr[S=s | T=t]` for uniform independent secret and mask. -/
def intervalAverageGuessingProbability
    (L M degree : ℕ) [NeZero L] [NeZero M] : ℝ :=
  (intervalHintSupport L M degree).card /
    Fintype.card (IntervalMaskedQuadratic.DigitSecret L degree × IntervalMaskedQuadratic.IntervalMask M degree)

/-- Exact average guessing probability `(M+L-1)^degree / (L*M)^degree`. -/
theorem intervalAverageGuessingProbability_eq
    (L M degree : ℕ) [NeZero L] [NeZero M] :
    intervalAverageGuessingProbability L M degree =
      ((((M + L - 1 : ℕ) : ℝ) / ((L : ℝ) * (M : ℝ))) ^ degree) := by
  rw [intervalAverageGuessingProbability, intervalHintSupport_eq_univ]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_prod, Nat.cast_pow, Nat.cast_mul]
  rw [div_pow]
  rw [mul_pow]

/-- Average conditional min-entropy in bits, defined from the exact guessing probability. -/
def intervalResidualMinEntropy
    (L M degree : ℕ) [NeZero L] [NeZero M] : ℝ :=
  -Real.logb 2 (intervalAverageGuessingProbability L M degree)

/-- Exact residual-entropy formula
`degree * log_2 (L*M/(M+L-1))`. -/
theorem intervalResidualMinEntropy_eq
    (L M degree : ℕ) [NeZero L] [NeZero M] :
    intervalResidualMinEntropy L M degree =
      (degree : ℝ) *
        Real.logb 2 (((L : ℝ) * (M : ℝ)) / ((M + L - 1 : ℕ) : ℝ)) := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hSupportNat : 0 < M + L - 1 := by
    have hLNat : 0 < L := Nat.pos_of_neZero L
    have hMNat : 0 < M := Nat.pos_of_neZero M
    omega
  have hSupport : (((M + L - 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold intervalResidualMinEntropy
  rw [intervalAverageGuessingProbability_eq, Real.logb_pow,
    Real.logb_div hSupport (mul_ne_zero hL hM),
    Real.logb_div (mul_ne_zero hL hM) hSupport]
  ring

/-- Binary residual entropy `n*log_2(2M/(M+1))`. -/
theorem binary_intervalResidualMinEntropy_eq
    (M degree : ℕ) [NeZero M] :
    intervalResidualMinEntropy 2 M degree =
      (degree : ℝ) * Real.logb 2 ((2 * (M : ℝ)) / ((M + 1 : ℕ) : ℝ)) := by
  rw [intervalResidualMinEntropy_eq]
  norm_num

/-- Ternary residual entropy `n*log_2(3M/(M+2))`. -/
theorem ternary_intervalResidualMinEntropy_eq
    (M degree : ℕ) [NeZero M] :
    intervalResidualMinEntropy 3 M degree =
      (degree : ℝ) * Real.logb 2 ((3 * (M : ℝ)) / ((M + 2 : ℕ) : ℝ)) := by
  rw [intervalResidualMinEntropy_eq]
  norm_num

/-- Binary centered-mask entropy with `M=2r+1`. -/
theorem binary_centeredResidualMinEntropy_eq
    (radius degree : ℕ) :
    intervalResidualMinEntropy 2 (2 * radius + 1) degree =
      (degree : ℝ) * Real.logb 2
        ((2 * ((2 * radius + 1 : ℕ) : ℝ)) / ((2 * radius + 2 : ℕ) : ℝ)) := by
  rw [binary_intervalResidualMinEntropy_eq]

/-- Centered-ternary centered-mask entropy with `M=2r+1`. -/
theorem ternary_centeredResidualMinEntropy_eq
    (radius degree : ℕ) :
    intervalResidualMinEntropy 3 (2 * radius + 1) degree =
      (degree : ℝ) * Real.logb 2
        ((3 * ((2 * radius + 1 : ℕ) : ℝ)) / ((2 * radius + 3 : ℕ) : ℝ)) := by
  rw [ternary_intervalResidualMinEntropy_eq]

/-! ## Masked correlated HNF source and exact compiler -/

/-- Public masked-source transcript `(T,b0,{(c_j,d_j)}_j)`. -/
structure MaskedSourceTranscript (R Row : Type) where
  hint : R
  anchor : R
  coefficient : Row → R
  body : Row → R

@[ext]
theorem MaskedSourceTranscript.ext
    {R Row : Type} {left right : MaskedSourceTranscript R Row}
    (hHint : left.hint = right.hint) (hAnchor : left.anchor = right.anchor)
    (hCoefficient : left.coefficient = right.coefficient) (hBody : left.body = right.body) :
    left = right := by
  cases left
  cases right
  simp_all

/-- A family of two-component target rows. -/
abbrev TargetTranscript (R Row : Type) := QuadraticKDM.TargetTranscript R Row

/-- Assemble a real masked HNF source transcript from ring-valued secret and mask. -/
def rawRealSourceTranscript {R Row : Type} [CommRing R]
    (weight : Row → R) (auxiliarySecret secret mask : R)
    (finalError coefficient : Row → R) : MaskedSourceTranscript R Row where
  hint := secret - mask
  anchor := auxiliarySecret - secret
  coefficient := coefficient
  body := fun row ↦ coefficient row * auxiliarySecret +
    weight row * mask ^ 2 + finalError row

/-- Assemble a real source transcript from a finite interval encoding. -/
def realSourceTranscript
    {R Secret Mask Hint Row : Type} [CommRing R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (auxiliarySecret : R) (secret : Secret) (mask : Mask)
    (finalError coefficient : Row → R) : MaskedSourceTranscript R Row :=
  rawRealSourceTranscript weight auxiliarySecret
    (encoding.secretValue secret) (encoding.maskValue mask) finalError coefficient

/-- Canonical fixed-gadget target KDM rows. -/
def kdmTranscript {R Row : Type} [CommRing R]
    (weight : Row → R) (secret : R) (finalError mask : Row → R) :
    TargetTranscript R Row :=
  (mask, fun row ↦ mask row * secret + weight row * secret ^ 2 + finalError row)

/-- Canonical zero-message rows with the same exact secret and final-error values. -/
def zeroTranscript {R Row : Type} [CommRing R]
    (secret : R) (finalError mask : Row → R) : TargetTranscript R Row :=
  (mask, fun row ↦ mask row * secret + finalError row)

/-- Public masked-source compiler from the extension document. -/
def compile {R Row : Type} [CommRing R]
    (weight : Row → R) (source : MaskedSourceTranscript R Row) :
    TargetTranscript R Row :=
  (fun row ↦ source.coefficient row - 2 * weight row * source.hint,
    fun row ↦ source.body row - source.coefficient row * source.anchor -
      weight row * source.hint ^ 2)

/-- **Exact masked-source compiler identity.**  The source term `g_j Z²` cancels and the final
target error is exactly `E_j`, without a gadget-weight factor. -/
theorem compile_realSourceTranscript
    {R Secret Mask Hint Row : Type} [CommRing R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (auxiliarySecret : R) (secret : Secret) (mask : Mask)
    (finalError coefficient : Row → R) :
    compile weight
        (realSourceTranscript encoding weight auxiliarySecret secret mask
          finalError coefficient) =
      kdmTranscript weight (encoding.secretValue secret) finalError
        (fun row ↦ coefficient row -
          2 * weight row * encoding.hintValue (encoding.hint secret mask)) := by
  apply Prod.ext
  · funext row
    simp only [compile, realSourceTranscript, rawRealSourceTranscript, kdmTranscript]
    rw [encoding.hintValue_hint]
  · funext row
    simp only [compile, realSourceTranscript, rawRealSourceTranscript, kdmTranscript]
    rw [encoding.hintValue_hint]
    ring

/-- Coefficient translation induced by the real compiler. -/
def coefficientShift
    {R Secret Mask Hint Row : Type} [CommRing R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (secret : Secret) (mask : Mask)
    (coefficient : Row → R) : Row → R :=
  fun row ↦ coefficient row -
    2 * weight row * encoding.hintValue (encoding.hint secret mask)

/-- The real-branch coefficient translation is a permutation. -/
theorem coefficientShift_bijective
    {R Secret Mask Hint Row : Type} [CommRing R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (secret : Secret) (mask : Mask) :
    Function.Bijective (coefficientShift encoding weight secret mask) := by
  let inverse : (Row → R) → (Row → R) := fun targetMask row ↦
    targetMask row + 2 * weight row *
      encoding.hintValue (encoding.hint secret mask)
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro coefficient
    funext row
    simp [inverse, coefficientShift]
  · intro targetMask
    funext row
    simp [inverse, coefficientShift]

/-- Fixed random-branch map on all source coefficient/body vectors. -/
def randomCompilerMap {R Row : Type} [CommRing R]
    (weight : Row → R) (hint anchor : R)
    (pair : TargetTranscript R Row) : TargetTranscript R Row :=
  compile weight ⟨hint, anchor, pair.1, pair.2⟩

/-- Explicit inverse of the random-branch compiler. -/
def randomCompilerMapInv {R Row : Type} [CommRing R]
    (weight : Row → R) (hint anchor : R)
    (output : TargetTranscript R Row) : TargetTranscript R Row :=
  (fun row ↦ output.1 row + 2 * weight row * hint,
    fun row ↦ output.2 row + (output.1 row + 2 * weight row * hint) * anchor +
      weight row * hint ^ 2)

@[simp]
theorem randomCompilerMapInv_randomCompilerMap
    {R Row : Type} [CommRing R]
    (weight : Row → R) (hint anchor : R) (pair : TargetTranscript R Row) :
    randomCompilerMapInv weight hint anchor
        (randomCompilerMap weight hint anchor pair) = pair := by
  apply Prod.ext
  · funext row
    simp [randomCompilerMapInv, randomCompilerMap, compile]
  · funext row
    simp [randomCompilerMapInv, randomCompilerMap, compile]
    ring

@[simp]
theorem randomCompilerMap_randomCompilerMapInv
    {R Row : Type} [CommRing R]
    (weight : Row → R) (hint anchor : R) (output : TargetTranscript R Row) :
    randomCompilerMap weight hint anchor
        (randomCompilerMapInv weight hint anchor output) = output := by
  apply Prod.ext
  · funext row
    simp [randomCompilerMapInv, randomCompilerMap, compile]
  · funext row
    simp [randomCompilerMapInv, randomCompilerMap, compile]
    ring

/-- Conditioned on the public hint and random anchor, the compiler is a permutation. -/
theorem randomCompilerMap_bijective
    {R Row : Type} [CommRing R]
    (weight : Row → R) (hint anchor : R) :
    Function.Bijective (randomCompilerMap weight hint anchor) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨randomCompilerMapInv weight hint anchor,
      randomCompilerMapInv_randomCompilerMap weight hint anchor,
      randomCompilerMap_randomCompilerMapInv weight hint anchor⟩

/-! ## Source residual change of variables -/

/-- The secret/final-error variables entering one conditioned source-error block. -/
abbrev SourceLatentError (R Row : Type) := R × (Row → R)

/-- For fixed public hint, the source error change of variables
`(S,E) ↦ (-S, (g_j(S-T)²+E_j)_j)`. -/
def sourceErrorChange {R Row : Type} [CommRing R]
    (weight : Row → R) (hint : R) (input : SourceLatentError R Row) :
    SourceLatentError R Row :=
  (-input.1, fun row ↦ weight row * (input.1 - hint) ^ 2 + input.2 row)

/-- Explicit inverse of the conditioned source-error change of variables. -/
def sourceErrorChangeInv {R Row : Type} [CommRing R]
    (weight : Row → R) (hint : R) (output : SourceLatentError R Row) :
    SourceLatentError R Row :=
  (-output.1, fun row ↦
    output.2 row - weight row * ((-output.1) - hint) ^ 2)

@[simp]
theorem sourceErrorChangeInv_sourceErrorChange
    {R Row : Type} [CommRing R] (weight : Row → R) (hint : R)
    (input : SourceLatentError R Row) :
    sourceErrorChangeInv weight hint (sourceErrorChange weight hint input) = input := by
  apply Prod.ext
  · simp [sourceErrorChangeInv, sourceErrorChange]
  · funext row
    simp only [sourceErrorChangeInv, sourceErrorChange, neg_neg]
    ring

@[simp]
theorem sourceErrorChange_sourceErrorChangeInv
    {R Row : Type} [CommRing R] (weight : Row → R) (hint : R)
    (output : SourceLatentError R Row) :
    sourceErrorChange weight hint (sourceErrorChangeInv weight hint output) = output := by
  apply Prod.ext
  · simp [sourceErrorChangeInv, sourceErrorChange]
  · funext row
    simp only [sourceErrorChangeInv, sourceErrorChange, neg_neg]
    ring

/-- The conditioned source-error map is a bijection.  This is the deterministic step behind
preservation of conditional min-entropy in the source-residual-entropy lemma. -/
theorem sourceErrorChange_bijective
    {R Row : Type} [CommRing R] (weight : Row → R) (hint : R) :
    Function.Bijective (sourceErrorChange weight hint) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨sourceErrorChangeInv weight hint,
      sourceErrorChangeInv_sourceErrorChange weight hint,
      sourceErrorChange_sourceErrorChangeInv weight hint⟩

/-! ## Signed finite-alphabet actions -/

/-- A signed permutation of coefficient positions.  A true sign bit complements a finite digit;
after centering an odd alphabet, this complement is exactly negation. -/
structure SignedCoordinateAction (Index : Type) where
  permutation : Equiv.Perm Index
  negated : Index → Bool

/-- Apply a signed coordinate action to a finite-alphabet vector. -/
def signedDigitAction {Index : Type} {alphabet : ℕ}
    (action : SignedCoordinateAction Index) (value : Index → Fin alphabet) :
    Index → Fin alphabet :=
  fun index ↦
    if action.negated index then
      (value (action.permutation index)).rev
    else
      value (action.permutation index)

/-- Explicit inverse of a signed digit action. -/
def signedDigitActionInv {Index : Type} {alphabet : ℕ}
    (action : SignedCoordinateAction Index) (value : Index → Fin alphabet) :
    Index → Fin alphabet :=
  fun index ↦
    let source := action.permutation.symm index
    if action.negated source then (value source).rev else value source

@[simp]
theorem signedDigitActionInv_signedDigitAction
    {Index : Type} {alphabet : ℕ} (action : SignedCoordinateAction Index)
    (value : Index → Fin alphabet) :
    signedDigitActionInv action (signedDigitAction action value) = value := by
  funext index
  simp only [signedDigitActionInv]
  split <;> simp_all [signedDigitAction]

@[simp]
theorem signedDigitAction_signedDigitActionInv
    {Index : Type} {alphabet : ℕ} (action : SignedCoordinateAction Index)
    (value : Index → Fin alphabet) :
    signedDigitAction action (signedDigitActionInv action value) = value := by
  funext index
  simp only [signedDigitAction]
  split <;> simp_all [signedDigitActionInv]

/-- Signed coordinate actions permute every finite product alphabet. -/
theorem signedDigitAction_bijective
    {Index : Type} {alphabet : ℕ} (action : SignedCoordinateAction Index) :
    Function.Bijective (signedDigitAction (alphabet := alphabet) action) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨signedDigitActionInv action,
      signedDigitActionInv_signedDigitAction action,
      signedDigitAction_signedDigitActionInv action⟩

/-- Consequently a signed coordinate action preserves the exact uniform law. -/
theorem signedDigitAction_uniform_evalDist
    {Index : Type} {alphabet : ℕ}
    [Fintype Index] [DecidableEq Index] [Fintype (Fin alphabet)]
    [DecidableEq (Fin alphabet)] [SampleableType (Index → Fin alphabet)]
    (action : SignedCoordinateAction Index) :
    evalDist (signedDigitAction action <$> ($ᵗ (Index → Fin alphabet))) =
      evalDist ($ᵗ (Index → Fin alphabet)) :=
  evalDist_map_bijective_uniform_cross
    (α := Index → Fin alphabet) (β := Index → Fin alphabet)
    (signedDigitAction action) (signedDigitAction_bijective action)

/-- Integer value of a digit centered by a natural offset. -/
def centeredDigitValue {alphabet : ℕ} (offset : ℕ) (digit : Fin alphabet) : ℤ :=
  (digit.val : ℤ) - (offset : ℤ)

/-- Complementing a digit in an odd alphabet centered at `radius` negates its value. -/
theorem centeredDigitValue_rev
    (radius : ℕ) (digit : Fin (2 * radius + 1)) :
    centeredDigitValue radius digit.rev = -centeredDigitValue radius digit := by
  simp only [centeredDigitValue]
  change ((2 * radius + 1 - (digit.val + 1) : ℕ) : ℤ) - (radius : ℤ) =
    -((digit.val : ℤ) - (radius : ℤ))
  have hDigit := digit.isLt
  omega

/-- Pointwise centered-value law for a signed action on any odd alphabet. -/
theorem signedDigitAction_centeredValue
    {Index : Type} (radius : ℕ) (action : SignedCoordinateAction Index)
    (value : Index → Fin (2 * radius + 1)) (index : Index) :
    centeredDigitValue radius (signedDigitAction action value index) =
      if action.negated index then
        -centeredDigitValue radius (value (action.permutation index))
      else
        centeredDigitValue radius (value (action.permutation index)) := by
  by_cases h : action.negated index = true
  · simp [signedDigitAction, h, centeredDigitValue_rev]
  · have hFalse : action.negated index = false := Bool.eq_false_of_not_eq_true h
    simp [signedDigitAction, hFalse]

/-- Centered ternary coefficients `{-1,0,1}` are literally closed under every signed
permutation. -/
theorem ternary_signedDigitAction_centeredValue
    {Index : Type} (action : SignedCoordinateAction Index)
    (secret : Index → Fin 3) (index : Index) :
    centeredDigitValue 1 (signedDigitAction action secret index) =
      if action.negated index then
        -centeredDigitValue 1 (secret (action.permutation index))
      else
        centeredDigitValue 1 (secret (action.permutation index)) :=
  signedDigitAction_centeredValue 1 action secret index

/-- The centered interval mask `{-r,…,r}` is likewise closed under signed permutations. -/
theorem centeredMask_signedDigitAction_value
    {Index : Type} (radius : ℕ) (action : SignedCoordinateAction Index)
    (mask : Index → Fin (2 * radius + 1)) (index : Index) :
    centeredDigitValue radius (signedDigitAction action mask index) =
      if action.negated index then
        -centeredDigitValue radius (mask (action.permutation index))
      else
        centeredDigitValue radius (mask (action.permutation index)) :=
  signedDigitAction_centeredValue radius action mask index

/-- The binary affine correction bit `τ`: one precisely at negatively signed coordinates. -/
def binaryCorrection {Index : Type} (action : SignedCoordinateAction Index) (index : Index) : ℤ :=
  if action.negated index then 1 else 0

/-- Binary complementation is the affine rule `s ↦ -s+1`; positive coordinates are unchanged. -/
theorem binary_signedDigitAction_value
    {Index : Type} (action : SignedCoordinateAction Index)
    (secret : Index → Fin 2) (index : Index) :
    ((signedDigitAction action secret index).val : ℤ) =
      (if action.negated index then
          -((secret (action.permutation index)).val : ℤ)
        else
          ((secret (action.permutation index)).val : ℤ)) +
        binaryCorrection action index := by
  by_cases h : action.negated index = true
  · simp [signedDigitAction, binaryCorrection, h]
    have hDigit := (secret (action.permutation index)).isLt
    omega
  · have hFalse : action.negated index = false := Bool.eq_false_of_not_eq_true h
    simp [signedDigitAction, binaryCorrection, hFalse]

/-! ## Affine equivariance of the masked source -/

/-- The public transcript transformation used for binary affine equivariance.  Setting `tau=0`
gives the literal centered-ternary signed action at ring level. -/
def affineSourceTransform {R Row : Type} [CommRing R]
    (sigma : R ≃+* R) (tau : R) (source : MaskedSourceTranscript R Row) :
    MaskedSourceTranscript R Row where
  hint := sigma source.hint + tau
  anchor := sigma source.anchor
  coefficient := fun row ↦ sigma (source.coefficient row)
  body := fun row ↦ sigma (source.body row) + sigma (source.coefficient row) * tau

/-- Explicit inverse of the affine source transformation. -/
def affineSourceTransformInv {R Row : Type} [CommRing R]
    (sigma : R ≃+* R) (tau : R) (source : MaskedSourceTranscript R Row) :
    MaskedSourceTranscript R Row where
  hint := sigma.symm (source.hint - tau)
  anchor := sigma.symm source.anchor
  coefficient := fun row ↦ sigma.symm (source.coefficient row)
  body := fun row ↦ sigma.symm (source.body row - source.coefficient row * tau)

@[simp]
theorem affineSourceTransformInv_affineSourceTransform
    {R Row : Type} [CommRing R] (sigma : R ≃+* R) (tau : R)
    (source : MaskedSourceTranscript R Row) :
    affineSourceTransformInv sigma tau (affineSourceTransform sigma tau source) = source := by
  cases source with
  | mk hint anchor coefficient body =>
      apply MaskedSourceTranscript.ext
      · simp [affineSourceTransformInv, affineSourceTransform]
      · simp [affineSourceTransformInv, affineSourceTransform]
      · funext row
        simp [affineSourceTransformInv, affineSourceTransform]
      · funext row
        simp [affineSourceTransformInv, affineSourceTransform]

@[simp]
theorem affineSourceTransform_affineSourceTransformInv
    {R Row : Type} [CommRing R] (sigma : R ≃+* R) (tau : R)
    (source : MaskedSourceTranscript R Row) :
    affineSourceTransform sigma tau (affineSourceTransformInv sigma tau source) = source := by
  cases source with
  | mk hint anchor coefficient body =>
      apply MaskedSourceTranscript.ext
      · simp [affineSourceTransformInv, affineSourceTransform]
      · simp [affineSourceTransformInv, affineSourceTransform]
      · funext row
        simp [affineSourceTransformInv, affineSourceTransform]
      · funext row
        simp [affineSourceTransformInv, affineSourceTransform]

/-- The affine source map is a permutation of public transcripts. -/
theorem affineSourceTransform_bijective
    {R Row : Type} [CommRing R] (sigma : R ≃+* R) (tau : R) :
    Function.Bijective (affineSourceTransform (Row := Row) sigma tau) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨affineSourceTransformInv sigma tau,
      affineSourceTransformInv_affineSourceTransform sigma tau,
      affineSourceTransform_affineSourceTransformInv sigma tau⟩

/-- **Binary affine source identity.**  If the public weights are fixed by the automorphism, the
TeX transformation maps a real source transcript to the same source formula under
`S'=σ(S)+τ`, `Z'=σ(Z)`, `X'=σ(X)+τ`, and `E'=σ(E)`. -/
theorem affineSourceTransform_rawRealSourceTranscript
    {R Row : Type} [CommRing R] (sigma : R ≃+* R) (tau : R)
    (weight : Row → R) (hWeight : ∀ row, sigma (weight row) = weight row)
    (auxiliarySecret secret mask : R) (finalError coefficient : Row → R) :
    affineSourceTransform sigma tau
        (rawRealSourceTranscript weight auxiliarySecret secret mask finalError coefficient) =
      rawRealSourceTranscript weight (sigma auxiliarySecret + tau) (sigma secret + tau)
        (sigma mask) (fun row ↦ sigma (finalError row))
        (fun row ↦ sigma (coefficient row)) := by
  apply MaskedSourceTranscript.ext
  · simp [affineSourceTransform, rawRealSourceTranscript]
    ring
  · simp [affineSourceTransform, rawRealSourceTranscript]
  · rfl
  · funext row
    simp only [affineSourceTransform, rawRealSourceTranscript, RingEquiv.map_add,
      RingEquiv.map_mul, map_pow, hWeight]
    ring

/-- The affine transcript permutation preserves an exact uniform transcript law. -/
theorem affineSourceTransform_uniform_evalDist
    {R Row : Type} [CommRing R]
    [Fintype (MaskedSourceTranscript R Row)]
    [DecidableEq (MaskedSourceTranscript R Row)]
    [SampleableType (MaskedSourceTranscript R Row)]
    (sigma : R ≃+* R) (tau : R) :
    evalDist (affineSourceTransform sigma tau <$>
        ($ᵗ (MaskedSourceTranscript R Row))) =
      evalDist ($ᵗ (MaskedSourceTranscript R Row)) :=
  evalDist_map_bijective_uniform_cross
    (α := MaskedSourceTranscript R Row) (β := MaskedSourceTranscript R Row)
    (affineSourceTransform sigma tau) (affineSourceTransform_bijective sigma tau)

/-- Hidden variables used to assemble one raw real source block. -/
structure RealSourceCoins (R Row : Type) where
  auxiliarySecret : R
  secret : R
  proofMask : R
  finalError : Row → R
  coefficient : Row → R

/-- Assemble the source transcript determined by a hidden coin tuple. -/
def transcriptOfRealSourceCoins {R Row : Type} [CommRing R]
    (weight : Row → R) (coins : RealSourceCoins R Row) : MaskedSourceTranscript R Row :=
  rawRealSourceTranscript weight coins.auxiliarySecret coins.secret coins.proofMask
    coins.finalError coins.coefficient

/-- Affine action on all hidden real-source variables. -/
def affineRealSourceCoins {R Row : Type} [CommRing R]
    (sigma : R ≃+* R) (tau : R) (coins : RealSourceCoins R Row) :
    RealSourceCoins R Row where
  auxiliarySecret := sigma coins.auxiliarySecret + tau
  secret := sigma coins.secret + tau
  proofMask := sigma coins.proofMask
  finalError := fun row ↦ sigma (coins.finalError row)
  coefficient := fun row ↦ sigma (coins.coefficient row)

/-- Pointwise commutation of the hidden and public binary affine actions. -/
theorem affineSourceTransform_transcriptOfRealSourceCoins
    {R Row : Type} [CommRing R] (sigma : R ≃+* R) (tau : R)
    (weight : Row → R) (hWeight : ∀ row, sigma (weight row) = weight row)
    (coins : RealSourceCoins R Row) :
    affineSourceTransform sigma tau (transcriptOfRealSourceCoins weight coins) =
      transcriptOfRealSourceCoins weight (affineRealSourceCoins sigma tau coins) :=
  affineSourceTransform_rawRealSourceTranscript sigma tau weight hWeight
    coins.auxiliarySecret coins.secret coins.proofMask coins.finalError coins.coefficient

/-- If the exact hidden coin law is invariant, the assembled real-source law is invariant under
the public affine map.  The finite signed-action theorems above discharge the binary/ternary
secret and centered-mask parts of this premise. -/
theorem affineSourceTransform_real_evalDist_of_coins_invariant
    {R Row : Type} [CommRing R]
    (sigma : R ≃+* R) (tau : R) (weight : Row → R)
    (hWeight : ∀ row, sigma (weight row) = weight row)
    (coinsSampler : ProbComp (RealSourceCoins R Row))
    (hCoins : evalDist (affineRealSourceCoins sigma tau <$> coinsSampler) =
      evalDist coinsSampler) :
    evalDist (affineSourceTransform sigma tau <$>
        (transcriptOfRealSourceCoins weight <$> coinsSampler)) =
      evalDist (transcriptOfRealSourceCoins weight <$> coinsSampler) := by
  calc
    evalDist (affineSourceTransform sigma tau <$>
        (transcriptOfRealSourceCoins weight <$> coinsSampler)) =
      evalDist ((affineRealSourceCoins sigma tau <$> coinsSampler) >>= fun coins ↦
        pure (transcriptOfRealSourceCoins weight coins)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine evalDist_bind_congr' coinsSampler fun coins ↦ ?_
      rw [affineSourceTransform_transcriptOfRealSourceCoins
        sigma tau weight hWeight coins]
    _ = evalDist (coinsSampler >>= fun coins ↦
        pure (transcriptOfRealSourceCoins weight coins)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hCoins _
    _ = evalDist (transcriptOfRealSourceCoins weight <$> coinsSampler) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- Uniform variables in the random source branch, conditioned on its genuine public hint. -/
abbrev RandomSourcePayload (R Row : Type) := R × TargetTranscript R Row

/-- Assemble a random source transcript from a fixed hint and uniform payload. -/
def randomSourceTranscript {R Row : Type}
    (hint : R) (payload : RandomSourcePayload R Row) : MaskedSourceTranscript R Row :=
  ⟨hint, payload.1, payload.2.1, payload.2.2⟩

/-- The binary affine action on the conditioned random payload. -/
def affineRandomSourcePayload {R Row : Type} [CommRing R]
    (sigma : R ≃+* R) (tau : R) (payload : RandomSourcePayload R Row) :
    RandomSourcePayload R Row :=
  (sigma payload.1,
    (fun row ↦ sigma (payload.2.1 row),
      fun row ↦ sigma (payload.2.2 row) + sigma (payload.2.1 row) * tau))

/-- Explicit inverse of the affine random-payload action. -/
def affineRandomSourcePayloadInv {R Row : Type} [CommRing R]
    (sigma : R ≃+* R) (tau : R) (payload : RandomSourcePayload R Row) :
    RandomSourcePayload R Row :=
  (sigma.symm payload.1,
    (fun row ↦ sigma.symm (payload.2.1 row),
      fun row ↦ sigma.symm (payload.2.2 row - payload.2.1 row * tau)))

@[simp]
theorem affineRandomSourcePayloadInv_affineRandomSourcePayload
    {R Row : Type} [CommRing R] (sigma : R ≃+* R) (tau : R)
    (payload : RandomSourcePayload R Row) :
    affineRandomSourcePayloadInv sigma tau
        (affineRandomSourcePayload sigma tau payload) = payload := by
  apply Prod.ext
  · simp [affineRandomSourcePayloadInv, affineRandomSourcePayload]
  · apply Prod.ext <;> funext row
    · simp [affineRandomSourcePayloadInv, affineRandomSourcePayload]
    · simp [affineRandomSourcePayloadInv, affineRandomSourcePayload]

@[simp]
theorem affineRandomSourcePayload_affineRandomSourcePayloadInv
    {R Row : Type} [CommRing R] (sigma : R ≃+* R) (tau : R)
    (payload : RandomSourcePayload R Row) :
    affineRandomSourcePayload sigma tau
        (affineRandomSourcePayloadInv sigma tau payload) = payload := by
  apply Prod.ext
  · simp [affineRandomSourcePayloadInv, affineRandomSourcePayload]
  · apply Prod.ext <;> funext row
    · simp [affineRandomSourcePayloadInv, affineRandomSourcePayload]
    · simp [affineRandomSourcePayloadInv, affineRandomSourcePayload]

/-- The conditioned random-branch transformation is a permutation. -/
theorem affineRandomSourcePayload_bijective
    {R Row : Type} [CommRing R] (sigma : R ≃+* R) (tau : R) :
    Function.Bijective (affineRandomSourcePayload (Row := Row) sigma tau) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨affineRandomSourcePayloadInv sigma tau,
      affineRandomSourcePayloadInv_affineRandomSourcePayload sigma tau,
      affineRandomSourcePayload_affineRandomSourcePayloadInv sigma tau⟩

/-- The public affine source action commutes with random-source assembly. -/
theorem affineSourceTransform_randomSourceTranscript
    {R Row : Type} [CommRing R] (sigma : R ≃+* R) (tau hint : R)
    (payload : RandomSourcePayload R Row) :
    affineSourceTransform sigma tau (randomSourceTranscript hint payload) =
      randomSourceTranscript (sigma hint + tau)
        (affineRandomSourcePayload sigma tau payload) := by
  rfl

/-- Random source distribution conditioned on one public hint. -/
def randomSourceAtHint
    {R Row : Type} [SampleableType (RandomSourcePayload R Row)]
    (hint : R) : ProbComp (MaskedSourceTranscript R Row) := do
  let payload ← $ᵗ (RandomSourcePayload R Row)
  return randomSourceTranscript hint payload

/-- **Exact random-branch affine symmetry.**  Conditioned on a hint, the public map produces the
same random source law at the affinely transformed hint. -/
theorem affineSourceTransform_randomSourceAtHint_evalDist
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (sigma : R ≃+* R) (tau hint : R) :
    evalDist (affineSourceTransform sigma tau <$> randomSourceAtHint (Row := Row) hint) =
      evalDist (randomSourceAtHint (Row := Row) (sigma hint + tau)) := by
  have hPayload :
      evalDist (affineRandomSourcePayload sigma tau <$>
          ($ᵗ (RandomSourcePayload R Row))) =
        evalDist ($ᵗ (RandomSourcePayload R Row)) :=
    evalDist_map_bijective_uniform_cross
      (α := RandomSourcePayload R Row) (β := RandomSourcePayload R Row)
      (affineRandomSourcePayload sigma tau)
      (affineRandomSourcePayload_bijective sigma tau)
  unfold randomSourceAtHint
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    evalDist (($ᵗ (RandomSourcePayload R Row)) >>= fun payload ↦
        pure (affineSourceTransform sigma tau (randomSourceTranscript hint payload))) =
      evalDist ((affineRandomSourcePayload sigma tau <$>
          ($ᵗ (RandomSourcePayload R Row))) >>= fun payload ↦
        pure (randomSourceTranscript (sigma hint + tau) payload)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine evalDist_bind_congr' ($ᵗ (RandomSourcePayload R Row)) fun payload ↦ ?_
      rw [affineSourceTransform_randomSourceTranscript]
    _ = evalDist (($ᵗ (RandomSourcePayload R Row)) >>= fun payload ↦
        pure (randomSourceTranscript (sigma hint + tau) payload)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hPayload _

/-- Random source law obtained by first sampling its genuine marginal hint. -/
def randomSourceFromHintSampler
    {R Row : Type} [SampleableType (RandomSourcePayload R Row)]
    (hintSampler : ProbComp R) : ProbComp (MaskedSourceTranscript R Row) :=
  hintSampler >>= randomSourceAtHint (Row := Row)

/-- If the genuine hint marginal has binary affine (or ternary linear) invariance, then the whole
random source distribution has exactly the same invariance. -/
theorem affineSourceTransform_random_evalDist_of_hint_invariant
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (sigma : R ≃+* R) (tau : R) (hintSampler : ProbComp R)
    (hHint : evalDist ((fun hint ↦ sigma hint + tau) <$> hintSampler) =
      evalDist hintSampler) :
    evalDist (affineSourceTransform sigma tau <$>
        randomSourceFromHintSampler (Row := Row) hintSampler) =
      evalDist (randomSourceFromHintSampler (Row := Row) hintSampler) := by
  calc
    evalDist (affineSourceTransform sigma tau <$>
        randomSourceFromHintSampler (Row := Row) hintSampler) =
      evalDist (hintSampler >>= fun hint ↦
        affineSourceTransform sigma tau <$> randomSourceAtHint (Row := Row) hint) := by
      simp only [randomSourceFromHintSampler, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc]
    _ =
      evalDist (((fun hint ↦ sigma hint + tau) <$> hintSampler) >>= fun hint ↦
        randomSourceAtHint (Row := Row) hint) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine evalDist_bind_congr' hintSampler fun hint ↦ ?_
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (affineSourceTransform_randomSourceAtHint_evalDist
          (Row := Row) sigma tau hint)
    _ = evalDist (hintSampler >>= randomSourceAtHint (Row := Row)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hHint _
    _ = evalDist (randomSourceFromHintSampler (Row := Row) hintSampler) := rfl

/-! ## Source boundedness and the complementary direct transform -/

/-- Abstract source-terminal-error bound.  Unlike the compiler's final error, this bound visibly
contains the public gadget-weight magnitude. -/
theorem sourceTerminalError_size_le
    {R : Type} [CommRing R]
    (size : R → ℝ) (weight mask finalError : R)
    (weightMagnitude gamma radius finalErrorBound : ℝ)
    (hAdd : ∀ left right, size (left + right) ≤ size left + size right)
    (hWeightMagnitude : 0 ≤ weightMagnitude)
    (hWeighted : size (weight * mask ^ 2) ≤ weightMagnitude * size (mask ^ 2))
    (hSquare : size (mask ^ 2) ≤ gamma * radius ^ 2)
    (hFinal : size finalError ≤ finalErrorBound) :
    size (weight * mask ^ 2 + finalError) ≤
      weightMagnitude * gamma * radius ^ 2 + finalErrorBound := by
  calc
    size (weight * mask ^ 2 + finalError) ≤
        size (weight * mask ^ 2) + size finalError := hAdd _ _
    _ ≤ weightMagnitude * size (mask ^ 2) + finalErrorBound :=
      add_le_add hWeighted hFinal
    _ ≤ weightMagnitude * (gamma * radius ^ 2) + finalErrorBound :=
      add_le_add (mul_le_mul_of_nonneg_left hSquare hWeightMagnitude) le_rfl
    _ = weightMagnitude * gamma * radius ^ 2 + finalErrorBound := by ring

/-- Weighted public hinted-RLWE transform used by the complementary direct proof. -/
def weightedQuadraticTransform
    {R Secret Mask Hint : Type} [Ring R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint) (weight : R)
    (transcript : IntervalMaskedQuadratic.HintTranscript Hint R) :
    IntervalMaskedQuadratic.Transcript R :=
  (transcript.mask - 2 * weight * encoding.hintValue transcript.hint,
    transcript.body - weight * encoding.hintValue transcript.hint ^ 2)

/-- The direct transform gives error `W-gZ²`; it does not synthesize a narrow independent `E`. -/
theorem weightedQuadraticTransform_real
    {R Secret Mask Hint : Type} [CommRing R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : R) (secret : Secret) (proofMask : Mask) (publicMask baseError : R) :
    weightedQuadraticTransform encoding weight
        ⟨encoding.hint secret proofMask,
          publicMask, publicMask * encoding.secretValue secret + baseError⟩ =
      let targetMask := publicMask -
        2 * weight * (encoding.secretValue secret - encoding.maskValue proofMask)
      (targetMask,
        targetMask * encoding.secretValue secret +
          weight * encoding.secretValue secret ^ 2 +
            (baseError - weight * encoding.maskValue proofMask ^ 2)) := by
  rw [weightedQuadraticTransform, encoding.hintValue_hint]
  apply Prod.ext
  · rfl
  · dsimp
    ring

/-- For each public hint, the weighted direct transform is a permutation of random pairs. -/
theorem weightedQuadraticTransform_pair_bijective
    {R Secret Mask Hint : Type} [Ring R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : R) (hint : Hint) :
    Function.Bijective (fun sample : R × R ↦
      (sample.1 - 2 * weight * encoding.hintValue hint,
        sample.2 - weight * encoding.hintValue hint ^ 2)) := by
  let inverse : R × R → R × R := fun sample ↦
    (sample.1 + 2 * weight * encoding.hintValue hint,
      sample.2 + weight * encoding.hintValue hint ^ 2)
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro sample
    apply Prod.ext <;> simp [inverse]
  · intro sample
    apply Prod.ext <;> simp [inverse]

/-! ## Exact masked-source and target games -/

/-- Real masked correlated HNF sampler for a fixed auxiliary secret `X`. -/
def sourceRealSampler
    {R Secret Mask Hint Row : Type} [CommRing R]
    [SampleableType Secret] [SampleableType Mask] [SampleableType (Row → R)]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R))
    (auxiliarySecret : R) : ProbComp (MaskedSourceTranscript R Row) := do
  let secret ← $ᵗ Secret
  let proofMask ← $ᵗ Mask
  let finalError ← finalErrorSampler
  let coefficient ← $ᵗ (Row → R)
  return realSourceTranscript encoding weight auxiliarySecret secret proofMask
    finalError coefficient

/-- Random source sampler retaining the genuine marginal hint but replacing anchor and all right
hand sides by mutually independent uniforms. -/
def sourceRandomSampler
    {R Secret Mask Hint Row : Type} [CommRing R]
    [SampleableType Secret] [SampleableType Mask] [SampleableType R]
    [SampleableType (TargetTranscript R Row)]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint) :
    ProbComp (MaskedSourceTranscript R Row) := do
  let secret ← $ᵗ Secret
  let proofMask ← $ᵗ Mask
  let anchor ← $ᵗ R
  let pair ← $ᵗ (TargetTranscript R Row)
  return ⟨encoding.hintValue (encoding.hint secret proofMask),
    anchor, pair.1, pair.2⟩

/-- Auxiliary-input source decision problem.  Its hidden secret is the auxiliary source secret
`X`; the finite-alphabet target secret and hint are sampled inside each public challenge. -/
def sourceProblem
    {R Secret Mask Hint Row : Type} [CommRing R]
    [SampleableType R] [SampleableType Secret] [SampleableType Mask]
    [SampleableType (Row → R)] [SampleableType (TargetTranscript R Row)]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R)) :
    FormalProof4FHE.LWE.AuxiliaryInput.Problem
      R (MaskedSourceTranscript R Row) Unit where
  sampleSecret := $ᵗ R
  sampleReal := sourceRealSampler encoding weight finalErrorSampler
  sampleZero := sourceRealSampler encoding weight finalErrorSampler
  sampleUniform := sourceRandomSampler encoding
  sampleAuxiliary := fun _ ↦ pure ()

/-- Target KDM sampler.  The independently sampled proof mask is deliberately retained in the
sampling code but does not occur in the output. -/
def kdmSampler
    {R Secret Mask Hint Row : Type} [CommRing R]
    [SampleableType Secret] [SampleableType Mask] [SampleableType (Row → R)]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R)) :
    ProbComp (TargetTranscript R Row) := do
  let secret ← $ᵗ Secret
  let _proofMask ← $ᵗ Mask
  let finalError ← finalErrorSampler
  let targetMask ← $ᵗ (Row → R)
  return kdmTranscript weight (encoding.secretValue secret) finalError targetMask

/-- Target zero-message sampler with the same exact secret and final-error laws. -/
def zeroSampler
    {R Secret Mask Hint Row : Type} [CommRing R]
    [SampleableType Secret] [SampleableType Mask] [SampleableType (Row → R)]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (finalErrorSampler : ProbComp (Row → R)) : ProbComp (TargetTranscript R Row) := do
  let secret ← $ᵗ Secret
  let _proofMask ← $ᵗ Mask
  let finalError ← finalErrorSampler
  let targetMask ← $ᵗ (Row → R)
  return zeroTranscript (encoding.secretValue secret) finalError targetMask

/-- Joint uniform target endpoint. -/
def uniformSampler {R Row : Type} [SampleableType (TargetTranscript R Row)] :
    ProbComp (TargetTranscript R Row) :=
  $ᵗ (TargetTranscript R Row)

/-- Target distinguisher. -/
abbrev Distinguisher (R Row : Type) := TargetTranscript R Row → ProbComp Bool

/-- KDM-versus-zero advantage. -/
noncomputable def kdmAdvantage
    {R Secret Mask Hint Row : Type} [CommRing R]
    [SampleableType Secret] [SampleableType Mask] [SampleableType (Row → R)]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R))
    (distinguisher : Distinguisher R Row) : ℝ :=
  (kdmSampler encoding weight finalErrorSampler >>= distinguisher).boolDistAdvantage
    (zeroSampler encoding finalErrorSampler >>= distinguisher)

/-- KDM-versus-uniform advantage. -/
noncomputable def kdmUniformAdvantage
    {R Secret Mask Hint Row : Type} [CommRing R]
    [SampleableType Secret] [SampleableType Mask] [SampleableType (Row → R)]
    [SampleableType (TargetTranscript R Row)]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R))
    (distinguisher : Distinguisher R Row) : ℝ :=
  (kdmSampler encoding weight finalErrorSampler >>= distinguisher).boolDistAdvantage
    (uniformSampler >>= distinguisher)

/-- Zero-message-versus-uniform advantage. -/
noncomputable def zeroUniformAdvantage
    {R Secret Mask Hint Row : Type} [CommRing R]
    [SampleableType Secret] [SampleableType Mask] [SampleableType (Row → R)]
    [SampleableType (TargetTranscript R Row)]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (finalErrorSampler : ProbComp (Row → R))
    (distinguisher : Distinguisher R Row) : ℝ :=
  (zeroSampler encoding finalErrorSampler >>= distinguisher).boolDistAdvantage
    (uniformSampler >>= distinguisher)

/-- Public source reduction induced by the masked compiler. -/
def sourceReduction {R Row : Type} [CommRing R]
    (weight : Row → R) (distinguisher : Distinguisher R Row) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (MaskedSourceTranscript R Row) Unit :=
  fun source _ ↦ distinguisher (compile weight source)

/-! ### Exact probability transport -/

/-- For fixed hidden context, translating the uniform source coefficients gives the canonical
target KDM row family. -/
theorem fixedRealCompile_evalDist_eq_kdm
    {R Secret Mask Hint Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (auxiliarySecret : R) (secret : Secret) (proofMask : Mask)
    (finalError : Row → R) :
    evalDist (($ᵗ (Row → R)) >>= fun coefficient ↦
        pure (compile weight
          (realSourceTranscript encoding weight auxiliarySecret secret proofMask
            finalError coefficient))) =
      evalDist (($ᵗ (Row → R)) >>= fun targetMask ↦
        pure (kdmTranscript weight (encoding.secretValue secret) finalError targetMask)) := by
  have hShift :
      evalDist (coefficientShift encoding weight secret proofMask <$>
        ($ᵗ (Row → R))) = evalDist ($ᵗ (Row → R)) :=
    evalDist_map_bijective_uniform_cross
      (α := Row → R) (β := Row → R)
      (coefficientShift encoding weight secret proofMask)
      (coefficientShift_bijective encoding weight secret proofMask)
  calc
    evalDist (($ᵗ (Row → R)) >>= fun coefficient ↦
        pure (compile weight
          (realSourceTranscript encoding weight auxiliarySecret secret proofMask
            finalError coefficient))) =
      evalDist ((coefficientShift encoding weight secret proofMask <$>
          ($ᵗ (Row → R))) >>= fun targetMask ↦
        pure (kdmTranscript weight (encoding.secretValue secret) finalError targetMask)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine evalDist_bind_congr' ($ᵗ (Row → R)) fun coefficient ↦ ?_
      rw [compile_realSourceTranscript]
      rfl
    _ = evalDist (($ᵗ (Row → R)) >>= fun targetMask ↦
        pure (kdmTranscript weight (encoding.secretValue secret) finalError targetMask)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hShift _

/-- Compiling the complete real source sampler gives the exact target KDM sampler. -/
theorem compiledSourceReal_evalDist_eq_kdm
    {R Secret Mask Hint Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [DecidableEq Secret] [Fintype Mask] [DecidableEq Mask]
    [SampleableType R] [SampleableType Secret] [SampleableType Mask]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R))
    (auxiliarySecret : R) :
    evalDist (sourceRealSampler encoding weight finalErrorSampler auxiliarySecret >>=
        fun source ↦ pure (compile weight source)) =
      evalDist (kdmSampler encoding weight finalErrorSampler) := by
  unfold sourceRealSampler kdmSampler
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' ($ᵗ Secret) fun secret ↦ ?_
  refine evalDist_bind_congr' ($ᵗ Mask) fun proofMask ↦ ?_
  refine evalDist_bind_congr' finalErrorSampler fun finalError ↦ ?_
  exact fixedRealCompile_evalDist_eq_kdm
    encoding weight auxiliarySecret secret proofMask finalError

/-- For fixed hint and anchor, the random compiler maps uniform vectors exactly to uniform. -/
theorem fixedRandomCompile_evalDist_eq_uniform
    {R Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (weight : Row → R) (hint anchor : R) :
    evalDist (($ᵗ (TargetTranscript R Row)) >>= fun pair ↦
        pure (compile weight ⟨hint, anchor, pair.1, pair.2⟩)) =
      evalDist (uniformSampler (R := R) (Row := Row)) := by
  simpa only [randomCompilerMap, uniformSampler, map_eq_bind_pure_comp,
      Function.comp_def] using
    (evalDist_map_bijective_uniform_cross
      (α := TargetTranscript R Row) (β := TargetTranscript R Row)
      (randomCompilerMap weight hint anchor)
      (randomCompilerMap_bijective weight hint anchor))

/-- Compiling the complete random source sampler gives the canonical uniform target sampler. -/
theorem compiledSourceRandom_evalDist_eq_uniform
    {R Secret Mask Hint Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [DecidableEq Secret] [Fintype Mask] [DecidableEq Mask]
    [SampleableType R] [SampleableType Secret] [SampleableType Mask]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) :
    evalDist (sourceRandomSampler encoding >>= fun source ↦
        pure (compile weight source)) =
      evalDist (uniformSampler (R := R) (Row := Row)) := by
  let Uniform := uniformSampler (R := R) (Row := Row)
  calc
    evalDist (sourceRandomSampler encoding >>= fun source ↦
        pure (compile weight source)) =
      evalDist (($ᵗ Secret) >>= fun secret ↦
        ($ᵗ Mask) >>= fun proofMask ↦
          ($ᵗ R) >>= fun _anchor ↦ Uniform) := by
      unfold sourceRandomSampler
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr' ($ᵗ Secret) fun secret ↦ ?_
      refine evalDist_bind_congr' ($ᵗ Mask) fun proofMask ↦ ?_
      refine evalDist_bind_congr' ($ᵗ R) fun anchor ↦ ?_
      exact fixedRandomCompile_evalDist_eq_uniform weight
        (encoding.hintValue (encoding.hint secret proofMask)) anchor
    _ = evalDist (($ᵗ Secret) >>= fun _secret ↦
        ($ᵗ Mask) >>= fun _proofMask ↦ Uniform) := by
      refine evalDist_bind_congr' ($ᵗ Secret) fun _secret ↦ ?_
      refine evalDist_bind_congr' ($ᵗ Mask) fun _proofMask ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _
    _ = evalDist (($ᵗ Secret) >>= fun _secret ↦ Uniform) := by
      refine evalDist_bind_congr' ($ᵗ Secret) fun _secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ Mask) (by simp) _
    _ = evalDist Uniform :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ Secret) (by simp) _

/-- The reduced source real game is exactly the target KDM game. -/
theorem sourceReduction_realGame_evalDist
    {R Secret Mask Hint Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [DecidableEq Secret] [Fintype Mask] [DecidableEq Mask]
    [SampleableType R] [SampleableType Secret] [SampleableType Mask]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R))
    (distinguisher : Distinguisher R Row) :
    evalDist (FormalProof4FHE.LWE.AuxiliaryInput.realGame
        (sourceProblem encoding weight finalErrorSampler)
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          (sourceReduction weight distinguisher))) =
      evalDist (kdmSampler encoding weight finalErrorSampler >>= distinguisher) := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.realGame
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
    sourceProblem sourceReduction
  simp only [pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun auxiliarySecret ↦
        sourceRealSampler encoding weight finalErrorSampler auxiliarySecret >>= fun source ↦
          distinguisher (compile weight source)) =
      evalDist (($ᵗ R) >>= fun _auxiliarySecret ↦
        kdmSampler encoding weight finalErrorSampler >>= distinguisher) := by
      refine evalDist_bind_congr' ($ᵗ R) fun auxiliarySecret ↦ ?_
      simpa only [bind_assoc, pure_bind] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (compiledSourceReal_evalDist_eq_kdm
            encoding weight finalErrorSampler auxiliarySecret) distinguisher)
    _ = evalDist (kdmSampler encoding weight finalErrorSampler >>= distinguisher) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _

/-- The reduced source random game is exactly the target uniform game. -/
theorem sourceReduction_randomGame_evalDist
    {R Secret Mask Hint Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [DecidableEq Secret] [Fintype Mask] [DecidableEq Mask]
    [SampleableType R] [SampleableType Secret] [SampleableType Mask]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R))
    (distinguisher : Distinguisher R Row) :
    evalDist (FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
        (sourceProblem encoding weight finalErrorSampler)
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          (sourceReduction weight distinguisher))) =
      evalDist (uniformSampler >>= distinguisher) := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
    sourceProblem sourceReduction
  simp only [pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun _auxiliarySecret ↦
        sourceRandomSampler encoding >>= fun source ↦
          distinguisher (compile weight source)) =
      evalDist (($ᵗ R) >>= fun _auxiliarySecret ↦
        uniformSampler >>= distinguisher) := by
      refine evalDist_bind_congr' ($ᵗ R) fun _auxiliarySecret ↦ ?_
      simpa only [bind_assoc, pure_bind] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (compiledSourceRandom_evalDist_eq_uniform encoding weight) distinguisher)
    _ = evalDist (uniformSampler >>= distinguisher) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _

/-- Target KDM-versus-uniform advantage equals the masked-source public decision advantage. -/
theorem kdmUniformAdvantage_eq_sourceAdvantage
    {R Secret Mask Hint Row : Type} [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [DecidableEq Secret] [Fintype Mask] [DecidableEq Mask]
    [SampleableType R] [SampleableType Secret] [SampleableType Mask]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R))
    (distinguisher : Distinguisher R Row) :
    kdmUniformAdvantage encoding weight finalErrorSampler distinguisher =
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (sourceProblem encoding weight finalErrorSampler)
        (sourceReduction weight distinguisher) := by
  unfold kdmUniformAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (sourceReduction_realGame_evalDist
        encoding weight finalErrorSampler distinguisher) true,
    evalDist_ext_iff.mp
      (sourceReduction_randomGame_evalDist
        encoding weight finalErrorSampler distinguisher) true]

/-- Triangle decomposition through the common uniform endpoint. -/
theorem kdmAdvantage_le_kdmUniform_add_zeroUniform
    {R Secret Mask Hint Row : Type} [CommRing R]
    [SampleableType Secret] [SampleableType Mask] [SampleableType (Row → R)]
    [SampleableType (TargetTranscript R Row)]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R))
    (distinguisher : Distinguisher R Row) :
    kdmAdvantage encoding weight finalErrorSampler distinguisher ≤
      kdmUniformAdvantage encoding weight finalErrorSampler distinguisher +
        zeroUniformAdvantage encoding finalErrorSampler distinguisher := by
  have h := ProbComp.boolDistAdvantage_triangle
    (kdmSampler encoding weight finalErrorSampler >>= distinguisher)
    (uniformSampler >>= distinguisher)
    (zeroSampler encoding finalErrorSampler >>= distinguisher)
  unfold kdmAdvantage kdmUniformAdvantage zeroUniformAdvantage
  rw [show (uniformSampler >>= distinguisher).boolDistAdvantage
      (zeroSampler encoding finalErrorSampler >>= distinguisher) =
      (zeroSampler encoding finalErrorSampler >>= distinguisher).boolDistAdvantage
        (uniformSampler >>= distinguisher) by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]] at h
  exact h

/-! ## Conditional binary/ternary security theorem -/

/-- **Conditional non-flooded finite-alphabet KDM security.**  The checked masked compiler,
split search-to-decision certificate, correlated-HNF search bound, and exact-distribution
zero-message RLWE bound imply fixed-gadget KDM security. -/
theorem kdmAdvantage_le_search_add_loss_add_zero
    {R Secret Mask Hint Row SearchChallenge SearchAuxiliary : Type}
    [CommRing R]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [DecidableEq Secret] [Fintype Mask] [DecidableEq Mask]
    [SampleableType R] [SampleableType Secret] [SampleableType Mask]
    (encoding : IntervalMaskedQuadratic.Encoding R Secret Mask Hint)
    (weight : Row → R) (finalErrorSampler : ProbComp (Row → R))
    (distinguisher : Distinguisher R Row)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      R SearchChallenge SearchAuxiliary)
    (certificate : QuadraticKDM.SplitSearchToDecisionCertificate
      (sourceProblem encoding weight finalErrorSampler) searchProblem)
    (searchBound lossBound zeroBound : ℝ)
    (hSearch :
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability searchProblem
        (certificate.toSolver (sourceReduction weight distinguisher))).toReal ≤ searchBound)
    (hLoss : certificate.loss (sourceReduction weight distinguisher) ≤ lossBound)
    (hZero : zeroUniformAdvantage encoding finalErrorSampler distinguisher ≤ zeroBound) :
    kdmAdvantage encoding weight finalErrorSampler distinguisher ≤
      (searchBound + lossBound) + zeroBound := by
  calc
    kdmAdvantage encoding weight finalErrorSampler distinguisher ≤
        kdmUniformAdvantage encoding weight finalErrorSampler distinguisher +
          zeroUniformAdvantage encoding finalErrorSampler distinguisher :=
      kdmAdvantage_le_kdmUniform_add_zeroUniform
        encoding weight finalErrorSampler distinguisher
    _ = FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (sourceProblem encoding weight finalErrorSampler)
          (sourceReduction weight distinguisher) +
        zeroUniformAdvantage encoding finalErrorSampler distinguisher := by
      rw [kdmUniformAdvantage_eq_sourceAdvantage
        encoding weight finalErrorSampler distinguisher]
    _ ≤ (searchBound + lossBound) + zeroBound :=
      add_le_add
        (QuadraticKDM.sourceAdvantage_le_search_add_loss
          (sourceProblem encoding weight finalErrorSampler) searchProblem certificate
          (sourceReduction weight distinguisher) searchBound lossBound hSearch hLoss)
        hZero

/-- Concrete centered-mask binary specialization of the conditional theorem.  The certificate
encapsulates the split-ring, transitivity, affine-equivariance, and hybrid accounting hypotheses;
`hSearch` and `hZero` are respectively the correlated-HNF search and exact binary RLWE bounds. -/
theorem binary_kdmAdvantage_le_search_add_loss_add_zero
    (q degree radius : ℕ) [NeZero q]
    {Row SearchChallenge SearchAuxiliary : Type}
    [Fintype Row] [DecidableEq Row]
    (weight : Row → RLWE.Rq q degree)
    (finalErrorSampler : ProbComp (Row → RLWE.Rq q degree))
    (distinguisher : Distinguisher (RLWE.Rq q degree) Row)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      (RLWE.Rq q degree) SearchChallenge SearchAuxiliary)
    (certificate : QuadraticKDM.SplitSearchToDecisionCertificate
      (sourceProblem (binaryCenteredEncoding q degree radius) weight finalErrorSampler)
      searchProblem)
    (searchBound lossBound zeroBound : ℝ)
    (hSearch :
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability searchProblem
        (certificate.toSolver (sourceReduction weight distinguisher))).toReal ≤ searchBound)
    (hLoss : certificate.loss (sourceReduction weight distinguisher) ≤ lossBound)
    (hZero : zeroUniformAdvantage (binaryCenteredEncoding q degree radius)
      finalErrorSampler distinguisher ≤ zeroBound) :
    kdmAdvantage (binaryCenteredEncoding q degree radius) weight finalErrorSampler
        distinguisher ≤
      (searchBound + lossBound) + zeroBound := by
  exact kdmAdvantage_le_search_add_loss_add_zero
    (binaryCenteredEncoding q degree radius) weight finalErrorSampler distinguisher
    searchProblem certificate searchBound lossBound zeroBound hSearch hLoss hZero

/-- Concrete centered-mask ternary specialization of the conditional theorem.  Here the
certificate records the literal signed-permutation invariance required by split-ring
search-to-decision, along with its remaining algebraic and complexity hypotheses. -/
theorem ternary_kdmAdvantage_le_search_add_loss_add_zero
    (q degree radius : ℕ) [NeZero q]
    {Row SearchChallenge SearchAuxiliary : Type}
    [Fintype Row] [DecidableEq Row]
    (weight : Row → RLWE.Rq q degree)
    (finalErrorSampler : ProbComp (Row → RLWE.Rq q degree))
    (distinguisher : Distinguisher (RLWE.Rq q degree) Row)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      (RLWE.Rq q degree) SearchChallenge SearchAuxiliary)
    (certificate : QuadraticKDM.SplitSearchToDecisionCertificate
      (sourceProblem (ternaryCenteredEncoding q degree radius) weight finalErrorSampler)
      searchProblem)
    (searchBound lossBound zeroBound : ℝ)
    (hSearch :
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability searchProblem
        (certificate.toSolver (sourceReduction weight distinguisher))).toReal ≤ searchBound)
    (hLoss : certificate.loss (sourceReduction weight distinguisher) ≤ lossBound)
    (hZero : zeroUniformAdvantage (ternaryCenteredEncoding q degree radius)
      finalErrorSampler distinguisher ≤ zeroBound) :
    kdmAdvantage (ternaryCenteredEncoding q degree radius) weight finalErrorSampler
        distinguisher ≤
      (searchBound + lossBound) + zeroBound := by
  exact kdmAdvantage_le_search_add_loss_add_zero
    (ternaryCenteredEncoding q degree radius) weight finalErrorSampler distinguisher
    searchProblem certificate searchBound lossBound zeroBound hSearch hLoss hZero

end

end FormalProof4FHE.RLWE.QuadraticKDMBinaryTernary
