/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveShiftedView

set_option autoImplicit false

/-!
# Relative-Mask Decomposition for the Direct Adaptive TFHE View

For a rank-one source GLWE key of positive degree, every complete nested coefficient mask has a
unique decomposition into:

* a normalized relative mask whose source coefficient zero is false; and
* one Boolean global-complement anchor.

This file proves the decomposition as an explicit equivalence and shows that sampling the two
pieces uniformly sends every fixed nested key to an exactly fresh nested key.  It is the sound
interface for composing a future nonlinear relative-mask evaluator with the already checked
global-complement complete-view transform.  No arbitrary coefficient mask is treated as a scalar-
affine ring map.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

open FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

/-- A normalized mask omits source coefficient zero, retains the other source coefficients, and
contains every suffix-ring coefficient.  The actual ring degree is `degree + 1`. -/
abbrev RelativeNestedMask (suffixRank degree : ℕ) :=
  BinarySecret degree × RingBinarySecret suffixRank (degree + 1)

/-- Reinsert the anchor and, when requested, globally complement every nested mask bit. -/
def encodeRelativeGlobalMask
    {suffixRank degree : ℕ}
    (mask : RelativeNestedMask suffixRank degree × Bool) :
    Mask 1 suffixRank (degree + 1) :=
  let relative := mask.1
  let toggle := mask.2
  (fun _ coefficient ↦
      Fin.cases toggle
        (fun tailCoordinate ↦
          LWE.MultiKeyAffine.maskedBit (relative.1 tailCoordinate) toggle)
        coefficient,
    fun component coefficient ↦
      LWE.MultiKeyAffine.maskedBit (relative.2 component coefficient) toggle)

/-- Recover the global bit from source coefficient zero, undo it everywhere, and remove the
normalized anchor. -/
def decodeRelativeGlobalMask
    {suffixRank degree : ℕ}
    (mask : Mask 1 suffixRank (degree + 1)) :
    RelativeNestedMask suffixRank degree × Bool :=
  let toggle := mask.1 0 0
  ((fun tailCoordinate ↦
      LWE.MultiKeyAffine.maskedBit (mask.1 0 tailCoordinate.succ) toggle,
    fun component coefficient ↦
      LWE.MultiKeyAffine.maskedBit (mask.2 component coefficient) toggle),
    toggle)

@[simp]
theorem decodeRelativeGlobalMask_encodeRelativeGlobalMask
    {suffixRank degree : ℕ}
    (mask : RelativeNestedMask suffixRank degree × Bool) :
    decodeRelativeGlobalMask (encodeRelativeGlobalMask mask) = mask := by
  rcases mask with ⟨⟨sourceTail, suffixMask⟩, toggle⟩
  apply Prod.ext
  · apply Prod.ext
    · funext coordinate
      cases toggle <;> simp [decodeRelativeGlobalMask, encodeRelativeGlobalMask,
        LWE.MultiKeyAffine.maskedBit]
    · funext component coefficient
      cases toggle <;> simp [decodeRelativeGlobalMask, encodeRelativeGlobalMask,
        LWE.MultiKeyAffine.maskedBit]
  · simp [decodeRelativeGlobalMask, encodeRelativeGlobalMask]

@[simp]
theorem encodeRelativeGlobalMask_decodeRelativeGlobalMask
    {suffixRank degree : ℕ}
    (mask : Mask 1 suffixRank (degree + 1)) :
    encodeRelativeGlobalMask (decodeRelativeGlobalMask mask) = mask := by
  rcases mask with ⟨sourceMask, suffixMask⟩
  apply Prod.ext
  · funext component coefficient
    have hcomponent : component = 0 := Subsingleton.elim _ _
    subst component
    refine Fin.cases ?_ (fun tailCoordinate ↦ ?_) coefficient
    · simp [decodeRelativeGlobalMask, encodeRelativeGlobalMask]
    · cases htoggle : sourceMask 0 0 <;>
        simp [decodeRelativeGlobalMask, encodeRelativeGlobalMask,
          LWE.MultiKeyAffine.maskedBit, htoggle]
  · funext component coefficient
    cases htoggle : sourceMask 0 0 <;>
      simp [decodeRelativeGlobalMask, encodeRelativeGlobalMask,
        LWE.MultiKeyAffine.maskedBit, htoggle]

/-- The relative-mask-plus-anchor representation is exactly equivalent to the complete nested
mask type. -/
def relativeGlobalMaskEquiv (suffixRank degree : ℕ) :
    (RelativeNestedMask suffixRank degree × Bool) ≃
      Mask 1 suffixRank (degree + 1) where
  toFun := encodeRelativeGlobalMask
  invFun := decodeRelativeGlobalMask
  left_inv := decodeRelativeGlobalMask_encodeRelativeGlobalMask
  right_inv := encodeRelativeGlobalMask_decodeRelativeGlobalMask

/-- Associativity of the Boolean XOR convention used throughout the nested-key action. -/
theorem maskedBit_assoc (first second third : Bool) :
    LWE.MultiKeyAffine.maskedBit
        (LWE.MultiKeyAffine.maskedBit first second) third =
      LWE.MultiKeyAffine.maskedBit first
        (LWE.MultiKeyAffine.maskedBit second third) := by
  cases first <;> cases second <;> cases third <;> rfl

/-- Nested coefficientwise XOR is associative. -/
theorem act_assoc
    {sourceRank suffixRank degree : ℕ}
    (first second third : Secret sourceRank suffixRank degree) :
    act (act first second) third = act first (act second third) := by
  rcases first with ⟨firstSource, firstSuffix⟩
  rcases second with ⟨secondSource, secondSuffix⟩
  rcases third with ⟨thirdSource, thirdSuffix⟩
  apply Prod.ext
  · funext component coefficient
    exact maskedBit_assoc (firstSource component coefficient)
      (secondSource component coefficient) (thirdSource component coefficient)
  · funext component coefficient
    exact maskedBit_assoc (firstSuffix component coefficient)
      (secondSuffix component coefficient) (thirdSuffix component coefficient)

/-- The normalized full nested mask, with the source anchor reinserted as false. -/
def liftRelativeNestedMask
    {suffixRank degree : ℕ}
    (mask : RelativeNestedMask suffixRank degree) :
    Mask 1 suffixRank (degree + 1) :=
  encodeRelativeGlobalMask (mask, false)

/-- The PKC vector-LWE key-homomorphic shift does not directly handle a nontrivial native
source-relative mask.  At modulus greater than two, the normalized source mask has a
scalar-affine ring-key transport exactly when every retained coefficient is false. -/
theorem scalarAffineXorTransport_liftRelativeSource_iff_trivial
    {q suffixRank degree : ℕ} (hq : 2 < q)
    (mask : RelativeNestedMask suffixRank degree) :
    ScalarAffineXorTransport q (degree + 1)
        ((liftRelativeNestedMask mask).1 0) ↔
      ∀ coordinate, mask.1 coordinate = false := by
  letI : NeZero q := ⟨by omega⟩
  constructor
  · intro htransport coordinate
    have hconstant := scalarAffineXorTransport_imp_constant hq
      ((liftRelativeNestedMask mask).1 0) htransport coordinate.succ
    simpa [liftRelativeNestedMask, encodeRelativeGlobalMask,
      LWE.MultiKeyAffine.maskedBit] using hconstant
  · intro hfalse
    apply scalarAffineXorTransport_of_all_false
    intro coordinate
    refine Fin.cases ?_ (fun tailCoordinate ↦ ?_) coordinate
    · simp [liftRelativeNestedMask, encodeRelativeGlobalMask]
    · simpa [liftRelativeNestedMask, encodeRelativeGlobalMask,
        LWE.MultiKeyAffine.maskedBit] using hfalse tailCoordinate

/-- In particular, one true normalized source-relative coefficient rules out every
scalar-affine native ring-key transport at `q > 2`. -/
theorem not_scalarAffineXorTransport_liftRelativeSource_of_eq_true
    {q suffixRank degree : ℕ} (hq : 2 < q)
    (mask : RelativeNestedMask suffixRank degree) (coordinate : Fin degree)
    (hcoordinate : mask.1 coordinate = true) :
    ¬ ScalarAffineXorTransport q (degree + 1)
      ((liftRelativeNestedMask mask).1 0) := by
  intro htransport
  have hfalse :=
    (scalarAffineXorTransport_liftRelativeSource_iff_trivial hq mask).mp
      htransport coordinate
  rw [hcoordinate] at hfalse
  exact Bool.noConfusion hfalse

/-- Applying the all-true mask after a normalized relative mask produces exactly its encoded
global-complement branch. -/
theorem act_liftRelativeNestedMask_nestedGlobalMask
    {suffixRank degree : ℕ}
    (mask : RelativeNestedMask suffixRank degree) :
    act (liftRelativeNestedMask mask)
        (nestedGlobalMask 1 suffixRank (degree + 1)) =
      encodeRelativeGlobalMask (mask, true) := by
  rcases mask with ⟨sourceTail, suffixMask⟩
  apply Prod.ext
  · funext component coefficient
    have hcomponent : component = 0 := Subsingleton.elim _ _
    subst component
    refine Fin.cases ?_ (fun tailCoordinate ↦ ?_) coefficient
    · simp [act, liftRelativeNestedMask, encodeRelativeGlobalMask,
        nestedGlobalMask, allTrueRingMask, maskedRingSecret,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
        allTruePolynomial, LWE.MultiKeyAffine.maskedBit]
    · cases sourceTail tailCoordinate <;>
        simp [act, liftRelativeNestedMask, encodeRelativeGlobalMask,
          nestedGlobalMask, allTrueRingMask, maskedRingSecret,
          FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
          allTruePolynomial, LWE.MultiKeyAffine.maskedBit]
  · funext component coefficient
    cases suffixMask component coefficient <;>
      simp [act, liftRelativeNestedMask, encodeRelativeGlobalMask,
        nestedGlobalMask, allTrueRingMask, maskedRingSecret,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
        allTruePolynomial, LWE.MultiKeyAffine.maskedBit]

/-- Apply a normalized relative mask, then optionally apply the global-complement anchor. -/
def relativeThenGlobalAct
    {suffixRank degree : ℕ}
    (secret : Secret 1 suffixRank (degree + 1))
    (mask : RelativeNestedMask suffixRank degree × Bool) :
    Secret 1 suffixRank (degree + 1) :=
  if mask.2 then
    act (act secret (liftRelativeNestedMask mask.1))
      (nestedGlobalMask 1 suffixRank (degree + 1))
  else
    act secret (liftRelativeNestedMask mask.1)

/-- Sequential relative-then-global action equals one XOR by the decoded complete mask. -/
theorem relativeThenGlobalAct_eq_act_encode
    {suffixRank degree : ℕ}
    (secret : Secret 1 suffixRank (degree + 1))
    (mask : RelativeNestedMask suffixRank degree × Bool) :
    relativeThenGlobalAct secret mask =
      act secret (encodeRelativeGlobalMask mask) := by
  rcases mask with ⟨relativeMask, toggle⟩
  cases toggle
  · rfl
  · simp only [relativeThenGlobalAct, if_true]
    rw [act_assoc, act_liftRelativeNestedMask_nestedGlobalMask]

/-- For a fixed nested secret, relative-mask-plus-anchor action is a permutation onto all fresh
nested secrets. -/
def relativeThenGlobalActEquiv
    {suffixRank degree : ℕ}
    (secret : Secret 1 suffixRank (degree + 1)) :
    (RelativeNestedMask suffixRank degree × Bool) ≃
      Secret 1 suffixRank (degree + 1) :=
  (relativeGlobalMaskEquiv suffixRank degree).trans (actEquiv secret)

/-- A uniform normalized relative mask and uniform anchor send every fixed nested key to an
exactly fresh nested key. -/
theorem relativeThenGlobalAct_uniform_evalDist
    (suffixRank degree : ℕ)
    (secret : Secret 1 suffixRank (degree + 1)) :
    evalDist (relativeThenGlobalAct secret <$>
        ($ᵗ (RelativeNestedMask suffixRank degree × Bool))) =
      evalDist (sampleNestedSecret 1 suffixRank (degree + 1)) := by
  calc
    _ = evalDist ((relativeThenGlobalActEquiv secret) <$>
        ($ᵗ (RelativeNestedMask suffixRank degree × Bool))) := by
      congr 2
      funext mask
      exact relativeThenGlobalAct_eq_act_encode secret mask
    _ = evalDist ($ᵗ (Secret 1 suffixRank (degree + 1))) :=
      evalDist_map_bijective_uniform_cross
        (α := RelativeNestedMask suffixRank degree × Bool)
        (β := Secret 1 suffixRank (degree + 1))
        (relativeThenGlobalActEquiv secret)
        (relativeThenGlobalActEquiv secret).bijective
    _ = _ :=
      (sampleNestedSecret_evalDist_eq_uniform 1 suffixRank (degree + 1)).symm

/-! ## Material-only normalized-relative evaluator -/

/-- The remaining nonlinear certificate after removing the exact input tape and the global
anchor.  It handles only normalized nonconstant masks on the BRK/extension material. -/
structure RelativeEvaluationMaterialEvaluator
    (q degree suffixRank levels : ℕ) [NeZero q]
    (narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1)) where
  evaluateRelative :
    RelativeNestedMask suffixRank degree →
      Auxiliary q (degree + 1) 1 suffixRank levels →
        ProbComp (Auxiliary q (degree + 1) 1 suffixRank levels)
  error : ℝ
  error_nonneg : 0 ≤ error
  materialDistance_le : ∀ secret relativeMask,
    tvDist
        (sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
            narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
          evaluateRelative relativeMask)
        (sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget
          (act secret (liftRelativeNestedMask relativeMask))) ≤ error

namespace RelativeEvaluationMaterialEvaluator

/-- Lift a normalized material evaluator to the complete adaptive view by transporting the input
tape under the same normalized nested mask. -/
def evaluateCompleteRelative
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (relativeMask : RelativeNestedMask suffixRank degree)
    (view : View q (degree + 1) 1 suffixRank levels queryCount) :
    ProbComp (View q (degree + 1) 1 suffixRank levels queryCount) := do
  let material ← evaluator.evaluateRelative relativeMask view.2
  return (transformTargetTape (liftRelativeNestedMask relativeMask) view.1, material)

/-- The normalized relative tape transport is exact, so lifting from material to complete view
preserves the evaluator's error unchanged. -/
theorem completeRelativeDistance_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (secret : Secret 1 suffixRank (degree + 1))
    (relativeMask : RelativeNestedMask suffixRank degree) :
    tvDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>= evaluator.evaluateCompleteRelative relativeMask)
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
          (act secret (liftRelativeNestedMask relativeMask))) ≤ evaluator.error := by
  let nestedMask := liftRelativeNestedMask relativeMask
  let targetSecret := act secret nestedMask
  let transformedTape := transformTargetTape nestedMask <$>
    sampleTargetTape q (degree + 1) 1 suffixRank queryCount inputErrorSampler secret
  let targetTape := sampleTargetTape q (degree + 1) 1 suffixRank queryCount
    inputErrorSampler targetSecret
  let evaluatedMaterial :=
    sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
        narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
      evaluator.evaluateRelative relativeMask
  let targetMaterial := sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
    wideBootstrapErrorSampler wideExtensionErrorSampler gadget targetSecret
  let combine := fun
      (tape : Challenge q (degree + 1) 1 suffixRank queryCount)
      (material : Auxiliary q (degree + 1) 1 suffixRank levels) ↦
    (tape, material)
  have htape : tvDist transformedTape targetTape = 0 := by
    unfold transformedTape targetTape targetSecret nestedMask tvDist
    rw [transformTargetTape_sampleTargetTape_evalDist]
    exact SPMF.tvDist_self _
  have hsource :
      sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>= evaluator.evaluateCompleteRelative relativeMask =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedTape evaluatedMaterial combine := by
    simp [sampleRealView, problem, sampleTargetTape, sampleEvaluationMaterial,
      evaluateCompleteRelative, transformedTape, evaluatedMaterial, nestedMask,
      combine, FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
      map_eq_bind_pure_comp, bind_assoc, monad_norm]
  have htarget :
      sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
          targetSecret =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          targetTape targetMaterial combine := by
    simp [sampleRealView, problem, sampleTargetTape, sampleEvaluationMaterial,
      targetTape, targetMaterial, combine,
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
      map_eq_bind_pure_comp, monad_norm]
  rw [hsource, show act secret (liftRelativeNestedMask relativeMask) =
      targetSecret by rfl, htarget]
  calc
    tvDist
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedTape evaluatedMaterial combine)
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          targetTape targetMaterial combine) ≤
      tvDist transformedTape targetTape + tvDist evaluatedMaterial targetMaterial :=
      FormalProof4FHE.TFHE.SamplerReplacement.tvDist_independentPair_le
        transformedTape targetTape evaluatedMaterial targetMaterial combine
    _ ≤ 0 + evaluator.error := add_le_add (le_of_eq htape)
      (evaluator.materialDistance_le secret relativeMask)
    _ = evaluator.error := zero_add _

end RelativeEvaluationMaterialEvaluator

/-! ## Relative evaluator plus checked global anchor -/

/-- The exact error budget of the already checked rank-one global-complement complete-view step. -/
noncomputable def globalComplementViewError
    {q degree suffixRank levels : ℕ}
    (bootstrapErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) : ℝ :=
  (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
    rankOneComplementNoiseDistance (levels := levels) bootstrapErrorSampler
      (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))

theorem globalComplementViewError_nonneg
    {q degree suffixRank levels : ℕ}
    (bootstrapErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    0 ≤ globalComplementViewError
      (suffixRank := suffixRank) (levels := levels) bootstrapErrorSampler := by
  apply mul_nonneg (Nat.cast_nonneg _)
  unfold rankOneComplementNoiseDistance
  exact tvDist_nonneg _ _

/-- Apply the checked global-complement public transform exactly when the anchor bit is true. -/
def transformCompleteViewByAnchor
    {q degree suffixRank levels queryCount : ℕ}
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (toggle : Bool)
    (view : View q (degree + 1) 1 suffixRank levels queryCount) :
    View q (degree + 1) 1 suffixRank levels queryCount :=
  if toggle then transformCompleteViewGlobalComplement gadget view else view

/-- The conditional anchor transform has the same uniform bound for both Boolean branches. -/
theorem transformCompleteViewByAnchor_tvDist_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        extensionErrorSampler)
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1))
    (toggle : Bool) :
    tvDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret >>=
          fun view ↦ pure (transformCompleteViewByAnchor gadget toggle view))
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          (if toggle then
            act secret (nestedGlobalMask 1 suffixRank (degree + 1))
          else secret)) ≤
      globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) bootstrapErrorSampler := by
  cases toggle
  · simpa [transformCompleteViewByAnchor] using
      (globalComplementViewError_nonneg
        (suffixRank := suffixRank) (levels := levels) bootstrapErrorSampler)
  · simp only [transformCompleteViewByAnchor, if_true]
    have hmap :
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret >>=
          fun view ↦ pure (transformCompleteViewGlobalComplement gadget view)) =
        transformCompleteViewGlobalComplement gadget <$>
          sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret := by
      rw [map_eq_bind_pure_comp]
      rfl
    rw [hmap]
    simpa only [globalComplementViewError] using
      (transformCompleteViewGlobalComplement_tvDist_le
        (queryCount := queryCount) bootstrapErrorSampler extensionErrorSampler
        inputErrorSampler hextensionSymmetric gadget secret)

namespace RelativeEvaluationMaterialEvaluator

/-- Execute the nonlinear normalized-relative step, transport the exact target tape, and finally
apply the checked global anchor transform. -/
def evaluateRelativeThenGlobal
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (mask : RelativeNestedMask suffixRank degree × Bool)
    (view : View q (degree + 1) 1 suffixRank levels queryCount) :
    ProbComp (View q (degree + 1) 1 suffixRank levels queryCount) := do
  let relativeView ← evaluator.evaluateCompleteRelative mask.1 view
  return transformCompleteViewByAnchor gadget mask.2 relativeView

/-- The relative evaluator error and the global-anchor shear error add exactly once under
sequential composition. -/
theorem relativeThenGlobalDistance_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (secret : Secret 1 suffixRank (degree + 1))
    (mask : RelativeNestedMask suffixRank degree × Bool) :
    tvDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>= evaluator.evaluateRelativeThenGlobal mask)
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
          (relativeThenGlobalAct secret mask)) ≤
      evaluator.error + globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler := by
  let relativeSecret := act secret (liftRelativeNestedMask mask.1)
  let afterRelative :=
    sampleRealView q (degree + 1) 1 suffixRank levels queryCount
      narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
          gadget secret >>=
      evaluator.evaluateCompleteRelative mask.1
  let wideRelative :=
    sampleRealView q (degree + 1) 1 suffixRank levels queryCount
      wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
      relativeSecret
  let finish := fun view : View q (degree + 1) 1 suffixRank levels queryCount ↦
    (pure (transformCompleteViewByAnchor gadget mask.2 view) :
      ProbComp (View q (degree + 1) 1 suffixRank levels queryCount))
  let afterGlobal := afterRelative >>= finish
  let wideAfterGlobal := wideRelative >>= finish
  have hrelative : tvDist afterRelative wideRelative ≤ evaluator.error := by
    exact evaluator.completeRelativeDistance_le inputErrorSampler secret mask.1
  have hpost : tvDist afterGlobal wideAfterGlobal ≤
      tvDist afterRelative wideRelative := by
    exact tvDist_bind_right_le finish afterRelative wideRelative
  have hglobal :
      tvDist wideAfterGlobal
          (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
            (relativeThenGlobalAct secret mask)) ≤
        globalComplementViewError
          (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler := by
    have h := transformCompleteViewByAnchor_tvDist_le
      (queryCount := queryCount) wideBootstrapErrorSampler wideExtensionErrorSampler
      inputErrorSampler hextensionSymmetric gadget relativeSecret mask.2
    have hsecret :
        (if mask.2 then
          act relativeSecret (nestedGlobalMask 1 suffixRank (degree + 1))
        else relativeSecret) = relativeThenGlobalAct secret mask := by
      rcases mask with ⟨relativeMask, toggle⟩
      cases toggle <;> rfl
    rw [hsecret] at h
    exact h
  have hsource :
      (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
          gadget secret >>= evaluator.evaluateRelativeThenGlobal mask) = afterGlobal := by
    change
      (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
          gadget secret >>=
        fun view ↦ evaluator.evaluateCompleteRelative mask.1 view >>= finish) =
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>= evaluator.evaluateCompleteRelative mask.1) >>= finish
    rw [bind_assoc]
  calc
    tvDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>= evaluator.evaluateRelativeThenGlobal mask)
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
          (relativeThenGlobalAct secret mask)) =
      tvDist afterGlobal
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
          (relativeThenGlobalAct secret mask)) := by
      rw [hsource]
    _ ≤ tvDist afterGlobal wideAfterGlobal +
        tvDist wideAfterGlobal
          (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
            (relativeThenGlobalAct secret mask)) := tvDist_triangle _ _ _
    _ ≤ evaluator.error + globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler :=
      add_le_add (hpost.trans hrelative) hglobal

/-- Package a normalized-relative material evaluator with the exact tape lift and checked global
anchor as the complete PKC-style fresh-key view randomizer. -/
def toRelativeThenGlobalViewRandomization
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      (Secret 1 suffixRank (degree + 1))
      (RelativeNestedMask suffixRank degree × Bool)
      (View q (degree + 1) 1 suffixRank levels queryCount) where
  sampleMask := $ᵗ (RelativeNestedMask suffixRank degree × Bool)
  act := relativeThenGlobalAct
  sampleFreshSecret := sampleNestedSecret 1 suffixRank (degree + 1)
  sampleNarrowView := sampleRealView q (degree + 1) 1 suffixRank levels queryCount
    narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget
  sampleWideView := sampleRealView q (degree + 1) 1 suffixRank levels queryCount
    wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
  evaluateAndSmudge := evaluator.evaluateRelativeThenGlobal
  error := evaluator.error + globalComplementViewError
    (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler
  error_nonneg := add_nonneg evaluator.error_nonneg
    (globalComplementViewError_nonneg wideBootstrapErrorSampler)
  secretLaw := relativeThenGlobalAct_uniform_evalDist suffixRank degree
  viewDistance_le := evaluator.relativeThenGlobalDistance_le inputErrorSampler
    hextensionSymmetric

@[simp]
theorem toRelativeThenGlobalViewRandomization_error
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler) :
    (evaluator.toRelativeThenGlobalViewRandomization
      (queryCount := queryCount) inputErrorSampler hextensionSymmetric).error =
      evaluator.error + globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler := rfl

end RelativeEvaluationMaterialEvaluator

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
