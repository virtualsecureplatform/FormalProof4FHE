/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.Basic
import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.SharedRandomness.Reduction

/-!
# Square-zero lifting for quadratic circular RLWE

This file formalizes the exact finite-game reduction in
`sketch/square_zero_quadratic_circular_rlwe.tex`.

The algebra is packaged by `DigitExtension Base Target`.  Its two digits represent an element of
`Target` as

`lift low + high highDigit`,

where the image of `high` is square-zero and multiplication of a lifted low digit by a high digit
agrees with multiplication in `Base`.  For `Base = R_p` and `Target = R_{p^2}`, `high x` is
`p * lift x`.

Starting with ordinary common-secret RLWE rows `(a, a*T + e)`, the reduction samples fresh low
digits and produces

`(A, A*S + g*S^2 + eta)`,

where `S = lift H + high T` and `eta = lift U + high e`.  The real and uniform simulations are
both exact.  In particular, the theorem has no correlated-source or circular-security premise.

The price is distributional rather than reduction-theoretic: the low digit `U` of every target
error is uniform.  Thus this proves the structured square-modulus family, not an unchanged
centered-binomial or discrete-Gaussian BFV parameter set.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.SquareZeroQuadraticCircular

noncomputable section

/-! ## Square-zero digit extensions -/

/-- Algebraic interface for a two-digit square-zero extension.

`lift` is only a set-theoretic section and is deliberately not required to preserve addition or
multiplication.  Only multiplication involving the square-zero high embedding is needed by the
reduction. -/
structure DigitExtension (Base Target : Type) [CommRing Base] [CommRing Target] where
  lift : Base → Target
  high : Base →+ Target
  digits : Base × Base ≃ Target
  digits_apply : ∀ low highDigit,
    digits (low, highDigit) = lift low + high highDigit
  lift_mul_high : ∀ left right,
    lift left * high right = high (left * right)
  high_mul_high : ∀ left right,
    high left * high right = 0

variable {Base Target Row : Type}
variable [CommRing Base] [CommRing Target]

/-- The two-digit target secret `S = [H] + p[T]`. -/
def targetSecret (extension : DigitExtension Base Target) (low highDigit : Base) : Target :=
  extension.lift low + extension.high highDigit

/-- The two-digit target error `eta = [U] + p[E]`. -/
def targetError (extension : DigitExtension Base Target) (low highDigit : Base) : Target :=
  extension.lift low + extension.high highDigit

/-- A two-digit lift of one source public mask. -/
def liftedMask (extension : DigitExtension Base Target) (low highDigit : Base) : Target :=
  extension.digits (low, highDigit)

@[simp]
theorem liftedMask_eq (extension : DigitExtension Base Target) (low highDigit : Base) :
    liftedMask extension low highDigit =
      extension.lift low + extension.high highDigit :=
  extension.digits_apply low highDigit

@[simp]
theorem digits_symm_lift_high
    (extension : DigitExtension Base Target) (low highDigit : Base) :
    extension.digits.symm
        (extension.lift low + extension.high highDigit) = (low, highDigit) := by
  rw [← extension.digits_apply]
  exact extension.digits.symm_apply_apply (low, highDigit)

@[simp]
theorem lift_high_digits_symm
    (extension : DigitExtension Base Target) (value : Target) :
    extension.lift (extension.digits.symm value).1 +
        extension.high (extension.digits.symm value).2 = value := by
  rw [← extension.digits_apply]
  exact extension.digits.apply_symm_apply value

/-- The difference between a lifted secret and its low digit belongs to the square-zero image. -/
theorem targetSecret_sub_lift
    (extension : DigitExtension Base Target) (low highDigit : Base) :
    targetSecret extension low highDigit - extension.lift low = extension.high highDigit := by
  simp [targetSecret]

/-- Every difference between a lifted secret and its low digit squares to zero. -/
theorem targetSecret_sub_lift_sq
    (extension : DigitExtension Base Target) (low highDigit : Base) :
    (targetSecret extension low highDigit - extension.lift low) ^ 2 = 0 := by
  rw [targetSecret_sub_lift]
  simpa [pow_two] using extension.high_mul_high highDigit highDigit

/-- Lifting a base linear row and adding an independent low error digit gives the intended
two-digit target linear row exactly. -/
theorem lifted_linear_body
    (extension : DigitExtension Base Target)
    (publicLow publicHigh secretLow secretHigh errorLow errorHigh : Base) :
    liftedMask extension publicLow publicHigh * extension.lift secretLow +
          extension.lift errorLow + extension.high (publicLow * secretHigh + errorHigh) =
      liftedMask extension publicLow publicHigh *
          targetSecret extension secretLow secretHigh +
        targetError extension errorLow errorHigh := by
  rw [map_add, liftedMask_eq]
  rw [← extension.lift_mul_high publicLow secretHigh]
  unfold targetSecret targetError
  simp only [mul_add, add_mul]
  rw [extension.high_mul_high]
  ring

/-! ## Square-zero completion -/

/-- The deterministic square-zero completion identity.  The sign convention here matches the
repository's ordinary RLWE rows `b = a*S + e`; it is equivalent to the TeX note's `-a*S + e`
convention after negating public masks. -/
theorem squareZeroCompletion
    (secret lowMask body lowSecret error weight : Target)
    (hSquareZero : (secret - lowSecret) ^ 2 = 0)
    (hBody : body = lowMask * secret + error) :
    body - weight * lowSecret ^ 2 =
      (lowMask - 2 * weight * lowSecret) * secret + weight * secret ^ 2 + error := by
  have hIdentity : secret ^ 2 - 2 * lowSecret * secret = -lowSecret ^ 2 := by
    calc
      secret ^ 2 - 2 * lowSecret * secret =
          (secret - lowSecret) ^ 2 - lowSecret ^ 2 := by ring
      _ = -lowSecret ^ 2 := by rw [hSquareZero]; ring
  rw [hBody]
  calc
    lowMask * secret + error - weight * lowSecret ^ 2 =
        lowMask * secret + weight * (secret ^ 2 - 2 * lowSecret * secret) + error := by
      rw [hIdentity]
      ring
    _ = (lowMask - 2 * weight * lowSecret) * secret + weight * secret ^ 2 + error := by
      ring

/-! ## Complete batch distributions -/

/-- A batch of ring masks or bodies. -/
abbrev Vector (R : Type) (Row : Type) := Row → R

/-- A complete public batch transcript. -/
abbrev Transcript (R : Type) (Row : Type) := Vector R Row × Vector R Row

/-- Ordinary common-secret base RLWE with an explicit joint error-vector sampler. -/
def baseProblem [DecidableEq Base] [SampleableType Base]
    [Fintype Row] [DecidableEq Row]
    (secretSampler : ProbComp Base) (errorSampler : ProbComp (Vector Base Row)) :
    LearningWithErrors.Problem (Vector Base Row) Base (Vector Base Row) where
  sampleChallenge := $ᵗ (Vector Base Row)
  sampleSecret := secretSampler
  sampleError := errorSampler
  noiseless := fun secret challenge row ↦ challenge row * secret
  sampleUniform := $ᵗ (Vector Base Row)

/-- The usual IID-error base RLWE problem. -/
abbrev iidBaseProblem [DecidableEq Base] [SampleableType Base]
    [Fintype Row] [DecidableEq Row]
    (secretSampler errorSampler : ProbComp Base) :=
  baseProblem (Row := Row) secretSampler
    (ProbComp.sampleIID (Fintype.card Row) errorSampler >>= fun values ↦
      pure (fun row ↦ values (Fintype.equivFin Row row)))

/-- Canonical target square transcript for fixed independent randomness. -/
def squareTranscript
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow secretHigh : Base) (errorLow errorHigh : Vector Base Row)
    (mask : Vector Target Row) : Transcript Target Row :=
  let secret := targetSecret extension secretLow secretHigh
  (mask, fun row ↦
    mask row * secret + weight row * secret ^ 2 +
      targetError extension (errorLow row) (errorHigh row))

/-- Canonical zero-message transcript with the identical secret and error laws. -/
def zeroTranscript
    (extension : DigitExtension Base Target)
    (secretLow secretHigh : Base) (errorLow errorHigh : Vector Base Row)
    (mask : Vector Target Row) : Transcript Target Row :=
  let secret := targetSecret extension secretLow secretHigh
  (mask, fun row ↦
    mask row * secret + targetError extension (errorLow row) (errorHigh row))

/-- Independent two-digit target-secret law. -/
def targetSecretSampler
    (extension : DigitExtension Base Target)
    (lowSampler highSampler : ProbComp Base) : ProbComp Target := do
  let low ← lowSampler
  let highDigit ← highSampler
  return targetSecret extension low highDigit

/-- Independent two-digit target-error-vector law, with a uniform low digit. -/
def targetErrorSampler [Fintype Base] [SampleableType Base]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target)
    (highSampler : ProbComp (Vector Base Row)) : ProbComp (Vector Target Row) := do
  let low ← $ᵗ (Vector Base Row)
  let highDigit ← highSampler
  return fun row ↦ targetError extension (low row) (highDigit row)

/-- Target quadratic-circular sampler.  Its target mask, secret block, and error block are sampled
independently. -/
def squareSampler [Fintype Base] [SampleableType Base]
    [Fintype Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (lowSecretSampler highSecretSampler : ProbComp Base)
    (highErrorSampler : ProbComp (Vector Base Row)) :
    ProbComp (Transcript Target Row) := do
  let secretLow ← lowSecretSampler
  let secretHigh ← highSecretSampler
  let errorLow ← $ᵗ (Vector Base Row)
  let errorHigh ← highErrorSampler
  let mask ← $ᵗ (Vector Target Row)
  return squareTranscript extension weight secretLow secretHigh errorLow errorHigh mask

/-- Target zero-message sampler with the same independent secret and error distributions. -/
def zeroSampler [Fintype Base] [SampleableType Base]
    [Fintype Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target)
    (lowSecretSampler highSecretSampler : ProbComp Base)
    (highErrorSampler : ProbComp (Vector Base Row)) :
    ProbComp (Transcript Target Row) := do
  let secretLow ← lowSecretSampler
  let secretHigh ← highSecretSampler
  let errorLow ← $ᵗ (Vector Base Row)
  let errorHigh ← highErrorSampler
  let mask ← $ᵗ (Vector Target Row)
  return zeroTranscript extension secretLow secretHigh errorLow errorHigh mask

/-- Common uniform target endpoint. -/
def uniformSampler [Fintype Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row] : ProbComp (Transcript Target Row) :=
  $ᵗ (Transcript Target Row)

/-- A target batch distinguisher. -/
abbrev Distinguisher (Target Row : Type) := Transcript Target Row → ProbComp Bool

/-! ## Public lifting reduction -/

/-- Deterministic lifted mask after the square-zero correction. -/
def compiledMask
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow : Base) (publicLow publicHigh : Vector Base Row) : Vector Target Row :=
  fun row ↦ liftedMask extension (publicLow row) (publicHigh row) -
    2 * weight row * extension.lift secretLow

/-- Deterministic public compiler for a base transcript and exposed reduction randomness. -/
def compile
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow : Base) (publicHigh errorLow : Vector Base Row)
    (source : Transcript Base Row) : Transcript Target Row :=
  let mask := compiledMask extension weight secretLow source.1 publicHigh
  (mask, fun row ↦
    liftedMask extension (source.1 row) (publicHigh row) * extension.lift secretLow +
      extension.lift (errorLow row) + extension.high (source.2 row) -
        weight row * extension.lift secretLow ^ 2)

/-- On a real base row, the compiler gives the target quadratic-circular row exactly. -/
theorem compile_real
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow secretHigh : Base)
    (publicLow publicHigh errorLow errorHigh : Vector Base Row) :
    compile extension weight secretLow publicHigh errorLow
        (publicLow, fun row ↦ publicLow row * secretHigh + errorHigh row) =
      squareTranscript extension weight secretLow secretHigh errorLow errorHigh
        (compiledMask extension weight secretLow publicLow publicHigh) := by
  apply Prod.ext
  · rfl
  · funext row
    have hLinear := lifted_linear_body extension
      (publicLow row) (publicHigh row) secretLow secretHigh
      (errorLow row) (errorHigh row)
    apply squareZeroCompletion
      (secret := targetSecret extension secretLow secretHigh)
      (lowMask := liftedMask extension (publicLow row) (publicHigh row))
      (body := liftedMask extension (publicLow row) (publicHigh row) *
          extension.lift secretLow + extension.lift (errorLow row) +
            extension.high (publicLow row * secretHigh + errorHigh row))
      (lowSecret := extension.lift secretLow)
      (error := targetError extension (errorLow row) (errorHigh row))
      (weight := weight row)
    · exact targetSecret_sub_lift_sq extension secretLow secretHigh
    · exact hLinear

/-- Randomized public reduction from the base transcript. -/
def reduction [Fintype Base] [SampleableType Base]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (lowSecretSampler : ProbComp Base)
    (source : Transcript Base Row) : ProbComp (Transcript Target Row) := do
  let secretLow ← lowSecretSampler
  let publicHigh ← $ᵗ (Vector Base Row)
  let errorLow ← $ᵗ (Vector Base Row)
  return compile extension weight secretLow publicHigh errorLow source

/-- The induced base-RLWE adversary. -/
def reductionAdversary [Fintype Base] [SampleableType Base]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (lowSecretSampler : ProbComp Base)
    (distinguisher : Distinguisher Target Row) :
    Transcript Base Row → ProbComp Bool :=
  fun source ↦ reduction extension weight lowSecretSampler source >>= distinguisher

/-! ## Uniform transports -/

/-- Pointwise digit decomposition is a bijection between two base vectors and one target vector. -/
def vectorDigitEquiv [Fintype Row]
    (extension : DigitExtension Base Target) :
    (Vector Base Row × Vector Base Row) ≃ Vector Target Row where
  toFun digits row := extension.digits (digits.1 row, digits.2 row)
  invFun value :=
    (fun row ↦ (extension.digits.symm (value row)).1,
      fun row ↦ (extension.digits.symm (value row)).2)
  left_inv digits := by
    apply Prod.ext <;> funext row
    · exact congrArg Prod.fst (extension.digits.symm_apply_apply
        (digits.1 row, digits.2 row))
    · exact congrArg Prod.snd (extension.digits.symm_apply_apply
        (digits.1 row, digits.2 row))
  right_inv value := by
    funext row
    exact extension.digits.apply_symm_apply (value row)

/-- The source mask digits followed by the public square correction form a bijection onto target
masks for every fixed low secret. -/
def maskEquiv [Fintype Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow : Base) :
    (Vector Base Row × Vector Base Row) ≃ Vector Target Row :=
  (vectorDigitEquiv extension).trans
    { toFun := fun value row ↦ value row - 2 * weight row * extension.lift secretLow
      invFun := fun value row ↦ value row + 2 * weight row * extension.lift secretLow
      left_inv := by intro value; funext row; simp
      right_inv := by intro value; funext row; simp }

@[simp]
theorem maskEquiv_apply [Fintype Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow : Base) (digits : Vector Base Row × Vector Base Row) :
    maskEquiv extension weight secretLow digits =
      compiledMask extension weight secretLow digits.1 digits.2 :=
  rfl

/-- The affine compiler on four independent uniform base vectors. -/
def uniformCompile
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow : Base)
    (randomness : Transcript Base Row ×
      (Vector Base Row × Vector Base Row)) : Transcript Target Row :=
  compile extension weight secretLow randomness.2.1 randomness.2.2 randomness.1

/-- Explicit inverse of `uniformCompile`. -/
def uniformDecompile
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow : Base) (target : Transcript Target Row) :
    Transcript Base Row × (Vector Base Row × Vector Base Row) :=
  let lowLift := extension.lift secretLow
  let liftedPublic : Vector Target Row :=
    fun row ↦ target.1 row + 2 * weight row * lowLift
  let liftedBody : Vector Target Row :=
    fun row ↦ target.2 row - liftedPublic row * lowLift + weight row * lowLift ^ 2
  let publicDigits : Vector Base Row × Vector Base Row :=
    (fun row ↦ (extension.digits.symm (liftedPublic row)).1,
      fun row ↦ (extension.digits.symm (liftedPublic row)).2)
  let bodyDigits : Vector Base Row × Vector Base Row :=
    (fun row ↦ (extension.digits.symm (liftedBody row)).1,
      fun row ↦ (extension.digits.symm (liftedBody row)).2)
  ((publicDigits.1, bodyDigits.2), (publicDigits.2, bodyDigits.1))

theorem uniformDecompile_compile
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow : Base)
    (randomness : Transcript Base Row ×
      (Vector Base Row × Vector Base Row)) :
    uniformDecompile extension weight secretLow
        (uniformCompile extension weight secretLow randomness) = randomness := by
  rcases randomness with ⟨⟨publicLow, sourceBody⟩, publicHigh, errorLow⟩
  apply Prod.ext
  · apply Prod.ext <;> funext row
    · simp [uniformDecompile, uniformCompile, compile, compiledMask, liftedMask]
    · have hBody :
          extension.digits (publicLow row, publicHigh row) *
                  extension.lift secretLow + extension.lift (errorLow row) +
                extension.high (sourceBody row) -
              weight row * extension.lift secretLow ^ 2 -
            extension.digits (publicLow row, publicHigh row) *
              extension.lift secretLow +
          weight row * extension.lift secretLow ^ 2 =
            extension.lift (errorLow row) + extension.high (sourceBody row) := by
          ring
      simp [uniformDecompile, uniformCompile, compile, compiledMask,
        liftedMask, hBody]
  · apply Prod.ext <;> funext row
    · simp [uniformDecompile, uniformCompile, compile, compiledMask, liftedMask]
    · have hBody :
          extension.digits (publicLow row, publicHigh row) *
                  extension.lift secretLow + extension.lift (errorLow row) +
                extension.high (sourceBody row) -
              weight row * extension.lift secretLow ^ 2 -
            extension.digits (publicLow row, publicHigh row) *
              extension.lift secretLow +
          weight row * extension.lift secretLow ^ 2 =
            extension.lift (errorLow row) + extension.high (sourceBody row) := by
          ring
      simp [uniformDecompile, uniformCompile, compile, compiledMask,
        liftedMask, hBody]

theorem uniformCompile_decompile
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow : Base) (target : Transcript Target Row) :
    uniformCompile extension weight secretLow
        (uniformDecompile extension weight secretLow target) = target := by
  apply Prod.ext <;> funext row
  · simp [uniformDecompile, uniformCompile, compile, compiledMask, liftedMask]
  · simp only [uniformDecompile, uniformCompile, compile, liftedMask]
    rw [extension.digits.apply_symm_apply]
    rw [add_assoc]
    rw [lift_high_digits_symm]
    ring

/-- For fixed low secret, the complete four-vector uniform compiler is a bijection. -/
theorem uniformCompile_bijective
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (secretLow : Base) :
    Function.Bijective (uniformCompile extension weight secretLow) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨uniformDecompile extension weight secretLow, ?_, ?_⟩
  · exact uniformDecompile_compile extension weight secretLow
  · exact uniformCompile_decompile extension weight secretLow

/-! ## Exact probability laws -/

/-- Reordering the six independent samplers used in the real reduction. -/
theorem evalDist_reorder_six
    {A B C D E F Output : Type}
    (a : ProbComp A) (b : ProbComp B) (c : ProbComp C)
    (d : ProbComp D) (e : ProbComp E) (f : ProbComp F)
    (finish : A → B → C → D → E → F → ProbComp Output) :
    evalDist (a >>= fun av ↦ b >>= fun bv ↦ c >>= fun cv ↦
      d >>= fun dv ↦ e >>= fun ev ↦ f >>= fun fv ↦
        finish av bv cv dv ev fv) =
    evalDist (d >>= fun dv ↦ b >>= fun bv ↦ f >>= fun fv ↦
      c >>= fun cv ↦ a >>= fun av ↦ e >>= fun ev ↦
        finish av bv cv dv ev fv) := by
  calc
    _ = evalDist (a >>= fun av ↦ b >>= fun bv ↦ d >>= fun dv ↦
        c >>= fun cv ↦ e >>= fun ev ↦ f >>= fun fv ↦
          finish av bv cv dv ev fv) := by
      refine evalDist_bind_congr' a fun av ↦ ?_
      refine evalDist_bind_congr' b fun bv ↦ ?_
      exact evalDist_bind_bind_swap c d _
    _ = evalDist (a >>= fun av ↦ d >>= fun dv ↦ b >>= fun bv ↦
        c >>= fun cv ↦ e >>= fun ev ↦ f >>= fun fv ↦
          finish av bv cv dv ev fv) := by
      refine evalDist_bind_congr' a fun av ↦ ?_
      exact evalDist_bind_bind_swap b d _
    _ = evalDist (d >>= fun dv ↦ a >>= fun av ↦ b >>= fun bv ↦
        c >>= fun cv ↦ e >>= fun ev ↦ f >>= fun fv ↦
          finish av bv cv dv ev fv) :=
      evalDist_bind_bind_swap a d _
    _ = evalDist (d >>= fun dv ↦ b >>= fun bv ↦ a >>= fun av ↦
        c >>= fun cv ↦ e >>= fun ev ↦ f >>= fun fv ↦
          finish av bv cv dv ev fv) := by
      refine evalDist_bind_congr' d fun dv ↦ ?_
      exact evalDist_bind_bind_swap a b _
    _ = evalDist (d >>= fun dv ↦ b >>= fun bv ↦ a >>= fun av ↦
        c >>= fun cv ↦ f >>= fun fv ↦ e >>= fun ev ↦
          finish av bv cv dv ev fv) := by
      refine evalDist_bind_congr' d fun dv ↦ ?_
      refine evalDist_bind_congr' b fun bv ↦ ?_
      refine evalDist_bind_congr' a fun av ↦ ?_
      refine evalDist_bind_congr' c fun cv ↦ ?_
      exact evalDist_bind_bind_swap e f _
    _ = evalDist (d >>= fun dv ↦ b >>= fun bv ↦ a >>= fun av ↦
        f >>= fun fv ↦ c >>= fun cv ↦ e >>= fun ev ↦
          finish av bv cv dv ev fv) := by
      refine evalDist_bind_congr' d fun dv ↦ ?_
      refine evalDist_bind_congr' b fun bv ↦ ?_
      refine evalDist_bind_congr' a fun av ↦ ?_
      exact evalDist_bind_bind_swap c f _
    _ = evalDist (d >>= fun dv ↦ b >>= fun bv ↦ f >>= fun fv ↦
        a >>= fun av ↦ c >>= fun cv ↦ e >>= fun ev ↦
          finish av bv cv dv ev fv) := by
      refine evalDist_bind_congr' d fun dv ↦ ?_
      refine evalDist_bind_congr' b fun bv ↦ ?_
      exact evalDist_bind_bind_swap a f _
    _ = evalDist (d >>= fun dv ↦ b >>= fun bv ↦ f >>= fun fv ↦
        c >>= fun cv ↦ a >>= fun av ↦ e >>= fun ev ↦
          finish av bv cv dv ev fv) := by
      refine evalDist_bind_congr' d fun dv ↦ ?_
      refine evalDist_bind_congr' b fun bv ↦ ?_
      refine evalDist_bind_congr' f fun fv ↦ ?_
      exact evalDist_bind_bind_swap a c _

/-- The reduction maps real base RLWE exactly to the structured quadratic-circular target. -/
theorem reduction_real_evalDist
    [Fintype Base] [DecidableEq Base] [SampleableType Base]
    [Fintype Target] [DecidableEq Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (lowSecretSampler highSecretSampler : ProbComp Base)
    (highErrorSampler : ProbComp (Vector Base Row)) :
    evalDist (LearningWithErrors.distr
        (baseProblem (Row := Row) highSecretSampler highErrorSampler) >>=
      reduction extension weight lowSecretSampler) =
    evalDist (squareSampler extension weight lowSecretSampler highSecretSampler
      highErrorSampler) := by
  simp only [LearningWithErrors.distr, baseProblem, reduction, bind_assoc, pure_bind]
  calc
    _ = evalDist (lowSecretSampler >>= fun secretLow ↦
        highSecretSampler >>= fun secretHigh ↦
          ($ᵗ (Vector Base Row)) >>= fun errorLow ↦
            highErrorSampler >>= fun errorHigh ↦
              ($ᵗ (Vector Base Row)) >>= fun publicLow ↦
                ($ᵗ (Vector Base Row)) >>= fun publicHigh ↦
                  pure (compile extension weight secretLow publicHigh errorLow
                    (publicLow, fun row ↦ publicLow row * secretHigh + errorHigh row))) := by
      exact evalDist_reorder_six
        ($ᵗ (Vector Base Row)) highSecretSampler highErrorSampler
        lowSecretSampler ($ᵗ (Vector Base Row)) ($ᵗ (Vector Base Row))
        (fun publicLow secretHigh errorHigh secretLow publicHigh errorLow ↦
          pure (compile extension weight secretLow publicHigh errorLow
            (publicLow, fun row ↦ publicLow row * secretHigh + errorHigh row)))
    _ = evalDist (lowSecretSampler >>= fun secretLow ↦
        highSecretSampler >>= fun secretHigh ↦
          ($ᵗ (Vector Base Row)) >>= fun errorLow ↦
            highErrorSampler >>= fun errorHigh ↦
              ($ᵗ (Vector Target Row)) >>= fun mask ↦
                pure (squareTranscript extension weight secretLow secretHigh
                  errorLow errorHigh mask)) := by
      refine evalDist_bind_congr' lowSecretSampler fun secretLow ↦ ?_
      refine evalDist_bind_congr' highSecretSampler fun secretHigh ↦ ?_
      refine evalDist_bind_congr' ($ᵗ (Vector Base Row)) fun errorLow ↦ ?_
      refine evalDist_bind_congr' highErrorSampler fun errorHigh ↦ ?_
      have hPair := FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
        (first := Vector Base Row) (second := Vector Base Row)
      have hMask :
          evalDist ((maskEquiv extension weight secretLow) <$>
            ($ᵗ (Vector Base Row × Vector Base Row))) =
            evalDist ($ᵗ (Vector Target Row)) :=
        evalDist_map_bijective_uniform_cross
          (α := Vector Base Row × Vector Base Row)
          (β := Vector Target Row) (maskEquiv extension weight secretLow)
          (maskEquiv extension weight secretLow).bijective
      calc
        _ = evalDist (($ᵗ (Vector Base Row × Vector Base Row)) >>= fun digits ↦
              pure (squareTranscript extension weight secretLow secretHigh
                errorLow errorHigh (maskEquiv extension weight secretLow digits))) := by
          simpa only [compile_real, maskEquiv_apply, bind_assoc, pure_bind] using
            FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hPair
              (fun digits ↦ pure (squareTranscript extension weight secretLow secretHigh
                errorLow errorHigh (maskEquiv extension weight secretLow digits)))
        _ = _ := by
          simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
            FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hMask
              (fun mask ↦ pure (squareTranscript extension weight secretLow secretHigh
                errorLow errorHigh mask))
    _ = _ := rfl

/-- The uniform branch of the base problem is the canonical uniform base transcript. -/
theorem base_uniformDistr_evalDist
    [Fintype Base] [DecidableEq Base] [SampleableType Base]
    [Fintype Row] [DecidableEq Row]
    (secretSampler : ProbComp Base) (errorSampler : ProbComp (Vector Base Row)) :
    evalDist (LearningWithErrors.uniformDistr
      (baseProblem (Row := Row) secretSampler errorSampler)) =
      evalDist ($ᵗ (Transcript Base Row)) := by
  simp only [LearningWithErrors.uniformDistr, baseProblem]
  exact FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product

/-- The reduction maps uniform base transcripts exactly to uniform target transcripts. -/
theorem reduction_uniform_evalDist
    [Fintype Base] [DecidableEq Base] [SampleableType Base]
    [Fintype Target] [DecidableEq Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (lowSecretSampler highSecretSampler : ProbComp Base)
    (highErrorSampler : ProbComp (Vector Base Row))
    (hLowSecret : Pr[⊥ | lowSecretSampler] = 0) :
    evalDist (LearningWithErrors.uniformDistr
        (baseProblem (Row := Row) highSecretSampler highErrorSampler) >>=
      reduction extension weight lowSecretSampler) =
    evalDist (uniformSampler (Target := Target) (Row := Row)) := by
  have hBase := base_uniformDistr_evalDist
    (Row := Row) highSecretSampler highErrorSampler
  rw [FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hBase
    (reduction extension weight lowSecretSampler)]
  simp only [uniformSampler]
  calc
    _ = evalDist (lowSecretSampler >>= fun secretLow ↦
        ($ᵗ (Transcript Base Row)) >>= fun source ↦
          ($ᵗ (Vector Base Row × Vector Base Row)) >>= fun auxiliary ↦
            pure (uniformCompile extension weight secretLow (source, auxiliary))) := by
      refine evalDist_bind_bind_swap ($ᵗ (Transcript Base Row)) lowSecretSampler _ |>.trans ?_
      refine evalDist_bind_congr' lowSecretSampler fun secretLow ↦ ?_
      refine evalDist_bind_congr' ($ᵗ (Transcript Base Row)) fun source ↦ ?_
      have hAux := FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
        (first := Vector Base Row) (second := Vector Base Row)
      simpa only [uniformCompile, bind_assoc, pure_bind] using
        FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hAux
          (fun auxiliary ↦ pure
            (uniformCompile extension weight secretLow (source, auxiliary)))
    _ = evalDist (lowSecretSampler >>= fun _secretLow ↦
        ($ᵗ (Transcript Target Row))) := by
      refine evalDist_bind_congr' lowSecretSampler fun secretLow ↦ ?_
      have hProduct := FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
        (first := Transcript Base Row)
        (second := Vector Base Row × Vector Base Row)
      calc
        _ = evalDist (($ᵗ (Transcript Base Row ×
              (Vector Base Row × Vector Base Row))) >>= fun randomness ↦
                pure (uniformCompile extension weight secretLow randomness)) := by
          simpa only [bind_assoc, pure_bind] using
            FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hProduct
              (fun randomness ↦ pure
                (uniformCompile extension weight secretLow randomness))
        _ = _ := by
          simpa only [map_eq_bind_pure_comp, Function.comp_def] using
            (evalDist_map_bijective_uniform_cross
              (α := Transcript Base Row × (Vector Base Row × Vector Base Row))
              (β := Transcript Target Row)
              (uniformCompile extension weight secretLow)
              (uniformCompile_bijective extension weight secretLow))
    _ = _ := FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      lowSecretSampler hLowSecret ($ᵗ (Transcript Target Row))

/-! ## Advantage equalities and quadratic-KDM composition -/

/-- Quadratic-circular real versus uniform advantage. -/
noncomputable def squareUniformAdvantage
    [Fintype Base] [SampleableType Base]
    [Fintype Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (lowSecretSampler highSecretSampler : ProbComp Base)
    (highErrorSampler : ProbComp (Vector Base Row))
    (distinguisher : Distinguisher Target Row) : ℝ :=
  (squareSampler extension weight lowSecretSampler highSecretSampler highErrorSampler >>=
      distinguisher).boolDistAdvantage
    (uniformSampler (Target := Target) (Row := Row) >>= distinguisher)

/-- Quadratic-circular real versus the matching zero-message distribution. -/
noncomputable def kdmAdvantage
    [Fintype Base] [SampleableType Base]
    [Fintype Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (lowSecretSampler highSecretSampler : ProbComp Base)
    (highErrorSampler : ProbComp (Vector Base Row))
    (distinguisher : Distinguisher Target Row) : ℝ :=
  (squareSampler extension weight lowSecretSampler highSecretSampler highErrorSampler >>=
      distinguisher).boolDistAdvantage
    (zeroSampler extension lowSecretSampler highSecretSampler highErrorSampler >>=
      distinguisher)

/-- Exact reduction of the structured quadratic-circular distribution to ordinary base RLWE. -/
theorem squareUniformAdvantage_eq_base
    [Fintype Base] [DecidableEq Base] [SampleableType Base]
    [Fintype Target] [DecidableEq Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (lowSecretSampler highSecretSampler : ProbComp Base)
    (highErrorSampler : ProbComp (Vector Base Row))
    (distinguisher : Distinguisher Target Row)
    (hLowSecret : Pr[⊥ | lowSecretSampler] = 0) :
    squareUniformAdvantage extension weight lowSecretSampler highSecretSampler
        highErrorSampler distinguisher =
      LearningWithErrors.advantage
        (baseProblem (Row := Row) highSecretSampler highErrorSampler)
        (reductionAdversary extension weight lowSecretSampler distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold squareUniformAdvantage reductionAdversary LearningWithErrors.game0
    LearningWithErrors.game1
  have hReal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (reduction_real_evalDist extension weight lowSecretSampler highSecretSampler
      highErrorSampler) distinguisher
  have hUniform := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (reduction_uniform_evalDist extension weight lowSecretSampler highSecretSampler
      highErrorSampler hLowSecret) distinguisher
  simp only [bind_assoc] at hReal hUniform ⊢
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp hReal true, evalDist_ext_iff.mp hUniform true]

/-- The zero target is the square target with the zero gadget family. -/
theorem squareSampler_zero_weight
    [Fintype Base] [SampleableType Base]
    [Fintype Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target)
    (lowSecretSampler highSecretSampler : ProbComp Base)
    (highErrorSampler : ProbComp (Vector Base Row)) :
    squareSampler extension (fun _row : Row ↦ 0) lowSecretSampler highSecretSampler
        highErrorSampler =
      zeroSampler extension lowSecretSampler highSecretSampler highErrorSampler := by
  simp [squareSampler, zeroSampler, squareTranscript, zeroTranscript]

/-- Exact two-hybrid KDM bound.  Both endpoints reduce to ordinary base RLWE; there is no circular
or correlated-source assumption. -/
theorem kdmAdvantage_le_two_base
    [Fintype Base] [DecidableEq Base] [SampleableType Base]
    [Fintype Target] [DecidableEq Target] [SampleableType Target]
    [Fintype Row] [DecidableEq Row]
    (extension : DigitExtension Base Target) (weight : Row → Target)
    (lowSecretSampler highSecretSampler : ProbComp Base)
    (highErrorSampler : ProbComp (Vector Base Row))
    (distinguisher : Distinguisher Target Row)
    (hLowSecret : Pr[⊥ | lowSecretSampler] = 0) :
    kdmAdvantage extension weight lowSecretSampler highSecretSampler
        highErrorSampler distinguisher ≤
      LearningWithErrors.advantage
        (baseProblem (Row := Row) highSecretSampler highErrorSampler)
        (reductionAdversary extension weight lowSecretSampler distinguisher) +
      LearningWithErrors.advantage
        (baseProblem (Row := Row) highSecretSampler highErrorSampler)
        (reductionAdversary extension (fun _row : Row ↦ 0)
          lowSecretSampler distinguisher) := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (squareSampler extension weight lowSecretSampler highSecretSampler highErrorSampler >>=
      distinguisher)
    (uniformSampler (Target := Target) (Row := Row) >>= distinguisher)
    (zeroSampler extension lowSecretSampler highSecretSampler highErrorSampler >>=
      distinguisher)
  unfold kdmAdvantage at hTriangle ⊢
  rw [show
      (uniformSampler (Target := Target) (Row := Row) >>= distinguisher).boolDistAdvantage
          (zeroSampler extension lowSecretSampler highSecretSampler highErrorSampler >>=
            distinguisher) =
        (zeroSampler extension lowSecretSampler highSecretSampler highErrorSampler >>=
            distinguisher).boolDistAdvantage
          (uniformSampler (Target := Target) (Row := Row) >>= distinguisher) by
      unfold ProbComp.boolDistAdvantage
      rw [abs_sub_comm]] at hTriangle
  apply hTriangle.trans_eq
  rw [← squareSampler_zero_weight extension lowSecretSampler highSecretSampler
    highErrorSampler]
  exact congrArg₂ (· + ·)
    (squareUniformAdvantage_eq_base extension weight lowSecretSampler highSecretSampler
      highErrorSampler distinguisher hLowSecret)
    (squareUniformAdvantage_eq_base extension (fun _row : Row ↦ 0)
      lowSecretSampler highSecretSampler highErrorSampler distinguisher hLowSecret)

/-! ## BFV relinearization correctness -/

/-- Standard BFV relinearization using the lifted evaluation-key rows leaves exactly the weighted
sum of the structured target errors. -/
theorem relinearization_phase
    [Fintype Row]
    (extension : DigitExtension Base Target) (weight digit : Row → Target)
    (secretLow secretHigh : Base) (errorLow errorHigh : Vector Base Row)
    (mask : Vector Target Row) (c0 c1 c2 : Target)
    (hDecomposition : c2 = ∑ row, digit row * weight row) :
    let evaluationKey := squareTranscript extension weight secretLow secretHigh
      errorLow errorHigh mask
    (c0 + ∑ row, digit row * evaluationKey.2 row) +
        (c1 - ∑ row, digit row * evaluationKey.1 row) *
          targetSecret extension secretLow secretHigh =
      c0 + c1 * targetSecret extension secretLow secretHigh +
        c2 * targetSecret extension secretLow secretHigh ^ 2 +
          ∑ row, digit row * targetError extension (errorLow row) (errorHigh row) := by
  let secret := targetSecret extension secretLow secretHigh
  have hMask :
      (∑ row, digit row * (mask row * secret)) =
        (∑ row, digit row * mask row) * secret := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro row _
    ring
  have hWeight :
      (∑ row, digit row * (weight row * secret ^ 2)) =
        (∑ row, digit row * weight row) * secret ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro row _
    ring
  change
    (c0 + ∑ row, digit row *
      (mask row * secret + weight row * secret ^ 2 +
        targetError extension (errorLow row) (errorHigh row))) +
        (c1 - ∑ row, digit row * mask row) * secret =
      c0 + c1 * secret + c2 * secret ^ 2 +
        ∑ row, digit row * targetError extension (errorLow row) (errorHigh row)
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hMask, hWeight]
  rw [hDecomposition]
  ring

/-! ## Coefficient-size arithmetic -/

/-- Pointwise arithmetic behind the lifted-error bound in the note.  Applying this inequality to
every centered coefficient gives the corresponding infinity-norm estimate. -/
theorem liftedErrorCoefficient_abs_le
    (p low highDigit bound : ℝ)
    (hp : 0 ≤ p)
    (hLow : |low| ≤ (p - 1) / 2)
    (hHigh : |highDigit| ≤ bound) :
    |low + p * highDigit| ≤ (p - 1) / 2 + p * bound := by
  calc
    |low + p * highDigit| ≤ |low| + |p * highDigit| := abs_add_le _ _
    _ = |low| + p * |highDigit| := by rw [abs_mul, abs_of_nonneg hp]
    _ ≤ (p - 1) / 2 + p * bound :=
      add_le_add hLow (mul_le_mul_of_nonneg_left hHigh hp)

/-- Dividing the pointwise lifted-error estimate by the square modulus gives the exact relative
bound `B/p + (p-1)/(2p²)`. -/
theorem liftedErrorCoefficient_relative_le
    (p low highDigit bound : ℝ)
    (hp : 0 < p)
    (hLow : |low| ≤ (p - 1) / 2)
    (hHigh : |highDigit| ≤ bound) :
    |low + p * highDigit| / p ^ 2 ≤
      bound / p + (p - 1) / (2 * p ^ 2) := by
  have hpSq : 0 < p ^ 2 := sq_pos_of_pos hp
  calc
    |low + p * highDigit| / p ^ 2 ≤
        ((p - 1) / 2 + p * bound) / p ^ 2 :=
      (div_le_div_iff_of_pos_right hpSq).2
        (liftedErrorCoefficient_abs_le p low highDigit bound hp.le hLow hHigh)
    _ = bound / p + (p - 1) / (2 * p ^ 2) := by
      field_simp
      ring

/-- Pointwise arithmetic behind the corresponding two-digit secret bound. -/
theorem liftedSecretCoefficient_abs_le
    (p low highDigit lowBound highBound : ℝ)
    (hp : 0 ≤ p)
    (hLow : |low| ≤ lowBound)
    (hHigh : |highDigit| ≤ highBound) :
    |low + p * highDigit| ≤ lowBound + p * highBound := by
  calc
    |low + p * highDigit| ≤ |low| + |p * highDigit| := abs_add_le _ _
    _ = |low| + p * |highDigit| := by rw [abs_mul, abs_of_nonneg hp]
    _ ≤ lowBound + p * highBound :=
      add_le_add hLow (mul_le_mul_of_nonneg_left hHigh hp)

/-! ## Optional unit-pivot normal form -/

/-- For a fixed unit pivot and pivot body, the usual uniform-secret-to-error-secret row
normalization is a bijection on public row pairs. -/
def unitPivotNormalFormEquiv
    (pivot : Baseˣ) (pivotBody : Base) : (Base × Base) ≃ (Base × Base) where
  toFun row :=
    (row.1 * (↑(pivot⁻¹) : Base),
      row.2 - row.1 * (↑(pivot⁻¹) : Base) * pivotBody)
  invFun row :=
    (row.1 * (pivot : Base), row.2 + row.1 * pivotBody)
  left_inv row := by
    rcases row with ⟨mask, body⟩
    apply Prod.ext
    · simp [mul_assoc]
    · change
        body - mask * (↑(pivot⁻¹) : Base) * pivotBody +
            (mask * (↑(pivot⁻¹) : Base)) * pivotBody = body
      ring
  right_inv row := by
    rcases row with ⟨mask, body⟩
    apply Prod.ext
    · simp [mul_assoc]
    · change
        body + mask * pivotBody -
            mask * (pivot : Base) * (↑(pivot⁻¹) : Base) * pivotBody = body
      have hUnit : (pivot : Base) * (↑(pivot⁻¹) : Base) = 1 := by simp
      have hCancel :
          mask * (pivot : Base) * (↑(pivot⁻¹) : Base) * pivotBody =
            mask * pivotBody := by
        calc
          _ = mask * ((pivot : Base) * (↑(pivot⁻¹) : Base)) * pivotBody := by
            ring
          _ = mask * pivotBody := by rw [hUnit]; ring
      rw [hCancel]
      ring

/-- In the real branch, pivot normalization cancels a uniform secret and turns the pivot error
into the new (negated, in the repository's `a*S+e` convention) secret. -/
theorem unitPivotNormalFormEquiv_real
    (pivot : Baseˣ) (secret pivotError mask error : Base) :
    unitPivotNormalFormEquiv pivot ((pivot : Base) * secret + pivotError)
      (mask, mask * secret + error) =
      (mask * (↑(pivot⁻¹) : Base),
        (mask * (↑(pivot⁻¹) : Base)) * (-pivotError) + error) := by
  apply Prod.ext
  · rfl
  · change
      mask * secret + error -
          mask * (↑(pivot⁻¹) : Base) * ((pivot : Base) * secret + pivotError) =
        (mask * (↑(pivot⁻¹) : Base)) * (-pivotError) + error
    have hUnit : (↑(pivot⁻¹) : Base) * (pivot : Base) = 1 := by simp
    rw [mul_add]
    have hCancel :
        mask * (↑(pivot⁻¹) : Base) * ((pivot : Base) * secret) =
          mask * secret := by
      calc
        _ = mask * ((↑(pivot⁻¹) : Base) * (pivot : Base)) * secret := by ring
        _ = mask * secret := by rw [hUnit]; ring
    rw [hCancel]
    ring

/-! ## Concrete `ZMod p` to `ZMod (p^2)` digit extension -/

/-- Canonical low representative in the square modulus. -/
def zmodLift (p : ℕ) [NeZero p] (value : ZMod p) : ZMod (p * p) :=
  value.val

/-- High-digit embedding `x ↦ p[x]`. -/
def zmodHigh (p : ℕ) [NeZero p] : ZMod p →+ ZMod (p * p) where
  toFun value := p * value.val
  map_zero' := by simp
  map_add' left right := by
    simp only [← Nat.cast_mul, ← Nat.cast_add]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    rw [ZMod.val_add]
    have h := (Nat.mod_modEq (left.val + right.val) p).mul_left' p
    simpa [Nat.mul_add] using h

/-- Splitting a square-modulus residue into its low and high base-`p` digits. -/
def zmodDigitEquiv (p : ℕ) [NeZero p] :
    ZMod p × ZMod p ≃ ZMod (p * p) :=
  (Equiv.prodCongr (ZMod.finEquiv p).symm.toEquiv
      (ZMod.finEquiv p).symm.toEquiv).trans
    ((Equiv.prodComm (Fin p) (Fin p)).trans
      (finProdFinEquiv.trans (ZMod.finEquiv (p * p)).toEquiv))

@[simp]
theorem zmodHigh_apply (p : ℕ) [NeZero p] (value : ZMod p) :
    zmodHigh p value = ((p * value.val : ℕ) : ZMod (p * p)) :=
  by simp [zmodHigh]

theorem zmodFinEquiv_apply (n : ℕ) [NeZero n] (value : Fin n) :
    ZMod.finEquiv n value = (value.val : ZMod n) := by
  rw [← ZMod.natCast_zmod_val (ZMod.finEquiv n value)]
  congr 1
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

theorem zmodFinEquiv_symm_val (n : ℕ) [NeZero n] (value : ZMod n) :
    ((ZMod.finEquiv n).symm value).val = value.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

@[simp]
theorem zmodDigitEquiv_apply (p : ℕ) [NeZero p]
    (low highDigit : ZMod p) :
    zmodDigitEquiv p (low, highDigit) =
      zmodLift p low + zmodHigh p highDigit := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p =>
      simp [zmodDigitEquiv, zmodLift, zmodHigh, zmodFinEquiv_apply,
        zmodFinEquiv_symm_val]

theorem zmodLift_mul_zmodHigh (p : ℕ) [NeZero p]
    (left right : ZMod p) :
    zmodLift p left * zmodHigh p right = zmodHigh p (left * right) := by
  rw [zmodHigh_apply, zmodHigh_apply]
  simp only [zmodLift, ← Nat.cast_mul]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  rw [ZMod.val_mul]
  have h := (Nat.mod_modEq (left.val * right.val) p).mul_left' p
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h.symm

theorem zmodHigh_mul_zmodHigh (p : ℕ) [NeZero p]
    (left right : ZMod p) :
    zmodHigh p left * zmodHigh p right = 0 := by
  rw [zmodHigh_apply, zmodHigh_apply]
  simp only [← Nat.cast_mul]
  rw [show
    (p * left.val) * (p * right.val) = (p * p) * (left.val * right.val) by ring]
  simp

/-- Concrete scalar square-zero extension. -/
def zmodDigitExtension (p : ℕ) [NeZero p] :
    DigitExtension (ZMod p) (ZMod (p * p)) where
  lift := zmodLift p
  high := zmodHigh p
  digits := zmodDigitEquiv p
  digits_apply := zmodDigitEquiv_apply p
  lift_mul_high := zmodLift_mul_zmodHigh p
  high_mul_high := zmodHigh_mul_zmodHigh p

/-!
The coefficientwise extension to the executable negacyclic carrier is intentionally kept as a
separate representation bridge.  The carrier currently exposes both its raw bundled
multiplication and the certified `CommRing` multiplication; identifying those instances before
lifting the coefficient proof avoids silently proving the law for the wrong operation.
-/

end

end FormalProof4FHE.RLWE.SquareZeroQuadraticCircular
