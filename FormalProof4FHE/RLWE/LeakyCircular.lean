/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.Security
import FormalProof4FHE.SharedRandomness.Reduction

/-!
# A Leaky-RLWE Reduction for One Unscaled Square Ciphertext

This module checks the candidate reduction in `rlwecircular.md`.  Four source errors and two
independent leakage errors define

* the target secret `S = e₂ + ρ₂`, and
* the target error `E = e₃ - e₀ * (e₁ + ρ₁)`.

From the public projection `(a₀, a₃, b₀, b₃, ℓ₁, ℓ₂)` of a four-sample error-only Leaky-RLWE
instance, with `a₀` a unit, the checked public map emits exactly

`(A, A * S + S^2 + E)`.

The random Leaky-RLWE branch is mapped exactly to the uniform distribution on `R × R`.  A second
checked reduction emits `(A, A * S + E)` with the same independent target secret and error laws.
The triangle inequality therefore bounds the quadratic real-versus-zero KDM advantage by two
error-only Leaky-RLWE advantages.

The module formalizes the finite-game algebra and probability transport.  It does **not**
reformalize the analytic discrete-Gaussian reduction in Lai--Swarnakar--Woo, *Leaky LWE: Learning
with Errors with Semi-Adaptive Secret- and Error-Leakage* (2025), Condition 2 and Theorem 3.  That
theorem applies to the full four-sample view, and its adversary may ignore the two unused source
samples to obtain the public projection used here.  Invoking it additionally requires its stated
Gaussian, smoothing, Gram-bound, and efficiency hypotheses.

The final section also checks the weighted identity.  A public weight `g` necessarily produces
the product error `e₃ - g * e₀ * (e₁ + ρ₁)` in this construction; no weight-independent gadget
noise claim is made.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.LeakyCircular

noncomputable section

/-! ## The error-only leakage matrix -/

/-- Four source errors, indexed as `e₀, e₁, e₂, e₃`. -/
abbrev ErrorVector (R : Type) := Fin 4 → R

/-- The two error-only leakage coordinates. -/
abbrev LeakageVector (R : Type) := Fin 2 → R

/-- The fixed error-leakage matrix from the reduction. -/
def leakageMatrix (R : Type) [Ring R] : Matrix (Fin 4) (Fin 2) R :=
  ![![-1, -1], ![1, 0], ![0, 1], ![0, 0]]

/-- Multiplication by the fixed leakage matrix gives `(e₁-e₀, e₂-e₀)`. -/
theorem vecMul_leakageMatrix {R : Type} [CommRing R] (error : ErrorVector R) :
    vecMul error (leakageMatrix R) = ![error 1 - error 0, error 2 - error 0] := by
  funext coordinate
  fin_cases coordinate <;>
    simp [vecMul, dotProduct, leakageMatrix, Fin.sum_univ_succ] <;> ring

/-- The integer Gram matrix is exactly `[[2,1],[1,2]]`. -/
theorem leakageMatrix_transpose_mul_self :
    (leakageMatrix ℤ)ᵀ * leakageMatrix ℤ = ![![2, 1], ![1, 2]] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, leakageMatrix, Fin.sum_univ_succ]

/-- The Gram matrix acts as `(2x+y, x+2y)`. -/
theorem gram_mulVec (vector : Fin 2 → ℝ) :
    Matrix.mulVec (![![2, 1], ![1, 2]] : Matrix (Fin 2) (Fin 2) ℝ) vector =
      ![2 * vector 0 + vector 1, vector 0 + 2 * vector 1] := by
  funext coordinate
  fin_cases coordinate <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- A Rayleigh-quotient certificate for the Gram upper bound `3`. -/
theorem gram_quadratic_le_three (vector : Fin 2 → ℝ) :
    dotProduct vector
        (Matrix.mulVec (![![2, 1], ![1, 2]] : Matrix (Fin 2) (Fin 2) ℝ) vector) ≤
      3 * dotProduct vector vector := by
  rw [gram_mulVec]
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (vector 0 - vector 1)]

/-- The all-ones vector attains the Gram bound `3`, certifying that it is sharp. -/
theorem gram_quadratic_eq_three_at_one :
    dotProduct (![1, 1] : Fin 2 → ℝ)
        (Matrix.mulVec (![![2, 1], ![1, 2]] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1]) =
      3 * dotProduct (![1, 1] : Fin 2 → ℝ) ![1, 1] := by
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-! ## Independent target-noise components -/

/-- The two independent draws used only by the target secret. -/
structure SecretNoise (R : Type) where
  e2 : R
  rho2 : R
  deriving DecidableEq

/-- The four independent draws used only by the target error. -/
structure ErrorNoise (R : Type) where
  e3 : R
  e0 : R
  e1 : R
  rho1 : R
  deriving DecidableEq

/-- All source noise, factored into independent secret-only and error-only blocks. -/
abbrev Noise (R : Type) := SecretNoise R × ErrorNoise R

/-- Sample the secret-only block. -/
def secretNoiseSampler {R : Type} (chi nu : ProbComp R) : ProbComp (SecretNoise R) := do
  let e2 ← chi
  let rho2 ← nu
  return ⟨e2, rho2⟩

/-- Sample the product part `(e₀,e₁,ρ₁)` of the target error. -/
def productNoiseSampler {R : Type} (chi nu : ProbComp R) : ProbComp (R × R × R) := do
  let e0 ← chi
  let e1 ← chi
  let rho1 ← nu
  return (e0, e1, rho1)

/-- Sample the error-only block. -/
def errorNoiseSampler {R : Type} (chi nu : ProbComp R) : ProbComp (ErrorNoise R) := do
  let e3 ← chi
  let productNoise ← productNoiseSampler chi nu
  return ⟨e3, productNoise.1, productNoise.2.1, productNoise.2.2⟩

/-- Sample the independent target-secret and target-error blocks. -/
def noiseSampler {R : Type} (chi nu : ProbComp R) : ProbComp (Noise R) := do
  let secretNoise ← secretNoiseSampler chi nu
  let errorNoise ← errorNoiseSampler chi nu
  return (secretNoise, errorNoise)

/-- The target secret `S = e₂ + ρ₂`. -/
def targetSecret {R : Type} [Add R] (noise : SecretNoise R) : R :=
  noise.e2 + noise.rho2

/-- The target error `E = e₃ - e₀ * (e₁ + ρ₁)`. -/
def targetError {R : Type} [Ring R] (noise : ErrorNoise R) : R :=
  noise.e3 - noise.e0 * (noise.e1 + noise.rho1)

/-! ## Public transcript and transformations -/

/-- The public projection of the four-sample Leaky-RLWE view used by the reduction. -/
structure SourceTranscript (R : Type) [Monoid R] where
  anchor : Rˣ
  a3 : R
  b0 : R
  b3 : R
  leak1 : R
  leak2 : R

/-- The hidden anchor product `T = a₀X`, used only in proofs. -/
def anchorProduct {R : Type} [Monoid R] (anchor : Rˣ) (secret : R) : R :=
  (anchor : R) * secret

/-- The public ratio `c = a₃ a₀⁻¹`. -/
def ratio {R : Type} [Monoid R] (transcript : SourceTranscript R) : R :=
  transcript.a3 * (transcript.anchor⁻¹ : Rˣ)

/-- The three public noisy copies `u₀,u₁,u₂`. -/
def u0 {R : Type} [Monoid R] (transcript : SourceTranscript R) : R := transcript.b0
def u1 {R : Type} [Semiring R] (transcript : SourceTranscript R) : R :=
  transcript.b0 + transcript.leak1
def u2 {R : Type} [Semiring R] (transcript : SourceTranscript R) : R :=
  transcript.b0 + transcript.leak2

/-- The intermediate mask `A~ = c-u₀-u₁`. -/
def intermediateA {R : Type} [Ring R] (transcript : SourceTranscript R) : R :=
  ratio transcript - u0 transcript - u1 transcript

/-- The intermediate body `B~ = d-u₀u₁`. -/
def intermediateB {R : Type} [Ring R] (transcript : SourceTranscript R) : R :=
  transcript.b3 - u0 transcript * u1 transcript

/-- The complete public secant-and-key-switch transformation. -/
def transform {R : Type} [Ring R] (transcript : SourceTranscript R) : R × R :=
  let aTilde := intermediateA transcript
  let bTilde := intermediateB transcript
  let shifted := u2 transcript
  (-aTilde - 2 * shifted,
    bTilde - aTilde * shifted - shifted ^ 2)

/-- Direct formula for the transformed mask. -/
theorem transform_fst {R : Type} [CommRing R] (transcript : SourceTranscript R) :
    (transform transcript).1 =
      -ratio transcript + u0 transcript + u1 transcript - 2 * u2 transcript := by
  simp [transform, intermediateA]
  ring

/-- Direct formula for the transformed body. -/
theorem transform_snd {R : Type} [CommRing R] (transcript : SourceTranscript R) :
    (transform transcript).2 =
      transcript.b3 - u0 transcript * u1 transcript - ratio transcript * u2 transcript +
        (u0 transcript + u1 transcript) * u2 transcript - u2 transcript ^ 2 := by
  simp [transform, intermediateA, intermediateB]
  ring

/-- Assemble the projected public transcript in the real Leaky-RLWE branch. -/
def realTranscript {R : Type} [CommRing R]
    (anchor : Rˣ) (a3 auxiliarySecret : R) (noise : Noise R) : SourceTranscript R where
  anchor := anchor
  a3 := a3
  b0 := anchorProduct anchor auxiliarySecret + noise.2.e0
  b3 := a3 * auxiliarySecret + noise.2.e3
  leak1 := noise.2.e1 - noise.2.e0 + noise.2.rho1
  leak2 := noise.1.e2 - noise.2.e0 + noise.1.rho2

/-- In the real branch, the three public copies have their claimed normal forms. -/
theorem realTranscript_u0_u1_u2 {R : Type} [CommRing R]
    (anchor : Rˣ) (a3 auxiliarySecret : R) (noise : Noise R) :
    u0 (realTranscript anchor a3 auxiliarySecret noise) =
        anchorProduct anchor auxiliarySecret + noise.2.e0 ∧
      u1 (realTranscript anchor a3 auxiliarySecret noise) =
        anchorProduct anchor auxiliarySecret + noise.2.e1 + noise.2.rho1 ∧
      u2 (realTranscript anchor a3 auxiliarySecret noise) =
        anchorProduct anchor auxiliarySecret + targetSecret noise.1 := by
  simp [u0, u1, u2, realTranscript, targetSecret]
  constructor <;> ring

/-- Multiplying the public ratio by `T` recovers `a₃X`. -/
theorem ratio_mul_anchorProduct {R : Type} [CommRing R]
    (anchor : Rˣ) (a3 auxiliarySecret : R) :
    (a3 * (anchor⁻¹ : Rˣ)) * anchorProduct anchor auxiliarySecret =
      a3 * auxiliarySecret := by
  calc
    (a3 * (anchor⁻¹ : Rˣ)) * anchorProduct anchor auxiliarySecret =
        a3 * ((anchor⁻¹ : Rˣ) : R) * (anchor : R) * auxiliarySecret := by
          simp only [anchorProduct]
          ring
    _ = a3 * auxiliarySecret := by simp

/-- The elementary secant identity used by the reduction. -/
theorem secant_identity {R : Type} [CommRing R] (T leftError rightError : R) :
    ((T + leftError) + (T + rightError)) * T -
        (T + leftError) * (T + rightError) =
      T ^ 2 - leftError * rightError := by
  ring

/-- The intermediate pair encrypts `T²` with the product error. -/
theorem intermediate_phase_real {R : Type} [CommRing R]
    (anchor : Rˣ) (a3 auxiliarySecret : R) (noise : Noise R) :
    intermediateB (realTranscript anchor a3 auxiliarySecret noise) =
      intermediateA (realTranscript anchor a3 auxiliarySecret noise) *
          anchorProduct anchor auxiliarySecret +
        anchorProduct anchor auxiliarySecret ^ 2 + targetError noise.2 := by
  have hratio := ratio_mul_anchorProduct anchor a3 auxiliarySecret
  have hratio' :
      a3 * anchorProduct anchor auxiliarySecret * ((anchor⁻¹ : Rˣ) : R) =
        a3 * auxiliarySecret := by
    calc
      _ = (a3 * ((anchor⁻¹ : Rˣ) : R)) *
          anchorProduct anchor auxiliarySecret := by ring
      _ = _ := hratio
  simp only [intermediateA, intermediateB, realTranscript, ratio, u0, u1,
    targetError]
  ring_nf
  rw [hratio']

/-- **Checked real-branch identity.**  The public transformation emits one unscaled encryption
of the square of its own target secret. -/
theorem transform_real {R : Type} [CommRing R]
    (anchor : Rˣ) (a3 auxiliarySecret : R) (noise : Noise R) :
    let output := transform (realTranscript anchor a3 auxiliarySecret noise)
    output.2 = output.1 * targetSecret noise.1 +
      targetSecret noise.1 ^ 2 + targetError noise.2 := by
  dsimp only
  have hintermediate := intermediate_phase_real anchor a3 auxiliarySecret noise
  have hu2 := (realTranscript_u0_u1_u2 anchor a3 auxiliarySecret noise).2.2
  simp only [transform]
  rw [hintermediate, hu2]
  ring

/-! ## Random-branch permutations -/

/-- The second public affine map in the reduction. -/
def finalMap {R : Type} [Ring R] (shifted : R) (pair : R × R) : R × R :=
  (-pair.1 - 2 * shifted, pair.2 - pair.1 * shifted - shifted ^ 2)

/-- Explicit inverse of `finalMap`. -/
def finalMapInv {R : Type} [Ring R] (shifted : R) (pair : R × R) : R × R :=
  let aTilde := -pair.1 - 2 * shifted
  (aTilde, pair.2 + aTilde * shifted + shifted ^ 2)

@[simp]
theorem finalMapInv_finalMap {R : Type} [CommRing R] (shifted : R) (pair : R × R) :
    finalMapInv shifted (finalMap shifted pair) = pair := by
  rcases pair with ⟨a, b⟩
  apply Prod.ext
  · simp [finalMap, finalMapInv]
  · simp [finalMap, finalMapInv]
    ring

@[simp]
theorem finalMap_finalMapInv {R : Type} [CommRing R] (shifted : R) (pair : R × R) :
    finalMap shifted (finalMapInv shifted pair) = pair := by
  rcases pair with ⟨a, b⟩
  apply Prod.ext
  · simp [finalMap, finalMapInv]
  · simp [finalMap, finalMapInv]
    ring

/-- The second public affine map is a permutation for every fixed `u₂`. -/
theorem finalMap_bijective {R : Type} [CommRing R] (shifted : R) :
    Function.Bijective (finalMap shifted) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨finalMapInv shifted, finalMapInv_finalMap shifted, finalMap_finalMapInv shifted⟩

/-- The first affine map `(c,d) ↦ (A~,B~)` is a permutation. -/
def intermediateMap {R : Type} [Ring R] (left right : R) (pair : R × R) : R × R :=
  (pair.1 - left - right, pair.2 - left * right)

/-- Explicit inverse of `intermediateMap`. -/
def intermediateMapInv {R : Type} [Ring R] (left right : R) (pair : R × R) : R × R :=
  (pair.1 + left + right, pair.2 + left * right)

@[simp]
theorem intermediateMapInv_intermediateMap {R : Type} [CommRing R]
    (left right : R) (pair : R × R) :
    intermediateMapInv left right (intermediateMap left right pair) = pair := by
  rcases pair with ⟨a, b⟩
  apply Prod.ext
  · simp [intermediateMap, intermediateMapInv]
    ring
  · simp [intermediateMap, intermediateMapInv]

@[simp]
theorem intermediateMap_intermediateMapInv {R : Type} [CommRing R]
    (left right : R) (pair : R × R) :
    intermediateMap left right (intermediateMapInv left right pair) = pair := by
  rcases pair with ⟨a, b⟩
  apply Prod.ext
  · simp [intermediateMap, intermediateMapInv]
    ring
  · simp [intermediateMap, intermediateMapInv]

/-- The first public affine map is a permutation for fixed noisy copies. -/
theorem intermediateMap_bijective {R : Type} [CommRing R] (left right : R) :
    Function.Bijective (intermediateMap left right) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨intermediateMapInv left right,
      intermediateMapInv_intermediateMap left right,
      intermediateMap_intermediateMapInv left right⟩

/-- The complete random-branch map on the two independent uniform values `(c,d)`. -/
def randomPairMap {R : Type} [Ring R] (left right shifted : R) (pair : R × R) : R × R :=
  finalMap shifted (intermediateMap left right pair)

/-- The complete random-branch map is a permutation. -/
theorem randomPairMap_bijective {R : Type} [CommRing R] (left right shifted : R) :
    Function.Bijective (randomPairMap left right shifted) :=
  (finalMap_bijective shifted).comp (intermediateMap_bijective left right)

/-! ## Zero-message map and additional public-key samples -/

/-- The real zero-message reduction before adding the independent product-noise correction. -/
def zeroBaseTransform {R : Type} [Ring R] (transcript : SourceTranscript R) : R × R :=
  (-ratio transcript, transcript.b3 - ratio transcript * u2 transcript)

/-- Add the independently sampled product component to the zero-message body. -/
def zeroTransform {R : Type} [Ring R] (fresh : R × R × R)
    (transcript : SourceTranscript R) : R × R :=
  let base := zeroBaseTransform transcript
  (base.1, base.2 - fresh.1 * (fresh.2.1 + fresh.2.2))

/-- **Checked zero-branch identity.** -/
theorem zeroTransform_real {R : Type} [CommRing R]
    (anchor : Rˣ) (a3 auxiliarySecret : R) (noise : Noise R) (fresh : R × R × R) :
    let output := zeroTransform fresh (realTranscript anchor a3 auxiliarySecret noise)
    output.2 = output.1 * targetSecret noise.1 +
      targetError ⟨noise.2.e3, fresh.1, fresh.2.1, fresh.2.2⟩ := by
  dsimp only
  have hratio := ratio_mul_anchorProduct anchor a3 auxiliarySecret
  have hu2 := (realTranscript_u0_u1_u2 anchor a3 auxiliarySecret noise).2.2
  simp only [zeroTransform, zeroBaseTransform]
  rw [hu2]
  simp only [realTranscript, ratio, targetError]
  ring_nf
  rw [hratio]
  ring

/-- A further source sample yields an ordinary public-key sample under the target secret. -/
theorem additional_sample_phase {R : Type} [CommRing R]
    (anchor : Rˣ) (auxiliarySecret aK eK : R) (secretNoise : SecretNoise R) :
    let cK := aK * (anchor⁻¹ : Rˣ)
    let T := anchorProduct anchor auxiliarySecret
    let shifted := T + targetSecret secretNoise
    (aK * auxiliarySecret + eK) - cK * shifted =
      (-cK) * targetSecret secretNoise + eK := by
  dsimp only
  have hratio := ratio_mul_anchorProduct anchor aK auxiliarySecret
  rw [mul_add, hratio]
  ring

/-! ## Finite samplers and distinguishing games -/

/-- Assemble the public projection in the random Leaky-RLWE branch.  The two bodies are
independent uniform values; all error-only leakages are retained. -/
def randomTranscript {R : Type} [CommRing R]
    (anchor : Rˣ) (noise : Noise R) (b0 : R) (a3b3 : R × R) : SourceTranscript R where
  anchor := anchor
  a3 := a3b3.1
  b0 := b0
  b3 := a3b3.2
  leak1 := noise.2.e1 - noise.2.e0 + noise.2.rho1
  leak2 := noise.1.e2 - noise.2.e0 + noise.1.rho2

/-- Reassemble the four source errors from the independent target-noise blocks. -/
def sourceErrors {R : Type} (noise : Noise R) : ErrorVector R :=
  ![noise.2.e0, noise.2.e1, noise.1.e2, noise.2.e3]

/-- The two independent leakage-error draws. -/
def sourceLeakageNoise {R : Type} (noise : Noise R) : LeakageVector R :=
  ![noise.2.rho1, noise.1.rho2]

/-- Matrix-form verification of the two noisy leakages used by the public transcript. -/
theorem sourceErrors_vecMul_add_leakageNoise {R : Type} [CommRing R] (noise : Noise R) :
    vecMul (sourceErrors noise) (leakageMatrix R) + sourceLeakageNoise noise =
      ![noise.2.e1 - noise.2.e0 + noise.2.rho1,
        noise.1.e2 - noise.2.e0 + noise.1.rho2] := by
  rw [vecMul_leakageMatrix]
  funext coordinate
  fin_cases coordinate <;> simp [sourceErrors, sourceLeakageNoise]

/-- The complete four-sample Leaky-RLWE public view.  The first mask is represented by a unit so
that the public transformation can use its certified inverse. -/
structure FullSourceTranscript (R : Type) [Monoid R] where
  anchor : Rˣ
  a1 : R
  a2 : R
  a3 : R
  b0 : R
  b1 : R
  b2 : R
  b3 : R
  leak1 : R
  leak2 : R

/-- Public projection used by the secant reduction. -/
def projectFullTranscript {R : Type} [Monoid R]
    (transcript : FullSourceTranscript R) : SourceTranscript R where
  anchor := transcript.anchor
  a3 := transcript.a3
  b0 := transcript.b0
  b3 := transcript.b3
  leak1 := transcript.leak1
  leak2 := transcript.leak2

/-- Assemble all four source samples in the real Leaky-RLWE branch. -/
def fullRealTranscript {R : Type} [CommRing R]
    (anchor : Rˣ) (a1 a2 a3 auxiliarySecret : R) (noise : Noise R) :
    FullSourceTranscript R where
  anchor := anchor
  a1 := a1
  a2 := a2
  a3 := a3
  b0 := anchorProduct anchor auxiliarySecret + noise.2.e0
  b1 := a1 * auxiliarySecret + noise.2.e1
  b2 := a2 * auxiliarySecret + noise.1.e2
  b3 := a3 * auxiliarySecret + noise.2.e3
  leak1 := noise.2.e1 - noise.2.e0 + noise.2.rho1
  leak2 := noise.1.e2 - noise.2.e0 + noise.1.rho2

/-- The core real transcript is exactly the public projection of the full four-sample view. -/
@[simp]
theorem projectFullTranscript_fullRealTranscript {R : Type} [CommRing R]
    (anchor : Rˣ) (a1 a2 a3 auxiliarySecret : R) (noise : Noise R) :
    projectFullTranscript (fullRealTranscript anchor a1 a2 a3 auxiliarySecret noise) =
      realTranscript anchor a3 auxiliarySecret noise := by
  rfl

/-- Assemble the full random branch from the three retained uniforms `(b₀,a₃,b₃)` and the four
discarded uniforms `(a₁,a₂,b₁,b₂)`. -/
def fullRandomTranscript {R : Type} [CommRing R]
    (anchor : Rˣ) (noise : Noise R) (b0 : R) (a3b3 : R × R)
    (unused : (R × R) × (R × R)) : FullSourceTranscript R where
  anchor := anchor
  a1 := unused.1.1
  a2 := unused.1.2
  a3 := a3b3.1
  b0 := b0
  b1 := unused.2.1
  b2 := unused.2.2
  b3 := a3b3.2
  leak1 := noise.2.e1 - noise.2.e0 + noise.2.rho1
  leak2 := noise.1.e2 - noise.2.e0 + noise.1.rho2

/-- The core random transcript is exactly the public projection of the full random view. -/
@[simp]
theorem projectFullTranscript_fullRandomTranscript {R : Type} [CommRing R]
    (anchor : Rˣ) (noise : Noise R) (b0 : R) (a3b3 : R × R)
    (unused : (R × R) × (R × R)) :
    projectFullTranscript (fullRandomTranscript anchor noise b0 a3b3 unused) =
      randomTranscript anchor noise b0 a3b3 := by
  rfl

/-- The projected real error-only Leaky-RLWE sampler. -/
def realLeakySampler {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R) :
    ProbComp (SourceTranscript R) := do
  let anchor ← anchorSampler
  let auxiliarySecret ← auxiliarySecretSampler
  let noise ← noiseSampler chi nu
  let a3 ← $ᵗ R
  return realTranscript anchor a3 auxiliarySecret noise

/-- The projected random error-only Leaky-RLWE sampler. -/
def randomLeakySampler {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R) :
    ProbComp (SourceTranscript R) := do
  let anchor ← anchorSampler
  let _auxiliarySecret ← auxiliarySecretSampler
  let noise ← noiseSampler chi nu
  let b0 ← $ᵗ R
  let a3b3 ← $ᵗ (R × R)
  return randomTranscript anchor noise b0 a3b3

/-- Full four-sample real Leaky-RLWE view. -/
def fullRealLeakySampler {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R) :
    ProbComp (FullSourceTranscript R) := do
  let anchor ← anchorSampler
  let auxiliarySecret ← auxiliarySecretSampler
  let noise ← noiseSampler chi nu
  let a1a2 ← $ᵗ (R × R)
  let a3 ← $ᵗ R
  return fullRealTranscript anchor a1a2.1 a1a2.2 a3 auxiliarySecret noise

/-- Full four-sample random Leaky-RLWE view, retaining the same noisy error leakages. -/
def fullRandomLeakySampler {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R) :
    ProbComp (FullSourceTranscript R) := do
  let anchor ← anchorSampler
  let _auxiliarySecret ← auxiliarySecretSampler
  let noise ← noiseSampler chi nu
  let b0 ← $ᵗ R
  let a3b3 ← $ᵗ (R × R)
  let unused ← $ᵗ ((R × R) × (R × R))
  return fullRandomTranscript anchor noise b0 a3b3 unused

/-- Projecting the full real view gives exactly the core real sampler. -/
theorem projectFull_real_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R) :
    evalDist (fullRealLeakySampler anchorSampler auxiliarySecretSampler chi nu >>=
        fun transcript ↦ pure (projectFullTranscript transcript)) =
      evalDist (realLeakySampler anchorSampler auxiliarySecretSampler chi nu) := by
  simp only [fullRealLeakySampler, realLeakySampler, bind_assoc, pure_bind,
    projectFullTranscript_fullRealTranscript]
  refine evalDist_bind_congr' anchorSampler fun anchor ↦ ?_
  refine evalDist_bind_congr' auxiliarySecretSampler fun auxiliarySecret ↦ ?_
  refine evalDist_bind_congr' (noiseSampler chi nu) fun noise ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
    ($ᵗ (R × R)) (by simp) _

/-- Projecting the full random view gives exactly the core random sampler. -/
theorem projectFull_random_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R) :
    evalDist (fullRandomLeakySampler anchorSampler auxiliarySecretSampler chi nu >>=
        fun transcript ↦ pure (projectFullTranscript transcript)) =
      evalDist (randomLeakySampler anchorSampler auxiliarySecretSampler chi nu) := by
  simp only [fullRandomLeakySampler, randomLeakySampler, bind_assoc, pure_bind,
    projectFullTranscript_fullRandomTranscript]
  refine evalDist_bind_congr' anchorSampler fun anchor ↦ ?_
  refine evalDist_bind_congr' auxiliarySecretSampler fun _auxiliarySecret ↦ ?_
  refine evalDist_bind_congr' (noiseSampler chi nu) fun noise ↦ ?_
  refine evalDist_bind_congr' ($ᵗ R) fun b0 ↦ ?_
  refine evalDist_bind_congr' ($ᵗ (R × R)) fun a3b3 ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
    ($ᵗ ((R × R) × (R × R))) (by simp) _

/-- A canonical one-row square ciphertext with explicit secret and error. -/
def squareOutput {R : Type} [Ring R] (mask secret error : R) : R × R :=
  (mask, mask * secret + secret ^ 2 + error)

/-- A canonical one-row zero-message ciphertext with explicit secret and error. -/
def zeroOutput {R : Type} [Ring R] (mask secret error : R) : R × R :=
  (mask, mask * secret + error)

/-- The target square-ciphertext sampler.  The sampler factorization makes the target secret and
target error independent by construction. -/
def squareSampler {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) : ProbComp (R × R) := do
  let noise ← noiseSampler chi nu
  let mask ← $ᵗ R
  return squareOutput mask (targetSecret noise.1) (targetError noise.2)

/-- The target zero-message sampler with exactly the same independent secret and error laws. -/
def zeroSampler {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) : ProbComp (R × R) := do
  let noise ← noiseSampler chi nu
  let mask ← $ᵗ R
  return zeroOutput mask (targetSecret noise.1) (targetError noise.2)

/-- The common uniform endpoint. -/
def uniformSampler {R : Type} [SampleableType R] : ProbComp (R × R) :=
  $ᵗ (R × R)

/-- Standalone target-secret law `χ * ν`. -/
def targetSecretSampler {R : Type} [Add R]
    (chi nu : ProbComp R) : ProbComp R :=
  targetSecret <$> secretNoiseSampler chi nu

/-- Standalone target product-error law. -/
def targetErrorSampler {R : Type} [Ring R]
    (chi nu : ProbComp R) : ProbComp R :=
  targetError <$> errorNoiseSampler chi nu

/-- The square sampler is exactly the product of the standalone target-secret and target-error
samplers, followed by an independent uniform mask. -/
theorem squareSampler_eq_independent {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) :
    squareSampler chi nu = do
      let secret ← targetSecretSampler chi nu
      let error ← targetErrorSampler chi nu
      let mask ← $ᵗ R
      return squareOutput mask secret error := by
  simp [squareSampler, noiseSampler, targetSecretSampler, targetErrorSampler,
    map_eq_bind_pure_comp, bind_assoc, monad_norm]

/-- The same exact independent target laws are used by the zero-message sampler. -/
theorem zeroSampler_eq_independent {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) :
    zeroSampler chi nu = do
      let secret ← targetSecretSampler chi nu
      let error ← targetErrorSampler chi nu
      let mask ← $ᵗ R
      return zeroOutput mask secret error := by
  simp [zeroSampler, noiseSampler, targetSecretSampler, targetErrorSampler,
    map_eq_bind_pure_comp, bind_assoc, monad_norm]

/-- Public square-ciphertext distinguishers. -/
abbrev Distinguisher (R : Type) := R × R → ProbComp Bool

/-- Distinguishers for the projected Leaky-RLWE source view. -/
abbrev LeakyDistinguisher (R : Type) [Monoid R] := SourceTranscript R → ProbComp Bool

/-- Distinguishers for the complete four-sample Leaky-RLWE view. -/
abbrev FullLeakyDistinguisher (R : Type) [Monoid R] :=
  FullSourceTranscript R → ProbComp Bool

/-- Square-ciphertext real-versus-uniform game. -/
def squareGame {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) (distinguisher : Distinguisher R) : ProbComp Bool :=
  squareSampler chi nu >>= distinguisher

/-- Zero-message real-versus-uniform game. -/
def zeroGame {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) (distinguisher : Distinguisher R) : ProbComp Bool :=
  zeroSampler chi nu >>= distinguisher

/-- Uniform target game. -/
def uniformGame {R : Type} [SampleableType R]
    (distinguisher : Distinguisher R) : ProbComp Bool :=
  uniformSampler >>= distinguisher

/-- Quadratic real-versus-zero KDM advantage. -/
noncomputable def kdmAdvantage {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) (distinguisher : Distinguisher R) : ℝ :=
  (squareGame chi nu distinguisher).boolDistAdvantage
    (zeroGame chi nu distinguisher)

/-- Square-ciphertext real-versus-uniform advantage. -/
noncomputable def squareAdvantage {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) (distinguisher : Distinguisher R) : ℝ :=
  (squareGame chi nu distinguisher).boolDistAdvantage (uniformGame distinguisher)

/-- Zero-message real-versus-uniform advantage. -/
noncomputable def zeroAdvantage {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) (distinguisher : Distinguisher R) : ℝ :=
  (zeroGame chi nu distinguisher).boolDistAdvantage (uniformGame distinguisher)

/-- Projected Leaky-RLWE real game. -/
def leakyRealGame {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : LeakyDistinguisher R) : ProbComp Bool :=
  realLeakySampler anchorSampler auxiliarySecretSampler chi nu >>= distinguisher

/-- Projected Leaky-RLWE random game. -/
def leakyRandomGame {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : LeakyDistinguisher R) : ProbComp Bool :=
  randomLeakySampler anchorSampler auxiliarySecretSampler chi nu >>= distinguisher

/-- Projected error-only Leaky-RLWE advantage. -/
noncomputable def leakyAdvantage {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : LeakyDistinguisher R) : ℝ :=
  (leakyRealGame anchorSampler auxiliarySecretSampler chi nu distinguisher).boolDistAdvantage
    (leakyRandomGame anchorSampler auxiliarySecretSampler chi nu distinguisher)

/-- Full four-sample Leaky-RLWE real game. -/
def fullLeakyRealGame {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : FullLeakyDistinguisher R) : ProbComp Bool :=
  fullRealLeakySampler anchorSampler auxiliarySecretSampler chi nu >>= distinguisher

/-- Full four-sample Leaky-RLWE random game. -/
def fullLeakyRandomGame {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : FullLeakyDistinguisher R) : ProbComp Bool :=
  fullRandomLeakySampler anchorSampler auxiliarySecretSampler chi nu >>= distinguisher

/-- Full four-sample error-only Leaky-RLWE advantage matching the view to which the 2025 theorem
applies (subject to its analytic parameter hypotheses). -/
noncomputable def fullLeakyAdvantage {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : FullLeakyDistinguisher R) : ℝ :=
  (fullLeakyRealGame anchorSampler auxiliarySecretSampler chi nu distinguisher).boolDistAdvantage
    (fullLeakyRandomGame anchorSampler auxiliarySecretSampler chi nu distinguisher)

/-- Lift a projected-view distinguisher to the complete four-sample view by ignoring the two
unused samples. -/
def fullProjectionReduction {R : Type} [Monoid R]
    (distinguisher : LeakyDistinguisher R) : FullLeakyDistinguisher R :=
  fun transcript ↦ distinguisher (projectFullTranscript transcript)

/-- Exact real-game equality for the full-view projection. -/
theorem fullProjectionReduction_realGame_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : LeakyDistinguisher R) :
    evalDist (fullLeakyRealGame anchorSampler auxiliarySecretSampler chi nu
        (fullProjectionReduction distinguisher)) =
      evalDist (leakyRealGame anchorSampler auxiliarySecretSampler chi nu distinguisher) := by
  unfold fullLeakyRealGame fullProjectionReduction leakyRealGame
  simpa only [bind_assoc, pure_bind] using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (projectFull_real_evalDist anchorSampler auxiliarySecretSampler chi nu) distinguisher)

/-- Exact random-game equality for the full-view projection. -/
theorem fullProjectionReduction_randomGame_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : LeakyDistinguisher R) :
    evalDist (fullLeakyRandomGame anchorSampler auxiliarySecretSampler chi nu
        (fullProjectionReduction distinguisher)) =
      evalDist (leakyRandomGame anchorSampler auxiliarySecretSampler chi nu distinguisher) := by
  unfold fullLeakyRandomGame fullProjectionReduction leakyRandomGame
  simpa only [bind_assoc, pure_bind] using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (projectFull_random_evalDist anchorSampler auxiliarySecretSampler chi nu) distinguisher)

/-- A projected-view attack has exactly the advantage of its lifted full-view attack. -/
theorem leakyAdvantage_eq_fullProjection {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : LeakyDistinguisher R) :
    leakyAdvantage anchorSampler auxiliarySecretSampler chi nu distinguisher =
      fullLeakyAdvantage anchorSampler auxiliarySecretSampler chi nu
        (fullProjectionReduction distinguisher) := by
  unfold leakyAdvantage fullLeakyAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (fullProjectionReduction_realGame_evalDist anchorSampler auxiliarySecretSampler chi nu
        distinguisher) true,
    evalDist_ext_iff.mp
      (fullProjectionReduction_randomGame_evalDist anchorSampler auxiliarySecretSampler chi nu
        distinguisher) true]

/-! ### Uniform reindexing certificates -/

/-- The affine unit map which turns the uniform source mask `a₃` into the target mask. -/
def unitAffineMap {R : Type} [Ring R] (anchor : Rˣ) (shift value : R) : R :=
  -(value * (anchor⁻¹ : Rˣ)) + shift

/-- Explicit inverse of `unitAffineMap`. -/
def unitAffineMapInv {R : Type} [Ring R] (anchor : Rˣ) (shift value : R) : R :=
  (shift - value) * (anchor : R)

@[simp]
theorem unitAffineMapInv_unitAffineMap {R : Type} [CommRing R]
    (anchor : Rˣ) (shift value : R) :
    unitAffineMapInv anchor shift (unitAffineMap anchor shift value) = value := by
  simp [unitAffineMapInv, unitAffineMap]

@[simp]
theorem unitAffineMap_unitAffineMapInv {R : Type} [CommRing R]
    (anchor : Rˣ) (shift value : R) :
    unitAffineMap anchor shift (unitAffineMapInv anchor shift value) = value := by
  simp [unitAffineMapInv, unitAffineMap]

/-- The real-branch mask change is a permutation. -/
theorem unitAffineMap_bijective {R : Type} [CommRing R] (anchor : Rˣ) (shift : R) :
    Function.Bijective (unitAffineMap anchor shift) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unitAffineMapInv anchor shift,
      unitAffineMapInv_unitAffineMap anchor shift,
      unitAffineMap_unitAffineMapInv anchor shift⟩

/-- Noise-dependent translation in the transformed real mask; the auxiliary secret cancels. -/
def realMaskShift {R : Type} [Ring R] (noise : Noise R) : R :=
  noise.2.e0 + noise.2.e1 + noise.2.rho1 -
    2 * (noise.1.e2 + noise.1.rho2)

/-- Exact normal form for the transformed real mask. -/
theorem transform_real_fst {R : Type} [CommRing R]
    (anchor : Rˣ) (a3 auxiliarySecret : R) (noise : Noise R) :
    (transform (realTranscript anchor a3 auxiliarySecret noise)).1 =
      unitAffineMap anchor (realMaskShift noise) a3 := by
  rw [transform_fst]
  simp [realTranscript, ratio, u0, u1, u2, unitAffineMap, realMaskShift,
    anchorProduct]
  ring

/-- Exact output normal form before reindexing the uniform source mask. -/
theorem transform_real_eq_squareOutput {R : Type} [CommRing R]
    (anchor : Rˣ) (a3 auxiliarySecret : R) (noise : Noise R) :
    transform (realTranscript anchor a3 auxiliarySecret noise) =
      squareOutput (unitAffineMap anchor (realMaskShift noise) a3)
        (targetSecret noise.1) (targetError noise.2) := by
  apply Prod.ext
  · exact transform_real_fst anchor a3 auxiliarySecret noise
  · rw [show (transform (realTranscript anchor a3 auxiliarySecret noise)).2 =
        (transform (realTranscript anchor a3 auxiliarySecret noise)).1 *
            targetSecret noise.1 + targetSecret noise.1 ^ 2 + targetError noise.2 from
      transform_real anchor a3 auxiliarySecret noise]
    rw [transform_real_fst]
    rfl

/-- Multiplication by the inverse anchor on the first coordinate is a permutation of pairs. -/
def anchorRatioMap {R : Type} [Monoid R] (anchor : Rˣ) (pair : R × R) : R × R :=
  (pair.1 * (anchor⁻¹ : Rˣ), pair.2)

/-- Explicit inverse of `anchorRatioMap`. -/
def anchorRatioMapInv {R : Type} [Monoid R] (anchor : Rˣ) (pair : R × R) : R × R :=
  (pair.1 * (anchor : R), pair.2)

@[simp]
theorem anchorRatioMapInv_anchorRatioMap {R : Type} [CommMonoid R]
    (anchor : Rˣ) (pair : R × R) :
    anchorRatioMapInv anchor (anchorRatioMap anchor pair) = pair := by
  rcases pair with ⟨a, b⟩
  ext <;> simp [anchorRatioMapInv, anchorRatioMap, mul_assoc]

@[simp]
theorem anchorRatioMap_anchorRatioMapInv {R : Type} [CommMonoid R]
    (anchor : Rˣ) (pair : R × R) :
    anchorRatioMap anchor (anchorRatioMapInv anchor pair) = pair := by
  rcases pair with ⟨a, b⟩
  ext <;> simp [anchorRatioMapInv, anchorRatioMap, mul_assoc]

theorem anchorRatioMap_bijective {R : Type} [CommMonoid R] (anchor : Rˣ) :
    Function.Bijective (anchorRatioMap anchor) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨anchorRatioMapInv anchor,
      anchorRatioMapInv_anchorRatioMap anchor,
      anchorRatioMap_anchorRatioMapInv anchor⟩

/-- The complete random-branch map on the independent uniforms `(a₃,b₃)`. -/
def randomOutputMap {R : Type} [CommRing R]
    (anchor : Rˣ) (noise : Noise R) (b0 : R) : R × R → R × R :=
  randomPairMap b0
    (b0 + (noise.2.e1 - noise.2.e0 + noise.2.rho1))
    (b0 + (noise.1.e2 - noise.2.e0 + noise.1.rho2)) ∘
      anchorRatioMap anchor

/-- The public transform of a random transcript is `randomOutputMap`. -/
theorem transform_randomTranscript {R : Type} [CommRing R]
    (anchor : Rˣ) (noise : Noise R) (b0 : R) (a3b3 : R × R) :
    transform (randomTranscript anchor noise b0 a3b3) =
      randomOutputMap anchor noise b0 a3b3 := by
  simp [transform, randomTranscript, randomOutputMap, randomPairMap, finalMap,
    intermediateMap, anchorRatioMap, intermediateA, intermediateB, ratio, u0, u1, u2,
    Function.comp_apply]

/-- The complete random-branch map is a permutation. -/
theorem randomOutputMap_bijective {R : Type} [CommRing R]
    (anchor : Rˣ) (noise : Noise R) (b0 : R) :
    Function.Bijective (randomOutputMap anchor noise b0) :=
  (randomPairMap_bijective b0
      (b0 + (noise.2.e1 - noise.2.e0 + noise.2.rho1))
      (b0 + (noise.1.e2 - noise.2.e0 + noise.1.rho2))).comp
    (anchorRatioMap_bijective anchor)

/-! ### Exact square-ciphertext game transport -/

/-- For fixed hidden context, reindexing the uniform source mask gives the canonical square
ciphertext distribution. -/
theorem fixedRealTransform_evalDist_eq_square {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchor : Rˣ) (auxiliarySecret : R) (noise : Noise R) :
    evalDist (($ᵗ R) >>= fun a3 ↦
        pure (transform (realTranscript anchor a3 auxiliarySecret noise))) =
      evalDist (($ᵗ R) >>= fun mask ↦
        pure (squareOutput mask (targetSecret noise.1) (targetError noise.2))) := by
  apply evalDist_ext
  intro output
  simpa only [transform_real_eq_squareOutput] using
    (probOutput_bind_bijective_uniform_cross
      (α := R) (β := R)
      (unitAffineMap anchor (realMaskShift noise))
      (unitAffineMap_bijective anchor (realMaskShift noise))
      (fun mask ↦ pure
        (squareOutput mask (targetSecret noise.1) (targetError noise.2))) output)

/-- Mapping the complete projected real Leaky-RLWE view gives the canonical square sampler.
The anchor and auxiliary-secret samplers are required to be lossless because both values disappear
from the target distribution. -/
theorem transformedRealLeaky_evalDist_eq_square {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0) :
    evalDist (realLeakySampler anchorSampler auxiliarySecretSampler chi nu >>= fun transcript ↦
        pure (transform transcript)) =
      evalDist (squareSampler chi nu) := by
  let Tail := fun noise : Noise R ↦
    ($ᵗ R) >>= fun mask ↦
      pure (squareOutput mask (targetSecret noise.1) (targetError noise.2))
  calc
    evalDist (realLeakySampler anchorSampler auxiliarySecretSampler chi nu >>=
        fun transcript ↦ pure (transform transcript)) =
      evalDist (anchorSampler >>= fun anchor ↦
        auxiliarySecretSampler >>= fun auxiliarySecret ↦
          noiseSampler chi nu >>= fun noise ↦ Tail noise) := by
      simp only [realLeakySampler, bind_assoc, pure_bind]
      refine evalDist_bind_congr' anchorSampler fun anchor ↦ ?_
      refine evalDist_bind_congr' auxiliarySecretSampler fun auxiliarySecret ↦ ?_
      refine evalDist_bind_congr' (noiseSampler chi nu) fun noise ↦ ?_
      exact fixedRealTransform_evalDist_eq_square anchor auxiliarySecret noise
    _ = evalDist (anchorSampler >>= fun _anchor ↦
        noiseSampler chi nu >>= Tail) := by
      refine evalDist_bind_congr' anchorSampler fun _anchor ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        auxiliarySecretSampler hAuxiliarySecret _
    _ = evalDist (noiseSampler chi nu >>= Tail) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        anchorSampler hAnchor _
    _ = evalDist (squareSampler chi nu) := by
      rfl

/-- For every fixed random-branch context, the complete public map preserves the uniform pair. -/
theorem fixedRandomTransform_evalDist_eq_uniform {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchor : Rˣ) (noise : Noise R) (b0 : R) :
    evalDist (($ᵗ (R × R)) >>= fun a3b3 ↦
        pure (transform (randomTranscript anchor noise b0 a3b3))) =
      evalDist (uniformSampler (R := R)) := by
  apply evalDist_ext
  intro output
  simpa [transform_randomTranscript, uniformSampler, monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := R × R) (β := R × R)
      (randomOutputMap anchor noise b0) (randomOutputMap_bijective anchor noise b0)
      (fun pair ↦ pure pair) output)

/-- Mapping the complete projected random Leaky-RLWE view gives the canonical uniform pair. -/
theorem transformedRandomLeaky_evalDist_eq_uniform {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0) :
    evalDist (randomLeakySampler anchorSampler auxiliarySecretSampler chi nu >>=
        fun transcript ↦ pure (transform transcript)) =
      evalDist (uniformSampler (R := R)) := by
  let Uniform := uniformSampler (R := R)
  calc
    evalDist (randomLeakySampler anchorSampler auxiliarySecretSampler chi nu >>=
        fun transcript ↦ pure (transform transcript)) =
      evalDist (anchorSampler >>= fun anchor ↦
        auxiliarySecretSampler >>= fun _auxiliarySecret ↦
          noiseSampler chi nu >>= fun noise ↦
            ($ᵗ R) >>= fun b0 ↦ Uniform) := by
      simp only [randomLeakySampler, bind_assoc, pure_bind]
      refine evalDist_bind_congr' anchorSampler fun anchor ↦ ?_
      refine evalDist_bind_congr' auxiliarySecretSampler fun _auxiliarySecret ↦ ?_
      refine evalDist_bind_congr' (noiseSampler chi nu) fun noise ↦ ?_
      refine evalDist_bind_congr' ($ᵗ R) fun b0 ↦ ?_
      exact fixedRandomTransform_evalDist_eq_uniform anchor noise b0
    _ = evalDist (anchorSampler >>= fun _anchor ↦
        auxiliarySecretSampler >>= fun _auxiliarySecret ↦
          noiseSampler chi nu >>= fun _noise ↦ Uniform) := by
      refine evalDist_bind_congr' anchorSampler fun _anchor ↦ ?_
      refine evalDist_bind_congr' auxiliarySecretSampler fun _auxiliarySecret ↦ ?_
      refine evalDist_bind_congr' (noiseSampler chi nu) fun _noise ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _
    _ = evalDist (anchorSampler >>= fun _anchor ↦
        auxiliarySecretSampler >>= fun _auxiliarySecret ↦ Uniform) := by
      refine evalDist_bind_congr' anchorSampler fun _anchor ↦ ?_
      refine evalDist_bind_congr' auxiliarySecretSampler fun _auxiliarySecret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (noiseSampler chi nu) hNoise _
    _ = evalDist (anchorSampler >>= fun _anchor ↦ Uniform) := by
      refine evalDist_bind_congr' anchorSampler fun _anchor ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        auxiliarySecretSampler hAuxiliarySecret _
    _ = evalDist Uniform :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        anchorSampler hAnchor _

/-- Deterministic reduction from square-ciphertext distinguishing to projected Leaky-RLWE. -/
def squareReduction {R : Type} [Ring R]
    (distinguisher : Distinguisher R) : LeakyDistinguisher R :=
  fun transcript ↦ distinguisher (transform transcript)

/-- Exact equality of the square real game and the reduced Leaky-RLWE real game. -/
theorem squareReduction_realGame_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0) :
    evalDist (leakyRealGame anchorSampler auxiliarySecretSampler chi nu
        (squareReduction distinguisher)) =
      evalDist (squareGame chi nu distinguisher) := by
  unfold leakyRealGame squareReduction squareGame
  simpa only [bind_assoc, pure_bind] using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (transformedRealLeaky_evalDist_eq_square
        anchorSampler auxiliarySecretSampler chi nu hAnchor hAuxiliarySecret)
      distinguisher)

/-- Exact equality of the square uniform game and the reduced Leaky-RLWE random game. -/
theorem squareReduction_randomGame_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0) :
    evalDist (leakyRandomGame anchorSampler auxiliarySecretSampler chi nu
        (squareReduction distinguisher)) =
      evalDist (uniformGame distinguisher) := by
  unfold leakyRandomGame squareReduction uniformGame
  simpa only [bind_assoc, pure_bind] using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (transformedRandomLeaky_evalDist_eq_uniform
        anchorSampler auxiliarySecretSampler chi nu hAnchor hAuxiliarySecret hNoise)
      distinguisher)

/-- **Exact square reduction.** -/
theorem squareAdvantage_eq_leaky {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0) :
    squareAdvantage chi nu distinguisher =
      leakyAdvantage anchorSampler auxiliarySecretSampler chi nu
        (squareReduction distinguisher) := by
  unfold squareAdvantage leakyAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (squareReduction_realGame_evalDist anchorSampler auxiliarySecretSampler chi nu
        distinguisher hAnchor hAuxiliarySecret) true,
    evalDist_ext_iff.mp
      (squareReduction_randomGame_evalDist anchorSampler auxiliarySecretSampler chi nu
        distinguisher hAnchor hAuxiliarySecret hNoise) true]

/-- Full four-sample form of the exact square-ciphertext reduction. -/
theorem squareAdvantage_eq_fullLeaky {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0) :
    squareAdvantage chi nu distinguisher =
      fullLeakyAdvantage anchorSampler auxiliarySecretSampler chi nu
        (fullProjectionReduction (squareReduction distinguisher)) := by
  rw [squareAdvantage_eq_leaky anchorSampler auxiliarySecretSampler chi nu distinguisher
      hAnchor hAuxiliarySecret hNoise,
    leakyAdvantage_eq_fullProjection]

/-! ### Exact zero-message game transport -/

/-- Pointwise normal form of the real zero-message reduction. -/
theorem zeroTransform_real_eq_zeroOutput {R : Type} [CommRing R]
    (anchor : Rˣ) (a3 auxiliarySecret : R) (noise : Noise R) (fresh : R × R × R) :
    zeroTransform fresh (realTranscript anchor a3 auxiliarySecret noise) =
      zeroOutput (unitAffineMap anchor 0 a3) (targetSecret noise.1)
        (targetError ⟨noise.2.e3, fresh.1, fresh.2.1, fresh.2.2⟩) := by
  apply Prod.ext
  · simp [zeroTransform, zeroBaseTransform, realTranscript, ratio, unitAffineMap, zeroOutput]
  · rw [show (zeroTransform fresh (realTranscript anchor a3 auxiliarySecret noise)).2 =
        (zeroTransform fresh (realTranscript anchor a3 auxiliarySecret noise)).1 *
            targetSecret noise.1 +
          targetError ⟨noise.2.e3, fresh.1, fresh.2.1, fresh.2.2⟩ from
      zeroTransform_real anchor a3 auxiliarySecret noise fresh]
    simp [zeroTransform, zeroBaseTransform, realTranscript, ratio, unitAffineMap, zeroOutput]

/-- For fixed source context, swap the fresh product noise forward and reindex the uniform source
mask to obtain a canonical zero-message ciphertext. -/
theorem fixedRealZeroTransform_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (chi nu : ProbComp R) (anchor : Rˣ) (auxiliarySecret : R)
    (secretNoise : SecretNoise R) (sourceError : ErrorNoise R) :
    evalDist (($ᵗ R) >>= fun a3 ↦
        productNoiseSampler chi nu >>= fun fresh ↦
          pure (zeroTransform fresh
            (realTranscript anchor a3 auxiliarySecret (secretNoise, sourceError)))) =
      evalDist (productNoiseSampler chi nu >>= fun fresh ↦
        ($ᵗ R) >>= fun mask ↦
          pure (zeroOutput mask (targetSecret secretNoise)
            (targetError ⟨sourceError.e3, fresh.1, fresh.2.1, fresh.2.2⟩))) := by
  calc
    _ = evalDist (productNoiseSampler chi nu >>= fun fresh ↦
        ($ᵗ R) >>= fun a3 ↦
          pure (zeroTransform fresh
            (realTranscript anchor a3 auxiliarySecret (secretNoise, sourceError)))) :=
      evalDist_bind_bind_swap ($ᵗ R) (productNoiseSampler chi nu) _
    _ = _ := by
      refine evalDist_bind_congr' (productNoiseSampler chi nu) fun fresh ↦ ?_
      apply evalDist_ext
      intro output
      simpa only [zeroTransform_real_eq_zeroOutput] using
        (probOutput_bind_bijective_uniform_cross
          (α := R) (β := R) (unitAffineMap anchor 0)
          (unitAffineMap_bijective anchor 0)
          (fun mask ↦ pure (zeroOutput mask (targetSecret secretNoise)
            (targetError ⟨sourceError.e3, fresh.1, fresh.2.1, fresh.2.2⟩))) output)

/-- Complete real-view transport for the zero-message reduction. -/
theorem transformedRealLeaky_evalDist_eq_zero {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0) :
    evalDist (realLeakySampler anchorSampler auxiliarySecretSampler chi nu >>= fun transcript ↦
        productNoiseSampler chi nu >>= fun fresh ↦
          pure (zeroTransform fresh transcript)) =
      evalDist (zeroSampler chi nu) := by
  let Finish := fun (secretNoise : SecretNoise R) (e3 : R) (fresh : R × R × R) ↦
    ($ᵗ R) >>= fun mask ↦ pure
      (zeroOutput mask (targetSecret secretNoise)
        (targetError ⟨e3, fresh.1, fresh.2.1, fresh.2.2⟩))
  calc
    evalDist (realLeakySampler anchorSampler auxiliarySecretSampler chi nu >>=
        fun transcript ↦ productNoiseSampler chi nu >>= fun fresh ↦
          pure (zeroTransform fresh transcript)) =
      evalDist (anchorSampler >>= fun anchor ↦
        auxiliarySecretSampler >>= fun auxiliarySecret ↦
          secretNoiseSampler chi nu >>= fun secretNoise ↦
            chi >>= fun e3 ↦
              productNoiseSampler chi nu >>= fun sourceProduct ↦
                productNoiseSampler chi nu >>= fun fresh ↦
                  Finish secretNoise e3 fresh) := by
      simp only [realLeakySampler, noiseSampler, errorNoiseSampler,
        bind_assoc, pure_bind]
      refine evalDist_bind_congr' anchorSampler fun anchor ↦ ?_
      refine evalDist_bind_congr' auxiliarySecretSampler fun auxiliarySecret ↦ ?_
      refine evalDist_bind_congr' (secretNoiseSampler chi nu) fun secretNoise ↦ ?_
      refine evalDist_bind_congr' chi fun e3 ↦ ?_
      refine evalDist_bind_congr' (productNoiseSampler chi nu) fun sourceProduct ↦ ?_
      simpa only [Finish] using
        fixedRealZeroTransform_evalDist chi nu anchor auxiliarySecret secretNoise
          ⟨e3, sourceProduct.1, sourceProduct.2.1, sourceProduct.2.2⟩
    _ = evalDist (anchorSampler >>= fun _anchor ↦
        auxiliarySecretSampler >>= fun _auxiliarySecret ↦
          secretNoiseSampler chi nu >>= fun secretNoise ↦
            chi >>= fun e3 ↦
              productNoiseSampler chi nu >>= fun fresh ↦
                Finish secretNoise e3 fresh) := by
      refine evalDist_bind_congr' anchorSampler fun _anchor ↦ ?_
      refine evalDist_bind_congr' auxiliarySecretSampler fun _auxiliarySecret ↦ ?_
      refine evalDist_bind_congr' (secretNoiseSampler chi nu) fun secretNoise ↦ ?_
      refine evalDist_bind_congr' chi fun e3 ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (productNoiseSampler chi nu) hProductNoise _
    _ = evalDist (anchorSampler >>= fun _anchor ↦
        secretNoiseSampler chi nu >>= fun secretNoise ↦
          chi >>= fun e3 ↦
            productNoiseSampler chi nu >>= fun fresh ↦ Finish secretNoise e3 fresh) := by
      refine evalDist_bind_congr' anchorSampler fun _anchor ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        auxiliarySecretSampler hAuxiliarySecret _
    _ = evalDist (secretNoiseSampler chi nu >>= fun secretNoise ↦
        chi >>= fun e3 ↦
          productNoiseSampler chi nu >>= fun fresh ↦ Finish secretNoise e3 fresh) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        anchorSampler hAnchor _
    _ = evalDist (zeroSampler chi nu) := by
      simp [zeroSampler, noiseSampler, errorNoiseSampler, Finish, bind_assoc, monad_norm]

/-- Triangular zero-message map on the independent uniform pair `(c,d)`. -/
def zeroPairMap {R : Type} [Ring R] (shift correction : R) (pair : R × R) : R × R :=
  (-pair.1, pair.2 - pair.1 * shift - correction)

/-- Explicit inverse of `zeroPairMap`. -/
def zeroPairMapInv {R : Type} [Ring R] (shift correction : R) (pair : R × R) : R × R :=
  (-pair.1, pair.2 + (-pair.1) * shift + correction)

@[simp]
theorem zeroPairMapInv_zeroPairMap {R : Type} [CommRing R]
    (shift correction : R) (pair : R × R) :
    zeroPairMapInv shift correction (zeroPairMap shift correction pair) = pair := by
  rcases pair with ⟨a, b⟩
  apply Prod.ext
  · simp [zeroPairMapInv, zeroPairMap]
  · simp [zeroPairMapInv, zeroPairMap]
    ring

@[simp]
theorem zeroPairMap_zeroPairMapInv {R : Type} [CommRing R]
    (shift correction : R) (pair : R × R) :
    zeroPairMap shift correction (zeroPairMapInv shift correction pair) = pair := by
  rcases pair with ⟨a, b⟩
  apply Prod.ext
  · simp [zeroPairMapInv, zeroPairMap]
  · simp [zeroPairMapInv, zeroPairMap]
    ring

theorem zeroPairMap_bijective {R : Type} [CommRing R] (shift correction : R) :
    Function.Bijective (zeroPairMap shift correction) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨zeroPairMapInv shift correction,
      zeroPairMapInv_zeroPairMap shift correction,
      zeroPairMap_zeroPairMapInv shift correction⟩

/-- Complete random zero-message output map on the source uniforms `(a₃,b₃)`. -/
def randomZeroOutputMap {R : Type} [CommRing R]
    (anchor : Rˣ) (shift correction : R) : R × R → R × R :=
  zeroPairMap shift correction ∘ anchorRatioMap anchor

theorem randomZeroOutputMap_bijective {R : Type} [CommRing R]
    (anchor : Rˣ) (shift correction : R) :
    Function.Bijective (randomZeroOutputMap anchor shift correction) :=
  (zeroPairMap_bijective shift correction).comp (anchorRatioMap_bijective anchor)

/-- Pointwise random-branch normal form for the zero reduction. -/
theorem zeroTransform_randomTranscript {R : Type} [CommRing R]
    (anchor : Rˣ) (noise : Noise R) (b0 : R) (fresh : R × R × R)
    (a3b3 : R × R) :
    zeroTransform fresh (randomTranscript anchor noise b0 a3b3) =
      randomZeroOutputMap anchor
        (b0 + (noise.1.e2 - noise.2.e0 + noise.1.rho2))
        (fresh.1 * (fresh.2.1 + fresh.2.2)) a3b3 := by
  simp [zeroTransform, zeroBaseTransform, randomTranscript, randomZeroOutputMap,
    zeroPairMap, anchorRatioMap, ratio, u2, Function.comp_apply]

/-- A fixed random Leaky-RLWE context followed by fresh product-noise addition is exactly
uniform. -/
theorem fixedRandomZeroTransform_evalDist_eq_uniform {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (chi nu : ProbComp R) (anchor : Rˣ) (noise : Noise R) (b0 : R)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0) :
    evalDist (($ᵗ (R × R)) >>= fun a3b3 ↦
        productNoiseSampler chi nu >>= fun fresh ↦
          pure (zeroTransform fresh (randomTranscript anchor noise b0 a3b3))) =
      evalDist (uniformSampler (R := R)) := by
  let Uniform := uniformSampler (R := R)
  calc
    _ = evalDist (productNoiseSampler chi nu >>= fun fresh ↦
        ($ᵗ (R × R)) >>= fun a3b3 ↦
          pure (zeroTransform fresh (randomTranscript anchor noise b0 a3b3))) :=
      evalDist_bind_bind_swap ($ᵗ (R × R)) (productNoiseSampler chi nu) _
    _ = evalDist (productNoiseSampler chi nu >>= fun _fresh ↦ Uniform) := by
      refine evalDist_bind_congr' (productNoiseSampler chi nu) fun fresh ↦ ?_
      apply evalDist_ext
      intro output
      simpa [zeroTransform_randomTranscript, Uniform, uniformSampler, monad_norm] using
        (probOutput_bind_bijective_uniform_cross
          (α := R × R) (β := R × R)
          (randomZeroOutputMap anchor
            (b0 + (noise.1.e2 - noise.2.e0 + noise.1.rho2))
            (fresh.1 * (fresh.2.1 + fresh.2.2)))
          (randomZeroOutputMap_bijective anchor
            (b0 + (noise.1.e2 - noise.2.e0 + noise.1.rho2))
            (fresh.1 * (fresh.2.1 + fresh.2.2)))
          (fun pair ↦ pure pair) output)
    _ = evalDist Uniform :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (productNoiseSampler chi nu) hProductNoise _

/-- Complete random-view transport for the zero-message reduction. -/
theorem transformedRandomLeaky_evalDist_eq_zeroUniform {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0) :
    evalDist (randomLeakySampler anchorSampler auxiliarySecretSampler chi nu >>=
        fun transcript ↦ productNoiseSampler chi nu >>= fun fresh ↦
          pure (zeroTransform fresh transcript)) =
      evalDist (uniformSampler (R := R)) := by
  let Uniform := uniformSampler (R := R)
  calc
    evalDist (randomLeakySampler anchorSampler auxiliarySecretSampler chi nu >>=
        fun transcript ↦ productNoiseSampler chi nu >>= fun fresh ↦
          pure (zeroTransform fresh transcript)) =
      evalDist (anchorSampler >>= fun anchor ↦
        auxiliarySecretSampler >>= fun _auxiliarySecret ↦
          noiseSampler chi nu >>= fun noise ↦
            ($ᵗ R) >>= fun b0 ↦ Uniform) := by
      simp only [randomLeakySampler, bind_assoc, pure_bind]
      refine evalDist_bind_congr' anchorSampler fun anchor ↦ ?_
      refine evalDist_bind_congr' auxiliarySecretSampler fun _auxiliarySecret ↦ ?_
      refine evalDist_bind_congr' (noiseSampler chi nu) fun noise ↦ ?_
      refine evalDist_bind_congr' ($ᵗ R) fun b0 ↦ ?_
      exact fixedRandomZeroTransform_evalDist_eq_uniform
        chi nu anchor noise b0 hProductNoise
    _ = evalDist (anchorSampler >>= fun _anchor ↦
        auxiliarySecretSampler >>= fun _auxiliarySecret ↦
          noiseSampler chi nu >>= fun _noise ↦ Uniform) := by
      refine evalDist_bind_congr' anchorSampler fun _anchor ↦ ?_
      refine evalDist_bind_congr' auxiliarySecretSampler fun _auxiliarySecret ↦ ?_
      refine evalDist_bind_congr' (noiseSampler chi nu) fun _noise ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _
    _ = evalDist (anchorSampler >>= fun _anchor ↦
        auxiliarySecretSampler >>= fun _auxiliarySecret ↦ Uniform) := by
      refine evalDist_bind_congr' anchorSampler fun _anchor ↦ ?_
      refine evalDist_bind_congr' auxiliarySecretSampler fun _auxiliarySecret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (noiseSampler chi nu) hNoise _
    _ = evalDist (anchorSampler >>= fun _anchor ↦ Uniform) := by
      refine evalDist_bind_congr' anchorSampler fun _anchor ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        auxiliarySecretSampler hAuxiliarySecret _
    _ = evalDist Uniform :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        anchorSampler hAnchor _

/-- Probabilistic zero-message reduction; its added product-noise component is independent of the
source Leaky-RLWE view. -/
def zeroReduction {R : Type} [Ring R]
    (chi nu : ProbComp R) (distinguisher : Distinguisher R) : LeakyDistinguisher R :=
  fun transcript ↦ do
    let fresh ← productNoiseSampler chi nu
    distinguisher (zeroTransform fresh transcript)

/-- Exact equality of the zero real game and the reduced Leaky-RLWE real game. -/
theorem zeroReduction_realGame_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0) :
    evalDist (leakyRealGame anchorSampler auxiliarySecretSampler chi nu
        (zeroReduction chi nu distinguisher)) =
      evalDist (zeroGame chi nu distinguisher) := by
  unfold leakyRealGame zeroReduction zeroGame
  simpa only [bind_assoc, pure_bind] using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (transformedRealLeaky_evalDist_eq_zero
        anchorSampler auxiliarySecretSampler chi nu
        hAnchor hAuxiliarySecret hProductNoise)
      distinguisher)

/-- Exact equality of the zero uniform game and the reduced Leaky-RLWE random game. -/
theorem zeroReduction_randomGame_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0) :
    evalDist (leakyRandomGame anchorSampler auxiliarySecretSampler chi nu
        (zeroReduction chi nu distinguisher)) =
      evalDist (uniformGame distinguisher) := by
  unfold leakyRandomGame zeroReduction uniformGame
  simpa only [bind_assoc, pure_bind] using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (transformedRandomLeaky_evalDist_eq_zeroUniform
        anchorSampler auxiliarySecretSampler chi nu
        hAnchor hAuxiliarySecret hNoise hProductNoise)
      distinguisher)

/-- **Exact zero-message reduction.** -/
theorem zeroAdvantage_eq_leaky {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0) :
    zeroAdvantage chi nu distinguisher =
      leakyAdvantage anchorSampler auxiliarySecretSampler chi nu
        (zeroReduction chi nu distinguisher) := by
  unfold zeroAdvantage leakyAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (zeroReduction_realGame_evalDist anchorSampler auxiliarySecretSampler chi nu
        distinguisher hAnchor hAuxiliarySecret hProductNoise) true,
    evalDist_ext_iff.mp
      (zeroReduction_randomGame_evalDist anchorSampler auxiliarySecretSampler chi nu
        distinguisher hAnchor hAuxiliarySecret hNoise hProductNoise) true]

/-- Full four-sample form of the exact zero-message reduction. -/
theorem zeroAdvantage_eq_fullLeaky {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0) :
    zeroAdvantage chi nu distinguisher =
      fullLeakyAdvantage anchorSampler auxiliarySecretSampler chi nu
        (fullProjectionReduction (zeroReduction chi nu distinguisher)) := by
  rw [zeroAdvantage_eq_leaky anchorSampler auxiliarySecretSampler chi nu distinguisher
      hAnchor hAuxiliarySecret hNoise hProductNoise,
    leakyAdvantage_eq_fullProjection]

/-! ### KDM composition and hardness interfaces -/

/-- The quadratic real-versus-zero advantage is bounded by the two pseudorandomness hops. -/
theorem kdmAdvantage_le_square_add_zero {R : Type}
    [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) (distinguisher : Distinguisher R) :
    kdmAdvantage chi nu distinguisher ≤
      squareAdvantage chi nu distinguisher + zeroAdvantage chi nu distinguisher := by
  have h := ProbComp.boolDistAdvantage_triangle
    (squareGame chi nu distinguisher)
    (uniformGame distinguisher)
    (zeroGame chi nu distinguisher)
  unfold kdmAdvantage squareAdvantage zeroAdvantage
  rw [show (uniformGame distinguisher).boolDistAdvantage
      (zeroGame chi nu distinguisher) =
      (zeroGame chi nu distinguisher).boolDistAdvantage
        (uniformGame distinguisher) by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]] at h
  exact h

/-- **Finite two-component quadratic KDM theorem.**  The candidate KDM advantage is bounded by
two projected error-only Leaky-RLWE advantages, with no statistical or hybrid loss beyond their
sum. -/
theorem kdmAdvantage_le_two_leaky {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0) :
    kdmAdvantage chi nu distinguisher ≤
      leakyAdvantage anchorSampler auxiliarySecretSampler chi nu
          (squareReduction distinguisher) +
        leakyAdvantage anchorSampler auxiliarySecretSampler chi nu
          (zeroReduction chi nu distinguisher) := by
  calc
    kdmAdvantage chi nu distinguisher ≤
        squareAdvantage chi nu distinguisher + zeroAdvantage chi nu distinguisher :=
      kdmAdvantage_le_square_add_zero chi nu distinguisher
    _ = _ := by
      rw [squareAdvantage_eq_leaky anchorSampler auxiliarySecretSampler chi nu distinguisher
          hAnchor hAuxiliarySecret hNoise,
        zeroAdvantage_eq_leaky anchorSampler auxiliarySecretSampler chi nu distinguisher
          hAnchor hAuxiliarySecret hNoise hProductNoise]

/-- Full-view form of the finite KDM theorem.  These are the four-sample Leaky-RLWE advantages
to which the error-only case of Lai--Swarnakar--Woo Theorem 3 applies. -/
theorem kdmAdvantage_le_two_fullLeaky {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0) :
    kdmAdvantage chi nu distinguisher ≤
      fullLeakyAdvantage anchorSampler auxiliarySecretSampler chi nu
          (fullProjectionReduction (squareReduction distinguisher)) +
        fullLeakyAdvantage anchorSampler auxiliarySecretSampler chi nu
          (fullProjectionReduction (zeroReduction chi nu distinguisher)) := by
  simpa only [leakyAdvantage_eq_fullProjection] using
    kdmAdvantage_le_two_leaky anchorSampler auxiliarySecretSampler chi nu distinguisher
      hAnchor hAuxiliarySecret hNoise hProductNoise

/-- Concrete hardness of the projected error-only Leaky-RLWE problem. -/
def LeakyHardAgainst {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (allowed : LeakyDistinguisher R → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    leakyAdvantage anchorSampler auxiliarySecretSampler chi nu distinguisher ≤ bound

/-- Concrete hardness of the complete four-sample error-only Leaky-RLWE problem. -/
def FullLeakyHardAgainst {R : Type} [CommRing R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (allowed : FullLeakyDistinguisher R → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    fullLeakyAdvantage anchorSampler auxiliarySecretSampler chi nu distinguisher ≤ bound

/-- Concrete hardness of the target quadratic real-versus-zero KDM problem. -/
def KDMHardAgainst {R : Type} [CommRing R] [SampleableType R]
    (chi nu : ProbComp R) (allowed : Distinguisher R → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher → kdmAdvantage chi nu distinguisher ≤ bound

/-- Projected Leaky-RLWE hardness for both reductions implies quadratic KDM hardness. -/
theorem kdmHardAgainst_of_leaky {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (kdmAllowed : Distinguisher R → Prop) (leakyAllowed : LeakyDistinguisher R → Prop)
    (bound : ℝ)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0)
    (hSquareClosed : ∀ distinguisher, kdmAllowed distinguisher →
      leakyAllowed (squareReduction distinguisher))
    (hZeroClosed : ∀ distinguisher, kdmAllowed distinguisher →
      leakyAllowed (zeroReduction chi nu distinguisher))
    (hLeaky : LeakyHardAgainst anchorSampler auxiliarySecretSampler chi nu
      leakyAllowed bound) :
    KDMHardAgainst chi nu kdmAllowed (bound + bound) := by
  intro distinguisher hAllowed
  exact (kdmAdvantage_le_two_leaky anchorSampler auxiliarySecretSampler chi nu
    distinguisher hAnchor hAuxiliarySecret hNoise hProductNoise).trans
      (add_le_add
        (hLeaky _ (hSquareClosed distinguisher hAllowed))
        (hLeaky _ (hZeroClosed distinguisher hAllowed)))

/-- Full four-sample Leaky-RLWE hardness implies quadratic KDM hardness. -/
theorem kdmHardAgainst_of_fullLeaky {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (kdmAllowed : Distinguisher R → Prop)
    (fullLeakyAllowed : FullLeakyDistinguisher R → Prop) (bound : ℝ)
    (hAnchor : Pr[⊥ | anchorSampler] = 0)
    (hAuxiliarySecret : Pr[⊥ | auxiliarySecretSampler] = 0)
    (hNoise : Pr[⊥ | noiseSampler chi nu] = 0)
    (hProductNoise : Pr[⊥ | productNoiseSampler chi nu] = 0)
    (hSquareClosed : ∀ distinguisher, kdmAllowed distinguisher →
      fullLeakyAllowed (fullProjectionReduction (squareReduction distinguisher)))
    (hZeroClosed : ∀ distinguisher, kdmAllowed distinguisher →
      fullLeakyAllowed
        (fullProjectionReduction (zeroReduction chi nu distinguisher)))
    (hLeaky : FullLeakyHardAgainst anchorSampler auxiliarySecretSampler chi nu
      fullLeakyAllowed bound) :
    KDMHardAgainst chi nu kdmAllowed (bound + bound) := by
  intro distinguisher hAllowed
  exact (kdmAdvantage_le_two_fullLeaky anchorSampler auxiliarySecretSampler chi nu
    distinguisher hAnchor hAuxiliarySecret hNoise hProductNoise).trans
      (add_le_add
        (hLeaky _ (hSquareClosed distinguisher hAllowed))
        (hLeaky _ (hZeroClosed distinguisher hAllowed)))

/-- Losslessness of the primitive samplers implies losslessness of the product-noise block. -/
theorem productNoiseSampler_probFailure_eq_zero {R : Type}
    (chi nu : ProbComp R) :
    Pr[⊥ | productNoiseSampler chi nu] = 0 := by
  simp [productNoiseSampler]

/-- Losslessness of the primitive samplers implies losslessness of the complete noise block. -/
theorem noiseSampler_probFailure_eq_zero {R : Type}
    (chi nu : ProbComp R) :
    Pr[⊥ | noiseSampler chi nu] = 0 := by
  simp [noiseSampler, secretNoiseSampler, errorNoiseSampler, productNoiseSampler]

/-- ProbComp samplers are lossless, so the full-view KDM bound needs no separate sampler
side conditions. -/
theorem kdmAdvantage_le_two_fullLeaky_probComp {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (distinguisher : Distinguisher R) :
    kdmAdvantage chi nu distinguisher ≤
      fullLeakyAdvantage anchorSampler auxiliarySecretSampler chi nu
          (fullProjectionReduction (squareReduction distinguisher)) +
        fullLeakyAdvantage anchorSampler auxiliarySecretSampler chi nu
          (fullProjectionReduction (zeroReduction chi nu distinguisher)) :=
  kdmAdvantage_le_two_fullLeaky anchorSampler auxiliarySecretSampler chi nu distinguisher
    (by simp) (by simp) (noiseSampler_probFailure_eq_zero chi nu)
    (productNoiseSampler_probFailure_eq_zero chi nu)

/-- Lossless-ProbComp convenience form of `kdmHardAgainst_of_fullLeaky`. -/
theorem kdmHardAgainst_of_fullLeaky_probComp {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (anchorSampler : ProbComp Rˣ) (auxiliarySecretSampler chi nu : ProbComp R)
    (kdmAllowed : Distinguisher R → Prop)
    (fullLeakyAllowed : FullLeakyDistinguisher R → Prop) (bound : ℝ)
    (hSquareClosed : ∀ distinguisher, kdmAllowed distinguisher →
      fullLeakyAllowed (fullProjectionReduction (squareReduction distinguisher)))
    (hZeroClosed : ∀ distinguisher, kdmAllowed distinguisher →
      fullLeakyAllowed
        (fullProjectionReduction (zeroReduction chi nu distinguisher)))
    (hLeaky : FullLeakyHardAgainst anchorSampler auxiliarySecretSampler chi nu
      fullLeakyAllowed bound) :
    KDMHardAgainst chi nu kdmAllowed (bound + bound) :=
  kdmHardAgainst_of_fullLeaky anchorSampler auxiliarySecretSampler chi nu
    kdmAllowed fullLeakyAllowed bound (by simp) (by simp)
    (noiseSampler_probFailure_eq_zero chi nu)
    (productNoiseSampler_probFailure_eq_zero chi nu)
    hSquareClosed hZeroClosed hLeaky

/-! ## Deterministic noise growth -/

/-- The target secret has the sum bound `B+Bρ` for any subadditive size function. -/
theorem targetSecret_size_le {R : Type} [Add R]
    (size : R → ℕ) (hadd : ∀ x y, size (x + y) ≤ size x + size y)
    (noise : SecretNoise R) (B Brho : ℕ)
    (he2 : size noise.e2 ≤ B) (hrho2 : size noise.rho2 ≤ Brho) :
    size (targetSecret noise) ≤ B + Brho := by
  exact (hadd _ _).trans (Nat.add_le_add he2 hrho2)

/-- The product-error bound `B + γ B (B+Bρ)`. -/
theorem targetError_size_le {R : Type} [Ring R]
    (size : R → ℕ)
    (hadd : ∀ x y, size (x + y) ≤ size x + size y)
    (hsub : ∀ x y, size (x - y) ≤ size x + size y)
    (noise : ErrorNoise R) (B Brho gamma : ℕ)
    (hmul : ∀ x y, size (x * y) ≤ gamma * (size x * size y))
    (he3 : size noise.e3 ≤ B) (he0 : size noise.e0 ≤ B)
    (he1 : size noise.e1 ≤ B) (hrho1 : size noise.rho1 ≤ Brho) :
    size (targetError noise) ≤ B + gamma * B * (B + Brho) := by
  have hsum : size (noise.e1 + noise.rho1) ≤ B + Brho :=
    (hadd _ _).trans (Nat.add_le_add he1 hrho1)
  have hproduct :
      size noise.e0 * size (noise.e1 + noise.rho1) ≤ B * (B + Brho) :=
    Nat.mul_le_mul he0 hsum
  have hscaled :
      gamma * (size noise.e0 * size (noise.e1 + noise.rho1)) ≤
        gamma * (B * (B + Brho)) :=
    Nat.mul_le_mul_left gamma hproduct
  unfold targetError
  calc
    size (noise.e3 - noise.e0 * (noise.e1 + noise.rho1)) ≤
        size noise.e3 + size (noise.e0 * (noise.e1 + noise.rho1)) := hsub _ _
    _ ≤ B + gamma * (size noise.e0 * size (noise.e1 + noise.rho1)) :=
      Nat.add_le_add he3 (hmul _ _)
    _ ≤ B + gamma * (B * (B + Brho)) := by
      exact Nat.add_le_add_left hscaled B
    _ = B + gamma * B * (B + Brho) := by simp [Nat.mul_assoc]

/-! ## Weighted extension -/

/-- Weighted intermediate mask `c-g(u₀+u₁)`. -/
def weightedIntermediateA {R : Type} [Ring R] (weight : R)
    (transcript : SourceTranscript R) : R :=
  ratio transcript - weight * (u0 transcript + u1 transcript)

/-- Weighted intermediate body `d-g u₀u₁`. -/
def weightedIntermediateB {R : Type} [Ring R] (weight : R)
    (transcript : SourceTranscript R) : R :=
  transcript.b3 - weight * u0 transcript * u1 transcript

/-- The direct weighted secant step scales the product error by the public weight. -/
theorem weighted_intermediate_phase_real {R : Type} [CommRing R]
    (weight : R) (anchor : Rˣ) (a3 auxiliarySecret : R) (noise : Noise R) :
    weightedIntermediateB weight (realTranscript anchor a3 auxiliarySecret noise) =
      weightedIntermediateA weight (realTranscript anchor a3 auxiliarySecret noise) *
          anchorProduct anchor auxiliarySecret +
        weight * anchorProduct anchor auxiliarySecret ^ 2 +
        (noise.2.e3 - weight * noise.2.e0 * (noise.2.e1 + noise.2.rho1)) := by
  have hratio := ratio_mul_anchorProduct anchor a3 auxiliarySecret
  have hratio' :
      a3 * anchorProduct anchor auxiliarySecret * ((anchor⁻¹ : Rˣ) : R) =
        a3 * auxiliarySecret := by
    calc
      _ = (a3 * ((anchor⁻¹ : Rˣ) : R)) *
          anchorProduct anchor auxiliarySecret := by ring
      _ = _ := hratio
  simp only [weightedIntermediateA, weightedIntermediateB, realTranscript, ratio, u0, u1]
  ring_nf
  rw [hratio']

end

end FormalProof4FHE.RLWE.LeakyCircular
