/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.LeakyCircular

/-!
# The source-aligned two-hint Leaky-RLWE compiler

This file formalizes the finite-game part of `sketch/leakycircular.md` without identifying it
with the older four-sample error-leakage construction in `RLWE.LeakyCircular`.

For every row `i`, the source view contains

`cᵢ = -aᵢ*s + eᵢ`, `rᵢ = αᵢ*s + fᵢ`, and `tᵢ = βᵢ*s + hᵢ`.

When `αᵢ*βᵢ = -gᵢ`, the public compiler emits the stock two-component row

`(Aᵢ, -Aᵢ*s + gᵢ*s^2 + eᵢ + fᵢ*hᵢ)`.

The real compiler branch and its target key law are proved equal in distribution.  The random
compiler branch is proved exactly uniform jointly over every row while retaining the hints as
side information.  An independent auxiliary-noise ordinary-RLWE branch gives the zero key law.
Their triangle inequality is the exact finite-game theorem requested by the sketch.

The analytic theorem producing a `LWE.Leaky.SimulationSound` certificate from discrete-Gaussian
covariance, smoothing, and leakage-norm hypotheses remains an explicit external premise, exactly
as documented in `FormalProof4FHE.LWE.Leaky`; this file introduces no axiom for it.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.LeakyCircular.TwoHint

noncomputable section

variable (R : Type) (rows : ℕ)

/-- A vector containing one ring element for every evaluation-key row. -/
abbrev RowVector := Fin rows → R

/-- A stock two-component evaluation key, represented as its mask and body vectors. -/
abbrev EvaluationKey := RowVector R rows × RowVector R rows

/-- The shared secret and ordinary RLWE errors. -/
structure BaseNoise where
  secret : R
  error : RowVector R rows

/-- The two independent noisy-hint error vectors. -/
structure HintNoise where
  left : RowVector R rows
  right : RowVector R rows

/-- Complete hidden context of the two-hint experiment. -/
abbrev HiddenNoise := BaseNoise R rows × HintNoise R rows

/-- The complete Leaky-RLWE source view. -/
structure SourceView where
  mask : RowVector R rows
  body : RowVector R rows
  leftHint : RowVector R rows
  rightHint : RowVector R rows

/-- The ordinary-RLWE source view used in the zero branch. -/
structure OrdinaryView where
  mask : RowVector R rows
  body : RowVector R rows

variable {R rows}

/-- Product-noise evaluation-key error `eᵢ + fᵢ*hᵢ`. -/
def outputError [Mul R] [Add R] (noise : HiddenNoise R rows) : RowVector R rows :=
  fun i ↦ noise.1.error i + noise.2.left i * noise.2.right i

/-- The prescribed real quadratic evaluation key for a fixed uniform mask. -/
def realKey [CommRing R] (gadget : RowVector R rows) (noise : HiddenNoise R rows)
    (mask : RowVector R rows) : EvaluationKey R rows :=
  (mask, fun i ↦
    -mask i * noise.1.secret + gadget i * noise.1.secret ^ 2 + outputError noise i)

/-- The zero-message evaluation key with the same shared secret and product-noise law. -/
def zeroKey [Ring R] (noise : HiddenNoise R rows)
    (mask : RowVector R rows) : EvaluationKey R rows :=
  (mask, fun i ↦ -mask i * noise.1.secret + outputError noise i)

/-- Assemble the real secret-leakage source view. -/
def realSourceView [Ring R] (alpha beta : RowVector R rows)
    (noise : HiddenNoise R rows) (mask : RowVector R rows) : SourceView R rows where
  mask := mask
  body := fun i ↦ -mask i * noise.1.secret + noise.1.error i
  leftHint := fun i ↦ alpha i * noise.1.secret + noise.2.left i
  rightHint := fun i ↦ beta i * noise.1.secret + noise.2.right i

/-- Assemble the random Leaky-RLWE source view; the hints retain their real law. -/
def randomSourceView [Ring R] (alpha beta : RowVector R rows)
    (noise : HiddenNoise R rows) (uniform : EvaluationKey R rows) : SourceView R rows where
  mask := uniform.1
  body := uniform.2
  leftHint := fun i ↦ alpha i * noise.1.secret + noise.2.left i
  rightHint := fun i ↦ beta i * noise.1.secret + noise.2.right i

/-- Apply the public two-hint compiler to every row. -/
def compile [Ring R] (alpha beta : RowVector R rows)
    (view : SourceView R rows) : EvaluationKey R rows :=
  (fun i ↦ view.mask i - alpha i * view.rightHint i - beta i * view.leftHint i,
   fun i ↦ view.body i + view.leftHint i * view.rightHint i)

/-- The real-source mask is translated to the target evaluation-key mask. -/
def realMaskMap [Ring R] (alpha beta : RowVector R rows)
    (noise : HiddenNoise R rows) : RowVector R rows → RowVector R rows :=
  fun mask i ↦ mask i -
    alpha i * (beta i * noise.1.secret + noise.2.right i) -
    beta i * (alpha i * noise.1.secret + noise.2.left i)

/-- Explicit inverse of `realMaskMap`. -/
def realMaskMapInv [Ring R] (alpha beta : RowVector R rows)
    (noise : HiddenNoise R rows) : RowVector R rows → RowVector R rows :=
  fun mask i ↦ mask i +
    (alpha i * (beta i * noise.1.secret + noise.2.right i) +
     beta i * (alpha i * noise.1.secret + noise.2.left i))

@[simp]
theorem realMaskMapInv_realMaskMap [CommRing R]
    (alpha beta : RowVector R rows) (noise : HiddenNoise R rows)
    (mask : RowVector R rows) :
    realMaskMapInv alpha beta noise (realMaskMap alpha beta noise mask) = mask := by
  funext i
  simp [realMaskMapInv, realMaskMap]

@[simp]
theorem realMaskMap_realMaskMapInv [CommRing R]
    (alpha beta : RowVector R rows) (noise : HiddenNoise R rows)
    (mask : RowVector R rows) :
    realMaskMap alpha beta noise (realMaskMapInv alpha beta noise mask) = mask := by
  funext i
  simp [realMaskMapInv, realMaskMap]
  ring

theorem realMaskMap_bijective [CommRing R]
    (alpha beta : RowVector R rows) (noise : HiddenNoise R rows) :
    Function.Bijective (realMaskMap alpha beta noise) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨realMaskMapInv alpha beta noise,
      realMaskMapInv_realMaskMap alpha beta noise,
      realMaskMap_realMaskMapInv alpha beta noise⟩

/-- Multi-row version of the fixed-gadget compiler identity. -/
theorem compile_realSourceView [CommRing R]
    (alpha beta gadget : RowVector R rows) (noise : HiddenNoise R rows)
    (mask : RowVector R rows) (hfactor : ∀ i, alpha i * beta i = -gadget i) :
    compile alpha beta (realSourceView alpha beta noise mask) =
      realKey gadget noise (realMaskMap alpha beta noise mask) := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [compile, realSourceView, realKey, realMaskMap, outputError]
    have hg : gadget i = -(alpha i * beta i) := by
      refine (eq_neg_iff_add_eq_zero).2 ?_
      simp [hfactor i]
    rw [hg]
    ring

/-- In a fixed hidden context, the real compiler output has exactly the target key law. -/
theorem fixedRealCompiler_evalDist [CommRing R] [Finite R] [DecidableEq R]
    [SampleableType R] (alpha beta gadget : RowVector R rows)
    (noise : HiddenNoise R rows) (hfactor : ∀ i, alpha i * beta i = -gadget i) :
    evalDist (($ᵗ (RowVector R rows)) >>= fun mask ↦
        pure (compile alpha beta (realSourceView alpha beta noise mask))) =
      evalDist (($ᵗ (RowVector R rows)) >>= fun mask ↦
        pure (realKey gadget noise mask)) := by
  apply evalDist_ext
  intro output
  simpa only [compile_realSourceView alpha beta gadget noise _ hfactor] using
    (probOutput_bind_bijective_uniform_cross
      (α := RowVector R rows) (β := RowVector R rows)
      (realMaskMap alpha beta noise) (realMaskMap_bijective alpha beta noise)
      (fun mask ↦ pure (realKey gadget noise mask)) output)

/-- On a fixed hidden context, compilation of a random source view is a translation. -/
def randomCompilerMap [Ring R] (alpha beta : RowVector R rows)
    (noise : HiddenNoise R rows) : EvaluationKey R rows → EvaluationKey R rows :=
  fun uniform ↦ compile alpha beta (randomSourceView alpha beta noise uniform)

/-- Explicit inverse of the random-branch compiler translation. -/
def randomCompilerMapInv [Ring R] (alpha beta : RowVector R rows)
    (noise : HiddenNoise R rows) : EvaluationKey R rows → EvaluationKey R rows :=
  fun output ↦
    (fun i ↦ output.1 i +
      (alpha i * (beta i * noise.1.secret + noise.2.right i) +
       beta i * (alpha i * noise.1.secret + noise.2.left i)),
     fun i ↦ output.2 i -
      (alpha i * noise.1.secret + noise.2.left i) *
      (beta i * noise.1.secret + noise.2.right i))

@[simp]
theorem randomCompilerMapInv_randomCompilerMap [CommRing R]
    (alpha beta : RowVector R rows) (noise : HiddenNoise R rows)
    (uniform : EvaluationKey R rows) :
    randomCompilerMapInv alpha beta noise (randomCompilerMap alpha beta noise uniform) = uniform := by
  apply Prod.ext <;> funext i <;>
    simp [randomCompilerMapInv, randomCompilerMap, compile, randomSourceView]

@[simp]
theorem randomCompilerMap_randomCompilerMapInv [CommRing R]
    (alpha beta : RowVector R rows) (noise : HiddenNoise R rows)
    (output : EvaluationKey R rows) :
    randomCompilerMap alpha beta noise (randomCompilerMapInv alpha beta noise output) = output := by
  apply Prod.ext <;> funext i
  all_goals simp [randomCompilerMapInv, randomCompilerMap, compile, randomSourceView] <;> ring

theorem randomCompilerMap_bijective [CommRing R]
    (alpha beta : RowVector R rows) (noise : HiddenNoise R rows) :
    Function.Bijective (randomCompilerMap alpha beta noise) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨randomCompilerMapInv alpha beta noise,
      randomCompilerMapInv_randomCompilerMap alpha beta noise,
      randomCompilerMap_randomCompilerMapInv alpha beta noise⟩

/-- Exact joint uniformity of every compiled row in the random Leaky-RLWE branch. -/
theorem fixedRandomCompiler_evalDist [CommRing R] [Finite R] [DecidableEq R]
    [SampleableType R] (alpha beta : RowVector R rows) (noise : HiddenNoise R rows) :
    evalDist (($ᵗ (EvaluationKey R rows)) >>= fun uniform ↦
        pure (compile alpha beta (randomSourceView alpha beta noise uniform))) =
      evalDist ($ᵗ (EvaluationKey R rows)) := by
  apply evalDist_ext
  intro output
  simpa [randomCompilerMap, monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := EvaluationKey R rows) (β := EvaluationKey R rows)
      (randomCompilerMap alpha beta noise) (randomCompilerMap_bijective alpha beta noise)
      (fun key ↦ pure key) output)

/-! ## Joint multi-row games -/

/-- Independently combine the base RLWE noise with the two noisy-hint errors. -/
def hiddenNoiseSampler (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) : ProbComp (HiddenNoise R rows) := do
  let base ← baseSampler
  let hint ← hintSampler
  return (base, hint)

/-- Canonical shared-secret/independent-row-error sampler used by RLWE. -/
def iidBaseNoiseSampler (secretSampler errorSampler : ProbComp R) :
    ProbComp (BaseNoise R rows) := do
  let secret ← secretSampler
  let error ← ProbComp.sampleIID rows errorSampler
  return ⟨secret, error⟩

/-- Canonical sampler making both hint-error families mutually independent and IID across rows. -/
def iidHintNoiseSampler (leftSampler rightSampler : ProbComp R) :
    ProbComp (HintNoise R rows) := do
  let left ← ProbComp.sampleIID rows leftSampler
  let right ← ProbComp.sampleIID rows rightSampler
  return ⟨left, right⟩

/-- The always-available factorization `αᵢ = 1`, `βᵢ = -gᵢ`. -/
theorem one_negGadget_factorization [Ring R] (gadget : RowVector R rows) :
    ∀ i, (1 : RowVector R rows) i * (-gadget) i = -gadget i := by
  intro i
  simp

/-- Target distribution `K₁` from the sketch. -/
def realKeySampler [CommRing R] [SampleableType R]
    (gadget : RowVector R rows) (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) : ProbComp (EvaluationKey R rows) := do
  let noise ← hiddenNoiseSampler baseSampler hintSampler
  let mask ← $ᵗ (RowVector R rows)
  return realKey gadget noise mask

/-- Target distribution `K₀` from the sketch. -/
def zeroKeySampler [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) : ProbComp (EvaluationKey R rows) := do
  let noise ← hiddenNoiseSampler baseSampler hintSampler
  let mask ← $ᵗ (RowVector R rows)
  return zeroKey noise mask

/-- Real secret-leaky RLWE source distribution, before the public compiler is applied. -/
def leakyRealSourceSampler [Ring R] [SampleableType R]
    (alpha beta : RowVector R rows) (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) : ProbComp (SourceView R rows) := do
  let noise ← hiddenNoiseSampler baseSampler hintSampler
  let mask ← $ᵗ (RowVector R rows)
  return realSourceView alpha beta noise mask

/-- Random secret-leaky RLWE source distribution.  Only the RLWE bodies are replaced by uniform;
the shared secret and noisy hints retain their real joint law. -/
def leakyRandomSourceSampler [Ring R] [SampleableType R]
    (alpha beta : RowVector R rows) (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) : ProbComp (SourceView R rows) := do
  let noise ← hiddenNoiseSampler baseSampler hintSampler
  let uniform ← $ᵗ (EvaluationKey R rows)
  return randomSourceView alpha beta noise uniform

/-- Exact transport of the complete real Leaky-RLWE source to `K₁`. -/
theorem compiledLeakyReal_evalDist [CommRing R] [Finite R] [DecidableEq R]
    [SampleableType R] (alpha beta gadget : RowVector R rows)
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows))
    (hfactor : ∀ i, alpha i * beta i = -gadget i) :
    evalDist (leakyRealSourceSampler alpha beta baseSampler hintSampler >>= fun view ↦
        pure (compile alpha beta view)) =
      evalDist (realKeySampler gadget baseSampler hintSampler) := by
  simp only [leakyRealSourceSampler, realKeySampler, bind_assoc, pure_bind]
  refine evalDist_bind_congr' (hiddenNoiseSampler baseSampler hintSampler) fun noise ↦ ?_
  exact fixedRealCompiler_evalDist alpha beta gadget noise hfactor

/-- Exact joint uniformity of the compiled random Leaky-RLWE source. -/
theorem compiledLeakyRandom_evalDist [CommRing R] [Finite R] [DecidableEq R]
    [SampleableType R] (alpha beta : RowVector R rows)
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows)) :
    evalDist (leakyRandomSourceSampler alpha beta baseSampler hintSampler >>= fun view ↦
        pure (compile alpha beta view)) =
      evalDist ($ᵗ (EvaluationKey R rows)) := by
  simp only [leakyRandomSourceSampler, bind_assoc, pure_bind]
  calc
    _ = evalDist (hiddenNoiseSampler baseSampler hintSampler >>= fun _noise ↦
        $ᵗ (EvaluationKey R rows)) := by
      refine evalDist_bind_congr' (hiddenNoiseSampler baseSampler hintSampler) fun noise ↦ ?_
      exact fixedRandomCompiler_evalDist alpha beta noise
    _ = evalDist ($ᵗ (EvaluationKey R rows)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (hiddenNoiseSampler baseSampler hintSampler) (by simp [hiddenNoiseSampler]) _

/-! ### Independence of the output mask and product error -/

/-- The joint mask/error law obtained from the real compiler. -/
def compiledMaskErrorSampler [CommRing R] [SampleableType R]
    (alpha beta : RowVector R rows) (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) :
    ProbComp (RowVector R rows × RowVector R rows) := do
  let noise ← hiddenNoiseSampler baseSampler hintSampler
  let sourceMask ← $ᵗ (RowVector R rows)
  return (realMaskMap alpha beta noise sourceMask, outputError noise)

/-- The explicitly independent mask/error law: the product error is sampled first and an
independent uniform mask is then attached. -/
def independentMaskErrorSampler [Mul R] [Add R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) :
    ProbComp (RowVector R rows × RowVector R rows) := do
  let noise ← hiddenNoiseSampler baseSampler hintSampler
  let mask ← $ᵗ (RowVector R rows)
  return (mask, outputError noise)

/-- The real compiler's public mask is jointly independent of the entire product-error vector. -/
theorem compiledMaskError_evalDist_eq_independent [CommRing R] [Finite R] [DecidableEq R]
    [SampleableType R] (alpha beta : RowVector R rows)
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows)) :
    evalDist (compiledMaskErrorSampler alpha beta baseSampler hintSampler) =
      evalDist (independentMaskErrorSampler baseSampler hintSampler) := by
  simp only [compiledMaskErrorSampler, independentMaskErrorSampler]
  refine evalDist_bind_congr' (hiddenNoiseSampler baseSampler hintSampler) fun noise ↦ ?_
  apply evalDist_ext
  intro output
  simpa only using
    (probOutput_bind_bijective_uniform_cross
      (α := RowVector R rows) (β := RowVector R rows)
      (realMaskMap alpha beta noise) (realMaskMap_bijective alpha beta noise)
      (fun mask ↦ pure (mask, outputError noise)) output)

/-! ## Ordinary-RLWE zero branch -/

/-- Assemble a real ordinary-RLWE batch with a shared secret. -/
def ordinaryRealView [Ring R] (base : BaseNoise R rows)
    (mask : RowVector R rows) : OrdinaryView R rows where
  mask := mask
  body := fun i ↦ -mask i * base.secret + base.error i

/-- Add the independently sampled product noise to an ordinary-RLWE batch. -/
def addProductNoise [Ring R] (hint : HintNoise R rows)
    (view : OrdinaryView R rows) : EvaluationKey R rows :=
  (view.mask, fun i ↦ view.body i + hint.left i * hint.right i)

theorem addProductNoise_real_eq_zeroKey [Ring R]
    (base : BaseNoise R rows) (hint : HintNoise R rows) (mask : RowVector R rows) :
    addProductNoise hint (ordinaryRealView base mask) = zeroKey (base, hint) mask := by
  apply Prod.ext
  · rfl
  · funext i
    simp [addProductNoise, ordinaryRealView, zeroKey, outputError]
    ac_rfl

/-- Real ordinary-RLWE zero-branch reduction, with independent auxiliary product noise. -/
def ordinaryRealReducedSampler [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) : ProbComp (EvaluationKey R rows) := do
  let base ← baseSampler
  let hint ← hintSampler
  let mask ← $ᵗ (RowVector R rows)
  return addProductNoise hint (ordinaryRealView base mask)

/-- Random ordinary-RLWE zero-branch reduction. -/
def ordinaryRandomReducedSampler [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) : ProbComp (EvaluationKey R rows) := do
  let _base ← baseSampler
  let hint ← hintSampler
  let uniform ← $ᵗ (EvaluationKey R rows)
  return addProductNoise hint ⟨uniform.1, uniform.2⟩

/-- The underlying ordinary-RLWE real source, before auxiliary product noise is sampled. -/
def ordinaryRealSourceSampler [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows)) : ProbComp (OrdinaryView R rows) := do
  let base ← baseSampler
  let mask ← $ᵗ (RowVector R rows)
  return ordinaryRealView base mask

/-- The underlying ordinary-RLWE random source.  Sampling the hidden base context keeps the two
branches aligned but reveals none of it. -/
def ordinaryRandomSourceSampler [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows)) : ProbComp (OrdinaryView R rows) := do
  let _base ← baseSampler
  let uniform ← $ᵗ (EvaluationKey R rows)
  return ⟨uniform.1, uniform.2⟩

abbrev OrdinaryDistinguisher (R : Type) (rows : ℕ) := OrdinaryView R rows → ProbComp Bool

/-- The actual reduction given an ordinary-RLWE challenge: sample `f,h` independently, add
`f*h` to every challenge body, and invoke the evaluation-key distinguisher. -/
def ordinaryReduction [Ring R] (hintSampler : ProbComp (HintNoise R rows))
    (distinguisher : EvaluationKey R rows → ProbComp Bool) : OrdinaryDistinguisher R rows :=
  fun view ↦ do
    let hint ← hintSampler
    distinguisher (addProductNoise hint view)

/-- Ordinary-RLWE advantage of an arbitrary source distinguisher. -/
noncomputable def ordinarySourceAdvantage [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows))
    (distinguisher : OrdinaryDistinguisher R rows) : ℝ :=
  (ordinaryRealSourceSampler baseSampler >>= distinguisher).boolDistAdvantage
    (ordinaryRandomSourceSampler baseSampler >>= distinguisher)

/-- The real ordinary-RLWE reduction is definitionally the target zero-key law. -/
theorem ordinaryRealReduced_evalDist_eq_zeroKey [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows)) :
    evalDist (ordinaryRealReducedSampler baseSampler hintSampler) =
      evalDist (zeroKeySampler baseSampler hintSampler) := by
  simp [ordinaryRealReducedSampler, zeroKeySampler, hiddenNoiseSampler, bind_assoc,
    addProductNoise_real_eq_zeroKey]

/-- Fixed-context body translation in the ordinary random branch. -/
def productNoiseMap [Ring R] (hint : HintNoise R rows) :
    EvaluationKey R rows → EvaluationKey R rows :=
  fun key ↦ (key.1, fun i ↦ key.2 i + hint.left i * hint.right i)

/-- Explicit inverse of `productNoiseMap`. -/
def productNoiseMapInv [Ring R] (hint : HintNoise R rows) :
    EvaluationKey R rows → EvaluationKey R rows :=
  fun key ↦ (key.1, fun i ↦ key.2 i - hint.left i * hint.right i)

theorem productNoiseMap_bijective [Ring R] (hint : HintNoise R rows) :
    Function.Bijective (productNoiseMap hint) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨productNoiseMapInv hint, ?_, ?_⟩
  · intro key
    apply Prod.ext <;> funext i <;> simp [productNoiseMapInv, productNoiseMap]
  · intro key
    apply Prod.ext <;> funext i <;> simp [productNoiseMapInv, productNoiseMap]

theorem fixedProductNoiseUniform_evalDist [Ring R] [Finite R] [DecidableEq R]
    [SampleableType R] (hint : HintNoise R rows) :
    evalDist (($ᵗ (EvaluationKey R rows)) >>= fun uniform ↦
        pure (addProductNoise hint ⟨uniform.1, uniform.2⟩)) =
      evalDist ($ᵗ (EvaluationKey R rows)) := by
  apply evalDist_ext
  intro output
  simpa [productNoiseMap, addProductNoise, monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := EvaluationKey R rows) (β := EvaluationKey R rows)
      (productNoiseMap hint) (productNoiseMap_bijective hint)
      (fun key ↦ pure key) output)

/-- Adding the independent product error preserves the complete uniform key law. -/
theorem ordinaryRandomReduced_evalDist_eq_uniform [Ring R] [Finite R] [DecidableEq R]
    [SampleableType R] (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) :
    evalDist (ordinaryRandomReducedSampler baseSampler hintSampler) =
      evalDist ($ᵗ (EvaluationKey R rows)) := by
  simp only [ordinaryRandomReducedSampler]
  calc
    _ = evalDist (baseSampler >>= fun _base ↦
        hintSampler >>= fun _hint ↦ $ᵗ (EvaluationKey R rows)) := by
      refine evalDist_bind_congr' baseSampler fun _base ↦ ?_
      refine evalDist_bind_congr' hintSampler fun hint ↦ ?_
      exact fixedProductNoiseUniform_evalDist hint
    _ = evalDist (hintSampler >>= fun _hint ↦ $ᵗ (EvaluationKey R rows)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        baseSampler (by simp) _
    _ = evalDist ($ᵗ (EvaluationKey R rows)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        hintSampler (by simp) _

/-! ## Exact security decomposition -/

abbrev Distinguisher (R : Type) (rows : ℕ) := EvaluationKey R rows → ProbComp Bool

def realKeyGame [CommRing R] [SampleableType R] (gadget : RowVector R rows)
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows))
    (distinguisher : Distinguisher R rows) : ProbComp Bool :=
  realKeySampler gadget baseSampler hintSampler >>= distinguisher

def zeroKeyGame [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows))
    (distinguisher : Distinguisher R rows) : ProbComp Bool :=
  zeroKeySampler baseSampler hintSampler >>= distinguisher

def uniformKeyGame [SampleableType R] (distinguisher : Distinguisher R rows) : ProbComp Bool :=
  ($ᵗ (EvaluationKey R rows)) >>= distinguisher

noncomputable def productNoiseKDMAdvantage [CommRing R] [SampleableType R]
    (gadget : RowVector R rows) (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) (distinguisher : Distinguisher R rows) : ℝ :=
  (realKeyGame gadget baseSampler hintSampler distinguisher).boolDistAdvantage
    (zeroKeyGame baseSampler hintSampler distinguisher)

noncomputable def twoHintLeakyAdvantage [CommRing R] [SampleableType R]
    (alpha beta : RowVector R rows) (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) (distinguisher : Distinguisher R rows) : ℝ :=
  ((leakyRealSourceSampler alpha beta baseSampler hintSampler >>= fun view ↦
      distinguisher (compile alpha beta view))).boolDistAdvantage
    (leakyRandomSourceSampler alpha beta baseSampler hintSampler >>= fun view ↦
      distinguisher (compile alpha beta view))

noncomputable def ordinaryRLWEAdvantage [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows))
    (distinguisher : Distinguisher R rows) : ℝ :=
  (ordinaryRealReducedSampler baseSampler hintSampler >>= distinguisher).boolDistAdvantage
    (ordinaryRandomReducedSampler baseSampler hintSampler >>= distinguisher)

/-- The named ordinary term is exactly an ordinary-RLWE source advantage for the explicit
auxiliary-noise reduction; it is not an additional hardness assumption. -/
theorem ordinaryRLWEAdvantage_eq_source [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows))
    (distinguisher : Distinguisher R rows) :
    ordinaryRLWEAdvantage baseSampler hintSampler distinguisher =
      ordinarySourceAdvantage baseSampler (ordinaryReduction hintSampler distinguisher) := by
  have hreal :
      evalDist (ordinaryRealReducedSampler baseSampler hintSampler >>= distinguisher) =
        evalDist (ordinaryRealSourceSampler baseSampler >>=
          ordinaryReduction hintSampler distinguisher) := by
    simp only [ordinaryRealReducedSampler, ordinaryRealSourceSampler, ordinaryReduction,
      bind_assoc, pure_bind]
    refine evalDist_bind_congr' baseSampler fun base ↦ ?_
    exact evalDist_bind_bind_swap hintSampler ($ᵗ (RowVector R rows))
      (fun hint mask ↦ distinguisher (addProductNoise hint (ordinaryRealView base mask)))
  have hrandom :
      evalDist (ordinaryRandomReducedSampler baseSampler hintSampler >>= distinguisher) =
        evalDist (ordinaryRandomSourceSampler baseSampler >>=
          ordinaryReduction hintSampler distinguisher) := by
    simp only [ordinaryRandomReducedSampler, ordinaryRandomSourceSampler, ordinaryReduction,
      bind_assoc, pure_bind]
    refine evalDist_bind_congr' baseSampler fun _base ↦ ?_
    exact evalDist_bind_bind_swap hintSampler ($ᵗ (EvaluationKey R rows))
      (fun hint uniform ↦
        distinguisher (addProductNoise hint ⟨uniform.1, uniform.2⟩))
  unfold ordinaryRLWEAdvantage ordinarySourceAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp hreal true, evalDist_ext_iff.mp hrandom true]

theorem realVsUniform_eq_twoHintLeaky [CommRing R] [Finite R] [DecidableEq R]
    [SampleableType R] (alpha beta gadget : RowVector R rows)
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows))
    (distinguisher : Distinguisher R rows) (hfactor : ∀ i, alpha i * beta i = -gadget i) :
    (realKeyGame gadget baseSampler hintSampler distinguisher).boolDistAdvantage
        (uniformKeyGame distinguisher) =
      twoHintLeakyAdvantage alpha beta baseSampler hintSampler distinguisher := by
  have hreal :
      evalDist (leakyRealSourceSampler alpha beta baseSampler hintSampler >>= fun view ↦
          distinguisher (compile alpha beta view)) =
        evalDist (realKeySampler gadget baseSampler hintSampler >>= distinguisher) := by
    simpa only [bind_assoc, pure_bind] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (compiledLeakyReal_evalDist alpha beta gadget baseSampler hintSampler hfactor)
        distinguisher)
  have hrandom :
      evalDist (leakyRandomSourceSampler alpha beta baseSampler hintSampler >>= fun view ↦
          distinguisher (compile alpha beta view)) =
        evalDist (($ᵗ (EvaluationKey R rows)) >>= distinguisher) := by
    simpa only [bind_assoc, pure_bind] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (compiledLeakyRandom_evalDist alpha beta baseSampler hintSampler) distinguisher)
  unfold realKeyGame uniformKeyGame twoHintLeakyAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp hreal.symm true, evalDist_ext_iff.mp hrandom.symm true]

theorem zeroVsUniform_eq_ordinaryRLWE [Ring R] [Finite R] [DecidableEq R]
    [SampleableType R] (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows)) (distinguisher : Distinguisher R rows) :
    (zeroKeyGame baseSampler hintSampler distinguisher).boolDistAdvantage
        (uniformKeyGame distinguisher) =
      ordinaryRLWEAdvantage baseSampler hintSampler distinguisher := by
  unfold zeroKeyGame uniformKeyGame ordinaryRLWEAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (ordinaryRealReduced_evalDist_eq_zeroKey baseSampler hintSampler).symm distinguisher) true,
    evalDist_ext_iff.mp
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (ordinaryRandomReduced_evalDist_eq_uniform baseSampler hintSampler) distinguisher) true]

/-- The exact multi-row theorem from the sketch: product-noise quadratic KDM is bounded by one
secret-leaky RLWE hop and one ordinary-RLWE hop. -/
theorem productNoiseKDMAdvantage_le [CommRing R] [Finite R] [DecidableEq R]
    [SampleableType R] (alpha beta gadget : RowVector R rows)
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows))
    (distinguisher : Distinguisher R rows) (hfactor : ∀ i, alpha i * beta i = -gadget i) :
    productNoiseKDMAdvantage gadget baseSampler hintSampler distinguisher ≤
      twoHintLeakyAdvantage alpha beta baseSampler hintSampler distinguisher +
        ordinaryRLWEAdvantage baseSampler hintSampler distinguisher := by
  have htriangle := ProbComp.boolDistAdvantage_triangle
    (realKeyGame gadget baseSampler hintSampler distinguisher)
    (uniformKeyGame distinguisher)
    (zeroKeyGame baseSampler hintSampler distinguisher)
  unfold productNoiseKDMAdvantage
  rw [show (uniformKeyGame distinguisher).boolDistAdvantage
      (zeroKeyGame baseSampler hintSampler distinguisher) =
      (zeroKeyGame baseSampler hintSampler distinguisher).boolDistAdvantage
        (uniformKeyGame distinguisher) by
      unfold ProbComp.boolDistAdvantage
      rw [abs_sub_comm]] at htriangle
  simpa only [realVsUniform_eq_twoHintLeaky alpha beta gadget baseSampler hintSampler
      distinguisher hfactor,
    zeroVsUniform_eq_ordinaryRLWE baseSampler hintSampler distinguisher] using htriangle

/-! ## Hardness interfaces -/

def TwoHintLeakyHardAgainst [CommRing R] [SampleableType R]
    (alpha beta : RowVector R rows) (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows))
    (allowed : Distinguisher R rows → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    twoHintLeakyAdvantage alpha beta baseSampler hintSampler distinguisher ≤ bound

def OrdinaryRLWEHardAgainst [Ring R] [SampleableType R]
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows))
    (allowed : Distinguisher R rows → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    ordinaryRLWEAdvantage baseSampler hintSampler distinguisher ≤ bound

def ProductNoiseKDMHardAgainst [CommRing R] [SampleableType R]
    (gadget : RowVector R rows) (baseSampler : ProbComp (BaseNoise R rows))
    (hintSampler : ProbComp (HintNoise R rows))
    (allowed : Distinguisher R rows → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    productNoiseKDMAdvantage gadget baseSampler hintSampler distinguisher ≤ bound

/-- Secret-leaky RLWE hardness and ordinary RLWE hardness imply security of the exact stock-format
product-noise quadratic evaluation key. -/
theorem productNoiseKDMHardAgainst_of_leaky_and_ordinary
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (alpha beta gadget : RowVector R rows)
    (baseSampler : ProbComp (BaseNoise R rows)) (hintSampler : ProbComp (HintNoise R rows))
    (allowed : Distinguisher R rows → Prop) (leakyBound ordinaryBound : ℝ)
    (hfactor : ∀ i, alpha i * beta i = -gadget i)
    (hLeaky : TwoHintLeakyHardAgainst alpha beta baseSampler hintSampler allowed leakyBound)
    (hOrdinary : OrdinaryRLWEHardAgainst baseSampler hintSampler allowed ordinaryBound) :
    ProductNoiseKDMHardAgainst gadget baseSampler hintSampler allowed
      (leakyBound + ordinaryBound) := by
  intro distinguisher hAllowed
  exact (productNoiseKDMAdvantage_le alpha beta gadget baseSampler hintSampler
    distinguisher hfactor).trans
      (add_le_add (hLeaky distinguisher hAllowed) (hOrdinary distinguisher hAllowed))

/-! ## Deterministic correctness bounds -/

/-- The single-row product-noise bound `E + μ*F²`. -/
theorem outputError_size_le [Mul R] [Add R]
    (size : R → ℕ) (hadd : ∀ x y, size (x + y) ≤ size x + size y)
    (E F μ : ℕ)
    (hmul : ∀ x y, size (x * y) ≤ μ * (size x * size y))
    (noise : HiddenNoise R rows) (i : Fin rows)
    (he : size (noise.1.error i) ≤ E)
    (hf : size (noise.2.left i) ≤ F)
    (hh : size (noise.2.right i) ≤ F) :
    size (outputError noise i) ≤ E + μ * (F * F) := by
  calc
    size (outputError noise i) ≤
        size (noise.1.error i) + size (noise.2.left i * noise.2.right i) := hadd _ _
    _ ≤ E + μ * (size (noise.2.left i) * size (noise.2.right i)) :=
      Nat.add_le_add he (hmul _ _)
    _ ≤ E + μ * (F * F) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left μ (Nat.mul_le_mul hf hh)) E

/-- Relinearization error obtained by multiplying every row error by its gadget digit. -/
def relinearizationError [Semiring R] (digits : RowVector R rows)
    (noise : HiddenNoise R rows) : R :=
  ∑ i, digits i * outputError noise i

/-- Deterministic multi-row correctness bound.  Written with natural-number sizes, it is the
formal counterpart of `μ_R * ℓ * D * (E + μ_R*F²)` in the sketch. -/
theorem relinearizationError_size_le [Semiring R]
    (size : R → ℕ)
    (hsum : ∀ values : Fin rows → R,
      size (∑ i, values i) ≤ ∑ i, size (values i))
    (hadd : ∀ x y, size (x + y) ≤ size x + size y)
    (D E F μ : ℕ)
    (hmul : ∀ x y, size (x * y) ≤ μ * (size x * size y))
    (digits : RowVector R rows) (noise : HiddenNoise R rows)
    (hdigits : ∀ i, size (digits i) ≤ D)
    (he : ∀ i, size (noise.1.error i) ≤ E)
    (hf : ∀ i, size (noise.2.left i) ≤ F)
    (hh : ∀ i, size (noise.2.right i) ≤ F) :
    size (relinearizationError digits noise) ≤
      rows * (μ * (D * (E + μ * (F * F)))) := by
  calc
    size (relinearizationError digits noise) ≤
        ∑ i, size (digits i * outputError noise i) := hsum _
    _ ≤ ∑ _i : Fin rows, μ * (D * (E + μ * (F * F))) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (hmul (digits i) (outputError noise i)).trans
        (Nat.mul_le_mul_left μ (Nat.mul_le_mul (hdigits i)
          (outputError_size_le size hadd E F μ hmul noise i (he i) (hf i) (hh i))))
    _ = rows * (μ * (D * (E + μ * (F * F)))) := by simp

end

end FormalProof4FHE.RLWE.LeakyCircular.TwoHint
