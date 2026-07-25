/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputSearchToDecision
import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.SharedRandomness.Reduction

/-!
# Conditional Quadratic KDM Security from Correlated HNF-RLWE

This module formalizes the finite-game content of `rlwe_quadratic_kdm_security.tex`.
For public gadget weights `g j` with proof-only factorizations

`sum r, alpha j r * beta j r = g j`,

the public compiler maps the correlated HNF source view

`b0 = X - S`, `d j = c j * X + sum r, F j r * G j r + H j`

with leakage `L = alpha*S+F`, `M = beta*S+G` exactly to the evaluation-key rows

`(A j, A j * S + g j * S^2 + H j)`.

The random source branch is mapped exactly to the uniform distribution: conditioned on the
anchor and leakage, the compiler is an explicitly inverted permutation of all coefficient/body
pairs.  No independence between the latent variables is needed for these algebraic and finite-game
statements; independence, boundedness, and residual entropy are obligations of a concrete source
search-hardness theorem.

The split-field section proves the correct-candidate identity and the decisive wrong-candidate
bijection from the TeX proof.  The global hybrid selection, amplification, CRT automorphisms, and
complexity accounting are represented by the library's checked `SearchToDecision.Reduction`
certificate.  Consequently the final security theorem is deliberately conditional: it combines
such a certificate, a concrete search-hardness bound, and a zero-message RLWE bound.  It does not
claim a reduction from ordinary decisional RLWE alone.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.QuadraticKDM

noncomputable section

/-! ## Fixed gadget and correlated latent variables -/

/-- Public gadget weights together with a proof-only factorization.  A varying number of factors
per row can be represented by a common finite type and zero padding. -/
structure Gadget (R Row Factor : Type) [CommRing R] [Fintype Factor] where
  weight : Row → R
  alpha : Row → Factor → R
  beta : Row → Factor → R
  factorization : ∀ row, ∑ factor, alpha row factor * beta row factor = weight row

/-- The target secret, two latent factor families, and the desired final errors. -/
structure Latent (R Row Factor : Type) where
  secret : R
  firstError : Row → Factor → R
  secondError : Row → Factor → R
  finalError : Row → R

/-- Public correlated leakage `(L,M)`. -/
abbrev Leakage (R Row Factor : Type) :=
  (Row → Factor → R) × (Row → Factor → R)

/-- A correlated HNF source transcript.  The leakage is part of the challenge rather than a
separately sampled auxiliary value, which preserves its correlation with the terminal errors. -/
structure SourceTranscript (R Row Factor : Type) where
  anchor : R
  coefficient : Row → R
  body : Row → R
  leakage : Leakage R Row Factor

/-- A joint family of two-component evaluation-key rows, stored as mask and body vectors. -/
abbrev TargetTranscript (R Row : Type) := (Row → R) × (Row → R)

/-- Public leakage generated from the latent variables. -/
def publicLeakage {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor) :
    Leakage R Row Factor :=
  (fun row factor ↦
      gadget.alpha row factor * latent.secret + latent.firstError row factor,
    fun row factor ↦
      gadget.beta row factor * latent.secret + latent.secondError row factor)

/-- The terminal correlated HNF error `Z_j = sum F_jr G_jr + H_j`. -/
def terminalError {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (latent : Latent R Row Factor) (row : Row) : R :=
  ∑ factor, latent.firstError row factor * latent.secondError row factor
    + latent.finalError row

/-- The mixed term used only in the proof of the compiler identity. -/
def mixedCorrection {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor) (row : Row) : R :=
  ∑ factor, (
    gadget.alpha row factor * latent.secondError row factor +
      gadget.beta row factor * latent.firstError row factor)

/-! ## The fixed-gadget compiler -/

/-- Public linear correction `K_j = sum (alpha*M + beta*L)`. -/
def linearCorrection {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (leakage : Leakage R Row Factor) (row : Row) : R :=
  ∑ factor, (
    gadget.alpha row factor * leakage.2 row factor +
      gadget.beta row factor * leakage.1 row factor)

/-- Public product correction `P_j = sum L*M`. -/
def productCorrection {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (leakage : Leakage R Row Factor) (row : Row) : R :=
  ∑ factor, leakage.1 row factor * leakage.2 row factor

/-- The deterministic public compiler. -/
def compile {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (source : SourceTranscript R Row Factor) :
    TargetTranscript R Row :=
  (fun row ↦ source.coefficient row - linearCorrection gadget source.leakage row,
    fun row ↦ source.body row - source.coefficient row * source.anchor -
      productCorrection source.leakage row)

/-- Expansion `K_j = 2*g_j*S + R_j`. -/
theorem linearCorrection_publicLeakage
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor) (row : Row) :
    linearCorrection gadget (publicLeakage gadget latent) row =
      2 * gadget.weight row * latent.secret + mixedCorrection gadget latent row := by
  unfold linearCorrection publicLeakage mixedCorrection
  calc
    (∑ factor, (
        gadget.alpha row factor *
            (gadget.beta row factor * latent.secret + latent.secondError row factor) +
          gadget.beta row factor *
            (gadget.alpha row factor * latent.secret + latent.firstError row factor))) =
      ∑ factor, (
        (2 * (gadget.alpha row factor * gadget.beta row factor) * latent.secret +
          (gadget.alpha row factor * latent.secondError row factor +
            gadget.beta row factor * latent.firstError row factor))) := by
        apply Finset.sum_congr rfl
        intro factor _
        ring
    _ = 2 * (∑ factor,
          gadget.alpha row factor * gadget.beta row factor) * latent.secret +
        ∑ factor,
          (gadget.alpha row factor * latent.secondError row factor +
            gadget.beta row factor * latent.firstError row factor) := by
      rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = 2 * gadget.weight row * latent.secret +
        ∑ factor,
          (gadget.alpha row factor * latent.secondError row factor +
            gadget.beta row factor * latent.firstError row factor) := by
      rw [gadget.factorization row]

/-- Expansion `P_j = g_j*S² + R_j*S + sum F_jr*G_jr`. -/
theorem productCorrection_publicLeakage
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor) (row : Row) :
    productCorrection (publicLeakage gadget latent) row =
      gadget.weight row * latent.secret ^ 2 +
        mixedCorrection gadget latent row * latent.secret +
        ∑ factor, latent.firstError row factor * latent.secondError row factor := by
  unfold productCorrection publicLeakage mixedCorrection
  calc
    (∑ factor,
        (gadget.alpha row factor * latent.secret + latent.firstError row factor) *
          (gadget.beta row factor * latent.secret + latent.secondError row factor)) =
      ∑ factor,
        ((gadget.alpha row factor * gadget.beta row factor) * latent.secret ^ 2 +
          (gadget.alpha row factor * latent.secondError row factor +
            gadget.beta row factor * latent.firstError row factor) * latent.secret +
          latent.firstError row factor * latent.secondError row factor) := by
        apply Finset.sum_congr rfl
        intro factor _
        ring
    _ = (∑ factor,
          gadget.alpha row factor * gadget.beta row factor) * latent.secret ^ 2 +
        (∑ factor,
          (gadget.alpha row factor * latent.secondError row factor +
            gadget.beta row factor * latent.firstError row factor)) * latent.secret +
        ∑ factor, latent.firstError row factor * latent.secondError row factor := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = gadget.weight row * latent.secret ^ 2 +
        (∑ factor,
          (gadget.alpha row factor * latent.secondError row factor +
            gadget.beta row factor * latent.firstError row factor)) * latent.secret +
        ∑ factor, latent.firstError row factor * latent.secondError row factor := by
      rw [gadget.factorization row]

/-- Assemble a real correlated HNF source transcript for fixed randomness. -/
def realSourceTranscript {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (auxiliarySecret : R)
    (latent : Latent R Row Factor) (coefficient : Row → R) :
    SourceTranscript R Row Factor where
  anchor := auxiliarySecret - latent.secret
  coefficient := coefficient
  body := fun row ↦ coefficient row * auxiliarySecret + terminalError latent row
  leakage := publicLeakage gadget latent

/-- Assemble the target fixed-gadget KDM rows for fixed randomness. -/
def kdmTranscript {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor)
    (mask : Row → R) : TargetTranscript R Row :=
  (mask, fun row ↦ mask row * latent.secret +
    gadget.weight row * latent.secret ^ 2 + latent.finalError row)

/-- Assemble the target zero-message rows for fixed randomness. -/
def zeroTranscript {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (_gadget : Gadget R Row Factor) (latent : Latent R Row Factor)
    (mask : Row → R) : TargetTranscript R Row :=
  (mask, fun row ↦ mask row * latent.secret + latent.finalError row)

/-- The exact real-branch compiler identity.  In particular, the final error is `H_j`, with no
factor depending on the gadget weight. -/
theorem compile_realSourceTranscript
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (auxiliarySecret : R)
    (latent : Latent R Row Factor) (coefficient : Row → R) :
    compile gadget (realSourceTranscript gadget auxiliarySecret latent coefficient) =
      kdmTranscript gadget latent
        (fun row ↦ coefficient row -
          linearCorrection gadget (publicLeakage gadget latent) row) := by
  apply Prod.ext
  · rfl
  · funext row
    change
      coefficient row * auxiliarySecret + terminalError latent row -
        coefficient row * (auxiliarySecret - latent.secret) -
          productCorrection (publicLeakage gadget latent) row =
        (coefficient row - linearCorrection gadget (publicLeakage gadget latent) row) *
            latent.secret + gadget.weight row * latent.secret ^ 2 +
          latent.finalError row
    rw [linearCorrection_publicLeakage, productCorrection_publicLeakage]
    simp only [terminalError]
    ring

/-! ## Exact source and target probability games -/

/-- Translate all source coefficients to the target masks. -/
def coefficientShift {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor)
    (coefficient : Row → R) : Row → R :=
  fun row ↦ coefficient row -
    linearCorrection gadget (publicLeakage gadget latent) row

/-- The coefficient translation is a permutation. -/
theorem coefficientShift_bijective
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor) :
    Function.Bijective (coefficientShift gadget latent) := by
  let inverse : (Row → R) → (Row → R) := fun mask row ↦
    mask row + linearCorrection gadget (publicLeakage gadget latent) row
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro coefficient
    funext row
    simp [inverse, coefficientShift]
  · intro mask
    funext row
    simp [inverse, coefficientShift]

/-- The real correlated HNF source sampler for a fixed auxiliary secret `X`. -/
def sourceRealSampler
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [SampleableType (Row → R)]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (auxiliarySecret : R) : ProbComp (SourceTranscript R Row Factor) := do
  let latent ← latentSampler
  let coefficient ← $ᵗ (Row → R)
  return realSourceTranscript gadget auxiliarySecret latent coefficient

/-- The random source sampler retains genuine leakage but replaces the anchor and all bodies by
independent uniforms.  The coefficient/body pair is sampled jointly uniformly for convenient
finite-game transport. -/
def sourceRandomSampler
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [SampleableType R] [SampleableType (TargetTranscript R Row)]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor)) :
    ProbComp (SourceTranscript R Row Factor) := do
  let latent ← latentSampler
  let anchor ← $ᵗ R
  let pair ← $ᵗ (TargetTranscript R Row)
  return ⟨anchor, pair.1, pair.2, publicLeakage gadget latent⟩

/-- Auxiliary-input decision problem for the source secret `X`.  Correlated leakage lives in the
challenge; the separate auxiliary type is `Unit`. -/
def sourceProblem
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [SampleableType R] [SampleableType (Row → R)]
    [SampleableType (TargetTranscript R Row)]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor)) :
    FormalProof4FHE.LWE.AuxiliaryInput.Problem
      R (SourceTranscript R Row Factor) Unit where
  sampleSecret := $ᵗ R
  sampleReal := sourceRealSampler gadget latentSampler
  sampleZero := sourceRealSampler gadget latentSampler
  sampleUniform := sourceRandomSampler gadget latentSampler
  sampleAuxiliary := fun _ ↦ pure ()

/-- Canonical target KDM sampler with independent uniform masks. -/
def kdmSampler
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [SampleableType (Row → R)]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor)) :
    ProbComp (TargetTranscript R Row) := do
  let latent ← latentSampler
  let mask ← $ᵗ (Row → R)
  return kdmTranscript gadget latent mask

/-- Canonical target zero-message sampler with the same secret and final-error law. -/
def zeroSampler
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [SampleableType (Row → R)]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor)) :
    ProbComp (TargetTranscript R Row) := do
  let latent ← latentSampler
  let mask ← $ᵗ (Row → R)
  return zeroTranscript gadget latent mask

/-- Canonical uniform endpoint for all target rows. -/
def uniformSampler {R Row : Type} [SampleableType (TargetTranscript R Row)] :
    ProbComp (TargetTranscript R Row) :=
  $ᵗ (TargetTranscript R Row)

/-- Boolean distinguisher for a joint target transcript. -/
abbrev Distinguisher (R Row : Type) := TargetTranscript R Row → ProbComp Bool

/-- Quadratic KDM-versus-zero advantage. -/
noncomputable def kdmAdvantage
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [SampleableType (Row → R)]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (distinguisher : Distinguisher R Row) : ℝ :=
  (kdmSampler gadget latentSampler >>= distinguisher).boolDistAdvantage
    (zeroSampler gadget latentSampler >>= distinguisher)

/-- Quadratic KDM-versus-uniform advantage. -/
noncomputable def kdmUniformAdvantage
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [SampleableType (Row → R)] [SampleableType (TargetTranscript R Row)]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (distinguisher : Distinguisher R Row) : ℝ :=
  (kdmSampler gadget latentSampler >>= distinguisher).boolDistAdvantage
    (uniformSampler >>= distinguisher)

/-- Zero-message-versus-uniform advantage. -/
noncomputable def zeroUniformAdvantage
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [SampleableType (Row → R)] [SampleableType (TargetTranscript R Row)]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (distinguisher : Distinguisher R Row) : ℝ :=
  (zeroSampler gadget latentSampler >>= distinguisher).boolDistAdvantage
    (uniformSampler >>= distinguisher)

/-- Reduction from a target distinguisher to the public source-decision problem. -/
def sourceReduction
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (distinguisher : Distinguisher R Row) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (SourceTranscript R Row Factor) Unit :=
  fun source _ ↦ distinguisher (compile gadget source)

/-! ### Probability transport for the compiler -/

/-- For fixed latent variables and auxiliary secret, translating the uniform source coefficients
gives the canonical target KDM distribution. -/
theorem fixedRealCompile_evalDist_eq_kdm
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (gadget : Gadget R Row Factor) (auxiliarySecret : R)
    (latent : Latent R Row Factor) :
    evalDist (($ᵗ (Row → R)) >>= fun coefficient ↦
        pure (compile gadget
          (realSourceTranscript gadget auxiliarySecret latent coefficient))) =
      evalDist (($ᵗ (Row → R)) >>= fun mask ↦
        pure (kdmTranscript gadget latent mask)) := by
  have hShift :
      evalDist (coefficientShift gadget latent <$> ($ᵗ (Row → R))) =
        evalDist ($ᵗ (Row → R)) :=
    evalDist_map_bijective_uniform_cross
      (α := Row → R) (β := Row → R)
      (coefficientShift gadget latent) (coefficientShift_bijective gadget latent)
  calc
    evalDist (($ᵗ (Row → R)) >>= fun coefficient ↦
        pure (compile gadget
          (realSourceTranscript gadget auxiliarySecret latent coefficient))) =
      evalDist ((coefficientShift gadget latent <$> ($ᵗ (Row → R))) >>= fun mask ↦
        pure (kdmTranscript gadget latent mask)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine evalDist_bind_congr' ($ᵗ (Row → R)) fun coefficient ↦ ?_
      rw [compile_realSourceTranscript]
      rfl
    _ = evalDist (($ᵗ (Row → R)) >>= fun mask ↦
        pure (kdmTranscript gadget latent mask)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hShift _

/-- Compiling the complete real source sampler gives the canonical target KDM sampler. -/
theorem compiledSourceReal_evalDist_eq_kdm
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (auxiliarySecret : R) :
    evalDist (sourceRealSampler gadget latentSampler auxiliarySecret >>= fun source ↦
        pure (compile gadget source)) =
      evalDist (kdmSampler gadget latentSampler) := by
  unfold sourceRealSampler kdmSampler
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' latentSampler fun latent ↦ ?_
  exact fixedRealCompile_evalDist_eq_kdm gadget auxiliarySecret latent

/-- The fixed random-branch affine map on all coefficient/body vectors. -/
def randomCompilerMap
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (anchor : R) (leakage : Leakage R Row Factor)
    (pair : TargetTranscript R Row) : TargetTranscript R Row :=
  compile gadget ⟨anchor, pair.1, pair.2, leakage⟩

/-- Explicit inverse of the random-branch compiler map. -/
def randomCompilerMapInv
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (anchor : R) (leakage : Leakage R Row Factor)
    (output : TargetTranscript R Row) : TargetTranscript R Row :=
  (fun row ↦ output.1 row + linearCorrection gadget leakage row,
    fun row ↦ output.2 row +
      (output.1 row + linearCorrection gadget leakage row) * anchor +
        productCorrection leakage row)

@[simp]
theorem randomCompilerMapInv_randomCompilerMap
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (anchor : R) (leakage : Leakage R Row Factor)
    (pair : TargetTranscript R Row) :
    randomCompilerMapInv gadget anchor leakage
        (randomCompilerMap gadget anchor leakage pair) = pair := by
  apply Prod.ext
  · funext row
    simp [randomCompilerMapInv, randomCompilerMap, compile]
  · funext row
    simp [randomCompilerMapInv, randomCompilerMap, compile]
    ring

@[simp]
theorem randomCompilerMap_randomCompilerMapInv
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (anchor : R) (leakage : Leakage R Row Factor)
    (output : TargetTranscript R Row) :
    randomCompilerMap gadget anchor leakage
        (randomCompilerMapInv gadget anchor leakage output) = output := by
  apply Prod.ext
  · funext row
    simp [randomCompilerMapInv, randomCompilerMap, compile]
  · funext row
    simp [randomCompilerMapInv, randomCompilerMap, compile]
    ring

/-- Conditioned on anchor and leakage, the random-branch compiler is a permutation. -/
theorem randomCompilerMap_bijective
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (anchor : R) (leakage : Leakage R Row Factor) :
    Function.Bijective (randomCompilerMap gadget anchor leakage) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨randomCompilerMapInv gadget anchor leakage,
      randomCompilerMapInv_randomCompilerMap gadget anchor leakage,
      randomCompilerMap_randomCompilerMapInv gadget anchor leakage⟩

/-- For every fixed random-branch context, the compiler preserves joint uniformity. -/
theorem fixedRandomCompile_evalDist_eq_uniform
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (gadget : Gadget R Row Factor) (anchor : R) (leakage : Leakage R Row Factor) :
    evalDist (($ᵗ (TargetTranscript R Row)) >>= fun pair ↦
        pure (compile gadget ⟨anchor, pair.1, pair.2, leakage⟩)) =
      evalDist (uniformSampler (R := R) (Row := Row)) := by
  simpa only [randomCompilerMap, uniformSampler, map_eq_bind_pure_comp,
      Function.comp_def] using
    (evalDist_map_bijective_uniform_cross
      (α := TargetTranscript R Row) (β := TargetTranscript R Row)
      (randomCompilerMap gadget anchor leakage)
      (randomCompilerMap_bijective gadget anchor leakage))

/-- Compiling the complete random source sampler gives the canonical uniform target sampler. -/
theorem compiledSourceRandom_evalDist_eq_uniform
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (hLatent : Pr[⊥ | latentSampler] = 0) :
    evalDist (sourceRandomSampler gadget latentSampler >>= fun source ↦
        pure (compile gadget source)) =
      evalDist (uniformSampler (R := R) (Row := Row)) := by
  let Uniform := uniformSampler (R := R) (Row := Row)
  calc
    evalDist (sourceRandomSampler gadget latentSampler >>= fun source ↦
        pure (compile gadget source)) =
      evalDist (latentSampler >>= fun latent ↦
        ($ᵗ R) >>= fun anchor ↦ Uniform) := by
      unfold sourceRandomSampler
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr' latentSampler fun latent ↦ ?_
      refine evalDist_bind_congr' ($ᵗ R) fun anchor ↦ ?_
      exact fixedRandomCompile_evalDist_eq_uniform
        gadget anchor (publicLeakage gadget latent)
    _ = evalDist (latentSampler >>= fun _latent ↦ Uniform) := by
      refine evalDist_bind_congr' latentSampler fun _latent ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _
    _ = evalDist Uniform :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        latentSampler hLatent _

/-- The reduced source real game is exactly the target KDM game. -/
theorem sourceReduction_realGame_evalDist
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (distinguisher : Distinguisher R Row) :
    evalDist (FormalProof4FHE.LWE.AuxiliaryInput.realGame
        (sourceProblem gadget latentSampler)
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          (sourceReduction gadget distinguisher))) =
      evalDist (kdmSampler gadget latentSampler >>= distinguisher) := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.realGame
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
    sourceProblem sourceReduction
  simp only [pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun auxiliarySecret ↦
        sourceRealSampler gadget latentSampler auxiliarySecret >>= fun source ↦
          distinguisher (compile gadget source)) =
      evalDist (($ᵗ R) >>= fun _auxiliarySecret ↦
        kdmSampler gadget latentSampler >>= distinguisher) := by
      refine evalDist_bind_congr' ($ᵗ R) fun auxiliarySecret ↦ ?_
      simpa only [bind_assoc, pure_bind] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (compiledSourceReal_evalDist_eq_kdm
            gadget latentSampler auxiliarySecret) distinguisher)
    _ = evalDist (kdmSampler gadget latentSampler >>= distinguisher) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _

/-- The reduced source random game is exactly the target uniform game. -/
theorem sourceReduction_randomGame_evalDist
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (distinguisher : Distinguisher R Row)
    (hLatent : Pr[⊥ | latentSampler] = 0) :
    evalDist (FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
        (sourceProblem gadget latentSampler)
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          (sourceReduction gadget distinguisher))) =
      evalDist (uniformSampler >>= distinguisher) := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.uniformGame
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
    sourceProblem sourceReduction
  simp only [pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun _auxiliarySecret ↦
        sourceRandomSampler gadget latentSampler >>= fun source ↦
          distinguisher (compile gadget source)) =
      evalDist (($ᵗ R) >>= fun _auxiliarySecret ↦
        uniformSampler >>= distinguisher) := by
      refine evalDist_bind_congr' ($ᵗ R) fun _auxiliarySecret ↦ ?_
      simpa only [bind_assoc, pure_bind] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (compiledSourceRandom_evalDist_eq_uniform gadget latentSampler hLatent)
          distinguisher)
    _ = evalDist (uniformSampler >>= distinguisher) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _

/-- **Exact fixed-gadget compiler.**  Target KDM-versus-uniform advantage is exactly the
corresponding public correlated-HNF source advantage. -/
theorem kdmUniformAdvantage_eq_sourceAdvantage
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (distinguisher : Distinguisher R Row)
    (hLatent : Pr[⊥ | latentSampler] = 0) :
    kdmUniformAdvantage gadget latentSampler distinguisher =
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (sourceProblem gadget latentSampler) (sourceReduction gadget distinguisher) := by
  unfold kdmUniformAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (sourceReduction_realGame_evalDist gadget latentSampler distinguisher) true,
    evalDist_ext_iff.mp
      (sourceReduction_randomGame_evalDist
        gadget latentSampler distinguisher hLatent) true]

/-- Triangle decomposition through the common uniform endpoint. -/
theorem kdmAdvantage_le_kdmUniform_add_zeroUniform
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    [SampleableType (Row → R)] [SampleableType (TargetTranscript R Row)]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (distinguisher : Distinguisher R Row) :
    kdmAdvantage gadget latentSampler distinguisher ≤
      kdmUniformAdvantage gadget latentSampler distinguisher +
        zeroUniformAdvantage gadget latentSampler distinguisher := by
  have h := ProbComp.boolDistAdvantage_triangle
    (kdmSampler gadget latentSampler >>= distinguisher)
    (uniformSampler >>= distinguisher)
    (zeroSampler gadget latentSampler >>= distinguisher)
  unfold kdmAdvantage kdmUniformAdvantage zeroUniformAdvantage
  rw [show (uniformSampler >>= distinguisher).boolDistAdvantage
      (zeroSampler gadget latentSampler >>= distinguisher) =
      (zeroSampler gadget latentSampler >>= distinguisher).boolDistAdvantage
        (uniformSampler >>= distinguisher) by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]] at h
  exact h

/-! ## One-coordinate split-field candidate test

The following definitions isolate the algebra used at one CRT coordinate.  Errors may be
arbitrarily correlated across rows; every theorem conditions on their complete value. -/

/-- One coordinate of an HNF block: anchor, public coefficients, and right-hand sides. -/
abbrev CoordinateView (K Row : Type) := K × ((Row → K) × (Row → K))

/-- A real one-coordinate HNF block with fixed error vector. -/
def coordinateReal {K Row : Type} [CommRing K]
    (secret anchorError : K) (rowError coefficient : Row → K) :
    CoordinateView K Row :=
  (secret + anchorError,
    (coefficient, fun row ↦ coefficient row * secret + rowError row))

/-- Candidate randomization from the TeX proof:
`bhat=b0-z+v`, `chat=c+rho`, `dhat=d-c*z+chat*v`. -/
def candidateTransform {K Row : Type} [CommRing K]
    (candidate freshSecret : K) (coefficientMask : Row → K)
    (source : CoordinateView K Row) : CoordinateView K Row :=
  (source.1 - candidate + freshSecret,
    (fun row ↦ source.2.1 row + coefficientMask row,
      fun row ↦ source.2.2 row - source.2.1 row * candidate +
        (source.2.1 row + coefficientMask row) * freshSecret))

/-- A correct candidate produces a real HNF block under the fresh secret, with the complete
correlated error vector unchanged. -/
theorem candidateTransform_correct
    {K Row : Type} [CommRing K]
    (secret anchorError : K) (rowError coefficient coefficientMask : Row → K)
    (freshSecret : K) :
    candidateTransform secret freshSecret coefficientMask
        (coordinateReal secret anchorError rowError coefficient) =
      coordinateReal freshSecret anchorError rowError
        (fun row ↦ coefficient row + coefficientMask row) := by
  apply Prod.ext
  · dsimp [candidateTransform, coordinateReal]
    ring
  · apply Prod.ext
    · rfl
    · funext row
      dsimp [candidateTransform, coordinateReal]
      ring

/-- Wrong-candidate normal form, with `delta = secret-candidate`. -/
theorem candidateTransform_wrong_normalForm
    {K Row : Type} [CommRing K]
    (secret candidate anchorError : K) (rowError coefficient coefficientMask : Row → K)
    (freshSecret : K) :
    candidateTransform candidate freshSecret coefficientMask
        (coordinateReal secret anchorError rowError coefficient) =
      (freshSecret + (secret - candidate) + anchorError,
        (fun row ↦ coefficient row + coefficientMask row,
          fun row ↦
            (coefficient row + coefficientMask row) *
                (freshSecret + (secret - candidate)) + rowError row -
              coefficientMask row * (secret - candidate))) := by
  apply Prod.ext
  · dsimp [candidateTransform, coordinateReal]
    ring
  · apply Prod.ext
    · rfl
    · funext row
      dsimp [candidateTransform, coordinateReal]
      ring

/-- The full wrong-candidate map.  Its inputs are the fresh secret, original public
coefficients, and coefficient masks. -/
def wrongCandidateMap {K Row : Type} [CommRing K]
    (secret candidate anchorError : K) (rowError : Row → K)
    (coins : CoordinateView K Row) : CoordinateView K Row :=
  candidateTransform candidate coins.1 coins.2.2
    (coordinateReal secret anchorError rowError coins.2.1)

/-- Explicit inverse of `wrongCandidateMap`, matching the formulas in the TeX proof. -/
def wrongCandidateMapInv {K Row : Type} [Field K]
    (secret candidate anchorError : K) (rowError : Row → K)
    (output : CoordinateView K Row) : CoordinateView K Row :=
  let delta := secret - candidate
  let shiftedSecret := output.1 - anchorError
  let coefficientMask := fun row ↦
    delta⁻¹ *
      (rowError row - (output.2.2 row - output.2.1 row * shiftedSecret))
  (shiftedSecret - delta,
    (fun row ↦ output.2.1 row - coefficientMask row, coefficientMask))

@[simp]
theorem wrongCandidateMapInv_wrongCandidateMap
    {K Row : Type} [Field K]
    (secret candidate anchorError : K) (rowError : Row → K)
    (hWrong : candidate ≠ secret) (coins : CoordinateView K Row) :
    wrongCandidateMapInv secret candidate anchorError rowError
        (wrongCandidateMap secret candidate anchorError rowError coins) = coins := by
  have hDelta : secret - candidate ≠ 0 := sub_ne_zero.mpr (Ne.symm hWrong)
  rcases coins with ⟨freshSecret, coefficient, coefficientMask⟩
  apply Prod.ext
  · dsimp [wrongCandidateMapInv, wrongCandidateMap, candidateTransform, coordinateReal]
    ring
  · apply Prod.ext
    · funext row
      dsimp [wrongCandidateMapInv, wrongCandidateMap, candidateTransform, coordinateReal]
      field_simp
      ring
    · funext row
      dsimp [wrongCandidateMapInv, wrongCandidateMap, candidateTransform, coordinateReal]
      field_simp
      ring

@[simp]
theorem wrongCandidateMap_wrongCandidateMapInv
    {K Row : Type} [Field K]
    (secret candidate anchorError : K) (rowError : Row → K)
    (hWrong : candidate ≠ secret) (output : CoordinateView K Row) :
    wrongCandidateMap secret candidate anchorError rowError
        (wrongCandidateMapInv secret candidate anchorError rowError output) = output := by
  have hDelta : secret - candidate ≠ 0 := sub_ne_zero.mpr (Ne.symm hWrong)
  rcases output with ⟨outputAnchor, outputCoefficient, outputBody⟩
  apply Prod.ext
  · dsimp [wrongCandidateMapInv, wrongCandidateMap, candidateTransform, coordinateReal]
    ring
  · apply Prod.ext
    · funext row
      dsimp [wrongCandidateMapInv, wrongCandidateMap, candidateTransform, coordinateReal]
      field_simp
      ring
    · funext row
      dsimp [wrongCandidateMapInv, wrongCandidateMap, candidateTransform, coordinateReal]
      field_simp
      ring

/-- For an incorrect candidate, the conditioned coordinate map is a permutation. -/
theorem wrongCandidateMap_bijective
    {K Row : Type} [Field K]
    (secret candidate anchorError : K) (rowError : Row → K)
    (hWrong : candidate ≠ secret) :
    Function.Bijective (wrongCandidateMap secret candidate anchorError rowError) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨wrongCandidateMapInv secret candidate anchorError rowError,
      wrongCandidateMapInv_wrongCandidateMap
        secret candidate anchorError rowError hWrong,
      wrongCandidateMap_wrongCandidateMapInv
        secret candidate anchorError rowError hWrong⟩

/-- Therefore every incorrect candidate gives an exactly uniform target coordinate after
conditioning on the complete correlated error vector (and on any leakage derived from it). -/
theorem wrongCandidate_evalDist_eq_uniform
    {K Row : Type} [Field K]
    [Fintype K] [DecidableEq K] [Fintype Row] [DecidableEq Row]
    [SampleableType K]
    (secret candidate anchorError : K) (rowError : Row → K)
    (hWrong : candidate ≠ secret) :
    evalDist (wrongCandidateMap secret candidate anchorError rowError <$>
        ($ᵗ (CoordinateView K Row))) =
      evalDist ($ᵗ (CoordinateView K Row)) :=
  evalDist_map_bijective_uniform_cross
    (α := CoordinateView K Row) (β := CoordinateView K Row)
    (wrongCandidateMap secret candidate anchorError rowError)
    (wrongCandidateMap_bijective
      secret candidate anchorError rowError hWrong)

/-- Translation of the coefficient masks used by the correct-candidate branch. -/
def correctCoinShift {K Row : Type} [AddCommGroup K]
    (coefficient : Row → K) (coins : K × (Row → K)) : K × (Row → K) :=
  (coins.1, fun row ↦ coefficient row + coins.2 row)

/-- The correct-candidate coin translation is a permutation. -/
theorem correctCoinShift_bijective {K Row : Type} [AddCommGroup K]
    (coefficient : Row → K) : Function.Bijective (correctCoinShift coefficient) := by
  let inverse : K × (Row → K) → K × (Row → K) := fun coins ↦
    (coins.1, fun row ↦ coins.2 row - coefficient row)
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro coins
    apply Prod.ext
    · rfl
    · funext row
      simp [inverse, correctCoinShift]
  · intro coins
    apply Prod.ext
    · rfl
    · funext row
      simp [inverse, correctCoinShift]

/-- Sampling the candidate masks in the correct branch gives exactly a fresh-secret real HNF
coordinate with the original correlated errors. -/
theorem correctCandidate_evalDist_eq_freshReal
    {K Row : Type} [Field K]
    [Fintype K] [DecidableEq K] [Fintype Row] [DecidableEq Row]
    [SampleableType K]
    (secret anchorError : K) (rowError coefficient : Row → K) :
    evalDist (($ᵗ (K × (Row → K))) >>= fun coins ↦
        pure (candidateTransform secret coins.1 coins.2
          (coordinateReal secret anchorError rowError coefficient))) =
      evalDist (($ᵗ (K × (Row → K))) >>= fun fresh ↦
        pure (coordinateReal fresh.1 anchorError rowError fresh.2)) := by
  have hShift :
      evalDist (correctCoinShift coefficient <$> ($ᵗ (K × (Row → K)))) =
        evalDist ($ᵗ (K × (Row → K))) :=
    evalDist_map_bijective_uniform_cross
      (α := K × (Row → K)) (β := K × (Row → K))
      (correctCoinShift coefficient) (correctCoinShift_bijective coefficient)
  calc
    evalDist (($ᵗ (K × (Row → K))) >>= fun coins ↦
        pure (candidateTransform secret coins.1 coins.2
          (coordinateReal secret anchorError rowError coefficient))) =
      evalDist ((correctCoinShift coefficient <$> ($ᵗ (K × (Row → K)))) >>= fun fresh ↦
        pure (coordinateReal fresh.1 anchorError rowError fresh.2)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine evalDist_bind_congr' ($ᵗ (K × (Row → K))) fun coins ↦ ?_
      rw [candidateTransform_correct]
      rfl
    _ = evalDist (($ᵗ (K × (Row → K))) >>= fun fresh ↦
        pure (coordinateReal fresh.1 anchorError rowError fresh.2)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hShift _

/-! ## Conditional split-ring search-to-decision and main theorem -/

/-- A checked split-ring search-to-decision certificate with a separately specified search view.

`SearchChallenge` may package the polynomial number of independent source blocks used by the
global CRT hybrid.  Constructing this object is exactly where a concrete instantiation must prove
the hybrid-position/candidate enumeration, acceptance-probability estimation, transitive
automorphism, joint error/leakage invariance, and sample-count claims.  The local bijections above
are the algebraic core of such a construction. -/
structure SplitSearchToDecisionCertificate
    {Secret DecisionChallenge DecisionAuxiliary SearchChallenge SearchAuxiliary : Type}
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      Secret DecisionChallenge DecisionAuxiliary)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      Secret SearchChallenge SearchAuxiliary) where
  toSolver :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
        DecisionChallenge DecisionAuxiliary →
      FormalProof4FHE.LWE.AuxiliaryInput.Search.Solver
        Secret SearchChallenge SearchAuxiliary
  loss :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      DecisionChallenge DecisionAuxiliary → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le : ∀ distinguisher,
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        decisionProblem distinguisher ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        searchProblem (toSolver distinguisher)).toReal + loss distinguisher

/-- Search hardness transfers to source-decision hardness through a checked split-ring
certificate, including its explicit finite reduction loss. -/
theorem sourceAdvantage_le_search_add_loss
    {Secret DecisionChallenge DecisionAuxiliary SearchChallenge SearchAuxiliary : Type}
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      Secret DecisionChallenge DecisionAuxiliary)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      Secret SearchChallenge SearchAuxiliary)
    (certificate : SplitSearchToDecisionCertificate decisionProblem searchProblem)
    (distinguisher :
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
        DecisionChallenge DecisionAuxiliary)
    (searchBound lossBound : ℝ)
    (hSearch :
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        searchProblem (certificate.toSolver distinguisher)).toReal ≤ searchBound)
    (hLoss : certificate.loss distinguisher ≤ lossBound) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        decisionProblem distinguisher ≤ searchBound + lossBound := by
  exact (certificate.advantage_le distinguisher).trans (add_le_add hSearch hLoss)

/-- **Conditional non-flooded quadratic KDM security.**  A checked split-ring certificate,
hardness of its correlated HNF search problem, and zero-message RLWE security bound the joint
fixed-gadget KDM advantage.  The target error in `kdmSampler` is exactly `latent.finalError`. -/
theorem kdmAdvantage_le_search_add_loss_add_zero
    {R Row Factor SearchChallenge SearchAuxiliary : Type}
    [CommRing R] [Fintype Factor]
    [Fintype R] [DecidableEq R] [Fintype Row] [DecidableEq Row]
    [SampleableType R]
    (gadget : Gadget R Row Factor) (latentSampler : ProbComp (Latent R Row Factor))
    (distinguisher : Distinguisher R Row)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      R SearchChallenge SearchAuxiliary)
    (certificate : SplitSearchToDecisionCertificate
      (sourceProblem gadget latentSampler) searchProblem)
    (searchBound lossBound zeroBound : ℝ)
    (hLatent : Pr[⊥ | latentSampler] = 0)
    (hSearch :
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability searchProblem
        (certificate.toSolver (sourceReduction gadget distinguisher))).toReal ≤ searchBound)
    (hLoss : certificate.loss (sourceReduction gadget distinguisher) ≤ lossBound)
    (hZero : zeroUniformAdvantage gadget latentSampler distinguisher ≤ zeroBound) :
    kdmAdvantage gadget latentSampler distinguisher ≤
      (searchBound + lossBound) + zeroBound := by
  calc
    kdmAdvantage gadget latentSampler distinguisher ≤
        kdmUniformAdvantage gadget latentSampler distinguisher +
          zeroUniformAdvantage gadget latentSampler distinguisher :=
      kdmAdvantage_le_kdmUniform_add_zeroUniform gadget latentSampler distinguisher
    _ = FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (sourceProblem gadget latentSampler) (sourceReduction gadget distinguisher) +
        zeroUniformAdvantage gadget latentSampler distinguisher := by
      rw [kdmUniformAdvantage_eq_sourceAdvantage
        gadget latentSampler distinguisher hLatent]
    _ ≤ (searchBound + lossBound) + zeroBound :=
      add_le_add
        (sourceAdvantage_le_search_add_loss
          (sourceProblem gadget latentSampler) searchProblem certificate
          (sourceReduction gadget distinguisher) searchBound lossBound hSearch hLoss)
        hZero

/-! ## Joint public-key extension -/

/-- Transform additional source rows `d=c*X+E` using the same anchor `b0=X-S`. -/
def publicKeyTransform {R PublicRow : Type} [Ring R]
    (anchor : R) (source : TargetTranscript R PublicRow) :
    TargetTranscript R PublicRow :=
  (source.1, fun row ↦ source.2 row - source.1 row * anchor)

/-- Additional real source rows become ordinary RLWE rows under the target secret. -/
theorem publicKeyTransform_real
    {R PublicRow : Type} [CommRing R]
    (auxiliarySecret targetSecret : R)
    (coefficient error : PublicRow → R) :
    publicKeyTransform (auxiliarySecret - targetSecret)
        (coefficient,
          fun row ↦ coefficient row * auxiliarySecret + error row) =
      (coefficient,
        fun row ↦ coefficient row * targetSecret + error row) := by
  apply Prod.ext
  · rfl
  · funext row
    dsimp [publicKeyTransform]
    ring

/-- Explicit inverse of the public-key affine transformation. -/
def publicKeyTransformInv {R PublicRow : Type} [Ring R]
    (anchor : R) (output : TargetTranscript R PublicRow) :
    TargetTranscript R PublicRow :=
  (output.1, fun row ↦ output.2 row + output.1 row * anchor)

@[simp]
theorem publicKeyTransformInv_publicKeyTransform
    {R PublicRow : Type} [Ring R]
    (anchor : R) (source : TargetTranscript R PublicRow) :
    publicKeyTransformInv anchor (publicKeyTransform anchor source) = source := by
  apply Prod.ext
  · rfl
  · funext row
    simp [publicKeyTransformInv, publicKeyTransform]

@[simp]
theorem publicKeyTransform_publicKeyTransformInv
    {R PublicRow : Type} [Ring R]
    (anchor : R) (output : TargetTranscript R PublicRow) :
    publicKeyTransform anchor (publicKeyTransformInv anchor output) = output := by
  apply Prod.ext
  · rfl
  · funext row
    simp [publicKeyTransformInv, publicKeyTransform]

/-- The public-key random-branch transformation is a permutation. -/
theorem publicKeyTransform_bijective
    {R PublicRow : Type} [Ring R] (anchor : R) :
    Function.Bijective (publicKeyTransform (PublicRow := PublicRow) anchor) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨publicKeyTransformInv anchor,
      publicKeyTransformInv_publicKeyTransform anchor,
      publicKeyTransform_publicKeyTransformInv anchor⟩

/-- Hence additional random source rows remain exactly uniform. -/
theorem publicKeyTransform_evalDist_eq_uniform
    {R PublicRow : Type} [Ring R]
    [Fintype R] [DecidableEq R] [Fintype PublicRow] [DecidableEq PublicRow]
    [SampleableType R]
    (anchor : R) :
    evalDist (publicKeyTransform (PublicRow := PublicRow) anchor <$>
        ($ᵗ (TargetTranscript R PublicRow))) =
      evalDist ($ᵗ (TargetTranscript R PublicRow)) :=
  evalDist_map_bijective_uniform_cross
    (α := TargetTranscript R PublicRow) (β := TargetTranscript R PublicRow)
    (publicKeyTransform anchor) (publicKeyTransform_bijective anchor)

/-- Joint random map for evaluation-key rows and any finite family of ordinary public-key rows. -/
def jointRandomMap {R Row Factor PublicRow : Type}
    [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (anchor : R) (leakage : Leakage R Row Factor)
    (source : TargetTranscript R Row × TargetTranscript R PublicRow) :
    TargetTranscript R Row × TargetTranscript R PublicRow :=
  (randomCompilerMap gadget anchor leakage source.1,
    publicKeyTransform anchor source.2)

/-- Explicit inverse of the joint random map. -/
def jointRandomMapInv {R Row Factor PublicRow : Type}
    [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (anchor : R) (leakage : Leakage R Row Factor)
    (output : TargetTranscript R Row × TargetTranscript R PublicRow) :
    TargetTranscript R Row × TargetTranscript R PublicRow :=
  (randomCompilerMapInv gadget anchor leakage output.1,
    publicKeyTransformInv anchor output.2)

/-- The joint random transformation is a permutation, so the compiler remains exact when the
evaluation key is published together with ordinary public-key samples under the same secret. -/
theorem jointRandomMap_bijective
    {R Row Factor PublicRow : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (anchor : R) (leakage : Leakage R Row Factor) :
    Function.Bijective
      (jointRandomMap (PublicRow := PublicRow) gadget anchor leakage) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨jointRandomMapInv gadget anchor leakage, ?_, ?_⟩
  · intro source
    apply Prod.ext
    · exact randomCompilerMapInv_randomCompilerMap gadget anchor leakage source.1
    · exact publicKeyTransformInv_publicKeyTransform anchor source.2
  · intro output
    apply Prod.ext
    · exact randomCompilerMap_randomCompilerMapInv gadget anchor leakage output.1
    · exact publicKeyTransform_publicKeyTransformInv anchor output.2

/-! ## Relinearization correctness -/

/-- The weighted evaluation-key phase used by relinearization. -/
def evaluationKeyBody {R Row : Type} [CommRing R]
    (secret : R) (weight mask error : Row → R) (row : Row) : R :=
  mask row * secret + weight row * secret ^ 2 + error row

/-- **Relinearization correctness.**  If `c2 = sum d_j*g_j`, the relinearized phase equals the
original degree-two phase plus exactly `sum d_j*H_j`. -/
theorem relinearization_phase
    {R Row : Type} [CommRing R] [Fintype Row]
    (secret c0 c1 c2 : R) (digit weight mask error : Row → R)
    (hDecomposition : c2 = ∑ row, digit row * weight row) :
    (c0 + ∑ row, digit row * evaluationKeyBody secret weight mask error row) +
        (c1 - ∑ row, digit row * mask row) * secret =
      c0 + c1 * secret + c2 * secret ^ 2 +
        ∑ row, digit row * error row := by
  have hBodySum :
      (∑ row, digit row * evaluationKeyBody secret weight mask error row) =
        (∑ row, digit row * mask row) * secret +
          (∑ row, digit row * weight row) * secret ^ 2 +
            ∑ row, digit row * error row := by
    calc
      (∑ row, digit row * evaluationKeyBody secret weight mask error row) =
          ∑ row,
            ((digit row * mask row) * secret +
              (digit row * weight row) * secret ^ 2 + digit row * error row) := by
        apply Finset.sum_congr rfl
        intro row _
        simp only [evaluationKeyBody]
        ring
      _ = (∑ row, digit row * mask row) * secret +
          (∑ row, digit row * weight row) * secret ^ 2 +
            ∑ row, digit row * error row := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hBodySum, hDecomposition]
  ring

/-! ## Instantiation sanity checks -/

/-- Recover the first latent factor from a candidate secret and the public leakage. -/
def recoverFirstError {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (secret : R) (leakage : Leakage R Row Factor)
    (row : Row) (factor : Factor) : R :=
  leakage.1 row factor - gadget.alpha row factor * secret

/-- Recover the second latent factor from a candidate secret and the public leakage. -/
def recoverSecondError {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (secret : R) (leakage : Leakage R Row Factor)
    (row : Row) (factor : Factor) : R :=
  leakage.2 row factor - gadget.beta row factor * secret

/-- Recover the final error from the terminal source error after reconstructing the factors. -/
def recoverFinalError {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (secret : R) (leakage : Leakage R Row Factor)
    (terminal : Row → R) (row : Row) : R :=
  terminal row - ∑ factor,
    recoverFirstError gadget secret leakage row factor *
      recoverSecondError gadget secret leakage row factor

/-- The genuine leakage reconstructs every first latent factor when `S` is known. -/
@[simp]
theorem recoverFirstError_publicLeakage
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor)
    (row : Row) (factor : Factor) :
    recoverFirstError gadget latent.secret (publicLeakage gadget latent) row factor =
      latent.firstError row factor := by
  simp [recoverFirstError, publicLeakage]

/-- The genuine leakage reconstructs every second latent factor when `S` is known. -/
@[simp]
theorem recoverSecondError_publicLeakage
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor)
    (row : Row) (factor : Factor) :
    recoverSecondError gadget latent.secret (publicLeakage gadget latent) row factor =
      latent.secondError row factor := by
  simp [recoverSecondError, publicLeakage]

/-- Once `S`, leakage, and `Z` are known, the genuine final error is reconstructed exactly.  This
is the deterministic change-of-variables underlying the residual-entropy calculation in the TeX
document; the entropy chain rule and independence premise remain obligations of an entropy model. -/
@[simp]
theorem recoverFinalError_terminalError
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : Gadget R Row Factor) (latent : Latent R Row Factor) (row : Row) :
    recoverFinalError gadget latent.secret (publicLeakage gadget latent)
        (terminalError latent) row = latent.finalError row := by
  simp [recoverFinalError, terminalError]

/-- The error-free relation caused by exposing the forbidden extra row `p=uX+F`. -/
theorem exposedFactorRow_relation
    {R : Type} [CommRing R] (publicCoefficient factorWeight auxiliarySecret targetSecret
      factorError : R) :
    (publicCoefficient * auxiliarySecret + factorError) -
        (factorWeight * targetSecret + factorError) -
          factorWeight * (auxiliarySecret - targetSecret) =
      (publicCoefficient - factorWeight) * auxiliarySecret := by
  ring

/-- A generic finite-sum triangle inequality for an abstract ring size. -/
theorem size_sum_le_sum_size
    {R Index : Type} [AddCommMonoid R] [Fintype Index] [DecidableEq Index]
    (size : R → ℝ) (hZero : size 0 = 0)
    (hAdd : ∀ left right, size (left + right) ≤ size left + size right)
    (value : Index → R) :
    size (∑ index, value index) ≤ ∑ index, size (value index) := by
  classical
  have hFinite : ∀ indices : Finset Index,
      size (∑ index ∈ indices, value index) ≤
        ∑ index ∈ indices, size (value index) := by
    intro indices
    induction indices using Finset.induction_on with
    | empty => simp [hZero]
    | @insert index indices hNotMem inductionHypothesis =>
        simp only [Finset.sum_insert hNotMem]
        exact (hAdd _ _).trans (add_le_add le_rfl inductionHypothesis)
  simpa using hFinite Finset.univ

/-- Abstract form of the source-error norm bound
`|Z_j| <= #Factor * mu * B_F * B_G + B_H`.  The bound contains no gadget weight. -/
theorem terminalError_size_le
    {R Row Factor : Type} [CommRing R] [Fintype Factor] [DecidableEq Factor]
    (latent : Latent R Row Factor) (row : Row)
    (size : R → ℝ) (mu boundFirst boundSecond boundFinal : ℝ)
    (hZero : size 0 = 0)
    (hSizeNonneg : ∀ value, 0 ≤ size value)
    (hAdd : ∀ left right, size (left + right) ≤ size left + size right)
    (hMul : ∀ left right, size (left * right) ≤ mu * size left * size right)
    (hMu : 0 ≤ mu) (hBoundFirst : 0 ≤ boundFirst)
    (hFirst : ∀ factor, size (latent.firstError row factor) ≤ boundFirst)
    (hSecond : ∀ factor, size (latent.secondError row factor) ≤ boundSecond)
    (hFinal : size (latent.finalError row) ≤ boundFinal) :
    size (terminalError latent row) ≤
      (Fintype.card Factor : ℝ) * mu * boundFirst * boundSecond + boundFinal := by
  have hProduct (factor : Factor) :
      size (latent.firstError row factor * latent.secondError row factor) ≤
        mu * boundFirst * boundSecond := by
    calc
      size (latent.firstError row factor * latent.secondError row factor) ≤
          mu * size (latent.firstError row factor) *
            size (latent.secondError row factor) :=
        hMul _ _
      _ ≤ mu * boundFirst * boundSecond := by
        calc
          mu * size (latent.firstError row factor) *
                size (latent.secondError row factor) ≤
              mu * boundFirst * size (latent.secondError row factor) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hFirst factor) hMu)
              (hSizeNonneg _)
          _ ≤ mu * boundFirst * boundSecond :=
            mul_le_mul_of_nonneg_left (hSecond factor)
              (mul_nonneg hMu hBoundFirst)
  have hSum :
      size (∑ factor,
        latent.firstError row factor * latent.secondError row factor) ≤
        (Fintype.card Factor : ℝ) * mu * boundFirst * boundSecond := by
    calc
      size (∑ factor,
          latent.firstError row factor * latent.secondError row factor) ≤
          ∑ factor,
            size (latent.firstError row factor * latent.secondError row factor) :=
        size_sum_le_sum_size size hZero hAdd _
      _ ≤ ∑ _factor : Factor, mu * boundFirst * boundSecond := by
        exact Finset.sum_le_sum fun factor _ ↦ hProduct factor
      _ = (Fintype.card Factor : ℝ) * mu * boundFirst * boundSecond := by
        simp
        ring
  unfold terminalError
  exact (hAdd _ _).trans (add_le_add hSum hFinal)

/-! ### Necessary field-projection check -/

/-- The projected discriminant used by the unconditional quadratic-character test. -/
def discriminant {K : Type} [Ring K] (weight reference : K) (sample : K × K) : K :=
  sample.1 ^ 2 + 4 * weight * (sample.2 - reference)

/-- In the quadratic KDM distribution the discriminant is a shifted square. -/
theorem discriminant_kdm_identity
    {K : Type} [CommRing K] (mask secret error reference weight : K) :
    discriminant weight reference
        (mask, mask * secret + weight * secret ^ 2 + error) =
      (mask + 2 * weight * secret) ^ 2 + 4 * weight * (error - reference) := by
  simp only [discriminant]
  ring

/-- Pair map exposing the discriminant as its second coordinate. -/
def discriminantMap {K : Type} [Ring K] (weight reference : K)
    (sample : K × K) : K × K :=
  (sample.1, discriminant weight reference sample)

/-- Explicit inverse when `4*weight` is nonzero. -/
def discriminantMapInv {K : Type} [Field K] (weight reference : K)
    (output : K × K) : K × K :=
  (output.1,
    ((4 * weight)⁻¹ * (output.2 - output.1 ^ 2)) + reference)

/-- For nonzero projected gadget weight in odd characteristic, the uniform-pair discriminant map
is a permutation. -/
theorem discriminantMap_bijective
    {K : Type} [Field K] (weight reference : K)
    (hScale : (4 : K) * weight ≠ 0) :
    Function.Bijective (discriminantMap weight reference) := by
  have hFour : (4 : K) ≠ 0 := by
    intro h
    apply hScale
    rw [h, zero_mul]
  have hWeight : weight ≠ 0 := by
    intro h
    apply hScale
    rw [h, mul_zero]
  refine Function.bijective_iff_has_inverse.mpr
    ⟨discriminantMapInv weight reference, ?_, ?_⟩
  · intro sample
    apply Prod.ext
    · rfl
    · dsimp [discriminantMapInv, discriminantMap, discriminant]
      field_simp [hScale, hFour, hWeight]
      ring
  · intro output
    apply Prod.ext
    · rfl
    · dsimp [discriminantMapInv, discriminantMap, discriminant]
      field_simp [hScale, hFour, hWeight]
      ring

/-- Consequently the discriminant of a uniform pair is itself jointly uniform with the mask. -/
theorem discriminantMap_evalDist_eq_uniform
    {K : Type} [Field K] [Fintype K] [DecidableEq K] [SampleableType K]
    (weight reference : K) (hScale : (4 : K) * weight ≠ 0) :
    evalDist (discriminantMap weight reference <$> ($ᵗ (K × K))) =
      evalDist ($ᵗ (K × K)) :=
  evalDist_map_bijective_uniform_cross
    (α := K × K) (β := K × K) (discriminantMap weight reference)
    (discriminantMap_bijective weight reference hScale)

end

end FormalProof4FHE.RLWE.QuadraticKDM
