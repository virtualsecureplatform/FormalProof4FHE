/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.Security
import FormalProof4FHE.Probability.BinaryGuessCheck
import FormalProof4FHE.Probability.MajorityAmplification
import FormalProof4FHE.SharedRandomness.Reduction

/-!
# Security reductions for Binary-NTT and quadratic-hint RLWE

This module formalizes the algebraic and finite-loss core of Section 6.1 of Jain--Lin--Liu--
Saha, *New Techniques for Fast and Shallow FHE Bootstrapping and Beyond* (2026/1730).

The paper studies three decision assumptions:

* Binary-NTT RLWE, whose secret is idempotent (`s^2 = s`);
* quadratic-hint RLWE, which publishes `v = s^2 - u*s`;
* quadratic-hint small-secret RLWE.

The checked results below include the four public algebraic transformations, the invertible-event
loss calculation, and the idempotent-secret rerandomization used by the search-to-decision proof.

The formalization also records a boundary in the published proof of Theorem 5.  Its algorithm
samples an invertible multiplier `u`, but the subsequent distribution calculation treats `u` as
uniform over the whole ring.  The transformed pair `(u',s')` always satisfies that `u' - 2*s'`
is a unit.  An unconditioned quadratic-hint sample need not satisfy this.  Consequently the exact
distributional claim in Lemmas 6 and 8 requires either a conditioned QH game or an additional
statistical-distance term; it is not used as an unconditional theorem here.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity

noncomputable section

/-! ## Generic finite decision reductions -/

/-- A finite real-versus-random decision problem. -/
structure DecisionProblem (View : Type) where
  real : ProbComp View
  random : ProbComp View

/-- A distinguisher for a finite decision problem. -/
abbrev Distinguisher (View : Type) := View → ProbComp Bool

/-- Absolute distinguishing advantage. -/
noncomputable def advantage {View : Type} (problem : DecisionProblem View)
    (distinguisher : Distinguisher View) : ℝ :=
  (problem.real >>= distinguisher).boolDistAdvantage
    (problem.random >>= distinguisher)

/-- A public map that transports both endpoints of a source problem exactly to a target problem. -/
structure ExactMapReduction {SourceView TargetView : Type}
    (source : DecisionProblem SourceView) (target : DecisionProblem TargetView) where
  transform : SourceView → TargetView
  realLaw : evalDist (source.real >>= fun view ↦ pure (transform view)) = evalDist target.real
  randomLaw : evalDist (source.random >>= fun view ↦ pure (transform view)) =
    evalDist target.random

/-- Pull a target distinguisher through an exact public reduction. -/
def ExactMapReduction.pullback {SourceView TargetView : Type}
    {source : DecisionProblem SourceView} {target : DecisionProblem TargetView}
    (reduction : ExactMapReduction source target) (distinguisher : Distinguisher TargetView) :
    Distinguisher SourceView :=
  fun view ↦ distinguisher (reduction.transform view)

/-- Exact endpoint transport preserves distinguishing advantage. -/
theorem ExactMapReduction.advantage_pullback {SourceView TargetView : Type}
    {source : DecisionProblem SourceView} {target : DecisionProblem TargetView}
    (reduction : ExactMapReduction source target) (distinguisher : Distinguisher TargetView) :
    advantage source (reduction.pullback distinguisher) = advantage target distinguisher := by
  unfold advantage ExactMapReduction.pullback ProbComp.boolDistAdvantage
  have hreal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    reduction.realLaw distinguisher
  have hrandom := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    reduction.randomLaw distinguisher
  simp only [bind_assoc, pure_bind] at hreal hrandom
  rw [evalDist_ext_iff.mp hreal true, evalDist_ext_iff.mp hrandom true]

/-- Concrete hardness against a selected distinguisher class. -/
def HardAgainst {View : Type} (problem : DecisionProblem View)
    (allowed : Distinguisher View → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher → advantage problem distinguisher ≤ bound

/-- Exact public reductions transfer finite hardness without loss. -/
theorem hardAgainst_of_exactMap {SourceView TargetView : Type}
    {source : DecisionProblem SourceView} {target : DecisionProblem TargetView}
    (reduction : ExactMapReduction source target)
    (sourceAllowed : Distinguisher SourceView → Prop)
    (targetAllowed : Distinguisher TargetView → Prop) (bound : ℝ)
    (hClosed : ∀ distinguisher, targetAllowed distinguisher →
      sourceAllowed (reduction.pullback distinguisher))
    (hSource : HardAgainst source sourceAllowed bound) :
    HardAgainst target targetAllowed bound := by
  intro distinguisher hAllowed
  rw [← reduction.advantage_pullback distinguisher]
  exact hSource _ (hClosed distinguisher hAllowed)

/-- A quantitative reduction used when a transformation aborts on a bad public event.  The
paper's Theorems 10 and 15 aim to instantiate this with `factor = 4`. -/
structure AdvantageReduction {SourceView TargetView : Type}
    (source : DecisionProblem SourceView) (target : DecisionProblem TargetView) where
  pullback : Distinguisher TargetView → Distinguisher SourceView
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  advantage_le : ∀ distinguisher,
    advantage target distinguisher ≤ factor * advantage source (pullback distinguisher)

/-- Hardness transfer through a checked multiplicative-loss reduction. -/
theorem hardAgainst_of_advantageReduction {SourceView TargetView : Type}
    {source : DecisionProblem SourceView} {target : DecisionProblem TargetView}
    (reduction : AdvantageReduction source target)
    (sourceAllowed : Distinguisher SourceView → Prop)
    (targetAllowed : Distinguisher TargetView → Prop) (bound : ℝ)
    (hClosed : ∀ distinguisher, targetAllowed distinguisher →
      sourceAllowed (reduction.pullback distinguisher))
    (hSource : HardAgainst source sourceAllowed bound) :
    HardAgainst target targetAllowed (reduction.factor * bound) := by
  intro distinguisher hAllowed
  exact (reduction.advantage_le distinguisher).trans
    (mul_le_mul_of_nonneg_left (hSource _ (hClosed distinguisher hAllowed))
      reduction.factor_nonneg)

/-- A probabilistic public transformation whose two endpoints are close, rather than identical,
to the target endpoints.  This is the correct interface for repairing Theorem 5. -/
structure ApproximateReduction {SourceView TargetView : Type}
    (source : DecisionProblem SourceView) (target : DecisionProblem TargetView) where
  transform : SourceView → ProbComp TargetView
  realError : ℝ
  randomError : ℝ
  realError_nonneg : 0 ≤ realError
  randomError_nonneg : 0 ≤ randomError
  realLaw : tvDist (source.real >>= transform) target.real ≤ realError
  randomLaw : tvDist (source.random >>= transform) target.random ≤ randomError

def ApproximateReduction.pullback {SourceView TargetView : Type}
    {source : DecisionProblem SourceView} {target : DecisionProblem TargetView}
    (reduction : ApproximateReduction source target)
    (distinguisher : Distinguisher TargetView) : Distinguisher SourceView :=
  fun view ↦ reduction.transform view >>= distinguisher

/-- Approximate transport pays each endpoint error exactly once. -/
theorem ApproximateReduction.advantage_le {SourceView TargetView : Type}
    {source : DecisionProblem SourceView} {target : DecisionProblem TargetView}
    (reduction : ApproximateReduction source target)
    (distinguisher : Distinguisher TargetView) :
    advantage target distinguisher ≤
      advantage source (reduction.pullback distinguisher) +
        reduction.realError + reduction.randomError := by
  let sourceReal := source.real >>= reduction.transform >>= distinguisher
  let sourceRandom := source.random >>= reduction.transform >>= distinguisher
  let targetReal := target.real >>= distinguisher
  let targetRandom := target.random >>= distinguisher
  have hRealTV : tvDist sourceReal targetReal ≤ reduction.realError := by
    have hpost := tvDist_bind_right_le distinguisher
      (source.real >>= reduction.transform) target.real
    have hpost' : tvDist sourceReal targetReal ≤
        tvDist (source.real >>= reduction.transform) target.real := by
      simpa only [sourceReal, targetReal, bind_assoc] using hpost
    exact hpost'.trans reduction.realLaw
  have hRandomTV : tvDist sourceRandom targetRandom ≤ reduction.randomError := by
    have hpost := tvDist_bind_right_le distinguisher
      (source.random >>= reduction.transform) target.random
    have hpost' : tvDist sourceRandom targetRandom ≤
        tvDist (source.random >>= reduction.transform) target.random := by
      simpa only [sourceRandom, targetRandom, bind_assoc] using hpost
    exact hpost'.trans reduction.randomLaw
  have hRealAdv : targetReal.boolDistAdvantage sourceReal ≤ reduction.realError := by
    exact (abs_probOutput_toReal_sub_le_tvDist targetReal sourceReal).trans
      ((tvDist_comm sourceReal targetReal ▸ hRealTV))
  have hRandomAdv : sourceRandom.boolDistAdvantage targetRandom ≤ reduction.randomError :=
    (abs_probOutput_toReal_sub_le_tvDist sourceRandom targetRandom).trans hRandomTV
  have hFirst := ProbComp.boolDistAdvantage_triangle targetReal sourceReal targetRandom
  have hSecond := ProbComp.boolDistAdvantage_triangle sourceReal sourceRandom targetRandom
  have hfinal : targetReal.boolDistAdvantage targetRandom ≤
      sourceReal.boolDistAdvantage sourceRandom + reduction.realError + reduction.randomError := by
    linarith
  change (target.real >>= distinguisher).boolDistAdvantage
      (target.random >>= distinguisher) ≤
    (source.real >>= fun view ↦ reduction.transform view >>= distinguisher).boolDistAdvantage
        (source.random >>= fun view ↦ reduction.transform view >>= distinguisher) +
      reduction.realError + reduction.randomError
  simpa only [sourceReal, sourceRandom, targetReal, targetRandom, bind_assoc] using hfinal

/-- Hardness transfer through approximate endpoint transport. -/
theorem hardAgainst_of_approximateReduction {SourceView TargetView : Type}
    {source : DecisionProblem SourceView} {target : DecisionProblem TargetView}
    (reduction : ApproximateReduction source target)
    (sourceAllowed : Distinguisher SourceView → Prop)
    (targetAllowed : Distinguisher TargetView → Prop) (bound : ℝ)
    (hClosed : ∀ distinguisher, targetAllowed distinguisher →
      sourceAllowed (reduction.pullback distinguisher))
    (hSource : HardAgainst source sourceAllowed bound) :
    HardAgainst target targetAllowed
      (bound + reduction.realError + reduction.randomError) := by
  intro distinguisher hAllowed
  calc
    advantage target distinguisher ≤
        advantage source (reduction.pullback distinguisher) +
          reduction.realError + reduction.randomError := reduction.advantage_le distinguisher
    _ ≤ bound + reduction.realError + reduction.randomError := by
      gcongr
      exact hSource _ (hClosed distinguisher hAllowed)

/-! ### Corrected Theorem 5 -/

/-- Probability mass of quadratic hints whose discriminant gap has a zero NTT coordinate in the
split product-ring model. -/
def discriminantBadLoss (N q : ℕ) : ℝ :=
  1 - (1 - 1 / (q : ℝ)) ^ N

/-- Union/Bernoulli upper bound on the conditioning loss. -/
theorem discriminantBadLoss_le (N q : ℕ) (hq : 0 < q) :
    discriminantBadLoss N q ≤ (N : ℝ) / q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hinv : 1 / (q : ℝ) ≤ 1 := (div_le_one hqpos).mpr hqone
  have ha : (-2 : ℝ) ≤ -(1 / (q : ℝ)) := by linarith
  have hbernoulli := one_add_mul_le_pow ha N
  unfold discriminantBadLoss
  have hone : 1 + (N : ℝ) * (-(1 / (q : ℝ))) = 1 - (N : ℝ) / q := by
    field_simp
    ring
  rw [hone] at hbernoulli
  have hbase : (1 : ℝ) + -(1 / (q : ℝ)) = 1 - 1 / q := by ring
  rw [hbase] at hbernoulli
  linarith

/-- Corrected quantitative form of Theorem 5.  The forward transform is exact for the QH law
conditioned on an invertible discriminant gap.  If replacing each conditioned endpoint by the
ordinary QH endpoint costs at most `delta`, QH advantage is at most Binary-NTT advantage plus
`2*delta`.  In the split NTT model one takes `delta = discriminantBadLoss N q`. -/
theorem correctedTheorem5_advantage_le {SourceView QHView : Type}
    {binaryNTT : DecisionProblem SourceView} {quadraticHint : DecisionProblem QHView}
    (reduction : ApproximateReduction binaryNTT quadraticHint)
    (delta : ℝ)
    (hReal : reduction.realError ≤ delta)
    (hRandom : reduction.randomError ≤ delta)
    (distinguisher : Distinguisher QHView) :
    advantage quadraticHint distinguisher ≤
      advantage binaryNTT (reduction.pullback distinguisher) + 2 * delta := by
  exact (reduction.advantage_le distinguisher).trans (by linarith)

/-- Hardness implication corresponding to the corrected Theorem 5. -/
theorem correctedTheorem5_hardAgainst {SourceView QHView : Type}
    {binaryNTT : DecisionProblem SourceView} {quadraticHint : DecisionProblem QHView}
    (reduction : ApproximateReduction binaryNTT quadraticHint)
    (sourceAllowed : Distinguisher SourceView → Prop)
    (targetAllowed : Distinguisher QHView → Prop)
    (sourceBound delta : ℝ)
    (hReal : reduction.realError ≤ delta)
    (hRandom : reduction.randomError ≤ delta)
    (hClosed : ∀ distinguisher, targetAllowed distinguisher →
      sourceAllowed (reduction.pullback distinguisher))
    (hSource : HardAgainst binaryNTT sourceAllowed sourceBound) :
    HardAgainst quadraticHint targetAllowed (sourceBound + 2 * delta) := by
  intro distinguisher hAllowed
  exact (correctedTheorem5_advantage_le reduction delta hReal hRandom distinguisher).trans
    (by
      have h := hSource _ (hClosed distinguisher hAllowed)
      linarith)

/-- Corrected same-sample form of Theorem 19.  The public reduction samples a fresh shift, so it is
represented by a probabilistic reduction with zero endpoint errors.  The implication has no
quarter loss and consumes no extra sample. -/
theorem correctedTheorem19_sameSample_hardAgainst {SmallView UniformView : Type}
    {qhSmallSecret : DecisionProblem SmallView} {qhUniformSecret : DecisionProblem UniformView}
    (reduction : ApproximateReduction qhSmallSecret qhUniformSecret)
    (smallAllowed : Distinguisher SmallView → Prop)
    (uniformAllowed : Distinguisher UniformView → Prop) (bound : ℝ)
    (hReal : reduction.realError = 0)
    (hRandom : reduction.randomError = 0)
    (hClosed : ∀ distinguisher, uniformAllowed distinguisher →
      smallAllowed (reduction.pullback distinguisher))
    (hSmall : HardAgainst qhSmallSecret smallAllowed bound) :
    HardAgainst qhUniformSecret uniformAllowed bound := by
  intro distinguisher hAllowed
  have h := reduction.advantage_le distinguisher
  rw [hReal, hRandom] at h
  simpa using h.trans (by
    have hs := hSmall _ (hClosed distinguisher hAllowed)
    linarith)

/-! ## Games and public views -/

/-- A batch of ordinary RLWE masks and bodies. -/
structure RLWEView (R Row : Type) where
  mask : Row → R
  body : Row → R

@[ext]
theorem RLWEView.ext {R Row : Type} {left right : RLWEView R Row}
    (hmask : left.mask = right.mask) (hbody : left.body = right.body) : left = right := by
  cases left
  cases right
  simp_all

/-- Representation equivalence used to inherit the canonical finite sampler. -/
def rlweViewEquiv (R Row : Type) :
    ((Row → R) × (Row → R)) ≃ RLWEView R Row where
  toFun pair := ⟨pair.1, pair.2⟩
  invFun view := (view.mask, view.body)
  left_inv pair := rfl
  right_inv view := by cases view; rfl

noncomputable instance rlweViewFintype {R Row : Type}
    [Fintype R] [Fintype Row] [DecidableEq Row] : Fintype (RLWEView R Row) :=
  Fintype.ofEquiv ((Row → R) × (Row → R)) (rlweViewEquiv R Row)

noncomputable instance rlweViewSampleableType {R Row : Type}
    [SampleableType ((Row → R) × (Row → R))] : SampleableType (RLWEView R Row) :=
  SampleableType.ofEquiv (rlweViewEquiv R Row)

/-- An RLWE batch together with the public quadratic equation `s^2 = u*s + v`. -/
structure QuadraticHintView (R Row : Type) where
  u : R
  v : R
  mask : Row → R
  body : Row → R

/-- The public quadratic hint attached to a secret. -/
def quadraticHint {R : Type} [Ring R] (u secret : R) : R :=
  secret ^ 2 - u * secret

/-- An ordinary real RLWE batch. -/
def realView {R Row : Type} [Ring R]
    (mask : Row → R) (secret : R) (error : Row → R) : RLWEView R Row :=
  ⟨mask, fun i ↦ mask i * secret + error i⟩

/-- A real quadratic-hint RLWE batch. -/
def realQuadraticHintView {R Row : Type} [Ring R]
    (u : R) (mask : Row → R) (secret : R) (error : Row → R) :
    QuadraticHintView R Row :=
  ⟨u, quadraticHint u secret, mask, fun i ↦ mask i * secret + error i⟩

/-! ## Theorem 5: forward affine transformation -/

/-- The secret produced by the Binary-NTT-to-QH affine transformation. -/
def forwardSecret {R : Type} [Ring R] (multiplier : R) (offset secret : R) : R :=
  multiplier * secret + offset

/-- Public linear coefficient of the transformed quadratic equation. -/
def forwardHintU {R : Type} [Ring R] (multiplier offset : R) : R :=
  multiplier + 2 * offset

/-- Public constant coefficient of the transformed quadratic equation. -/
def forwardHintV {R : Type} [Ring R] (multiplier offset : R) : R :=
  -offset ^ 2 - multiplier * offset

/-- The complete public transformation from Figure 1. -/
def forwardTransform {R Row : Type} [CommRing R]
    (multiplier : Rˣ) (offset : R) (view : RLWEView R Row) : QuadraticHintView R Row where
  u := forwardHintU (multiplier : R) offset
  v := forwardHintV (multiplier : R) offset
  mask := fun i ↦ view.mask i * (multiplier⁻¹ : Rˣ)
  body := fun i ↦ view.body i +
    (view.mask i * (multiplier⁻¹ : Rˣ)) * offset

/-- Lemma 7's body identity. -/
theorem forwardTransform_real_body {R Row : Type} [CommRing R]
    (multiplier : Rˣ) (offset secret : R) (mask error : Row → R) (i : Row) :
    (forwardTransform multiplier offset (realView mask secret error)).body i =
      (forwardTransform multiplier offset (realView mask secret error)).mask i *
        forwardSecret (multiplier : R) offset secret + error i := by
  have hunit : ((multiplier⁻¹ : Rˣ) : R) * (multiplier : R) = 1 := by simp
  simp only [forwardTransform, realView, forwardSecret]
  linear_combination -(mask i * secret) * hunit

/-- Lemma 7's quadratic-hint identity. -/
theorem forwardSecret_quadratic {R : Type} [CommRing R]
    (multiplier offset secret : R) (hidempotent : secret ^ 2 = secret) :
    forwardSecret multiplier offset secret ^ 2 =
      forwardHintU multiplier offset * forwardSecret multiplier offset secret +
        forwardHintV multiplier offset := by
  simp only [forwardSecret, forwardHintU, forwardHintV]
  linear_combination multiplier ^ 2 * hidempotent

/-- The discriminant root carried by the forward transformation. -/
theorem forward_discriminant_root {R : Type} [CommRing R]
    (multiplier offset : R) :
    forwardHintU multiplier offset ^ 2 + 4 * forwardHintV multiplier offset =
      multiplier ^ 2 := by
  simp [forwardHintU, forwardHintV]
  ring

/-! ### The conditioning gap in the published Theorem 5 proof -/

/-- An idempotent gives an involution `1 - 2s`. -/
theorem one_sub_two_mul_sq {R : Type} [CommRing R] (secret : R)
    (hidempotent : secret ^ 2 = secret) :
    (1 - 2 * secret) * (1 - 2 * secret) = 1 := by
  linear_combination 4 * hidempotent

/-- Therefore `1 - 2s` is a unit in every commutative ring. -/
theorem isUnit_one_sub_two_mul {R : Type} [CommRing R] (secret : R)
    (hidempotent : secret ^ 2 = secret) : IsUnit (1 - 2 * secret) := by
  exact isUnit_iff_exists_inv.mpr ⟨1 - 2 * secret, one_sub_two_mul_sq secret hidempotent⟩

/-- The transformed public coefficient and transformed secret cannot have zero discriminant gap
when the multiplier is a unit. -/
theorem forward_hint_secret_gap {R : Type} [CommRing R]
    (multiplier offset secret : R) :
    forwardHintU multiplier offset - 2 * forwardSecret multiplier offset secret =
      multiplier * (1 - 2 * secret) := by
  simp [forwardHintU, forwardSecret]
  ring

/-- Formal support obstruction to Lemmas 6 and 8 as written: the forward reduction always lands
in the conditioned subset where `u' - 2s'` is invertible. -/
theorem forward_hint_secret_gap_isUnit {R : Type} [CommRing R]
    (multiplier : Rˣ) (offset secret : R) (hidempotent : secret ^ 2 = secret) :
    IsUnit
      (forwardHintU (multiplier : R) offset -
        2 * forwardSecret (multiplier : R) offset secret) := by
  rw [forward_hint_secret_gap]
  exact multiplier.isUnit.mul (isUnit_one_sub_two_mul secret hidempotent)

/-- In a nontrivial ring, the same gap is never zero. -/
theorem forward_hint_secret_gap_ne_zero {R : Type} [CommRing R] [Nontrivial R]
    (multiplier : Rˣ) (offset secret : R) (hidempotent : secret ^ 2 = secret) :
    forwardHintU (multiplier : R) offset ≠
      2 * forwardSecret (multiplier : R) offset secret := by
  intro heq
  have hzero :
      forwardHintU (multiplier : R) offset -
        2 * forwardSecret (multiplier : R) offset secret = 0 := sub_eq_zero.mpr heq
  have hunit := forward_hint_secret_gap_isUnit multiplier offset secret hidempotent
  rw [hzero] at hunit
  exact not_isUnit_zero hunit

/-- The unconditioned QH distribution contains a valid zero-gap point, for example
`(u',s',v')=(0,0,0)`, while the forward transform cannot reach it. -/
theorem forwardTransform_cannot_reach_zero_hint_secret
    {R : Type} [CommRing R] [Nontrivial R]
    (multiplier : Rˣ) (offset secret : R) (hidempotent : secret ^ 2 = secret) :
    ¬ (forwardHintU (multiplier : R) offset = 0 ∧
      forwardSecret (multiplier : R) offset secret = 0) := by
  rintro ⟨hu, hs⟩
  apply forward_hint_secret_gap_ne_zero multiplier offset secret hidempotent
  rw [hu, hs]
  simp

@[simp]
theorem quadraticHint_zero_zero {R : Type} [Ring R] :
    quadraticHint (0 : R) 0 = 0 := by
  simp [quadraticHint]

/-! ## Theorem 10: normalization of a quadratic hint to an idempotent secret -/

/-- `β = (α-u)/2`, parameterized by a checked inverse of two. -/
def inverseTransformBeta {R : Type} [Ring R] (half alpha u : R) : R :=
  (alpha - u) * half

/-- `s' = (s+β)/α`. -/
def inverseTransformSecret {R : Type} [CommRing R]
    (half : R) (alpha : Rˣ) (u secret : R) : R :=
  (secret + inverseTransformBeta half (alpha : R) u) * (alpha⁻¹ : Rˣ)

/-- The public sample transformation from Figure 2. -/
def inverseTransform {R Row : Type} [CommRing R]
    (half : R) (alpha : Rˣ) (view : QuadraticHintView R Row) : RLWEView R Row where
  mask := fun i ↦ view.mask i * (alpha : R)
  body := fun i ↦ view.body i + view.mask i *
    inverseTransformBeta half (alpha : R) view.u

/-- Lemma 11: the discriminant of an honestly generated quadratic hint is a square. -/
theorem quadraticHint_discriminant {R : Type} [CommRing R] (u secret : R) :
    4 * quadraticHint u secret + u ^ 2 = (2 * secret - u) ^ 2 := by
  simp [quadraticHint]
  ring

/-- Lemma 14's transformed body identity. -/
theorem inverseTransform_real_body {R Row : Type} [CommRing R]
    (half : R) (alpha : Rˣ) (u secret : R) (mask error : Row → R) (i : Row) :
    (inverseTransform half alpha (realQuadraticHintView u mask secret error)).body i =
      (inverseTransform half alpha (realQuadraticHintView u mask secret error)).mask i *
        inverseTransformSecret half alpha u secret + error i := by
  have hunit : (alpha : R) * ((alpha⁻¹ : Rˣ) : R) = 1 := by simp
  simp only [inverseTransform, realQuadraticHintView, inverseTransformSecret,
    inverseTransformBeta]
  linear_combination
    -(mask i * (secret + ((alpha : R) - u) * half)) * hunit

/-- Lemma 14's algebraic core: a square root of the discriminant normalizes the secret to an
idempotent. -/
theorem inverseTransformSecret_idempotent {R : Type} [CommRing R]
    (half : R) (alpha : Rˣ) (u v secret : R)
    (hhalf : 2 * half = 1)
    (hhint : secret ^ 2 = u * secret + v)
    (hroot : (alpha : R) ^ 2 = 4 * v + u ^ 2) :
    inverseTransformSecret half alpha u secret ^ 2 =
      inverseTransformSecret half alpha u secret := by
  let beta := inverseTransformBeta half (alpha : R) u
  have hbeta : 2 * beta = (alpha : R) - u := by
    dsimp [beta, inverseTransformBeta]
    linear_combination ((alpha : R) - u) * hhalf
  have hfour :
      4 * ((secret + beta) ^ 2 - (alpha : R) * (secret + beta)) = 0 := by
    linear_combination 4 * hhint - hroot +
      (4 * secret + 2 * beta - (alpha : R) - u) * hbeta
  have hfourInv : (4 : R) * half ^ 2 = 1 := by
    linear_combination (2 * half + 1) * hhalf
  have hnumerator : (secret + beta) ^ 2 = (alpha : R) * (secret + beta) := by
    apply sub_eq_zero.mp
    calc
      (secret + beta) ^ 2 - (alpha : R) * (secret + beta) =
          ((4 : R) * half ^ 2) *
            ((secret + beta) ^ 2 - (alpha : R) * (secret + beta)) := by rw [hfourInv]; simp
      _ = half ^ 2 *
          (4 * ((secret + beta) ^ 2 - (alpha : R) * (secret + beta))) := by ring
      _ = 0 := by rw [hfour]; simp
  have hunit : (alpha : R) * ((alpha⁻¹ : Rˣ) : R) = 1 := by simp
  change ((secret + beta) * ((alpha⁻¹ : Rˣ) : R)) ^ 2 =
    (secret + beta) * ((alpha⁻¹ : Rˣ) : R)
  calc
    ((secret + beta) * ((alpha⁻¹ : Rˣ) : R)) ^ 2 =
        (secret + beta) ^ 2 * ((alpha⁻¹ : Rˣ) : R) ^ 2 := by ring
    _ = (alpha : R) * (secret + beta) * ((alpha⁻¹ : Rˣ) : R) ^ 2 := by
      rw [hnumerator]
    _ = (secret + beta) * ((alpha⁻¹ : Rˣ) : R) *
        ((alpha : R) * ((alpha⁻¹ : Rˣ) : R)) := by ring
    _ = (secret + beta) * ((alpha⁻¹ : Rˣ) : R) := by rw [hunit]; simp

/-! ## Theorem 15: use the final error as the new small secret -/

/-- Public transformation from Figure 3, parameterized by the invertible final mask. -/
def smallSecretTransform {R Row : Type} [CommRing R]
    (anchorMask : Rˣ) (anchorBody oldU oldV : R)
    (mask body : Row → R) : QuadraticHintView R Row where
  u := 2 * anchorBody - (anchorMask : R) * oldU
  v := (anchorMask : R) * anchorBody * oldU +
    (anchorMask : R) ^ 2 * oldV - anchorBody ^ 2
  mask := fun i ↦ -mask i * (anchorMask⁻¹ : Rˣ)
  body := fun i ↦ body i - (anchorBody * (anchorMask⁻¹ : Rˣ)) * mask i

/-- Lemma 17(1): the final error becomes the new secret. -/
theorem smallSecretTransform_real_body {R Row : Type} [CommRing R]
    (anchorMask : Rˣ) (oldU oldV oldSecret anchorError : R)
    (mask error : Row → R) (i : Row) :
    let anchorBody := (anchorMask : R) * oldSecret + anchorError
    (smallSecretTransform anchorMask anchorBody oldU oldV mask
        (fun j ↦ mask j * oldSecret + error j)).body i =
      (smallSecretTransform anchorMask anchorBody oldU oldV mask
        (fun j ↦ mask j * oldSecret + error j)).mask i * anchorError + error i := by
  have hunit : ((anchorMask : R) * ((anchorMask⁻¹ : Rˣ) : R)) = 1 := by simp
  dsimp [smallSecretTransform]
  linear_combination -(mask i * oldSecret) * hunit

/-- Lemma 17(2): the final error satisfies the transformed quadratic hint. -/
theorem smallSecretTransform_real_hint {R : Type} [CommRing R]
    (anchorMask : Rˣ) (oldU oldV oldSecret anchorError : R)
    (hOldHint : oldSecret ^ 2 = oldU * oldSecret + oldV) :
    let anchorBody := (anchorMask : R) * oldSecret + anchorError
    anchorError ^ 2 =
      (smallSecretTransform (Row := Fin 0) anchorMask anchorBody oldU oldV
        Fin.elim0 Fin.elim0).u * anchorError +
      (smallSecretTransform (Row := Fin 0) anchorMask anchorBody oldU oldV
        Fin.elim0 Fin.elim0).v := by
  dsimp [smallSecretTransform]
  linear_combination (anchorMask : R) ^ 2 * hOldHint

/-- Lemma 18's random-branch hint identity. -/
theorem smallSecretTransform_random_hint {R : Type} [CommRing R]
    (anchorMask : Rˣ) (anchorBody oldU oldSecret : R) :
    let oldV := quadraticHint oldU oldSecret
    let newSecret := anchorBody - (anchorMask : R) * oldSecret
    (smallSecretTransform (Row := Fin 0) anchorMask anchorBody oldU oldV
        Fin.elim0 Fin.elim0).v =
      quadraticHint
        (smallSecretTransform (Row := Fin 0) anchorMask anchorBody oldU oldV
          Fin.elim0 Fin.elim0).u
        newSecret := by
  dsimp [smallSecretTransform, quadraticHint]
  ring

/-! ## Theorem 19: exact secret randomization -/

/-- Public transformation that adds an independently sampled shift to the hidden secret. -/
def shiftQuadraticHintView {R Row : Type} [CommRing R]
    (shift : R) (view : QuadraticHintView R Row) : QuadraticHintView R Row where
  u := view.u + 2 * shift
  v := view.v - view.u * shift - shift ^ 2
  mask := view.mask
  body := fun i ↦ view.body i + view.mask i * shift

/-- The body encrypts the shifted secret with unchanged error. -/
theorem shiftQuadraticHintView_real_body {R Row : Type} [CommRing R]
    (shift u secret : R) (mask error : Row → R) (i : Row) :
    (shiftQuadraticHintView shift (realQuadraticHintView u mask secret error)).body i =
      (shiftQuadraticHintView shift (realQuadraticHintView u mask secret error)).mask i *
        (secret + shift) + error i := by
  simp [shiftQuadraticHintView, realQuadraticHintView]
  ring

/-- The transformed hint is exactly the quadratic hint of the shifted secret. -/
theorem shiftQuadraticHintView_real_hint {R Row : Type} [CommRing R]
    (shift u secret : R) (mask error : Row → R) :
    (shiftQuadraticHintView shift (realQuadraticHintView u mask secret error)).v =
      quadraticHint
        (shiftQuadraticHintView shift (realQuadraticHintView u mask secret error)).u
        (secret + shift) := by
  simp [shiftQuadraticHintView, realQuadraticHintView, quadraticHint]
  ring

/-! ### Exact distribution transports for the corrected same-sample Theorem 19 -/

/-- Joint map `(u,t) ↦ (u+2t,s+t)` used to randomize a fixed small secret. -/
def realShiftCoinsMap {R : Type} [Ring R] (secret : R) : R × R → R × R :=
  fun coins ↦ (coins.1 + 2 * coins.2, secret + coins.2)

/-- Explicit inverse of `realShiftCoinsMap`. -/
def realShiftCoinsMapInv {R : Type} [Ring R] (secret : R) : R × R → R × R :=
  fun output ↦
    (output.1 - 2 * (output.2 - secret), output.2 - secret)

@[simp]
theorem realShiftCoinsMapInv_realShiftCoinsMap {R : Type} [CommRing R]
    (secret : R) (coins : R × R) :
    realShiftCoinsMapInv secret (realShiftCoinsMap secret coins) = coins := by
  rcases coins with ⟨u, shift⟩
  apply Prod.ext <;> simp [realShiftCoinsMapInv, realShiftCoinsMap]

@[simp]
theorem realShiftCoinsMap_realShiftCoinsMapInv {R : Type} [CommRing R]
    (secret : R) (output : R × R) :
    realShiftCoinsMap secret (realShiftCoinsMapInv secret output) = output := by
  rcases output with ⟨u, shiftedSecret⟩
  apply Prod.ext <;> simp [realShiftCoinsMapInv, realShiftCoinsMap]

theorem realShiftCoinsMap_bijective {R : Type} [CommRing R] (secret : R) :
    Function.Bijective (realShiftCoinsMap secret) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨realShiftCoinsMapInv secret, realShiftCoinsMapInv_realShiftCoinsMap secret,
      realShiftCoinsMap_realShiftCoinsMapInv secret⟩

/-- For every fixed starting secret, the shifted secret and transformed public `u` are jointly
uniform.  This is the real-branch distribution argument omitted in Theorem 19. -/
theorem realShiftCoins_uniform_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R] (secret : R) :
    evalDist (($ᵗ (R × R)) >>= fun coins ↦ pure (realShiftCoinsMap secret coins)) =
      evalDist ($ᵗ (R × R)) := by
  apply evalDist_ext
  intro output
  simpa [monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := R × R) (β := R × R)
      (realShiftCoinsMap secret) (realShiftCoinsMap_bijective secret)
      (fun value ↦ pure value) output)

/-- For a fixed randomization shift, transport the random-branch hint witness `(u,z)`. -/
def randomHintShiftMap {R : Type} [Ring R] (shift : R) : R × R → R × R :=
  fun hint ↦ (hint.1 + 2 * shift, hint.2 + shift)

/-- Inverse of `randomHintShiftMap`. -/
def randomHintShiftMapInv {R : Type} [Ring R] (shift : R) : R × R → R × R :=
  fun hint ↦ (hint.1 - 2 * shift, hint.2 - shift)

theorem randomHintShiftMap_bijective {R : Type} [CommRing R] (shift : R) :
    Function.Bijective (randomHintShiftMap shift) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨randomHintShiftMapInv shift, ?_, ?_⟩
  · rintro ⟨u, z⟩
    apply Prod.ext <;> simp [randomHintShiftMapInv, randomHintShiftMap]
  · rintro ⟨u, z⟩
    apply Prod.ext <;> simp [randomHintShiftMapInv, randomHintShiftMap]

theorem randomHintShiftMap_uniform_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R] (shift : R) :
    evalDist (($ᵗ (R × R)) >>= fun hint ↦ pure (randomHintShiftMap shift hint)) =
      evalDist ($ᵗ (R × R)) := by
  apply evalDist_ext
  intro output
  simpa [monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := R × R) (β := R × R)
      (randomHintShiftMap shift) (randomHintShiftMap_bijective shift)
      (fun value ↦ pure value) output)

/-- For fixed shift, add `a*t` to every random RLWE body. -/
def randomBatchShiftMap {R Row : Type} [Ring R] (shift : R) :
    RLWEView R Row → RLWEView R Row :=
  fun view ↦ ⟨view.mask, fun i ↦ view.body i + view.mask i * shift⟩

/-- Explicit inverse of `randomBatchShiftMap`. -/
def randomBatchShiftMapInv {R Row : Type} [Ring R] (shift : R) :
    RLWEView R Row → RLWEView R Row :=
  fun view ↦ ⟨view.mask, fun i ↦ view.body i - view.mask i * shift⟩

theorem randomBatchShiftMap_bijective {R Row : Type} [CommRing R] (shift : R) :
    Function.Bijective (randomBatchShiftMap (Row := Row) shift) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨randomBatchShiftMapInv shift, ?_, ?_⟩
  · intro view
    apply RLWEView.ext
    · rfl
    · funext i
      simp [randomBatchShiftMapInv, randomBatchShiftMap]
  · intro view
    apply RLWEView.ext
    · rfl
    · funext i
      simp [randomBatchShiftMapInv, randomBatchShiftMap]

/-- The random RLWE batch remains exactly uniform after the secret-shift body correction. -/
theorem randomBatchShiftMap_uniform_evalDist {R Row : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    [Finite Row] [DecidableEq Row] [SampleableType (RLWEView R Row)] (shift : R) :
    evalDist (($ᵗ (RLWEView R Row)) >>= fun view ↦ pure (randomBatchShiftMap shift view)) =
      evalDist ($ᵗ (RLWEView R Row)) := by
  apply evalDist_ext
  intro output
  simpa [monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := RLWEView R Row) (β := RLWEView R Row)
      (randomBatchShiftMap shift) (randomBatchShiftMap_bijective shift)
      (fun value ↦ pure value) output)

/-! ## Binary-NTT rerandomization for search-to-decision -/

/-- XOR of two binary NTT-coordinate vectors. -/
def binaryVectorXor {Slot : Type} (left right : Slot → Bool) : Slot → Bool :=
  fun slot ↦ xor (left slot) (right slot)

@[simp]
theorem binaryVectorXor_self_left {Slot : Type}
    (left right : Slot → Bool) :
    binaryVectorXor left (binaryVectorXor left right) = right := by
  funext slot
  simp [binaryVectorXor]

@[simp]
theorem binaryVectorXor_self_right {Slot : Type}
    (left right : Slot → Bool) :
    binaryVectorXor (binaryVectorXor left right) right = left := by
  funext slot
  simp [binaryVectorXor]

/-- XOR by a fixed vector is a permutation, with itself as inverse. -/
theorem binaryVectorXor_bijective {Slot : Type} (fixed : Slot → Bool) :
    Function.Bijective (binaryVectorXor fixed) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨binaryVectorXor fixed, binaryVectorXor_self_left fixed,
      binaryVectorXor_self_left fixed⟩

/-- Lemma 21's secret-law claim: XOR with a uniformly sampled binary vector produces the
uniform Binary-NTT coordinate law for every fixed binary secret. -/
theorem binaryVectorXor_uniform_evalDist {Slot : Type}
    [Fintype Slot] [DecidableEq Slot] (secret : Slot → Bool) :
    evalDist (($ᵗ (Slot → Bool)) >>= fun coin ↦ pure (binaryVectorXor secret coin)) =
      evalDist ($ᵗ (Slot → Bool)) := by
  apply evalDist_ext
  intro output
  simpa [monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := Slot → Bool) (β := Slot → Bool)
      (binaryVectorXor secret) (binaryVectorXor_bijective secret)
      (fun value ↦ pure value) output)

/-- Coordinatewise XOR written as a ring polynomial.  On idempotents this is Boolean XOR. -/
def idempotentXor {R : Type} [Ring R] (left right : R) : R :=
  left + right - 2 * left * right

/-- XOR preserves idempotence. -/
theorem idempotentXor_idempotent {R : Type} [CommRing R] (left right : R)
    (hleft : left ^ 2 = left) (hright : right ^ 2 = right) :
    idempotentXor left right ^ 2 = idempotentXor left right := by
  simp only [idempotentXor]
  linear_combination (1 - 2 * right) ^ 2 * hleft + hright

/-- The mask sign used by Lemma 21. -/
def xorMaskMultiplier {R : Type} [Ring R] (coin : R) : R :=
  1 - 2 * coin

/-- Lemma 21's pointwise sample identity. -/
theorem xor_rerandomize_sample {R : Type} [CommRing R]
    (mask secret error coin : R)
    (_hsecret : secret ^ 2 = secret) (hcoin : coin ^ 2 = coin) :
    (mask * secret + error) - mask * coin =
      (mask * xorMaskMultiplier coin) * idempotentXor secret coin + error := by
  simp only [xorMaskMultiplier, idempotentXor]
  linear_combination 2 * mask * (1 - 2 * secret) * hcoin

/-- The rerandomization mask multiplier is a unit, so it preserves a uniform mask exactly. -/
theorem xorMaskMultiplier_isUnit {R : Type} [CommRing R] (coin : R)
    (hcoin : coin ^ 2 = coin) : IsUnit (xorMaskMultiplier coin) := by
  exact isUnit_one_sub_two_mul coin hcoin

/-! ### Hybrid and automorphism premises in Theorem 20 -/

/-- Endpoint distance is bounded by the sum of the adjacent hybrid distances. -/
theorem abs_sub_le_sum_adjacent (values : ℕ → ℝ) (count : ℕ) :
    |values 0 - values count| ≤
      ∑ index ∈ Finset.range count, |values index - values (index + 1)| := by
  rw [← Finset.sum_range_sub' values count]
  exact Finset.abs_sum_le_sum_abs
    (fun index ↦ values index - values (index + 1)) (Finset.range count)

/-- The hybrid lemma used in Theorem 20: one binary NTT coordinate retains at least the average
endpoint gap. -/
theorem exists_adjacent_gap_ge_average
    (values : ℕ → ℝ) (count : ℕ) (hCount : 0 < count) :
    ∃ index : Fin count,
      |values 0 - values count| / (count : ℝ) ≤
        |values index.val - values (index.val + 1)| := by
  let endpointGap := |values 0 - values count|
  have hConstantSum :
      (∑ _index ∈ Finset.range count, endpointGap / (count : ℝ)) = endpointGap := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  by_contra hNoIndex
  push Not at hNoIndex
  have hStrict :
      (∑ index ∈ Finset.range count, |values index - values (index + 1)|) <
        ∑ _index ∈ Finset.range count, endpointGap / (count : ℝ) := by
    apply Finset.sum_lt_sum
    · intro index hindex
      have hlt : index < count := Finset.mem_range.mp hindex
      exact le_of_lt (hNoIndex ⟨index, hlt⟩)
    · exact ⟨0, Finset.mem_range.mpr hCount, hNoIndex ⟨0, hCount⟩⟩
  rw [hConstantSum] at hStrict
  exact (not_lt_of_ge (abs_sub_le_sum_adjacent values count)) hStrict

/-- The error-law hypothesis silently used by Lemma 23.  For the paper's coefficientwise IID
noise, it follows from coefficient symmetry because every odd cyclotomic automorphism is a signed
coefficient permutation. -/
def ErrorAutomorphismInvariant {R Coordinate : Type}
    (errorSampler : ProbComp R) (automorphism : Coordinate → R → R) : Prop :=
  ∀ coordinate,
    evalDist (errorSampler >>= fun error ↦ pure (automorphism coordinate error)) =
      evalDist errorSampler

/-- A checked finite interface for the non-algebraic parts of the paper's search-to-decision
argument.  `randomizationLaw` is supplied by `binaryVectorXor_uniform_evalDist`; the remaining
fields are the coordinate guess/check and fresh-sample amplification claims. -/
structure SearchToDecisionCertificate (Secret View : Type) [DecidableEq Secret] where
  decisionProblem : DecisionProblem View
  searchSampler : ProbComp (Secret × View)
  recover : Distinguisher View → View → ProbComp Secret
  loss : Distinguisher View → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le_failure_add_loss : ∀ distinguisher,
    advantage decisionProblem distinguisher ≤
      (1 - (Pr[= true | do
        let secretAndView ← searchSampler
        let guess ← recover distinguisher secretAndView.2
        return decide (guess = secretAndView.1)]).toReal) + loss distinguisher

/-- Corrected Theorem 20 interface.  In addition to the finite recovery certificate, it requires
the automorphism-invariance hypothesis used in Lemma 23 and a positive coordinate count. -/
structure CorrectedSearchToDecisionCertificate
    (Secret View Error Coordinate : Type) [DecidableEq Secret]
    extends SearchToDecisionCertificate Secret View where
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  errorSampler : ProbComp Error
  automorphism : Coordinate → Error → Error
  errorInvariant : ErrorAutomorphismInvariant errorSampler automorphism

/-! ## Constant-probability abort accounting -/

/-- The arithmetic used in Theorems 10 and 15: invoking an adversary with probability at least
`1/4` and guessing randomly otherwise retains at least one quarter of its success bias. -/
theorem quarter_success_bias
    (success epsilon goodProbability : ℝ)
    (hSuccess : 1 / 2 + epsilon ≤ success)
    (hGood : 1 / 4 ≤ goodProbability)
    (_hGoodOne : goodProbability ≤ 1)
    (hEpsilon : 0 ≤ epsilon) :
    1 / 2 + epsilon / 4 ≤
      goodProbability * success + (1 - goodProbability) * (1 / 2) := by
  nlinarith

/-- Numerical part of Lemmas 12 and 16.  The paper's divisibility hypothesis implies
`q ≥ 2N+1`; Bernoulli's inequality then gives a stronger `1/2` lower bound, hence the stated
quarter bound. -/
theorem nonzeroCoordinatesProbability_ge_quarter (N q : ℕ) (_hN : 0 < N)
    (hq : 2 * N < q) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ N := by
  have hqnat : 0 < q := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqnat
  have ha : (-2 : ℝ) ≤ -(1 / (q : ℝ)) := by
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.succ_le_iff.mpr (by omega : 0 < q))
    have hinv : 1 / (q : ℝ) ≤ 1 := (div_le_one hqpos).mpr hqone
    linarith
  have hbernoulli := one_add_mul_le_pow ha N
  have hcast : (2 : ℝ) * N < q := by exact_mod_cast hq
  have hratio : (N : ℝ) / q < 1 / 2 := by
    rw [div_lt_iff₀ hqpos]
    nlinarith
  have hhalf : (1 / 2 : ℝ) < 1 - (N : ℝ) / q := by linarith
  have hone : 1 + (N : ℝ) * (-(1 / (q : ℝ))) = 1 - (N : ℝ) / q := by
    field_simp
    ring
  rw [hone] at hbernoulli
  have hquarter : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  exact hquarter.trans (hhalf.le.trans hbernoulli)

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity
