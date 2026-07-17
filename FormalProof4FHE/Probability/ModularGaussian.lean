/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import LatticeCrypto.DiscreteGaussian
import Mathlib.Data.ZMod.ValMinAbs
import VCVio.EvalDist.TVDist

/-!
# Modular Discrete Gaussians

This module defines the exact ideal discrete Gaussian over `ZMod q` obtained by sampling the
centered integer discrete Gaussian and reducing modulo `q`.  A torus standard deviation `alpha`
is converted to the integer standard deviation `alpha * q`; this is the standard-deviation
convention used by the concrete TFHE entries in `lattice-estimator`.

The module also distinguishes two noise-absorption quantities:

* `conditionalShiftCost` conditions on the full summed narrow-error shift before taking TV.  This
  is the sound quantity when the public transcript may reveal information about that shift.
* `convolutionDistance` mixes over the summed shift before taking TV.  It retains both additive
  cancellation and mixture overlap, and is formally no larger than the conditional cost.

These are mathematical `PMF`s, not executable `ProbComp` samplers.  The distinction is necessary:
an ideal discrete Gaussian has infinite support, whereas a `ProbComp` computation has finite
support.  The finite reduction therefore applies directly to an implemented sampler, while this
module specifies the exact ideal distribution against which such a sampler can be compared.
-/

open BigOperators

namespace FormalProof4FHE.ModularGaussian

/-- Push the centered integer discrete Gaussian forward to `ZMod q`. -/
noncomputable def distribution (q : ℕ) [NeZero q] (sigma : ℝ) (hsigma : 0 < sigma) :
    PMF (ZMod q) :=
  (fun z : ℤ ↦ (z : ZMod q)) <$> LatticeCrypto.discreteGaussianDist sigma 0 hsigma

theorem distribution_apply (q : ℕ) [NeZero q] (sigma : ℝ) (hsigma : 0 < sigma)
    (residue : ZMod q) :
    distribution q sigma hsigma residue =
      ∑' z : ℤ, if residue = (z : ZMod q) then
        ENNReal.ofReal (LatticeCrypto.discreteGaussianPMF sigma 0 z) else 0 := by
  rw [distribution, PMF.monad_map_eq_map, PMF.map_apply]
  apply tsum_congr
  intro z
  by_cases h : residue = (z : ZMod q)
  · rw [if_pos h, if_pos h]
    change ENNReal.ofReal (LatticeCrypto.discreteGaussianPMF sigma 0 z) = _
    rfl
  · rw [if_neg h, if_neg h]

/-- Integer-domain standard deviation corresponding to torus standard deviation `alpha`. -/
def integerStddev (q : ℕ) (alpha : ℝ) : ℝ := alpha * q

theorem integerStddev_pos (q : ℕ) [NeZero q] {alpha : ℝ} (halpha : 0 < alpha) :
    0 < integerStddev q alpha := by
  unfold integerStddev
  exact mul_pos halpha (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))

/-- The exact mod-`q` ideal discrete Gaussian for torus standard deviation `alpha`.
The integer lift has standard deviation `alpha * q`. -/
noncomputable def torusDistribution (q : ℕ) [NeZero q]
    (alpha : ℝ) (halpha : 0 < alpha) : PMF (ZMod q) :=
  distribution q (integerStddev q alpha) (integerStddev_pos q halpha)

/-- Translate a PMF in an additive group. -/
noncomputable def translate {G : Type} [Add G] (shift : G) (p : PMF G) : PMF G :=
  (fun value ↦ shift + value) <$> p

/-- Exact total-variation cost of a fixed translation. -/
noncomputable def shiftDistance {G : Type} [Add G] (p : PMF G) (shift : G) : ℝ :=
  PMF.tvDist (translate shift p) p

@[simp]
theorem shiftDistance_zero {G : Type} [AddGroup G] (p : PMF G) :
    shiftDistance p 0 = 0 := by
  simp [shiftDistance, translate]

/-- Mapping both PMFs through an equivalence preserves total variation exactly. -/
theorem tvDist_map_equiv {A B : Type} (equiv : A ≃ B) (p q : PMF A) :
    PMF.tvDist (equiv <$> p) (equiv <$> q) = PMF.tvDist p q := by
  apply le_antisymm
  · exact PMF.tvDist_map_le equiv p q
  · have h := PMF.tvDist_map_le equiv.symm (equiv <$> p) (equiv <$> q)
    have hp : equiv.symm <$> (equiv <$> p) = p := by
      simp only [PMF.monad_map_eq_map]
      rw [PMF.map_comp]
      rw [show equiv.symm ∘ equiv = id by
        funext value
        exact equiv.symm_apply_apply value]
      exact PMF.map_id p
    have hq : equiv.symm <$> (equiv <$> q) = q := by
      simp only [PMF.monad_map_eq_map]
      rw [PMF.map_comp]
      rw [show equiv.symm ∘ equiv = id by
        funext value
        exact equiv.symm_apply_apply value]
      exact PMF.map_id q
    rwa [hp, hq] at h

/-- Translation costs are subadditive; no norm or moment hypothesis is needed. -/
theorem shiftDistance_add_le {G : Type} [AddCommGroup G]
    (p : PMF G) (first second : G) :
    shiftDistance p (first + second) ≤
      shiftDistance p first + shiftDistance p second := by
  let firstShifted := translate first p
  have htranslate :
      PMF.tvDist (translate (first + second) p) firstShifted ≤
        shiftDistance p second := by
    have hdata := PMF.tvDist_map_le (fun value : G ↦ first + value)
      (translate second p) p
    simpa only [translate, Functor.map_map, Function.comp_apply, add_assoc,
      firstShifted, shiftDistance] using hdata
  exact (PMF.tvDist_triangle _ firstShifted _).trans
    (add_le_add htranslate le_rfl) |>.trans_eq (add_comm _ _)

theorem translate_distribution_intCast (q : ℕ) [NeZero q]
    (sigma : ℝ) (hsigma : 0 < sigma) (shift : ℤ) :
    translate (shift : ZMod q) (distribution q sigma hsigma) =
      (fun z : ℤ ↦ (z : ZMod q)) <$>
        translate shift (LatticeCrypto.discreteGaussianDist sigma 0 hsigma) := by
  simp [translate, distribution, Functor.map_map, add_comm]

/-- Reducing modulo `q` cannot increase the translation distance. -/
theorem shiftDistance_distribution_intCast_le (q : ℕ) [NeZero q]
    (sigma : ℝ) (hsigma : 0 < sigma) (shift : ℤ) :
    shiftDistance (distribution q sigma hsigma) (shift : ZMod q) ≤
      shiftDistance (LatticeCrypto.discreteGaussianDist sigma 0 hsigma) shift := by
  rw [shiftDistance, translate_distribution_intCast]
  exact PMF.tvDist_map_le (fun z : ℤ ↦ (z : ZMod q))
    (translate shift (LatticeCrypto.discreteGaussianDist sigma 0 hsigma))
    (LatticeCrypto.discreteGaussianDist sigma 0 hsigma)

/-- Every modular shift is bounded using its centered, minimum-absolute-value integer lift. -/
theorem shiftDistance_distribution_le_valMinAbs (q : ℕ) [NeZero q]
    (sigma : ℝ) (hsigma : 0 < sigma) (shift : ZMod q) :
    shiftDistance (distribution q sigma hsigma) shift ≤
      shiftDistance (LatticeCrypto.discreteGaussianDist sigma 0 hsigma)
        shift.valMinAbs := by
  simpa only [ZMod.coe_valMinAbs] using
    shiftDistance_distribution_intCast_le q sigma hsigma shift.valMinAbs

private theorem etvDist_bind_left_le {A B : Type}
    (p : PMF A) (left right : A → PMF B) :
    (p.bind left).etvDist (p.bind right) ≤
      ∑' value, (left value).etvDist (right value) * p value := by
  have hrhs :
      (∑' value, (left value).etvDist (right value) * p value) =
        (∑' value,
          (∑' output, ENNReal.absDiff ((left value) output) ((right value) output)) *
            p value) / 2 := by
    simp only [PMF.etvDist, div_eq_mul_inv, ← ENNReal.tsum_mul_right, mul_right_comm]
  rw [PMF.etvDist, hrhs]
  refine ENNReal.div_le_div_right ?_ 2
  calc
    (∑' output,
      ENNReal.absDiff (∑' value, p value * (left value) output)
        (∑' value, p value * (right value) output)) ≤
        ∑' output, ∑' value,
          ENNReal.absDiff (p value * (left value) output)
            (p value * (right value) output) :=
      ENNReal.tsum_le_tsum fun output ↦ ENNReal.absDiff_tsum_le _ _
    _ ≤ ∑' output, ∑' value,
        ENNReal.absDiff ((left value) output) ((right value) output) * p value :=
      ENNReal.tsum_le_tsum fun output ↦ ENNReal.tsum_le_tsum fun value ↦ by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          ENNReal.absDiff_mul_right_le
            ((left value) output) ((right value) output) (p value)
    _ = ∑' value, ∑' output,
        ENNReal.absDiff ((left value) output) ((right value) output) * p value :=
      ENNReal.tsum_comm
    _ = ∑' value,
        (∑' output, ENNReal.absDiff ((left value) output) ((right value) output)) *
          p value := by
      simp_rw [ENNReal.tsum_mul_right]

/-- TV of two mixtures with the same mixing PMF is bounded by the exact expected conditional TV. -/
theorem tvDist_bind_left_le {A B : Type}
    (p : PMF A) (left right : A → PMF B) :
    PMF.tvDist (p.bind left) (p.bind right) ≤
      ∑' value, (p value).toReal * PMF.tvDist (left value) (right value) := by
  simp only [PMF.tvDist]
  refine le_trans (ENNReal.toReal_mono ?_ (etvDist_bind_left_le p left right)) ?_
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans
        (ENNReal.tsum_le_tsum fun value ↦
          mul_le_mul' (PMF.etvDist_le_one _ _) le_rfl)
        (by simp [p.tsum_coe]))
  · refine le_of_eq ?_
    calc
      (∑' value, (left value).etvDist (right value) * p value).toReal =
          ∑' value,
            ((left value).etvDist (right value) * p value).toReal :=
        ENNReal.tsum_toReal_eq fun value ↦
          ENNReal.mul_ne_top (PMF.etvDist_ne_top _ _) (PMF.apply_ne_top _ _)
      _ = ∑' value,
          (p value).toReal * PMF.tvDist (left value) (right value) := by
        refine tsum_congr fun value ↦ ?_
        rw [ENNReal.toReal_mul, PMF.tvDist]
        ac_rfl

/-- Independent samples from a PMF, represented as a finite function. -/
noncomputable def iid {A : Type} : (count : ℕ) → PMF A → PMF (Fin count → A)
  | 0, _ => pure Fin.elim0
  | count + 1, p => p.bind fun head =>
      (Fin.cons head) <$> iid count p

/-- Sum of `count` independent additive errors. -/
noncomputable def sumIID {G : Type} [AddCommMonoid G]
    (count : ℕ) (p : PMF G) : PMF G :=
  (fun errors ↦ ∑ index, errors index) <$> iid count p

/-- Exact distance after mixing over the sum of `count` independent narrow errors.
This is the convolution-aware quantity: cancellation and mixture overlap occur before TV. -/
noncomputable def convolutionDistance {G : Type} [AddCommGroup G]
    (count : ℕ) (narrow wide : PMF G) : ℝ :=
  PMF.tvDist
    ((sumIID count narrow).bind fun shift ↦ translate shift wide)
    wide

/-- Conditional expected-shift cost before mixture overlap is exploited.  The shift is already
the full sum, so additive cancellation among the narrow errors is retained. -/
noncomputable def conditionalShiftCost {G : Type} [AddCommGroup G]
    (count : ℕ) (narrow wide : PMF G) : ℝ :=
  ∑' shift, (sumIID count narrow shift).toReal * shiftDistance wide shift

/-- Convolving before taking TV is never worse than conditioning on and revealing the shift. -/
theorem convolutionDistance_le_conditionalShiftCost {G : Type} [AddCommGroup G]
    (count : ℕ) (narrow wide : PMF G) :
    convolutionDistance count narrow wide ≤
      conditionalShiftCost count narrow wide := by
  let aggregate := sumIID count narrow
  calc
    convolutionDistance count narrow wide =
        PMF.tvDist
          (aggregate.bind fun shift ↦ translate shift wide)
          (aggregate.bind fun _shift ↦ wide) := by
      simp [convolutionDistance, aggregate]
    _ ≤ ∑' shift, (aggregate shift).toReal *
        PMF.tvDist (translate shift wide) wide :=
      tvDist_bind_left_le aggregate (fun shift ↦ translate shift wide) (fun _shift ↦ wide)
    _ = conditionalShiftCost count narrow wide := by
      rfl

/-- The conditional expected-shift cost is a probability-scale quantity. -/
theorem conditionalShiftCost_le_one {G : Type} [AddCommGroup G]
    (count : ℕ) (narrow wide : PMF G) :
    conditionalShiftCost count narrow wide ≤ 1 := by
  let aggregate := sumIID count narrow
  have hprobFinite : ∀ shift, aggregate shift ≠ ⊤ := fun shift ↦
    PMF.apply_ne_top aggregate shift
  have hprobSummable : Summable (fun shift ↦ (aggregate shift).toReal) :=
    ENNReal.summable_toReal aggregate.tsum_coe_ne_top
  have hprobSum : (∑' shift, (aggregate shift).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq hprobFinite, aggregate.tsum_coe, ENNReal.toReal_one]
  have hnonneg : ∀ shift,
      0 ≤ (aggregate shift).toReal * shiftDistance wide shift := fun shift ↦
    mul_nonneg ENNReal.toReal_nonneg (PMF.tvDist_nonneg _ _)
  have hle : ∀ shift,
      (aggregate shift).toReal * shiftDistance wide shift ≤
        (aggregate shift).toReal := fun shift ↦
    mul_le_of_le_one_right ENNReal.toReal_nonneg (PMF.tvDist_le_one _ _)
  have hcostSummable :
      Summable (fun shift ↦ (aggregate shift).toReal * shiftDistance wide shift) :=
    Summable.of_nonneg_of_le hnonneg hle hprobSummable
  unfold conditionalShiftCost
  change (∑' shift, (aggregate shift).toReal * shiftDistance wide shift) ≤ 1
  exact (Summable.tsum_le_tsum hle hcostSummable hprobSummable).trans_eq hprobSum

theorem convolutionDistance_le_one {G : Type} [AddCommGroup G]
    (count : ℕ) (narrow wide : PMF G) :
    convolutionDistance count narrow wide ≤ 1 := by
  exact PMF.tvDist_le_one _ _

@[simp]
theorem convolutionDistance_zero {G : Type} [AddCommGroup G]
    (narrow wide : PMF G) : convolutionDistance 0 narrow wide = 0 := by
  have hsum : sumIID 0 narrow = pure 0 := by
    unfold sumIID iid
    rw [PMF.monad_map_eq_map]
    calc
      PMF.map (fun errors : Fin 0 → G ↦ ∑ index, errors index)
          (pure Fin.elim0) =
          pure ((fun errors : Fin 0 → G ↦ ∑ index, errors index) Fin.elim0) :=
        PMF.pure_map _ _
      _ = pure 0 := by simp
  have htranslate : translate (0 : G) wide = wide := by
    unfold translate
    rw [PMF.monad_map_eq_map]
    rw [show (fun value : G ↦ 0 + value) = id by funext value; simp]
    exact PMF.map_id wide
  unfold convolutionDistance
  rw [hsum]
  have hbind :
      ((PMF.pure 0 : PMF G).bind fun shift ↦ translate shift wide) =
        translate 0 wide := PMF.pure_bind _ _
  change PMF.tvDist
    ((PMF.pure 0 : PMF G).bind fun shift ↦ translate shift wide) wide = 0
  rw [hbind, htranslate, PMF.tvDist_self]

/-- Concrete convolution-aware cost for modular ideal discrete Gaussians. -/
noncomputable def gaussianConvolutionDistance (q count : ℕ) [NeZero q]
    (narrowAlpha wideAlpha : ℝ) (hnarrow : 0 < narrowAlpha) (hwide : 0 < wideAlpha) : ℝ :=
  convolutionDistance count
    (torusDistribution q narrowAlpha hnarrow)
    (torusDistribution q wideAlpha hwide)

/-- Conditional expected-shift cost for the same modular ideal discrete Gaussians. -/
noncomputable def gaussianConditionalShiftCost (q count : ℕ) [NeZero q]
    (narrowAlpha wideAlpha : ℝ) (hnarrow : 0 < narrowAlpha) (hwide : 0 < wideAlpha) : ℝ :=
  conditionalShiftCost count
    (torusDistribution q narrowAlpha hnarrow)
    (torusDistribution q wideAlpha hwide)

/-- The concrete Gaussian convolution cost is formally no larger than its conditional cost. -/
theorem gaussianConvolutionDistance_le_conditionalShiftCost
    (q count : ℕ) [NeZero q]
    (narrowAlpha wideAlpha : ℝ) (hnarrow : 0 < narrowAlpha) (hwide : 0 < wideAlpha) :
    gaussianConvolutionDistance q count narrowAlpha wideAlpha hnarrow hwide ≤
      gaussianConditionalShiftCost q count narrowAlpha wideAlpha hnarrow hwide :=
  convolutionDistance_le_conditionalShiftCost count _ _

theorem gaussianConvolutionDistance_le_one (q count : ℕ) [NeZero q]
    (narrowAlpha wideAlpha : ℝ) (hnarrow : 0 < narrowAlpha) (hwide : 0 < wideAlpha) :
    gaussianConvolutionDistance q count narrowAlpha wideAlpha hnarrow hwide ≤ 1 :=
  convolutionDistance_le_one count _ _

theorem gaussianConditionalShiftCost_le_one (q count : ℕ) [NeZero q]
    (narrowAlpha wideAlpha : ℝ) (hnarrow : 0 < narrowAlpha) (hwide : 0 < wideAlpha) :
    gaussianConditionalShiftCost q count narrowAlpha wideAlpha hnarrow hwide ≤ 1 :=
  conditionalShiftCost_le_one count _ _

end FormalProof4FHE.ModularGaussian
