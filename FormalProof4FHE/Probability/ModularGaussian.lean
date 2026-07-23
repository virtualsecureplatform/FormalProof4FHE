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

@[simp]
theorem translate_int_one_apply (p : PMF ℤ) (value : ℤ) :
    translate 1 p value = p (value - 1) := by
  classical
  simp only [translate, PMF.monad_map_eq_map, PMF.map_apply]
  have hfiber : ∀ input : ℤ, (value = 1 + input) = (input = value - 1) := by
    intro input
    apply propext
    omega
  simp_rw [hfiber]
  simp

/-- Real-valued `L¹/2` formula for total variation. -/
theorem tvDist_eq_half_tsum_abs_toReal {A : Type} (p q : PMF A) :
    PMF.tvDist p q =
      (∑' value, |(p value).toReal - (q value).toReal|) / 2 := by
  rw [PMF.tvDist, PMF.etvDist, ENNReal.toReal_div]
  rw [ENNReal.tsum_toReal_eq]
  · simp_rw [ENNReal.absDiff_toReal (PMF.apply_ne_top p _) (PMF.apply_ne_top q _)]
    norm_num
  · intro value
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top p value, PMF.apply_ne_top q value⟩)
      (ENNReal.absDiff_le_add (p value) (q value))

/-- A centered integer discrete Gaussian is symmetric. -/
theorem discreteGaussianPMF_zero_neg (sigma : ℝ) (value : ℤ) :
    LatticeCrypto.discreteGaussianPMF sigma 0 (-value) =
      LatticeCrypto.discreteGaussianPMF sigma 0 value := by
  unfold LatticeCrypto.discreteGaussianPMF LatticeCrypto.discreteGaussianWeight
  congr 2
  push_cast
  ring

/-- Reducing a centered integer discrete Gaussian modulo `q` preserves negation symmetry. -/
theorem distribution_apply_neg
    (q : ℕ) [NeZero q] (sigma : ℝ) (hsigma : 0 < sigma)
    (residue : ZMod q) :
    distribution q sigma hsigma (-residue) = distribution q sigma hsigma residue := by
  rw [distribution_apply, distribution_apply]
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro value
  simp only [Equiv.neg_apply, Int.cast_neg]
  rw [discreteGaussianPMF_zero_neg]
  congr 1
  apply propext
  constructor
  · intro h
    have := congrArg Neg.neg h
    simpa using this
  · intro h
    simpa using congrArg Neg.neg h

/-- The torus-scaled modular discrete Gaussian is exactly invariant under negation. -/
theorem torusDistribution_apply_neg
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha)
    (residue : ZMod q) :
    torusDistribution q alpha halpha (-residue) =
      torusDistribution q alpha halpha residue := by
  exact distribution_apply_neg q (integerStddev q alpha)
    (integerStddev_pos q halpha) residue

/-- On the nonnegative integers, a centered discrete Gaussian decreases away from zero. -/
theorem discreteGaussianPMF_zero_nat_succ_le
    (sigma : ℝ) (hsigma : 0 < sigma) (index : ℕ) :
    LatticeCrypto.discreteGaussianPMF sigma 0 (index + 1) ≤
      LatticeCrypto.discreteGaussianPMF sigma 0 index := by
  unfold LatticeCrypto.discreteGaussianPMF
  rw [div_le_div_iff_of_pos_right
    (LatticeCrypto.discreteGaussianSum_pos sigma 0 hsigma)]
  unfold LatticeCrypto.discreteGaussianWeight
  apply Real.exp_le_exp.mpr
  rw [div_le_div_iff_of_pos_right (show 0 < 2 * sigma ^ 2 by positivity)]
  push_cast
  have hindex : 0 ≤ (index : ℝ) := Nat.cast_nonneg index
  nlinarith

set_option maxHeartbeats 2000000 in
/-- The `L¹` difference between a centered integer discrete Gaussian and its unit translate is
twice its mass at zero. -/
theorem tsum_abs_translate_discreteGaussian_unit_eq_two_mul_mass_zero
    (sigma : ℝ) (hsigma : 0 < sigma) :
    (∑' value : ℤ,
      |(translate 1 (LatticeCrypto.discreteGaussianDist sigma 0 hsigma) value).toReal -
        (LatticeCrypto.discreteGaussianDist sigma 0 hsigma value).toReal|) =
      2 * LatticeCrypto.discreteGaussianPMF sigma 0 0 := by
  let p := LatticeCrypto.discreteGaussianDist sigma 0 hsigma
  let mass := LatticeCrypto.discreteGaussianPMF sigma 0
  have hp_apply (value : ℤ) : (p value).toReal = mass value := by
    exact LatticeCrypto.discreteGaussianDist_apply sigma 0 hsigma value
  have htranslate (value : ℤ) :
      (translate 1 p value).toReal = mass (value - 1) := by
    rw [translate_int_one_apply, hp_apply]
  have hmass_neg (value : ℤ) : mass (-value) = mass value := by
    exact discreteGaussianPMF_zero_neg sigma value
  have hmass_succ (index : ℕ) :
      mass ((index + 1 : ℕ) : ℤ) ≤ mass (index : ℤ) := by
    exact discreteGaussianPMF_zero_nat_succ_le sigma hsigma index
  have hpositive (index : ℕ) :
      |(translate 1 p ((index + 1 : ℕ) : ℤ)).toReal -
          (p ((index + 1 : ℕ) : ℤ)).toReal| =
        mass (index : ℤ) - mass ((index + 1 : ℕ) : ℤ) := by
    rw [htranslate, hp_apply]
    have hindex : (((index + 1 : ℕ) : ℤ) - 1) = (index : ℤ) := by omega
    rw [hindex, abs_of_nonneg (sub_nonneg.mpr (hmass_succ index))]
  have hzero :
      |(translate 1 p 0).toReal - (p 0).toReal| = mass 0 - mass 1 := by
    rw [htranslate, hp_apply]
    have hminus : (0 : ℤ) - 1 = -1 := by omega
    rw [hminus, hmass_neg 1, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (hmass_succ 0)
  have hnegative (index : ℕ) :
      |(translate 1 p (-((index + 1 : ℕ) : ℤ))).toReal -
          (p (-((index + 1 : ℕ) : ℤ))).toReal| =
        mass ((index + 1 : ℕ) : ℤ) - mass ((index + 2 : ℕ) : ℤ) := by
    rw [htranslate, hp_apply]
    have hshift : -((index + 1 : ℕ) : ℤ) - 1 = -((index + 2 : ℕ) : ℤ) := by omega
    rw [hshift, hmass_neg ((index + 2 : ℕ) : ℤ),
      hmass_neg ((index + 1 : ℕ) : ℤ), abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (hmass_succ (index + 1))
  have hpositive' (index : ℕ) :
      |(translate 1 p ((index : ℤ) + 1)).toReal -
          (p ((index : ℤ) + 1)).toReal| =
        mass (index : ℤ) - mass ((index + 1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hpositive index
  have hnegative' (index : ℕ) :
      |(translate 1 p (-((index : ℤ) + 1))).toReal -
          (p (-((index : ℤ) + 1))).toReal| =
        mass ((index + 1 : ℕ) : ℤ) - mass ((index + 2 : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hnegative index
  have hmassSummable : Summable mass := by
    exact LatticeCrypto.discreteGaussianPMF_summable sigma 0 hsigma
  have hnat : Summable (fun index : ℕ ↦ mass (index : ℤ)) :=
    hmassSummable.comp_injective Nat.cast_injective
  have htail : Summable (fun index : ℕ ↦ mass ((index + 1 : ℕ) : ℤ)) := by
    exact (summable_nat_add_iff 1).2 hnat
  have htail₂ : Summable (fun index : ℕ ↦ mass ((index + 2 : ℕ) : ℤ)) := by
    simpa only [Nat.add_assoc, one_add_one_eq_two] using
      (summable_nat_add_iff 1).2 htail
  have htelescope :
      (∑' index : ℕ,
          (mass (index : ℤ) - mass ((index + 1 : ℕ) : ℤ))) = mass 0 := by
    rw [hnat.tsum_sub htail]
    have hsplit := hnat.tsum_eq_zero_add
    simp only [Nat.cast_zero] at hsplit
    linarith
  have htelescopeTail :
      (∑' index : ℕ,
          (mass ((index + 1 : ℕ) : ℤ) - mass ((index + 2 : ℕ) : ℤ))) = mass 1 := by
    rw [htail.tsum_sub htail₂]
    have hsplit := htail.tsum_eq_zero_add
    simp only [Nat.zero_add, Nat.cast_one, Nat.add_assoc, one_add_one_eq_two] at hsplit
    linarith
  have hsummablePositive : Summable (fun index : ℕ ↦
      |(translate 1 p ((index + 1 : ℕ) : ℤ)).toReal -
        (p ((index + 1 : ℕ) : ℤ)).toReal|) := by
    simpa only [hpositive] using hnat.sub htail
  have hsummableNegative : Summable (fun index : ℕ ↦
      |(translate 1 p (-((index + 1 : ℕ) : ℤ))).toReal -
        (p (-((index + 1 : ℕ) : ℤ))).toReal|) := by
    simpa only [hnegative] using htail.sub htail₂
  change (∑' value : ℤ, |(translate 1 p value).toReal - (p value).toReal|) = _
  rw [tsum_of_add_one_of_neg_add_one hsummablePositive hsummableNegative]
  rw [show (∑' index : ℕ,
      |(translate 1 p ((index : ℤ) + 1)).toReal -
        (p ((index : ℤ) + 1)).toReal|) = mass 0 by
      calc
        _ = ∑' index : ℕ,
            (mass (index : ℤ) - mass ((index + 1 : ℕ) : ℤ)) :=
          tsum_congr hpositive'
        _ = mass 0 := htelescope]
  rw [hzero]
  rw [show (∑' index : ℕ,
      |(translate 1 p (-((index : ℤ) + 1))).toReal -
        (p (-((index : ℤ) + 1))).toReal|) = mass 1 by
      calc
        _ = ∑' index : ℕ,
            (mass ((index + 1 : ℕ) : ℤ) - mass ((index + 2 : ℕ) : ℤ)) :=
          tsum_congr hnegative'
        _ = mass 1 := htelescopeTail]
  ring

/-- Exact total-variation cost of a fixed translation. -/
noncomputable def shiftDistance {G : Type} [Add G] (p : PMF G) (shift : G) : ℝ :=
  PMF.tvDist (translate shift p) p

/-- Exact unit-shift distance for the centered integer discrete Gaussian. -/
theorem shiftDistance_discreteGaussian_unit_eq_mass_zero
    (sigma : ℝ) (hsigma : 0 < sigma) :
    shiftDistance (LatticeCrypto.discreteGaussianDist sigma 0 hsigma) 1 =
      LatticeCrypto.discreteGaussianPMF sigma 0 0 := by
  rw [shiftDistance, tvDist_eq_half_tsum_abs_toReal,
    tsum_abs_translate_discreteGaussian_unit_eq_two_mul_mass_zero sigma hsigma]
  ring

/-- A finite central window gives an explicit upper bound on the mass at zero.  Taking any
natural `window` with `window ≤ sigma` yields an `O(1 / window)` estimate without invoking a
continuous-Gaussian approximation. -/
theorem discreteGaussianPMF_zero_le_exp_half_div_nat_succ
    (sigma : ℝ) (hsigma : 0 < sigma) (window : ℕ)
    (hwindow : (window : ℝ) ≤ sigma) :
    LatticeCrypto.discreteGaussianPMF sigma 0 0 ≤
      Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ) := by
  let embedding : ℕ ↪ ℤ :=
    ⟨fun index ↦ (index : ℤ), Nat.cast_injective⟩
  let indices : Finset ℤ := (Finset.range (window + 1)).map embedding
  have hpoint (index : ℕ) (hindex : index ∈ Finset.range (window + 1)) :
      Real.exp (-(1 / 2 : ℝ)) ≤
        LatticeCrypto.discreteGaussianWeight sigma 0 (index : ℤ) := by
    have hindexNat : index ≤ window := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hindex
    have hindexReal : (index : ℝ) ≤ sigma :=
      (Nat.cast_le.mpr hindexNat).trans hwindow
    have hsquare : (index : ℝ) ^ 2 ≤ sigma ^ 2 :=
      (sq_le_sq₀ (Nat.cast_nonneg index) hsigma.le).2 hindexReal
    unfold LatticeCrypto.discreteGaussianWeight
    apply Real.exp_le_exp.mpr
    simp only [Int.cast_natCast, sub_zero]
    have hdenominator : 0 < 2 * sigma ^ 2 := by positivity
    have hhalf : -(1 / 2 : ℝ) = -(sigma ^ 2) / (2 * sigma ^ 2) := by
      field_simp [ne_of_gt hsigma]
    rw [hhalf, div_le_div_iff_of_pos_right hdenominator]
    exact neg_le_neg hsquare
  have hfinite_le_sum :
      ∑ value ∈ indices, LatticeCrypto.discreteGaussianWeight sigma 0 value ≤
        LatticeCrypto.discreteGaussianSum sigma 0 := by
    exact (LatticeCrypto.discreteGaussianSum_summable sigma 0 hsigma).sum_le_tsum
      indices (fun value _ ↦ LatticeCrypto.discreteGaussianWeight_nonneg sigma 0 value)
  have hrange_le_sum :
      ∑ index ∈ Finset.range (window + 1),
          LatticeCrypto.discreteGaussianWeight sigma 0 (index : ℤ) ≤
        LatticeCrypto.discreteGaussianSum sigma 0 := by
    simpa [indices, embedding] using hfinite_le_sum
  have hnormalizer :
      ((window + 1 : ℕ) : ℝ) * Real.exp (-(1 / 2 : ℝ)) ≤
        LatticeCrypto.discreteGaussianSum sigma 0 := by
    calc
      ((window + 1 : ℕ) : ℝ) * Real.exp (-(1 / 2 : ℝ)) =
          ∑ _index ∈ Finset.range (window + 1), Real.exp (-(1 / 2 : ℝ)) := by simp
      _ ≤ ∑ index ∈ Finset.range (window + 1),
          LatticeCrypto.discreteGaussianWeight sigma 0 (index : ℤ) := by
        exact Finset.sum_le_sum fun index hindex ↦ hpoint index hindex
      _ ≤ LatticeCrypto.discreteGaussianSum sigma 0 := hrange_le_sum
  calc
    LatticeCrypto.discreteGaussianPMF sigma 0 0 =
        1 / LatticeCrypto.discreteGaussianSum sigma 0 := by
      simp [LatticeCrypto.discreteGaussianPMF, LatticeCrypto.discreteGaussianWeight]
    _ ≤ 1 / (((window + 1 : ℕ) : ℝ) * Real.exp (-(1 / 2 : ℝ))) :=
      one_div_le_one_div_of_le
        (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos window)) (Real.exp_pos _)) hnormalizer
    _ = Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ) := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]

/-- Explicit finite-window bound for the centered integer-Gaussian unit translation. -/
theorem shiftDistance_discreteGaussian_unit_le_exp_half_div_nat_succ
    (sigma : ℝ) (hsigma : 0 < sigma) (window : ℕ)
    (hwindow : (window : ℝ) ≤ sigma) :
    shiftDistance (LatticeCrypto.discreteGaussianDist sigma 0 hsigma) 1 ≤
      Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ) := by
  rw [shiftDistance_discreteGaussian_unit_eq_mass_zero sigma hsigma]
  exact discreteGaussianPMF_zero_le_exp_half_div_nat_succ sigma hsigma window hwindow

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

/-- Translating in the opposite direction has exactly the same total-variation cost. -/
theorem shiftDistance_neg {G : Type} [AddCommGroup G]
    (p : PMF G) (shift : G) :
    shiftDistance p (-shift) = shiftDistance p shift := by
  let addShift : G ≃ G :=
    { toFun := fun value ↦ shift + value
      invFun := fun value ↦ -shift + value
      left_inv := by intro value; simp
      right_inv := by intro value; simp }
  have hcancel : addShift <$> translate (-shift) p = p := by
    simp [addShift, translate, Functor.map_map]
  have htranslate : addShift <$> p = translate shift p := by
    rfl
  calc
    shiftDistance p (-shift) =
        PMF.tvDist (addShift <$> translate (-shift) p) (addShift <$> p) := by
      unfold shiftDistance
      exact (tvDist_map_equiv addShift _ _).symm
    _ = PMF.tvDist p (translate shift p) := by rw [hcancel, htranslate]
    _ = shiftDistance p shift := by
      rw [PMF.tvDist_comm]
      rfl

/-- Repeating one additive translation at most adds its TV cost once per repetition. -/
theorem shiftDistance_nsmul_le {G : Type} [AddCommGroup G]
    (p : PMF G) (shift : G) (count : ℕ) :
    shiftDistance p (count • shift) ≤
      (count : ℝ) * shiftDistance p shift := by
  induction count with
  | zero => simp
  | succ count ih =>
      calc
        shiftDistance p ((count + 1) • shift) =
            shiftDistance p (count • shift + shift) := by rw [add_nsmul, one_nsmul]
        _ ≤ shiftDistance p (count • shift) + shiftDistance p shift :=
          shiftDistance_add_le p _ _
        _ ≤ (count : ℝ) * shiftDistance p shift + shiftDistance p shift :=
          add_le_add ih le_rfl
        _ = ((count + 1 : ℕ) : ℝ) * shiftDistance p shift := by
          push_cast
          ring

/-- Integer repetitions reduce to the absolute number of unit translations. -/
theorem shiftDistance_zsmul_le {G : Type} [AddCommGroup G]
    (p : PMF G) (shift : G) (multiple : ℤ) :
    shiftDistance p (multiple • shift) ≤
      (multiple.natAbs : ℝ) * shiftDistance p shift := by
  cases multiple with
  | ofNat count =>
      simpa only [Int.ofNat_eq_natCast, natCast_zsmul, Int.natAbs_natCast] using
        shiftDistance_nsmul_le p shift count
  | negSucc count =>
      calc
        shiftDistance p (Int.negSucc count • shift) =
            shiftDistance p (-((count + 1) • shift)) := by rw [negSucc_zsmul]
        _ = shiftDistance p ((count + 1) • shift) := shiftDistance_neg p _
        _ ≤ ((count + 1 : ℕ) : ℝ) * shiftDistance p shift :=
          shiftDistance_nsmul_le p shift (count + 1)
        _ = (Int.negSucc count).natAbs * shiftDistance p shift := by simp

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

/-- Every modular Gaussian translation reduces to the centered shift magnitude times the single
unit-shift cost of the underlying integer discrete Gaussian. -/
theorem shiftDistance_distribution_le_natAbs_mul_unit (q : ℕ) [NeZero q]
    (sigma : ℝ) (hsigma : 0 < sigma) (shift : ZMod q) :
    shiftDistance (distribution q sigma hsigma) shift ≤
      (shift.valMinAbs.natAbs : ℝ) *
        shiftDistance (LatticeCrypto.discreteGaussianDist sigma 0 hsigma) 1 := by
  calc
    shiftDistance (distribution q sigma hsigma) shift ≤
        shiftDistance (LatticeCrypto.discreteGaussianDist sigma 0 hsigma)
          shift.valMinAbs :=
      shiftDistance_distribution_le_valMinAbs q sigma hsigma shift
    _ = shiftDistance (LatticeCrypto.discreteGaussianDist sigma 0 hsigma)
        (shift.valMinAbs • (1 : ℤ)) := by simp
    _ ≤ (shift.valMinAbs.natAbs : ℝ) *
        shiftDistance (LatticeCrypto.discreteGaussianDist sigma 0 hsigma) 1 :=
      shiftDistance_zsmul_le
        (LatticeCrypto.discreteGaussianDist sigma 0 hsigma) 1 shift.valMinAbs

/-- Torus-parameter form of `shiftDistance_distribution_le_natAbs_mul_unit`. -/
theorem shiftDistance_torusDistribution_le_natAbs_mul_unit
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha)
    (shift : ZMod q) :
    shiftDistance (torusDistribution q alpha halpha) shift ≤
      (shift.valMinAbs.natAbs : ℝ) *
        shiftDistance
          (LatticeCrypto.discreteGaussianDist (integerStddev q alpha) 0
            (integerStddev_pos q halpha)) 1 := by
  exact shiftDistance_distribution_le_natAbs_mul_unit q
    (integerStddev q alpha) (integerStddev_pos q halpha) shift

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

/-- A PMF on a finite additive group that is close to each of its translates is close to the
uniform PMF.  This is the PMF-level averaging converse to translation invariance: averaging all
translates over a uniform shift gives the exact uniform law, while averaging the untranslated
law gives the original PMF. -/
theorem tvDist_uniformOfFintype_le_of_shiftDistance_le
    {G : Type} [AddCommGroup G] [Fintype G]
    (p : PMF G) (bound : ℝ)
    (hshift : ∀ shift : G, shiftDistance p shift ≤ bound) :
    PMF.tvDist p (PMF.uniformOfFintype G) ≤ bound := by
  classical
  let uniform : PMF G := PMF.uniformOfFintype G
  let shiftedMixture : PMF G :=
    uniform.bind fun shift ↦ translate shift p
  let constantMixture : PMF G :=
    uniform.bind fun _shift ↦ p
  have hbound : 0 ≤ bound := by
    exact (PMF.tvDist_nonneg (translate 0 p) p).trans (hshift 0)
  have huniformSum : (∑ shift : G, (uniform shift).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun shift _ ↦ uniform.apply_ne_top shift)]
    have hsum : ∑ shift : G, uniform shift = 1 := by
      simpa only [tsum_fintype] using uniform.tsum_coe
    rw [hsum]
    simp
  have hmixture : PMF.tvDist shiftedMixture constantMixture ≤ bound := by
    calc
      PMF.tvDist shiftedMixture constantMixture ≤
          ∑' shift, (uniform shift).toReal *
            PMF.tvDist (translate shift p) p := by
        exact tvDist_bind_left_le uniform (fun shift ↦ translate shift p) (fun _ ↦ p)
      _ = ∑ shift : G, (uniform shift).toReal *
            PMF.tvDist (translate shift p) p := by
        rw [tsum_fintype]
      _ ≤ ∑ shift : G, (uniform shift).toReal * bound := by
        exact Finset.sum_le_sum fun shift _ ↦
          mul_le_mul_of_nonneg_left (hshift shift) ENNReal.toReal_nonneg
      _ = bound := by
        rw [← Finset.sum_mul, huniformSum, one_mul]
  have hconstant : constantMixture = p := by
    exact PMF.bind_const uniform p
  have hshifted : shiftedMixture = uniform := by
    calc
      shiftedMixture =
          uniform.bind fun shift ↦
            p.bind fun value ↦ PMF.pure (shift + value) := by
        rfl
      _ = p.bind fun value ↦
          uniform.bind fun shift ↦ PMF.pure (shift + value) := by
        exact PMF.bind_comm uniform p
          (fun shift value ↦ PMF.pure (shift + value))
      _ = p.bind fun _value ↦ uniform := by
        congr 1
        funext value
        change PMF.map (fun shift : G ↦ shift + value) uniform = uniform
        exact PMF.uniformOfFintype_map_of_bijective
          (fun shift : G ↦ shift + value) (AddGroup.addRight_bijective value)
      _ = uniform := PMF.bind_const p uniform
  rw [hshifted, hconstant, PMF.tvDist_comm] at hmixture
  exact hmixture

/-- Universal real bound for the distance between a torus-scaled modular Gaussian and uniform.
It is the largest centered residue magnitude times the unit translation cost of the underlying
integer Gaussian. -/
noncomputable def torusUniformBound
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha) : ℝ :=
  (q / 2 : ℕ) *
    shiftDistance
      (LatticeCrypto.discreteGaussianDist (integerStddev q alpha) 0
        (integerStddev_pos q halpha)) 1

theorem torusUniformBound_nonneg
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha) :
    0 ≤ torusUniformBound q alpha halpha := by
  unfold torusUniformBound
  exact mul_nonneg (Nat.cast_nonneg _) (PMF.tvDist_nonneg _ _)

/-- A sufficiently translation-invariant modular Gaussian is close to the exact uniform PMF.
Unlike a one-sided hybrid, this follows by averaging every additive translate. -/
theorem tvDist_torusDistribution_uniform_le
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha) :
    PMF.tvDist (torusDistribution q alpha halpha)
        (PMF.uniformOfFintype (ZMod q)) ≤
      torusUniformBound q alpha halpha := by
  apply tvDist_uniformOfFintype_le_of_shiftDistance_le
  intro shift
  calc
    shiftDistance (torusDistribution q alpha halpha) shift ≤
        (shift.valMinAbs.natAbs : ℝ) *
          shiftDistance
            (LatticeCrypto.discreteGaussianDist (integerStddev q alpha) 0
              (integerStddev_pos q halpha)) 1 :=
      shiftDistance_torusDistribution_le_natAbs_mul_unit
        q alpha halpha shift
    _ ≤ (q / 2 : ℕ) *
          shiftDistance
            (LatticeCrypto.discreteGaussianDist (integerStddev q alpha) 0
              (integerStddev_pos q halpha)) 1 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast ZMod.natAbs_valMinAbs_le shift
      · exact PMF.tvDist_nonneg _ _
    _ = torusUniformBound q alpha halpha := rfl

/-- Finite-window estimate for the modular-Gaussian distance from uniform. -/
theorem torusUniformBound_le_exp_half_window
    (q : ℕ) [NeZero q] (alpha : ℝ) (halpha : 0 < alpha)
    (window : ℕ) (hwindow : (window : ℝ) ≤ integerStddev q alpha) :
    torusUniformBound q alpha halpha ≤
      (q / 2 : ℕ) * (Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ)) := by
  unfold torusUniformBound
  exact mul_le_mul_of_nonneg_left
    (shiftDistance_discreteGaussian_unit_le_exp_half_div_nat_succ
      (integerStddev q alpha) (integerStddev_pos q halpha) window hwindow)
    (Nat.cast_nonneg _)

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
