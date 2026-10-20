/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.RecursiveFeatureControlPolynomial

/-!
# Statistical body-message changes in the complete recursive control view

The key and every public mask are shared. Only designated scalar body errors
are translated, so the comparison retains the complete stored public view.
The low-level specialization removes genuine cubic messages below a cutoff.
This is a security hybrid, not a change to the correctly refreshing scheme.
The higher-weight joint ordinary-LWE comparison remains unproved.
-/

open Matrix OracleComp AsymmEncAlg
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.RecursiveFeatureLowLevelHybrid

open RecursiveMultiplication RecursiveFeatureGSW RecursiveFeatureBootstrap
open RecursiveFeatureSecurityView RecursiveFeatureControlPolynomial

noncomputable section

variable {q n p : ℕ} [NeZero q] (configuration : Parameters q)

noncomputable local instance : SampleableType (Challenge configuration n p) :=
  instSampleableTypeFinFunc

/-- A key-dependent message subtraction at each scalar body, with all other
error coordinates unchanged. The function is part of the mathematical hybrid. -/
def rawShift (shift : (Fin n → Bool) → Fin (scalarColumns configuration n p) → ZMod q)
    (bits : Fin n → Bool) : RawColumn configuration n p → ZMod q
  | .inl index => Fin.elim0 index
  | .inr (column, none) => shift bits column
  | .inr (_, some _) => 0

def shiftDraws (shift : (Fin n → Bool) → Fin (scalarColumns configuration n p) → ZMod q)
    (draws : Draws configuration n p) : Draws configuration n p :=
  (draws.1, draws.2.1, fun coordinate ↦ draws.2.2 coordinate - rawShift configuration shift draws.1 coordinate)

def shiftedKeyView (shift : (Fin n → Bool) → Fin (scalarColumns configuration n p) → ZMod q)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (View configuration n p) :=
  (fun draws ↦ publicView configuration (shiftDraws configuration shift draws)) <$>
    sampleDraws configuration secretSampler errorSampler

/-- Coordinatewise translation commutes with the actual finite IID sampler. -/
theorem iid_sub_tvDist_le (count : ℕ) (sampler : ProbComp (ZMod q))
    (shift : Fin count → ZMod q) :
    tvDist (ProbComp.sampleIID count sampler)
      ((fun values index ↦ values index - shift index) <$> ProbComp.sampleIID count sampler) ≤
        ∑ index, FiniteProduct.addShiftDistance sampler (shift index) := by
  unfold ProbComp.sampleIID
  rw [FiniteProduct.map_fin_mOfFn count (fun _ ↦ sampler) (fun index value ↦ value - shift index)]
  have h := FiniteProduct.tvDist_fin_mOfFn_le_sum count (fun _ ↦ sampler)
    (fun index ↦ (fun value ↦ value - shift index) <$> sampler)
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro index _
  have hshift := UniformInterval.shift_neg sampler (shift index)
  simpa only [FiniteProduct.addShiftDistance, sub_eq_add_neg, add_comm,
    tvDist_comm] using hshift

omit [NeZero q] in
/-- Reindexing charges only body coordinates, not mask errors or unused rows. -/
theorem sum_rawShift_distance
    (shift : (Fin n → Bool) → Fin (scalarColumns configuration n p) → ZMod q)
    (bits : Fin n → Bool) (sampler : ProbComp (ZMod q)) :
    (∑ index : Fin (errorCount configuration n p),
      FiniteProduct.addShiftDistance sampler
        (rawShift configuration shift bits ((errorColumnsEquiv configuration n p).symm index))) =
      ∑ column, FiniteProduct.addShiftDistance sampler (shift bits column) := by
  classical
  have hreindex := Fintype.sum_equiv (errorColumnsEquiv configuration n p)
    (fun coordinate ↦ FiniteProduct.addShiftDistance sampler (rawShift configuration shift bits coordinate))
    (fun index ↦ FiniteProduct.addShiftDistance sampler
      (rawShift configuration shift bits ((errorColumnsEquiv configuration n p).symm index)))
    (by intro coordinate; simp)
  rw [← hreindex]
  simp [RawColumn, RecursiveQuadratic.Column, Fintype.sum_sum_type,
    Fintype.sum_prod_type, rawShift]

/-- The complete public-key/control view changes by at most the sum of its
scalar body shifts, uniformly over the SAME sampled secret. -/
theorem keyView_tvDist_shifted_le
    (shift : (Fin n → Bool) → Fin (scalarColumns configuration n p) → ZMod q)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q))
    (bound : ℝ)
    (hbound : ∀ bits, (∑ column, FiniteProduct.addShiftDistance errorSampler (shift bits column)) ≤ bound) :
    tvDist (keyView configuration secretSampler errorSampler)
      (shiftedKeyView configuration shift secretSampler errorSampler) ≤ bound := by
  classical
  unfold keyView shiftedKeyView sampleDraws
  simp only [map_bind, map_pure]
  apply tvDist_bind_left_le_const'
  intro bits
  apply tvDist_bind_left_le_const'
  intro challenge
  let process : (Fin (errorCount configuration n p) → ZMod q) → View configuration n p := fun errors ↦
    publicView configuration (bits, challenge, fun coordinate ↦ errors (errorColumnsEquiv configuration n p coordinate))
  let shifts : Fin (errorCount configuration n p) → ZMod q := fun index ↦
    rawShift configuration shift bits ((errorColumnsEquiv configuration n p).symm index)
  have hmap := tvDist_map_le process (ProbComp.sampleIID (errorCount configuration n p) errorSampler)
    ((fun errors index ↦ errors index - shifts index) <$>
      ProbComp.sampleIID (errorCount configuration n p) errorSampler)
  have hiid := iid_sub_tvDist_le (errorCount configuration n p) errorSampler shifts
  have hsum : (∑ index, FiniteProduct.addShiftDistance errorSampler (shifts index)) ≤ bound := by
    simpa only [shifts, sum_rawShift_distance] using hbound bits
  have h := hmap.trans (hiid.trans hsum)
  simpa only [process, shifts, Functor.map_map, Function.comp_def,
    Equiv.symm_apply_apply, shiftDraws, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] using h

/-- A common arbitrary randomized continuation can inspect the entire view. -/
theorem observation_tvDist_le
    (shift : (Fin n → Bool) → Fin (scalarColumns configuration n p) → ZMod q)
    (secretSampler : ProbComp (Fin n → Bool)) (errorSampler : ProbComp (ZMod q))
    (bound : ℝ)
    (hbound : ∀ bits, (∑ column, FiniteProduct.addShiftDistance errorSampler (shift bits column)) ≤ bound)
    {Output : Type} (observe : View configuration n p → ProbComp Output) :
    tvDist (keyView configuration secretSampler errorSampler >>= observe)
      (shiftedKeyView configuration shift secretSampler errorSampler >>= observe) ≤ bound :=
  (tvDist_bind_right_le observe _ _).trans
    (keyView_tvDist_shifted_le configuration shift secretSampler errorSampler bound hbound)

/-- The exact message used by a scalar column of the original-bit table. -/
def originalMessage (bits : Fin n → Bool) (index : Fin n)
    (column : Fin (rows n * configuration.levels)) : ZMod q :=
  GSWGadget.bitMessage (bits index) *
    phase configuration (GSWSelfKey.binaryEmbed bits) (gadgetBatch configuration) column

/-- Only distinct-index cubic features below the chosen gadget cutoff. -/
def deleteColumn (cutoff : ℕ) (index : Fin n)
    (column : Fin (rows n * configuration.levels)) : Bool :=
  genuineCubic index ((featureEquiv n).symm (finProdFinEquiv.symm column).1) &&
    decide ((finProdFinEquiv.symm column).2.val < cutoff)

/-- Public encryption columns always have zero shift. -/
def deletionShift (cutoff : ℕ) (bits : Fin n → Bool)
    (column : Fin (scalarColumns configuration n p)) : ZMod q :=
  match finSumFinEquiv.symm column with
  | .inl _ => 0
  | .inr packed =>
      let pair := finProdFinEquiv.symm packed
      if deleteColumn configuration cutoff pair.1 pair.2 then originalMessage configuration bits pair.1 pair.2 else 0

@[simp] theorem deletionShift_public (cutoff : ℕ) (bits : Fin n → Bool) (index : Fin p) :
    deletionShift configuration cutoff bits (publicColumn configuration index) = 0 := by
  simp [deletionShift, publicColumn]

@[simp] theorem deletionShift_control (cutoff : ℕ) (bits : Fin n → Bool)
    (index : Fin n) (column : Fin (rows n * configuration.levels)) :
    deletionShift (p := p) configuration cutoff bits (controlColumn configuration index column) =
      if deleteColumn configuration cutoff index column then originalMessage configuration bits index column else 0 := by
  simp [deletionShift, controlColumn]

omit [NeZero q] in
theorem errorsAt_sub_rawShift
    (shift : (Fin n → Bool) → Fin (scalarColumns configuration n p) → ZMod q)
    (bits : Fin n → Bool) (errors : Errors configuration n p)
    (column : Fin (scalarColumns configuration n p)) :
    errorsAt configuration (fun coordinate ↦ errors coordinate - rawShift configuration shift bits coordinate) column =
      errorsAt configuration errors column := by
  funext row
  simp [errorsAt, rawShift]

/-- A separately materialized security hybrid: selected messages are zero,
while every mask and every sampled error is the original one. -/
def deletedView (cutoff : ℕ) (draws : Draws configuration n p) : View configuration n p :=
  (publicTable configuration draws, storeOriginal configuration (fun index column ↦
    freshCiphertext (GSWSelfKey.binaryEmbed draws.1)
      (if deleteColumn configuration cutoff index column then 0 else originalMessage configuration draws.1 index column)
      (maskAt configuration draws.2.1 (controlColumn configuration index column))
      (innerAt configuration draws.2.1 (controlColumn configuration index column))
      (errorsAt configuration draws.2.2 (controlColumn configuration index column))
      (bodyErrorAt configuration draws.2.2 (controlColumn configuration index column))))

/-- The error-translation coupling produces exactly the intended full hybrid. -/
theorem publicView_shiftDraws_deletion (cutoff : ℕ) (draws : Draws configuration n p) :
    publicView configuration (shiftDraws configuration (deletionShift configuration cutoff) draws) =
      deletedView configuration cutoff draws := by
  apply Prod.ext
  · funext index
    simp only [publicView, publicTable, deletedView, shiftDraws]
    rw [errorsAt_sub_rawShift]
    simp only [bodyErrorAt, rawShift, deletionShift_public, sub_zero]
  · change storeOriginal configuration _ = storeOriginal configuration _
    congr 1
    funext index column
    simp only [freshOriginal, shiftDraws]
    rw [errorsAt_sub_rawShift]
    simp only [bodyErrorAt, rawShift, deletionShift_control]
    split <;> simp_all only [freshCiphertext, originalMessage, sub_zero]
    all_goals (congr 2; ring)

/-- The stored hybrid exposes precisely the declared scalar ciphertexts. -/
theorem deleted_controls_view (cutoff : ℕ) (draws : Draws configuration n p)
    (index : Fin n) (column : Fin (rows n * configuration.levels)) :
    originalView configuration (deletedView configuration cutoff draws).2 index column =
      freshCiphertext (GSWSelfKey.binaryEmbed draws.1)
        (if deleteColumn configuration cutoff index column then 0 else originalMessage configuration draws.1 index column)
        (maskAt configuration draws.2.1 (controlColumn configuration index column))
        (innerAt configuration draws.2.1 (controlColumn configuration index column))
        (errorsAt configuration draws.2.2 (controlColumn configuration index column))
        (bodyErrorAt configuration draws.2.2 (controlColumn configuration index column)) := by
  change originalView configuration (storeOriginal configuration _) index column = _
  rw [originalView_storeOriginal]

/-- A column outside the deletion set is the identical actual control ciphertext. -/
theorem deleted_controls_retained (cutoff : ℕ) (draws : Draws configuration n p)
    (index : Fin n) (column : Fin (rows n * configuration.levels))
    (hretain : deleteColumn configuration cutoff index column = false) :
    originalView configuration (deletedView configuration cutoff draws).2 index column =
      originalView configuration (controls configuration draws) index column := by
  rw [deleted_controls_view, controls_view]
  simp only [hretain, Bool.false_eq_true, ↓reduceIte, freshOriginal, originalMessage]

omit [NeZero q] in
@[simp] theorem deleteColumn_zero (index : Fin n) (column : Fin (rows n * configuration.levels)) :
    deleteColumn configuration 0 index column = false := by
  simp [deleteColumn]

/-- On binary secrets each scalar message is either zero or its gadget weight. -/
theorem originalMessage_eq_zero_or_gadget (bits : Fin n → Bool) (index : Fin n)
    (column : Fin (rows n * configuration.levels)) :
    originalMessage configuration bits index column = 0 ∨
      originalMessage configuration bits index column =
        TFHE.Gadget.Base.gadget configuration (finProdFinEquiv.symm column).2 := by
  obtain ⟨⟨coordinate, level⟩, rfl⟩ := finProdFinEquiv.surjective column
  obtain ⟨coordinate, rfl⟩ := (featureEquiv n).surjective coordinate
  simp only [originalMessage, gadgetBatch_phase, feature_eq_bitMessage, Equiv.symm_apply_apply]
  cases bits index <;> cases featureBit bits coordinate <;>
    simp [GSWGadget.bitMessage]

/-- The explicit charge for each removed body, including finite-retry sampling. -/
def columnCost (radius rounds cutoff : ℕ) (index : Fin n)
    (column : Fin (rows n * configuration.levels)) : ℝ :=
  if deleteColumn configuration cutoff index column then
    (configuration.base ^ (finProdFinEquiv.symm column).2.val : ℕ) / (2 * radius + 1 : ℝ) +
      2 * (1 / 2 : ℝ) ^ rounds
  else 0

def deletionLoss (n : ℕ) (radius rounds cutoff : ℕ) : ℝ :=
  ∑ index : Fin n, ∑ column : Fin (rows n * configuration.levels),
    columnCost configuration radius rounds cutoff index column

omit [NeZero q] in
theorem columnCost_nonneg (radius rounds cutoff : ℕ) (index : Fin n)
    (column : Fin (rows n * configuration.levels)) :
    0 ≤ columnCost configuration radius rounds cutoff index column := by
  unfold columnCost
  split <;> positivity

omit [NeZero q] in
@[simp] theorem deletionLoss_zero (n radius rounds : ℕ) :
    deletionLoss configuration n radius rounds 0 = 0 := by
  simp [deletionLoss, columnCost]

theorem originalMessage_shift_le (radius rounds : ℕ) (bits : Fin n → Bool)
    (index : Fin n) (column : Fin (rows n * configuration.levels)) :
    FiniteProduct.addShiftDistance (UniformInterval.sample q radius rounds)
        (originalMessage configuration bits index column) ≤
      (configuration.base ^ (finProdFinEquiv.symm column).2.val : ℕ) / (2 * radius + 1 : ℝ) +
        2 * (1 / 2 : ℝ) ^ rounds := by
  rcases originalMessage_eq_zero_or_gadget configuration bits index column with hzero | hgadget
  · rw [hzero, FiniteProduct.addShiftDistance_zero]
    positivity
  · rw [hgadget]
    refine (UniformInterval.sample_shift_le_centered q radius rounds _).trans ?_
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h := TFHE.NoiseBounds.centeredRepr_natCast_natAbs_le
      (q := q) (configuration.base ^ (finProdFinEquiv.symm column).2.val)
    simp only [Nat.cast_pow] at h
    change (LatticeCrypto.centeredRepr ((configuration.base : ZMod q) ^ (finProdFinEquiv.symm column).2.val)).natAbs ≤ _ at h
    unfold TFHE.Gadget.Base.gadget
    exact_mod_cast h

theorem deletionShift_sum_le (radius rounds cutoff : ℕ) (bits : Fin n → Bool) :
    (∑ column : Fin (scalarColumns configuration n p),
      FiniteProduct.addShiftDistance (UniformInterval.sample q radius rounds)
        (deletionShift configuration cutoff bits column)) ≤ deletionLoss configuration n radius rounds cutoff := by
  classical
  unfold scalarColumns
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [deletionShift, Equiv.symm_apply_apply, FiniteProduct.addShiftDistance_zero,
    Finset.sum_const_zero, zero_add]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  unfold deletionLoss
  apply Finset.sum_le_sum
  intro index _
  apply Finset.sum_le_sum
  intro column _
  simp only [Equiv.symm_apply_apply, columnCost]
  split
  · exact originalMessage_shift_le configuration radius rounds bits index column
  · simp

/-- Full-view deletion bound for the actual sampled controls and public key. -/
theorem keyView_tvDist_deleted_le (radius rounds cutoff : ℕ)
    (secretSampler : ProbComp (Fin n → Bool)) :
    tvDist (keyView (p := p) configuration secretSampler (UniformInterval.sample q radius rounds))
      (deletedView configuration cutoff <$> sampleDraws configuration secretSampler (UniformInterval.sample q radius rounds)) ≤
        deletionLoss configuration n radius rounds cutoff := by
  have h := keyView_tvDist_shifted_le (p := p) configuration (deletionShift configuration cutoff)
    secretSampler (UniformInterval.sample q radius rounds) _
    (deletionShift_sum_le configuration radius rounds cutoff)
  simpa only [shiftedKeyView, publicView_shiftDraws_deletion] using h

/-- Arbitrary randomized/adaptive postprocessing of the complete view is covered. -/
theorem deleted_observation_tvDist_le (radius rounds cutoff : ℕ)
    (secretSampler : ProbComp (Fin n → Bool)) {Output : Type}
    (observe : View configuration n p → ProbComp Output) :
    tvDist (keyView configuration secretSampler (UniformInterval.sample q radius rounds) >>= observe)
      ((deletedView configuration cutoff <$> sampleDraws configuration secretSampler
        (UniformInterval.sample q radius rounds)) >>= observe) ≤ deletionLoss configuration n radius rounds cutoff :=
  (tvDist_bind_right_le observe _ _).trans
    (keyView_tvDist_deleted_le configuration radius rounds cutoff secretSampler)

omit [NeZero q] in
/-- A coarse closed-form majorant; untouched columns are overcounted only here. -/
theorem deletionLoss_le (n radius rounds cutoff : ℕ) :
    deletionLoss configuration n radius rounds cutoff ≤
      (n * (rows n * configuration.levels) : ℕ) *
        ((configuration.base ^ cutoff : ℕ) / (2 * radius + 1 : ℝ) + 2 * (1 / 2 : ℝ) ^ rounds) := by
  classical
  have hcolumn (index : Fin n) (column : Fin (rows n * configuration.levels)) :
      columnCost configuration radius rounds cutoff index column ≤
        (configuration.base ^ cutoff : ℕ) / (2 * radius + 1 : ℝ) + 2 * (1 / 2 : ℝ) ^ rounds := by
    unfold columnCost
    split
    · rename_i hdelete
      have hlevel : (finProdFinEquiv.symm column).2.val < cutoff := by
        have hdelete' :
            genuineCubic index ((featureEquiv n).symm (finProdFinEquiv.symm column).1) = true ∧
              (finProdFinEquiv.symm column).2.val < cutoff := by
          simpa only [deleteColumn, Bool.and_eq_true, decide_eq_true_eq] using hdelete
        exact hdelete'.2
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (pow_le_pow_right₀ (by have := configuration.one_lt_base; omega : 1 ≤ configuration.base) (Nat.le_of_lt hlevel))
    · positivity
  calc
    _ ≤ ∑ index : Fin n, ∑ column : Fin (rows n * configuration.levels),
        ((configuration.base ^ cutoff : ℕ) / (2 * radius + 1 : ℝ) + 2 * (1 / 2 : ℝ) ^ rounds) :=
      Finset.sum_le_sum (fun index _ ↦ Finset.sum_le_sum (fun column _ ↦ hcolumn index column))
    _ = _ := by simp [Nat.cast_mul, mul_assoc]; ring

open RecursiveFeatureControlHybrid

/-- The surviving complete-view replacement is an explicit experiment,
not an additional hardness assumption. -/
def deletedReplacementAdvantage (radius rounds cutoff : ℕ)
    (polynomial : ControlPolynomial configuration n) (secretSampler : ProbComp (Fin n → Bool))
    (adversary : GSWMasking.Adversary (dimension := Dimension n) (samples := p) configuration (StoredOriginal configuration n)) : ℝ :=
  |Pr[= true | GSWMasking.game configuration
      (deletedView configuration cutoff <$> sampleDraws configuration secretSampler (UniformInterval.sample q radius rounds))
      adversary].toReal -
    Pr[= true | GSWMasking.game configuration
      (keyViewWithPolynomial configuration polynomial secretSampler (UniformInterval.sample q radius rounds))
      adversary].toReal|

theorem controlReplacement_le_deletionLoss_add (radius rounds cutoff : ℕ)
    (polynomial : ControlPolynomial configuration n) (secretSampler : ProbComp (Fin n → Bool))
    (adversary : GSWMasking.Adversary (dimension := Dimension n) (samples := p) configuration (StoredOriginal configuration n)) :
    controlReplacementAdvantage configuration polynomial secretSampler (UniformInterval.sample q radius rounds) adversary ≤
      deletionLoss configuration n radius rounds cutoff +
        deletedReplacementAdvantage configuration radius rounds cutoff polynomial secretSampler adversary := by
  have htv := deleted_observation_tvDist_le configuration radius rounds cutoff secretSampler (observe configuration adversary)
  have hprob := (abs_probOutput_toReal_sub_le_tvDist _ _).trans htv
  unfold controlReplacementAdvantage deletedReplacementAdvantage
  rw [game_eq_bind, game_eq_bind, game_eq_bind]
  exact (abs_sub_le _ _ _).trans (add_le_add hprob le_rfl)

open RecursiveQuadraticParameters RecursiveFeaturePublicKeyParameters

/-- This bound narrows the unproved hop to the surviving higher-weight controls. -/
theorem family_oneTime_abs_signedAdvantage_le (parameter cutoff : ℕ)
    (adversary : IND_CPA_Adv (RecursiveFeatureSecurityParameters.family parameter)) :
    |IND_CPA_OneTime_signedAdvantageReal (RecursiveFeatureSecurityParameters.family parameter) adversary| ≤
      deletionLoss (params parameter) (dimension parameter) (radius parameter) (retries parameter) cutoff +
        deletedReplacementAdvantage (params parameter) (radius parameter) (retries parameter) cutoff
          (controlPolynomial (params parameter)) ($ᵗ (Fin (dimension parameter) → Bool))
          (familyObserver parameter adversary) +
        quadraticOrdinaryLoss parameter (params parameter) (controlPolynomial (params parameter))
          (familyObserver parameter adversary) +
        implementationLoss (RecursiveFeatureSecurityParameters.scalarErrorCount parameter) parameter +
        maskingBound parameter := by
  have h := RecursiveFeatureControlPolynomial.family_oneTime_abs_signedAdvantage_le parameter adversary
  have hdelete := controlReplacement_le_deletionLoss_add (params parameter)
    (radius parameter) (retries parameter) cutoff (controlPolynomial (params parameter))
    ($ᵗ (Fin (dimension parameter) → Bool)) (familyObserver parameter adversary)
  unfold familyControlReplacementAdvantage at h
  linarith

/-- A convenient real geometric envelope for the half-speed cutoff. -/
theorem half_pow_div_two_le (value : ℕ) :
    (1 / 2 : ℝ) ^ (value / 2) ≤ 2 * (3 / 4 : ℝ) ^ value := by
  have hvalue : value ≤ 2 * (value / 2) + 1 := by omega
  calc
    _ ≤ ((3 / 4 : ℝ) ^ 2) ^ (value / 2) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ ≤ (3 / 2 : ℝ) * ((3 / 4 : ℝ) ^ 2) ^ (value / 2) := by
      have : 0 ≤ ((3 / 4 : ℝ) ^ 2) ^ (value / 2) := by positivity
      linarith
    _ = 2 * (3 / 4 : ℝ) ^ (2 * (value / 2) + 1) := by
      rw [pow_add, pow_mul]
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hvalue) (by norm_num)

/-- A scalar charge is exponentially small at the chosen family cutoff. -/
theorem family_scalar_cost_le (parameter : ℕ) :
    (2 : ℝ) ^ (scale parameter / 2) / (2 * radius parameter + 1 : ℝ) +
        2 * (1 / 2 : ℝ) ^ retries parameter ≤ 4 * (3 / 4 : ℝ) ^ parameter := by
  have hscale : 2 * (scale parameter / 2) ≤ scale parameter := by omega
  have hpowers : (2 : ℝ) ^ (scale parameter / 2) * (2 : ℝ) ^ (scale parameter / 2) ≤
      (2 : ℝ) ^ scale parameter := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hhead : (2 : ℝ) ^ (scale parameter / 2) / (2 * radius parameter + 1 : ℝ) ≤
      (1 / 2 : ℝ) ^ (scale parameter / 2) := by
    rw [div_pow, one_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simp only [radius, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (scale parameter)]
  have hhalf := half_pow_div_two_le (scale parameter)
  have hgeometric : (3 / 4 : ℝ) ^ scale parameter ≤ (3 / 4 : ℝ) ^ parameter :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by simp [scale])
  have hretry : (1 / 2 : ℝ) ^ retries parameter ≤ (3 / 4 : ℝ) ^ parameter :=
    (retry_error_le_half_pow parameter).trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
  linarith

theorem family_deletionLoss_le (parameter : ℕ) :
    deletionLoss (params parameter) (dimension parameter) (radius parameter) (retries parameter)
        (scale parameter / 2) ≤
      (4 * (dimension parameter * (rows (dimension parameter) * (params parameter).levels)) : ℕ) *
        (3 / 4 : ℝ) ^ parameter := by
  have h := deletionLoss_le (params parameter) (dimension parameter) (radius parameter)
    (retries parameter) (scale parameter / 2)
  have hscalar := family_scalar_cost_le parameter
  have hcost := mul_le_mul_of_nonneg_left hscalar
    (Nat.cast_nonneg (dimension parameter * (rows (dimension parameter) * (params parameter).levels)) :
      (0 : ℝ) ≤ (dimension parameter * (rows (dimension parameter) * (params parameter).levels) : ℕ))
  have hfirst : deletionLoss (params parameter) (dimension parameter) (radius parameter) (retries parameter)
      (scale parameter / 2) ≤
        (dimension parameter * (rows (dimension parameter) * (params parameter).levels) : ℕ) *
          ((2 : ℝ) ^ (scale parameter / 2) / (2 * radius parameter + 1 : ℝ) +
            2 * (1 / 2 : ℝ) ^ retries parameter) := by
    simpa only [params, Nat.cast_pow, Nat.cast_ofNat] using h
  refine (hfirst.trans hcost).trans_eq ?_
  push_cast
  ring

open scoped Topology

/-- The geometric envelope used above has the standard negligible limit. -/
theorem three_quarters_pow_negligible :
    negligible (fun parameter : ℕ ↦ ENNReal.ofReal ((3 / 4 : ℝ) ^ parameter)) := by
  intro power
  have hreal : Filter.Tendsto
      (fun parameter : ℕ ↦ (parameter : ℝ) ^ power * (3 / 4 : ℝ) ^ parameter)
      Filter.atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one power (by norm_num) (by norm_num)
  have h := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  convert h using 1
  · funext parameter
    change (parameter : ℝ≥0∞) ^ power * ENNReal.ofReal ((3 / 4 : ℝ) ^ parameter) =
      ENNReal.ofReal ((parameter : ℝ) ^ power * (3 / 4 : ℝ) ^ parameter)
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (parameter : ℝ) ^ power),
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (parameter : ℝ)), ENNReal.ofReal_natCast]
  · simp

/-- Low-level deletion has negligible cost in the actual recursive family. -/
theorem family_deletionLoss_negligible :
    negligible (fun parameter ↦ ENNReal.ofReal
      (deletionLoss (params parameter) (dimension parameter) (radius parameter) (retries parameter)
        (scale parameter / 2))) := by
  apply negligible_of_le (g := fun parameter ↦
    ((4 * (dimension parameter * (rows (dimension parameter) * (params parameter).levels)) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((3 / 4 : ℝ) ^ parameter))
  · intro parameter
    have h := ENNReal.ofReal_le_ofReal (family_deletionLoss_le parameter)
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h
  · have h := negligible_polynomial_mul three_quarters_pow_negligible
      (4 * (2 * (Polynomial.X + 1) ^ 5 * (featureRowsPolynomial * (Polynomial.X + 1) ^ 2)))
    simpa [featureRowsPolynomial_eval, featureRows, rows, params, binaryDimension, scale] using h

end

end FormalProof4FHE.LWE.RecursiveFeatureLowLevelHybrid
