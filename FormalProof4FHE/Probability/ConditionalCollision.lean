/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.LeftoverHash

/-!
# Collision Bounds with Retained Side Information

This file gives a finite, assumption-free collision bound for replacing one component of a
joint distribution by an independent uniform value while retaining the other component as side
information.  It is the appropriate interface for self-correlated TFHE hybrids: the public mask
should become uniform, but the error transformed by the same hidden randomness must remain in
the experiment.

The bound groups the ordinary `L¹` expression for total variation by the retained side value and
applies Cauchy--Schwarz only across the output coordinate.  No independence, linearity, or field
structure is assumed.
-/

open BigOperators OracleComp

namespace FormalProof4FHE.ConditionalCollision

noncomputable section

/-- Ordinary finite-output `L²` loss.  Unlike Pearson chi-square divergence, this quantity is
total even when the ideal sampler has zero-probability outputs.  It is therefore a convenient
interface for compiled finite Gaussian tables, whose downward rounding may leave some residues
outside the executable support. -/
noncomputable def l2Loss {Output : Type} [Fintype Output]
    (real ideal : ProbComp Output) : ℝ :=
  (1 / 2 : ℝ) *
    Real.sqrt
      ((Fintype.card Output : ℝ) *
        ∑ output : Output,
          (Pr[= output | real].toReal - Pr[= output | ideal].toReal) ^ 2)

theorem l2Loss_nonneg {Output : Type} [Fintype Output]
    (real ideal : ProbComp Output) :
    0 ≤ l2Loss real ideal := by
  unfold l2Loss
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- `l2Loss` depends only on the two output distributions. -/
theorem l2Loss_congr {Output : Type} [Fintype Output]
    {real real' ideal ideal' : ProbComp Output}
    (hReal : evalDist real = evalDist real')
    (hIdeal : evalDist ideal = evalDist ideal') :
    l2Loss real ideal = l2Loss real' ideal' := by
  unfold l2Loss
  congr 3
  apply Finset.sum_congr rfl
  intro output _
  rw [probOutput_congr rfl hReal, probOutput_congr rfl hIdeal]

/-- Cauchy--Schwarz bounds total variation by the ordinary finite-output `L²` loss.  No
absolute-continuity premise is needed. -/
theorem tvDist_le_l2Loss {Output : Type} [Fintype Output]
    (real ideal : ProbComp Output) :
    tvDist real ideal ≤ l2Loss real ideal := by
  classical
  rw [FormalProof4FHE.LeftoverHash.tvDist_eq_half_sum_abs]
  unfold l2Loss
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  let deviation := fun output : Output =>
    Pr[= output | real].toReal - Pr[= output | ideal].toReal
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Output => (1 : ℝ))
    (fun output => |deviation output|)
  have hsquare :
      (∑ output : Output, |deviation output|) ^ 2 ≤
        (Fintype.card Output : ℝ) *
          ∑ output : Output, (deviation output) ^ 2 := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul,
      mul_one, one_pow, sq_abs] using hcauchy
  exact Real.le_sqrt_of_sq_le hsquare

/-- Exact fiber-count form of ordinary `L²` loss between two deterministic images of possibly
different uniform finite input spaces. -/
noncomputable def twoUniformImagesL2Loss
    {RealInput IdealInput Output : Type}
    [Fintype RealInput] [Fintype IdealInput] [Fintype Output]
    [DecidableEq Output]
    (realTransform : RealInput → Output)
    (idealTransform : IdealInput → Output) : ℝ := by
  exact (1 / 2 : ℝ) *
    Real.sqrt
      ((Fintype.card Output : ℝ) *
        ∑ output : Output,
          ((Fintype.card RealInput : ℝ)⁻¹ *
                ((Finset.univ.filter fun input : RealInput =>
                  realTransform input = output).card : ℝ) -
              (Fintype.card IdealInput : ℝ)⁻¹ *
                ((Finset.univ.filter fun input : IdealInput =>
                  idealTransform input = output).card : ℝ)) ^ 2)

/-- `twoUniformImagesL2Loss` is definitionally the probabilistic `l2Loss` after converting
uniform-image point masses to exact fiber cardinalities. -/
theorem l2Loss_uniformImages_eq_twoUniformImagesL2Loss
    {RealInput IdealInput Output : Type}
    [Fintype RealInput] [Fintype IdealInput] [Fintype Output]
    [DecidableEq Output]
    [SampleableType RealInput] [SampleableType IdealInput]
    (realTransform : RealInput → Output)
    (idealTransform : IdealInput → Output) :
    l2Loss (realTransform <$> ($ᵗ RealInput))
        (idealTransform <$> ($ᵗ IdealInput)) =
      twoUniformImagesL2Loss realTransform idealTransform := by
  unfold l2Loss twoUniformImagesL2Loss
  simp_rw [FormalProof4FHE.LeftoverHash.probOutput_map_uniform_eq_fiberCard,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- Side-wise `L²` cost of replacing the second coordinate of a joint distribution. -/
noncomputable def sidewiseL2Loss {Side Output : Type}
    [Fintype Side] [Fintype Output]
    (real ideal : ProbComp (Side × Output)) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ side : Side,
      Real.sqrt
        ((Fintype.card Output : ℝ) *
          ∑ output : Output,
            (Pr[= (side, output) | real].toReal -
                Pr[= (side, output) | ideal].toReal) ^ 2)

/-- The side-wise collision cost is nonnegative. -/
theorem sidewiseL2Loss_nonneg {Side Output : Type}
    [Fintype Side] [Fintype Output]
    (real ideal : ProbComp (Side × Output)) :
    0 ≤ sidewiseL2Loss real ideal := by
  unfold sidewiseL2Loss
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)

/-- Grouping total variation by a retained side coordinate and applying Cauchy--Schwarz across
the replaced coordinate bounds the complete joint distance by `sidewiseL2Loss`. -/
theorem tvDist_le_sidewiseL2Loss {Side Output : Type}
    [Fintype Side] [Fintype Output]
    (real ideal : ProbComp (Side × Output)) :
    tvDist real ideal ≤ sidewiseL2Loss real ideal := by
  classical
  rw [FormalProof4FHE.LeftoverHash.tvDist_eq_half_sum_abs]
  rw [Fintype.sum_prod_type]
  unfold sidewiseL2Loss
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro side _
  let deviation := fun output : Output =>
    Pr[= (side, output) | real].toReal -
      Pr[= (side, output) | ideal].toReal
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Output => (1 : ℝ))
    (fun output => |deviation output|)
  have hsquare :
      (∑ output : Output, |deviation output|) ^ 2 ≤
        (Fintype.card Output : ℝ) *
          ∑ output : Output, (deviation output) ^ 2 := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul,
      mul_one, one_pow, sq_abs] using hcauchy
  exact Real.le_sqrt_of_sq_le hsquare

/-! ## Output replacement for an arbitrary finite joint law -/

/-- Keep the exact first-coordinate marginal of a joint experiment and resample its second
coordinate independently from a caller-supplied sampler.  This distribution-level form is useful
when the real experiment contains nonuniform error coins in addition to the uniform extractor
coins: all such coins may remain hidden behind the joint law instead of being flattened into one
artificially uniform seed. -/
def sideIndependentOutput
    {Side Output : Type} [Finite Side] [Finite Output]
    (joint : ProbComp (Side × Output)) (outputSampler : ProbComp Output) :
    ProbComp (Side × Output) := do
  let value ← joint
  let output ← outputSampler
  return (value.1, output)

/-- Side-wise finite `L²` loss for replacing the output of an arbitrary joint experiment by an
independent sample.  Unlike a bare total-variation premise, this is an explicit finite sum of
point-mass deviations, grouped by every retained side-information value. -/
noncomputable def outputReplacementL2Loss
    {Side Output : Type} [Fintype Side] [Fintype Output]
    (joint : ProbComp (Side × Output)) (outputSampler : ProbComp Output) : ℝ :=
  sidewiseL2Loss joint (sideIndependentOutput joint outputSampler)

theorem outputReplacementL2Loss_nonneg
    {Side Output : Type} [Fintype Side] [Fintype Output]
    (joint : ProbComp (Side × Output)) (outputSampler : ProbComp Output) :
    0 ≤ outputReplacementL2Loss joint outputSampler :=
  sidewiseL2Loss_nonneg _ _

/-- Replacing the second coordinate of any finite joint law by an independent sample costs at
most its explicit side-wise `L²` loss.  No uniformity, independence, or algebraic assumption is
made about the real joint experiment. -/
theorem tvDist_sideIndependentOutput_le_outputReplacementL2Loss
    {Side Output : Type} [Fintype Side] [Fintype Output]
    (joint : ProbComp (Side × Output)) (outputSampler : ProbComp Output) :
    tvDist joint (sideIndependentOutput joint outputSampler) ≤
      outputReplacementL2Loss joint outputSampler :=
  tvDist_le_sidewiseL2Loss _ _

/-- Pearson chi-square divergence of two finite `ProbComp` output laws.  Points outside the
support of the ideal law contribute zero; the comparison theorem below requires absolute
continuity of the real law with respect to the ideal law. -/
noncomputable def pearsonChiSquare {α : Type} [Fintype α]
    (real ideal : ProbComp α) : ℝ :=
  ∑ value : α,
    if Pr[= value | ideal].toReal = 0 then 0
    else
      (Pr[= value | real].toReal - Pr[= value | ideal].toReal) ^ 2 /
        Pr[= value | ideal].toReal

theorem pearsonChiSquare_nonneg {α : Type} [Fintype α]
    (real ideal : ProbComp α) :
    0 ≤ pearsonChiSquare real ideal := by
  unfold pearsonChiSquare
  apply Finset.sum_nonneg
  intro value _
  split_ifs
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg

/-- Pearson chi-square controls total variation whenever every real output with positive mass
also has positive ideal mass. -/
theorem tvDist_le_sqrt_pearsonChiSquare_div_two
    {α : Type} [Fintype α]
    (real ideal : ProbComp α)
    (hAbsolutelyContinuous : ∀ value : α,
      Pr[= value | ideal].toReal = 0 →
        Pr[= value | real].toReal = 0) :
    tvDist real ideal ≤ Real.sqrt (pearsonChiSquare real ideal) / 2 := by
  classical
  let p := fun value : α => Pr[= value | real].toReal
  let q := fun value : α => Pr[= value | ideal].toReal
  let active := Finset.univ.filter fun value : α => q value ≠ 0
  have hqpos : ∀ value ∈ active, 0 < q value := by
    intro value hvalue
    have hne : q value ≠ 0 := (Finset.mem_filter.1 hvalue).2
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
  have hmass : (∑ value : α, q value) = 1 := by
    dsimp [q]
    rw [← ENNReal.toReal_sum (fun value _ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top
        (probOutput_le_one (mx := ideal) (x := value))),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  have hactiveMass : (∑ value ∈ active, q value) = 1 := by
    calc
      (∑ value ∈ active, q value) =
          ∑ value : α, if q value ≠ 0 then q value else 0 := by
            simp only [active, Finset.sum_filter]
      _ = ∑ value : α, q value := by
            apply Finset.sum_congr rfl
            intro value _
            by_cases hzero : q value = 0 <;> simp [hzero]
      _ = 1 := hmass
  have hAbs :
      (∑ value : α, |p value - q value|) =
        ∑ value ∈ active, |p value - q value| := by
    symm
    calc
      (∑ value ∈ active, |p value - q value|) =
          ∑ value : α,
            if q value ≠ 0 then |p value - q value| else 0 := by
              simp only [active, Finset.sum_filter]
      _ = ∑ value : α, |p value - q value| := by
            apply Finset.sum_congr rfl
            intro value _
            by_cases hzero : q value = 0
            · have hpzero : p value = 0 := by
                exact hAbsolutelyContinuous value (by simpa [q] using hzero)
              simp [hzero, hpzero]
            · simp [hzero]
  have hChi :
      pearsonChiSquare real ideal =
        ∑ value ∈ active, (p value - q value) ^ 2 / q value := by
    unfold pearsonChiSquare
    calc
      (∑ value : α,
          if Pr[= value | ideal].toReal = 0 then 0
          else
            (Pr[= value | real].toReal - Pr[= value | ideal].toReal) ^ 2 /
              Pr[= value | ideal].toReal) =
          ∑ value : α,
            if q value ≠ 0 then (p value - q value) ^ 2 / q value else 0 := by
              apply Finset.sum_congr rfl
              intro value _
              by_cases hzero : q value = 0 <;> simp [p, q, hzero]
      _ = ∑ value ∈ active, (p value - q value) ^ 2 / q value := by
            simp only [active, Finset.sum_filter]
  have htitu := Finset.sq_sum_div_le_sum_sq_div active
    (fun value => |p value - q value|) hqpos
  have hsquareActive :
      (∑ value ∈ active, |p value - q value|) ^ 2 ≤
        ∑ value ∈ active, (p value - q value) ^ 2 / q value := by
    rw [hactiveMass, div_one] at htitu
    simpa only [sq_abs] using htitu
  have hsquare :
      (∑ value : α, |p value - q value|) ^ 2 ≤
        pearsonChiSquare real ideal := by
    rw [hAbs, hChi]
    exact hsquareActive
  have hsqrt :
      (∑ value : α, |p value - q value|) ≤
        Real.sqrt (pearsonChiSquare real ideal) :=
    Real.le_sqrt_of_sq_le hsquare
  rw [FormalProof4FHE.LeftoverHash.tvDist_eq_half_sum_abs]
  change (1 / 2 : ℝ) * (∑ value : α, |p value - q value|) ≤ _
  calc
    _ ≤ (1 / 2 : ℝ) * Real.sqrt (pearsonChiSquare real ideal) :=
      mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = _ := by ring

/-! ## Conditional Pearson collision for arbitrary joint laws -/

/-- A side-independent uniform replacement has point mass equal to the exact side marginal times
one uniform-output mass. -/
theorem probOutput_sideIndependentOutput_uniform
    {Side Output : Type} [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    [SampleableType Output]
    (joint : ProbComp (Side × Output)) (side : Side) (output : Output) :
    Pr[= (side, output) |
        sideIndependentOutput joint ($ᵗ Output)] =
      Pr[= side | Prod.fst <$> joint] *
        (Fintype.card Output : ENNReal)⁻¹ := by
  classical
  simp [sideIndependentOutput, probOutput_bind_eq_sum_fintype,
    probOutput_map_eq_sum_fintype_ite, probOutput_uniformSample]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro value _
  by_cases hside : side = value.1
  · have hcard : (Finset.univ.filter fun fresh : Output ↦ output = fresh).card = 1 := by
      rw [show (Finset.univ.filter fun fresh : Output ↦ output = fresh) = {output} by
        ext fresh
        simp [eq_comm]]
      exact Finset.card_singleton output
    simp [hside, hcard]
  · simp [hside]

/-- Pearson divergence incurred by replacing the output coordinate of an arbitrary finite joint
law by a fresh uniform value while retaining its exact side marginal. -/
noncomputable def outputReplacementChiSquare
    {Side Output : Type} [Fintype Side] [Fintype Output]
    [SampleableType Output]
    (joint : ProbComp (Side × Output)) : ℝ :=
  pearsonChiSquare joint (sideIndependentOutput joint ($ᵗ Output))

/-- Conditional output-collision second moment of an arbitrary joint law.  For each retained
side value it sums squared joint point masses and divides by the side marginal mass; empty side
fibers contribute zero. -/
noncomputable def outputConditionalSecondMoment
    {Side Output : Type} [Fintype Side] [Fintype Output]
    (joint : ProbComp (Side × Output)) : ℝ :=
  ∑ side : Side,
    let sideMass := Pr[= side | Prod.fst <$> joint].toReal
    if sideMass = 0 then 0
    else
      (∑ output : Output, Pr[= (side, output) | joint].toReal ^ 2) / sideMass

/-- One joint point mass is bounded by the corresponding side-marginal mass. -/
theorem jointPoint_toReal_le_sideMarginal
    {Side Output : Type} [Fintype Output]
    (joint : ProbComp (Side × Output)) (side : Side) (output : Output) :
    Pr[= (side, output) | joint].toReal ≤
      Pr[= side | Prod.fst <$> joint].toReal := by
  have hle : Pr[= (side, output) | joint] ≤
      Pr[= side | Prod.fst <$> joint] := by
    rw [probOutput_fst_map_eq_sum]
    exact Finset.single_le_sum
      (fun candidate (_hcandidate : candidate ∈ (Finset.univ : Finset Output)) ↦
        (bot_le : (0 : ENNReal) ≤ Pr[= (side, candidate) | joint]))
      (Finset.mem_univ output)
  exact ENNReal.toReal_mono probOutput_ne_top hle

/-- A zero side marginal forces every joint point in that side fiber to have zero mass. -/
theorem jointPoint_toReal_eq_zero_of_sideMarginal_eq_zero
    {Side Output : Type} [Fintype Output]
    (joint : ProbComp (Side × Output)) (side : Side) (output : Output)
    (hside : Pr[= side | Prod.fst <$> joint].toReal = 0) :
    Pr[= (side, output) | joint].toReal = 0 := by
  have hle := jointPoint_toReal_le_sideMarginal joint side output
  rw [hside] at hle
  exact le_antisymm hle ENNReal.toReal_nonneg

/-- A real joint point with positive mass always has positive mass after independently replacing
its output by a uniform value: its side already has positive marginal mass, and every uniform
output has positive mass. -/
theorem outputReplacement_absolutelyContinuous_uniform
    {Side Output : Type} [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    [SampleableType Output]
    (joint : ProbComp (Side × Output)) (value : Side × Output)
    (hideal : Pr[= value |
        sideIndependentOutput joint ($ᵗ Output)].toReal = 0) :
    Pr[= value | joint].toReal = 0 := by
  have hpoint := probOutput_sideIndependentOutput_uniform
    joint value.1 value.2
  have hproduct :
      Pr[= value.1 | Prod.fst <$> joint].toReal *
          (Fintype.card Output : ℝ)⁻¹ = 0 := by
    rw [hpoint] at hideal
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast] using hideal
  have hcard : (Fintype.card Output : ℝ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card Output ≠ 0))
  have hmarginal : Pr[= value.1 | Prod.fst <$> joint].toReal = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right hcard
  have hle : Pr[= value | joint] ≤ Pr[= value.1 | Prod.fst <$> joint] := by
    rw [probOutput_fst_map_eq_sum]
    simpa only [Prod.eta] using
      (Finset.single_le_sum
        (fun output (_houtput : output ∈ (Finset.univ : Finset Output)) ↦
          (bot_le : (0 : ENNReal) ≤ Pr[= (value.1, output) | joint]))
        (Finset.mem_univ value.2))
  have hleReal := ENNReal.toReal_mono probOutput_ne_top hle
  rw [hmarginal] at hleReal
  exact le_antisymm hleReal ENNReal.toReal_nonneg

/-- Conditional Pearson collision controls replacement of an arbitrary joint output by a fresh
uniform value. -/
theorem tvDist_sideIndependentUniform_le_sqrt_outputReplacementChiSquare_div_two
    {Side Output : Type} [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    [SampleableType Output]
    (joint : ProbComp (Side × Output)) :
    tvDist joint (sideIndependentOutput joint ($ᵗ Output)) ≤
      Real.sqrt (outputReplacementChiSquare joint) / 2 := by
  exact tvDist_le_sqrt_pearsonChiSquare_div_two _ _
    (outputReplacement_absolutelyContinuous_uniform joint)

/-- Exact conditional-collision second-moment form of output-replacement Pearson divergence.
The joint computation is required to be total so its side marginal has unit mass. -/
theorem outputReplacementChiSquare_eq_card_mul_secondMoment_sub_one
    {Side Output : Type} [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    [SampleableType Output]
    (joint : ProbComp (Side × Output))
    (htotal : probFailure joint = 0) :
    outputReplacementChiSquare joint =
      (Fintype.card Output : ℝ) * outputConditionalSecondMoment joint - 1 := by
  classical
  let M : ℝ := Fintype.card Output
  have hM : M ≠ 0 := by
    dsimp [M]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Output ≠ 0)
  have hmarginal (side : Side) :
      (∑ output : Output, Pr[= (side, output) | joint].toReal) =
        Pr[= side | Prod.fst <$> joint].toReal := by
    rw [probOutput_fst_map_eq_sum,
      ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top)]
  have hSide (side : Side) :
      (∑ output : Output,
        let realMass := Pr[= (side, output) | joint].toReal
        let idealMass :=
          Pr[= side | Prod.fst <$> joint].toReal * M⁻¹
        if idealMass = 0 then 0
        else (realMass - idealMass) ^ 2 / idealMass) =
      M *
          (if Pr[= side | Prod.fst <$> joint].toReal = 0 then 0
          else
            (∑ output : Output,
              Pr[= (side, output) | joint].toReal ^ 2) /
                Pr[= side | Prod.fst <$> joint].toReal) -
        Pr[= side | Prod.fst <$> joint].toReal := by
    let sideMass := Pr[= side | Prod.fst <$> joint].toReal
    by_cases hzero : sideMass = 0
    · simp [sideMass, hzero]
    · have hideal : sideMass * M⁻¹ ≠ 0 :=
        mul_ne_zero hzero (inv_ne_zero hM)
      simp only [sideMass, hideal, if_false, hzero]
      have hterm (jointMass : ℝ) :
          (jointMass - sideMass * M⁻¹) ^ 2 / (sideMass * M⁻¹) =
            M * (jointMass ^ 2 / sideMass) - 2 * jointMass + sideMass / M := by
        field_simp [hM, hzero]
        ring
      change
        (∑ output : Output,
          (Pr[= (side, output) | joint].toReal - sideMass * M⁻¹) ^ 2 /
            (sideMass * M⁻¹)) =
          M * ((∑ output : Output,
            Pr[= (side, output) | joint].toReal ^ 2) / sideMass) - sideMass
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      have hfirst :
          (∑ output : Output,
              Pr[= (side, output) | joint].toReal ^ 2 / sideMass) =
            (∑ output : Output,
              Pr[= (side, output) | joint].toReal ^ 2) / sideMass := by
        rw [Finset.sum_div]
      have hsecond :
          (∑ output : Output,
              2 * Pr[= (side, output) | joint].toReal) =
            2 * sideMass := by
        rw [← Finset.mul_sum, hmarginal side]
      rw [hfirst, hsecond]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change
        M * ((∑ output : Output,
              Pr[= (side, output) | joint].toReal ^ 2) / sideMass) -
            2 * sideMass + M * (sideMass / M) =
          M * ((∑ output : Output,
              Pr[= (side, output) | joint].toReal ^ 2) / sideMass) - sideMass
      field_simp [hM, hzero]
      ring
  unfold outputReplacementChiSquare pearsonChiSquare
    outputConditionalSecondMoment
  rw [Fintype.sum_prod_type]
  simp_rw [probOutput_sideIndependentOutput_uniform,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  change
    (∑ side : Side, ∑ output : Output,
      let realMass := Pr[= (side, output) | joint].toReal
      let idealMass := Pr[= side | Prod.fst <$> joint].toReal * M⁻¹
      if idealMass = 0 then 0
      else (realMass - idealMass) ^ 2 / idealMass) =
      M *
        (∑ side : Side,
          if Pr[= side | Prod.fst <$> joint].toReal = 0 then 0
          else
            (∑ output : Output,
              Pr[= (side, output) | joint].toReal ^ 2) /
                Pr[= side | Prod.fst <$> joint].toReal) - 1
  simp_rw [hSide]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsideTotal :
      (∑ side : Side, Pr[= side | Prod.fst <$> joint].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top),
      sum_probOutput_eq_one]
    · exact ENNReal.toReal_one
    · simpa only [probFailure_map] using htotal
  rw [hsideTotal]

/-- Pointwise conditional collision certificate for an arbitrary joint law.  In every retained
side fiber, the output collision mass is at most `1 + ε` times the independent-uniform baseline. -/
def OutputConditionalCollisionBound
    {Side Output : Type} [Fintype Side] [Fintype Output]
    (joint : ProbComp (Side × Output)) (ε : ℝ) : Prop :=
  ∀ side : Side,
    (Fintype.card Output : ℝ) *
        ∑ output : Output, Pr[= (side, output) | joint].toReal ^ 2 ≤
      (1 + ε) * Pr[= side | Prod.fst <$> joint].toReal ^ 2

/-- A pointwise conditional collision certificate bounds the complete output-replacement
Pearson divergence. -/
theorem outputReplacementChiSquare_le_of_conditionalCollisionBound
    {Side Output : Type} [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    [SampleableType Output]
    (joint : ProbComp (Side × Output)) (ε : ℝ)
    (htotal : probFailure joint = 0)
    (hbound : OutputConditionalCollisionBound joint ε) :
    outputReplacementChiSquare joint ≤ ε := by
  classical
  let M : ℝ := Fintype.card Output
  have hlocal (side : Side) :
      M *
          (if Pr[= side | Prod.fst <$> joint].toReal = 0 then 0
          else
            (∑ output : Output,
              Pr[= (side, output) | joint].toReal ^ 2) /
                Pr[= side | Prod.fst <$> joint].toReal) ≤
        (1 + ε) * Pr[= side | Prod.fst <$> joint].toReal := by
    let sideMass := Pr[= side | Prod.fst <$> joint].toReal
    let collisionMass := ∑ output : Output,
      Pr[= (side, output) | joint].toReal ^ 2
    by_cases hzero : sideMass = 0
    · simp [sideMass, hzero]
    · have hpositive : 0 < sideMass :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      have hpair : M * collisionMass ≤ (1 + ε) * sideMass ^ 2 := by
        simpa only [M, collisionMass, sideMass] using hbound side
      rw [if_neg hzero]
      change M * (collisionMass / sideMass) ≤ (1 + ε) * sideMass
      apply (le_of_mul_le_mul_right ?_ hpositive)
      calc
        M * (collisionMass / sideMass) * sideMass = M * collisionMass := by
          field_simp [hzero]
        _ ≤ (1 + ε) * sideMass ^ 2 := hpair
        _ = (1 + ε) * sideMass * sideMass := by ring
  rw [outputReplacementChiSquare_eq_card_mul_secondMoment_sub_one
    joint htotal]
  unfold outputConditionalSecondMoment
  rw [Finset.mul_sum]
  apply (sub_le_iff_le_add).2
  calc
    ∑ side : Side,
        (Fintype.card Output : ℝ) *
          (if Pr[= side | Prod.fst <$> joint].toReal = 0 then 0
          else
            (∑ output : Output,
              Pr[= (side, output) | joint].toReal ^ 2) /
                Pr[= side | Prod.fst <$> joint].toReal) ≤
      ∑ side : Side,
        (1 + ε) * Pr[= side | Prod.fst <$> joint].toReal :=
      Finset.sum_le_sum fun side _ ↦ hlocal side
    _ = (1 + ε) *
        ∑ side : Side, Pr[= side | Prod.fst <$> joint].toReal := by
      rw [Finset.mul_sum]
    _ = ε + 1 := by
      rw [← ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top),
        sum_probOutput_eq_one]
      · simp only [ENNReal.toReal_one]
        ring
      · simpa only [probFailure_map] using htotal

/-- The same conditional collision certificate yields the familiar square-root statistical
loss. -/
theorem tvDist_sideIndependentUniform_le_sqrt_of_conditionalCollisionBound
    {Side Output : Type} [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    [SampleableType Output]
    (joint : ProbComp (Side × Output)) (ε : ℝ)
    (htotal : probFailure joint = 0)
    (hbound : OutputConditionalCollisionBound joint ε) :
    tvDist joint (sideIndependentOutput joint ($ᵗ Output)) ≤
      Real.sqrt ε / 2 := by
  refine (tvDist_sideIndependentUniform_le_sqrt_outputReplacementChiSquare_div_two
    joint).trans ?_
  gcongr
  exact outputReplacementChiSquare_le_of_conditionalCollisionBound
    joint ε htotal hbound

/-- Joint image of a uniform finite input, exposing a retained side value and an output. -/
def uniformJointImage {Input Side Output : Type}
    [SampleableType Input]
    (side : Input → Side) (output : Input → Output) :
    ProbComp (Side × Output) :=
  (fun input => (side input, output input)) <$> ($ᵗ Input)

/-- Ideal experiment with the exact side marginal of a uniform finite input and a fresh,
independent uniform output. -/
def uniformSideIndependentOutput {Input Side Output : Type}
    [SampleableType Input] [SampleableType Output]
    (side : Input → Side) : ProbComp (Side × Output) := do
  let input ← $ᵗ Input
  let output ← $ᵗ Output
  return (side input, output)

/-- The concrete side-information collision loss of a deterministic image of uniform input. -/
noncomputable def conditionalFiberCollisionLoss {Input Side Output : Type}
    [SampleableType Input] [SampleableType Output]
    [Fintype Side] [Fintype Output]
    (side : Input → Side) (output : Input → Output) : ℝ :=
  sidewiseL2Loss (uniformJointImage side output)
    (uniformSideIndependentOutput side)

/-- A deterministic image of uniform input is close to a fresh uniform output even with its
specified side information retained, with the exact side-wise collision loss. -/
theorem tvDist_uniformJointImage_sideIndependent_le
    {Input Side Output : Type}
    [SampleableType Input] [SampleableType Output]
    [Fintype Side] [Fintype Output]
    (side : Input → Side) (output : Input → Output) :
    tvDist (uniformJointImage side output)
        (uniformSideIndependentOutput side) ≤
      conditionalFiberCollisionLoss side output := by
  exact tvDist_le_sidewiseL2Loss _ _

theorem conditionalFiberCollisionLoss_nonneg
    {Input Side Output : Type}
    [SampleableType Input] [SampleableType Output]
    [Fintype Side] [Fintype Output]
    (side : Input → Side) (output : Input → Output) :
    0 ≤ conditionalFiberCollisionLoss side output :=
  sidewiseL2Loss_nonneg _ _

/-- Cardinality of one retained-side fiber. -/
def sideFiberCard {Input Side : Type}
    [Fintype Input] [DecidableEq Side]
    (side : Input → Side) (value : Side) : ℕ :=
  (Finset.univ.filter fun input : Input => side input = value).card

/-- Cardinality of one joint side/output fiber. -/
def jointFiberCard {Input Side Output : Type}
    [Fintype Input] [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output)
    (sideValue : Side) (outputValue : Output) : ℕ :=
  (Finset.univ.filter fun input : Input =>
    side input = sideValue ∧ output input = outputValue).card

/-- The retained-side fibers partition the complete finite input space. -/
theorem sum_sideFiberCard
    {Input Side : Type} [Fintype Input] [Fintype Side] [DecidableEq Side]
    (side : Input → Side) :
    (∑ sideValue : Side, sideFiberCard side sideValue) = Fintype.card Input := by
  classical
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset Input))
    (t := (Finset.univ : Finset Side)) (f := side) (by simp)
  simpa only [Finset.card_univ, sideFiberCard] using hpartition.symm

/-- If retained side information depends only on the first component of a product input, every
side fiber contains the complete second-component space. -/
theorem sideFiberCard_prod_fst
    {Seed Coin Side : Type}
    [Fintype Seed] [Fintype Coin] [DecidableEq Side]
    (side : Seed → Side) (sideValue : Side) :
    sideFiberCard (fun input : Seed × Coin => side input.1) sideValue =
      Fintype.card Coin * sideFiberCard side sideValue := by
  classical
  unfold sideFiberCard
  rw [show
    (Finset.univ.filter fun input : Seed × Coin => side input.1 = sideValue) =
      (Finset.univ.filter fun seed : Seed => side seed = sideValue).product
        (Finset.univ : Finset Coin) by
    ext input
    simp]
  simp [Finset.card_product, Nat.mul_comm]

/-- Real-valued count of ordered pairs in one finite side fiber. -/
theorem sideFiberPairCount_eq_sq
    {Input Side : Type} [Fintype Input] [DecidableEq Side]
    (side : Input → Side) (sideValue : Side) :
    (∑ left : Input, ∑ right : Input,
      if side left = sideValue ∧ side right = sideValue then (1 : ℝ) else 0) =
      (sideFiberCard side sideValue : ℝ) ^ 2 := by
  classical
  have hsingle :
      (∑ input : Input, if side input = sideValue then (1 : ℝ) else 0) =
        (sideFiberCard side sideValue : ℝ) := by
    simp [sideFiberCard]
  calc
    (∑ left : Input, ∑ right : Input,
        if side left = sideValue ∧ side right = sideValue then (1 : ℝ) else 0) =
        (∑ left : Input, if side left = sideValue then (1 : ℝ) else 0) *
          (∑ right : Input, if side right = sideValue then (1 : ℝ) else 0) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro left _
            by_cases hleft : side left = sideValue <;> simp [hleft]
    _ = _ := by rw [hsingle]; ring

theorem sideFiberPairWeightedCount_eq
    {Input Side : Type} [Fintype Input] [DecidableEq Side]
    (side : Input → Side) (sideValue : Side) (weight : ℝ) :
    (∑ left : Input, ∑ right : Input,
      if side left = sideValue ∧ side right = sideValue then weight else 0) =
      weight * (sideFiberCard side sideValue : ℝ) ^ 2 := by
  calc
    (∑ left : Input, ∑ right : Input,
        if side left = sideValue ∧ side right = sideValue then weight else 0) =
        weight *
          (∑ left : Input, ∑ right : Input,
            if side left = sideValue ∧ side right = sideValue then (1 : ℝ) else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro left _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro right _
              by_cases hside : side left = sideValue ∧ side right = sideValue <;>
                simp [hside]
    _ = _ := by rw [sideFiberPairCount_eq_sq]

/-- Summing a nonnegative pair weight only when both inputs lie in the same named side fiber is
bounded by summing that weight over all ordered pairs. -/
theorem sum_sameSidePairWeight_le_total
    {Input Side : Type} [Fintype Input] [Fintype Side] [DecidableEq Side]
    (side : Input → Side) (weight : Input → Input → ℝ)
    (hweight : ∀ left right, 0 ≤ weight left right) :
    (∑ sideValue : Side, ∑ left : Input, ∑ right : Input,
      if side left = sideValue ∧ side right = sideValue then
        weight left right
      else 0) ≤
      ∑ left : Input, ∑ right : Input, weight left right := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro right _
  by_cases heq : side left = side right
  · simp [heq]
  · have hnone : ∀ sideValue,
        ¬(side left = sideValue ∧ side right = sideValue) := by
      intro sideValue hside
      exact heq (hside.1.trans hside.2.symm)
    simpa [hnone] using hweight left right

/-- Dividing each same-side pair weight by the size of that side fiber can only decrease the
total nonnegative pair weight.  Empty fibers contribute zero. -/
theorem sum_sameSidePairWeight_div_fiberCard_le_total
    {Input Side : Type} [Fintype Input] [Fintype Side] [DecidableEq Side]
    (side : Input → Side) (weight : Input → Input → ℝ)
    (hweight : ∀ left right, 0 ≤ weight left right) :
    (∑ sideValue : Side,
      if sideFiberCard side sideValue = 0 then 0
      else
        (∑ left : Input, ∑ right : Input,
          if side left = sideValue ∧ side right = sideValue then
            weight left right
          else 0) / (sideFiberCard side sideValue : ℝ)) ≤
      ∑ left : Input, ∑ right : Input, weight left right := by
  calc
    (∑ sideValue : Side,
        if sideFiberCard side sideValue = 0 then 0
        else
          (∑ left : Input, ∑ right : Input,
            if side left = sideValue ∧ side right = sideValue then
              weight left right
            else 0) / (sideFiberCard side sideValue : ℝ)) ≤
        ∑ sideValue : Side, ∑ left : Input, ∑ right : Input,
          if side left = sideValue ∧ side right = sideValue then
            weight left right
          else 0 := by
      apply Finset.sum_le_sum
      intro sideValue _
      have hpair : 0 ≤ ∑ left : Input, ∑ right : Input,
          if side left = sideValue ∧ side right = sideValue then
            weight left right
          else 0 := by
        apply Finset.sum_nonneg
        intro left _
        apply Finset.sum_nonneg
        intro right _
        split_ifs
        · exact hweight left right
        · exact le_rfl
      by_cases hcard : sideFiberCard side sideValue = 0
      · simp [hcard, hpair]
      · simp only [hcard, if_false]
        apply div_le_self hpair
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard
    _ ≤ ∑ left : Input, ∑ right : Input, weight left right :=
      sum_sameSidePairWeight_le_total side weight hweight

/-- Scaled form of `sum_sameSidePairWeight_div_fiberCard_le_total`. -/
theorem sum_sameSidePairWeight_div_scaledFiberCard_le_total_div
    {Input Side : Type} [Fintype Input] [Fintype Side] [DecidableEq Side]
    (side : Input → Side) (weight : Input → Input → ℝ)
    (hweight : ∀ left right, 0 ≤ weight left right)
    (scale : ℝ) (hscale : 0 < scale) :
    (∑ sideValue : Side,
      if sideFiberCard side sideValue = 0 then 0
      else
        (∑ left : Input, ∑ right : Input,
          if side left = sideValue ∧ side right = sideValue then
            weight left right
          else 0) /
            (scale * (sideFiberCard side sideValue : ℝ))) ≤
      (∑ left : Input, ∑ right : Input, weight left right) / scale := by
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale
  have hterm (sideValue : Side) :
      (if sideFiberCard side sideValue = 0 then 0
      else
        (∑ left : Input, ∑ right : Input,
          if side left = sideValue ∧ side right = sideValue then
            weight left right
          else 0) /
            (scale * (sideFiberCard side sideValue : ℝ))) =
        (if sideFiberCard side sideValue = 0 then 0
        else
          (∑ left : Input, ∑ right : Input,
            if side left = sideValue ∧ side right = sideValue then
              weight left right
            else 0) / (sideFiberCard side sideValue : ℝ)) / scale := by
    by_cases hcard : sideFiberCard side sideValue = 0
    · simp [hcard]
    · have hcardReal : (sideFiberCard side sideValue : ℝ) ≠ 0 := by
        exact_mod_cast hcard
      simp only [hcard, if_false]
      field_simp [hscale_ne, hcardReal]
  simp_rw [hterm]
  conv_lhs => rw [← Finset.sum_div]
  exact (div_le_div_iff_of_pos_right hscale).2
    (sum_sameSidePairWeight_div_fiberCard_le_total side weight hweight)

/-- For a fixed retained-side value, the joint fibers partition its side fiber. -/
theorem sum_jointFiberCard
    {Input Side Output : Type}
    [Fintype Input] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output) (sideValue : Side) :
    (∑ outputValue : Output,
        jointFiberCard side output sideValue outputValue) =
      sideFiberCard side sideValue := by
  classical
  let sideSet := Finset.univ.filter fun input : Input => side input = sideValue
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := sideSet) (t := (Finset.univ : Finset Output)) (f := output) (by simp)
  calc
    (∑ outputValue : Output,
        jointFiberCard side output sideValue outputValue) =
        ∑ outputValue : Output,
          (sideSet.filter fun input => output input = outputValue).card := by
      apply Finset.sum_congr rfl
      intro outputValue _
      unfold jointFiberCard sideSet
      congr 1
      ext input
      simp
    _ = sideSet.card := hpartition.symm
    _ = sideFiberCard side sideValue := by rfl

/-- Every joint side/output fiber is contained in its retained-side fiber. -/
theorem jointFiberCard_le_sideFiberCard
    {Input Side Output : Type}
    [Fintype Input] [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output)
    (sideValue : Side) (outputValue : Output) :
    jointFiberCard side output sideValue outputValue ≤
      sideFiberCard side sideValue := by
  unfold jointFiberCard sideFiberCard
  apply Finset.card_le_card
  intro input hinput
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hinput ⊢
  exact hinput.1

/-- Point probabilities in the real joint image are normalized joint-fiber cardinalities. -/
theorem probOutput_uniformJointImage_eq_jointFiberCard
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output)
    (sideValue : Side) (outputValue : Output) :
    Pr[= (sideValue, outputValue) | uniformJointImage side output] =
      (Fintype.card Input : ENNReal)⁻¹ *
        (jointFiberCard side output sideValue outputValue : ENNReal) := by
  unfold uniformJointImage
  rw [FormalProof4FHE.LeftoverHash.probOutput_map_uniform_eq_fiberCard]
  unfold jointFiberCard
  have hfilter :
      (Finset.univ.filter fun input : Input =>
          (side input, output input) = (sideValue, outputValue)) =
        Finset.univ.filter fun input : Input =>
          side input = sideValue ∧ output input = outputValue := by
    ext input
    simp
  rw [hfilter]

/-- The retained-side marginal of a deterministic uniform-input joint image is the normalized
side-fiber cardinality. -/
theorem probOutput_fst_uniformJointImage_eq_sideFiberCard
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output)
    (sideValue : Side) :
    Pr[= sideValue | Prod.fst <$> uniformJointImage side output] =
      (Fintype.card Input : ENNReal)⁻¹ *
        (sideFiberCard side sideValue : ENNReal) := by
  rw [probOutput_fst_map_eq_sum]
  simp_rw [probOutput_uniformJointImage_eq_jointFiberCard side output]
  rw [← Finset.mul_sum]
  congr 1
  exact_mod_cast sum_jointFiberCard side output sideValue

/-- Literal finite-fiber counts imply the probability-level conditional collision certificate
for a deterministic image of a uniform random tape. -/
theorem outputConditionalCollisionBound_uniformJointImage_of_fiberBound
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output) (ε : ℝ)
    (hfiber : ∀ sideValue : Side,
      (Fintype.card Output : ℝ) *
          ∑ outputValue : Output,
            (jointFiberCard side output sideValue outputValue : ℝ) ^ 2 ≤
        (1 + ε) * (sideFiberCard side sideValue : ℝ) ^ 2) :
    OutputConditionalCollisionBound (uniformJointImage side output) ε := by
  classical
  intro sideValue
  simp_rw [probOutput_uniformJointImage_eq_jointFiberCard side output]
  rw [probOutput_fst_uniformJointImage_eq_sideFiberCard side output]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  let N : ℝ := Fintype.card Input
  let M : ℝ := Fintype.card Output
  have hN : 0 ≤ N⁻¹ ^ 2 := sq_nonneg _
  calc
    M * ∑ outputValue : Output,
          (N⁻¹ * (jointFiberCard side output sideValue outputValue : ℝ)) ^ 2 =
        N⁻¹ ^ 2 *
          (M * ∑ outputValue : Output,
            (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) := by
              simp_rw [mul_pow]
              rw [← Finset.mul_sum]
              ring
    _ ≤ N⁻¹ ^ 2 *
        ((1 + ε) * (sideFiberCard side sideValue : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa only [M] using hfiber sideValue) hN
    _ = (1 + ε) *
        (N⁻¹ * (sideFiberCard side sideValue : ℝ)) ^ 2 := by ring

/-- If an arbitrary joint sampler has an exact uniform-random-tape presentation, a pointwise
finite-fiber count for that presentation supplies its conditional collision certificate. -/
theorem outputConditionalCollisionBound_of_evalDist_eq_uniformJointImage
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    (joint : ProbComp (Side × Output))
    (side : Input → Side) (output : Input → Output) (ε : ℝ)
    (hdist : evalDist joint = evalDist (uniformJointImage side output))
    (hfiber : ∀ sideValue : Side,
      (Fintype.card Output : ℝ) *
          ∑ outputValue : Output,
            (jointFiberCard side output sideValue outputValue : ℝ) ^ 2 ≤
        (1 + ε) * (sideFiberCard side sideValue : ℝ) ^ 2) :
    OutputConditionalCollisionBound joint ε := by
  let uniformJoint := uniformJointImage side output
  have hbound : OutputConditionalCollisionBound uniformJoint ε :=
    outputConditionalCollisionBound_uniformJointImage_of_fiberBound
      side output ε hfiber
  have hmarginal : evalDist (Prod.fst <$> joint) =
      evalDist (Prod.fst <$> uniformJoint) :=
    evalDist_map_eq_of_evalDist_eq hdist Prod.fst
  intro sideValue
  simpa only [uniformJoint, probOutput_congr rfl hdist,
    probOutput_congr rfl hmarginal] using hbound sideValue

/-- Point probabilities in the ideal image are the side-fiber mass times a uniform output
probability. -/
theorem probOutput_uniformSideIndependentOutput_eq_sideFiberCard
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Output] [SampleableType Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (sideValue : Side) (outputValue : Output) :
    Pr[= (sideValue, outputValue) | uniformSideIndependentOutput
        (Output := Output) side] =
      (Fintype.card Input : ENNReal)⁻¹ *
        (sideFiberCard side sideValue : ENNReal) *
        (Fintype.card Output : ENNReal)⁻¹ := by
  classical
  simp [uniformSideIndependentOutput, sideFiberCard,
    probOutput_bind_eq_sum_fintype, probOutput_uniformSample, eq_comm]
  ring

/-- Explicit cardinality form of the retained-side collision loss.  The two normalized terms
inside each square are respectively the real joint-fiber mass and the exact side-fiber mass
times one uniform-output mass. -/
noncomputable def conditionalFiberCardinalityLoss
    {Input Side Output : Type}
    [Fintype Input] [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output] :
    (Input → Side) → (Input → Output) → ℝ :=
  fun side output =>
    (1 / 2 : ℝ) *
      ∑ sideValue : Side,
        Real.sqrt
          ((Fintype.card Output : ℝ) *
            ∑ outputValue : Output,
              ((Fintype.card Input : ℝ)⁻¹ *
                    (jointFiberCard side output sideValue outputValue : ℝ) -
                  (Fintype.card Input : ℝ)⁻¹ *
                    (sideFiberCard side sideValue : ℝ) *
                    (Fintype.card Output : ℝ)⁻¹) ^ 2)

/-- The probability-level collision loss is exactly its normalized finite-fiber cardinality
expression.  This is the bridge used by construction-specific counting arguments. -/
theorem conditionalFiberCollisionLoss_eq_cardinalityLoss
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Side] [DecidableEq Side]
    [Fintype Output] [DecidableEq Output] [SampleableType Output]
    (side : Input → Side) (output : Input → Output) :
    conditionalFiberCollisionLoss side output =
      conditionalFiberCardinalityLoss side output := by
  unfold conditionalFiberCollisionLoss sidewiseL2Loss
    conditionalFiberCardinalityLoss
  apply congrArg (fun value : ℝ => (1 / 2 : ℝ) * value)
  apply Finset.sum_congr rfl
  intro sideValue _
  apply congrArg Real.sqrt
  congr 1
  apply Finset.sum_congr rfl
  intro outputValue _
  rw [probOutput_uniformJointImage_eq_jointFiberCard,
    probOutput_uniformSideIndependentOutput_eq_sideFiberCard]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

/-- Pearson chi-square divergence for the concrete uniform-input joint image, written entirely
as normalized finite-fiber cardinalities. -/
noncomputable def conditionalFiberChiSquare
    {Input Side Output : Type}
    [Fintype Input] [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output) : ℝ :=
  ∑ sideValue : Side, ∑ outputValue : Output,
    let realMass :=
      (Fintype.card Input : ℝ)⁻¹ *
        (jointFiberCard side output sideValue outputValue : ℝ)
    let idealMass :=
      (Fintype.card Input : ℝ)⁻¹ *
        (sideFiberCard side sideValue : ℝ) *
        (Fintype.card Output : ℝ)⁻¹
    if idealMass = 0 then 0 else (realMass - idealMass) ^ 2 / idealMass

/-- Sum of output-fiber second moments normalized by the corresponding retained-side fiber.
This is the collision-pair form of the conditional extractor quantity. -/
noncomputable def conditionalFiberSecondMoment
    {Input Side Output : Type}
    [Fintype Input] [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output) : ℝ :=
  ∑ sideValue : Side,
    if sideFiberCard side sideValue = 0 then 0
    else
      (∑ outputValue : Output,
          (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) /
        (sideFiberCard side sideValue : ℝ)

/-- Number of ordered input pairs in one retained-side fiber whose extracted outputs collide,
represented as a real-valued finite count. -/
noncomputable def conditionalFiberCollisionPairCount
    {Input Side Output : Type}
    [Fintype Input] [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output) (sideValue : Side) : ℝ :=
  ∑ left : Input, ∑ right : Input,
    if side left = sideValue ∧ side right = sideValue ∧
        output left = output right then
      1
    else 0

/-- Product-input expansion of the retained-side collision-pair count.  It first selects the two
seed values in the requested side fiber and then counts collisions between their independent
coin inputs. -/
theorem conditionalFiberCollisionPairCount_prod
    {Seed Coin Side Output : Type}
    [Fintype Seed] [Fintype Coin]
    [DecidableEq Side] [DecidableEq Output]
    (side : Seed → Side) (output : Seed → Coin → Output) (sideValue : Side) :
    conditionalFiberCollisionPairCount
        (fun input : Seed × Coin => side input.1)
        (fun input : Seed × Coin => output input.1 input.2) sideValue =
      ∑ leftSeed : Seed, ∑ rightSeed : Seed,
        if side leftSeed = sideValue ∧ side rightSeed = sideValue then
          ∑ leftCoin : Coin, ∑ rightCoin : Coin,
            if output leftSeed leftCoin = output rightSeed rightCoin then
              1
            else 0
        else 0 := by
  classical
  unfold conditionalFiberCollisionPairCount
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro leftSeed _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rightSeed _
  by_cases hleft : side leftSeed = sideValue
  · by_cases hright : side rightSeed = sideValue
    · simp [hleft, hright]
    · simp [hleft, hright]
  · simp [hleft]

/-- Squared joint-fiber sizes count exactly the ordered colliding pairs inside one side
fiber. -/
theorem sum_jointFiberCard_sq_eq_collisionPairCount
    {Input Side Output : Type}
    [Fintype Input] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output) (sideValue : Side) :
    (∑ outputValue : Output,
        (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) =
      conditionalFiberCollisionPairCount side output sideValue := by
  classical
  simp_rw [show ∀ outputValue : Output,
      (jointFiberCard side output sideValue outputValue : ℝ) =
        ∑ input : Input,
          if side input = sideValue ∧ output input = outputValue then
            (1 : ℝ)
          else 0 by
    intro outputValue
    simp [jointFiberCard]]
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  by_cases hleft : side left = sideValue
  · by_cases hright : side right = sideValue
    · by_cases houtput : output left = output right
      · simp [hleft, hright, houtput]
      · simp [hleft, hright, houtput]
    · simp [hleft, hright]
  · simp [hleft]

/-- Pair-count normal form of the conditional second moment. -/
theorem conditionalFiberSecondMoment_eq_collisionPairCount
    {Input Side Output : Type}
    [Fintype Input] [Fintype Side] [Fintype Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output) :
    conditionalFiberSecondMoment side output =
      ∑ sideValue : Side,
        if sideFiberCard side sideValue = 0 then 0
        else
          conditionalFiberCollisionPairCount side output sideValue /
            (sideFiberCard side sideValue : ℝ) := by
  unfold conditionalFiberSecondMoment
  apply Finset.sum_congr rfl
  intro sideValue _
  rw [sum_jointFiberCard_sq_eq_collisionPairCount]

/-- An indicator sum over a finite predicate is the cardinality of its subtype. -/
theorem indicatorSum_eq_card_subtype
    {α : Type} [Fintype α] (predicate : α → Prop) [DecidablePred predicate] :
    (∑ value : α, if predicate value then (1 : ℝ) else 0) =
      (Fintype.card {value // predicate value} : ℝ) := by
  rw [show Fintype.card {value // predicate value} =
      (Finset.univ.filter predicate).card by
    apply Fintype.card_of_subtype
    intro value
    simp]
  simp

/-- The zero fiber and the range of a homomorphism of finite additive groups partition its
domain exactly.  This integral form is useful when a lower bound on the image cardinality is
available but the map need not be surjective. -/
theorem zeroFiberCard_mul_card_range_addHom_eq_card
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    (transform : Domain →+ Codomain) :
    (Finset.univ.filter fun input : Domain => transform input = 0).card *
        Fintype.card transform.range =
      Fintype.card Domain := by
  classical
  let rangeTransform : Domain →+ transform.range := transform.rangeRestrict
  have hsurjective : Function.Surjective rangeTransform :=
    AddMonoidHom.rangeRestrict_surjective transform
  have hfiber (value : Set.range transform) :
      (Finset.univ.filter fun input : Domain => rangeTransform input = value).card =
        (Finset.univ.filter fun input : Domain => rangeTransform input = 0).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range rangeTransform
      (Set.mem_range.2 (hsurjective value)) (Set.mem_range.2 (hsurjective 0))
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset Domain))
    (t := (Finset.univ : Finset transform.range))
    (f := rangeTransform) (by simp)
  have hzeroFiber :
      (Finset.univ.filter fun input : Domain => transform input = 0) =
        (Finset.univ.filter fun input : Domain => rangeTransform input = 0) := by
    ext input
    simp [rangeTransform, Subtype.ext_iff]
  calc
    (Finset.univ.filter fun input : Domain => transform input = 0).card *
          Fintype.card transform.range =
        ∑ _value : transform.range,
          (Finset.univ.filter fun input : Domain => rangeTransform input = 0).card := by
            rw [hzeroFiber]
            simp [Nat.mul_comm]
    _ = ∑ value : transform.range,
          (Finset.univ.filter fun input : Domain => rangeTransform input = value).card := by
            apply Finset.sum_congr rfl
            intro value _
            exact (hfiber value).symm
    _ = Fintype.card Domain := by
      simpa only [Finset.card_univ] using hpartition.symm

/-- A surjective homomorphism of finite additive groups has the uniform number of preimages at
zero.  This is the counting lemma used when a paired collision equation becomes a rectangular
surjective linear map. -/
theorem zeroFiberCount_addHom_eq_card_div
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    (transform : Domain →+ Codomain) (hsurjective : Function.Surjective transform) :
    (∑ input : Domain, if transform input = 0 then (1 : ℝ) else 0) =
      (Fintype.card Domain : ℝ) / (Fintype.card Codomain : ℝ) := by
  classical
  have hfiber (value : Codomain) :
      (Finset.univ.filter fun input : Domain => transform input = value).card =
        (Finset.univ.filter fun input : Domain => transform input = 0).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range transform
      (Set.mem_range.2 (hsurjective value)) (Set.mem_range.2 (hsurjective 0))
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset Domain))
    (t := (Finset.univ : Finset Codomain)) (f := transform) (by simp)
  have hcardNat :
      Fintype.card Domain = Fintype.card Codomain *
        (Finset.univ.filter fun input : Domain => transform input = 0).card := by
    calc
      Fintype.card Domain =
          ∑ value : Codomain,
            (Finset.univ.filter fun input : Domain => transform input = value).card := by
              simpa only [Finset.card_univ] using hpartition
      _ = ∑ _value : Codomain,
          (Finset.univ.filter fun input : Domain => transform input = 0).card := by
            apply Finset.sum_congr rfl
            intro value _
            exact hfiber value
      _ = _ := by simp
  have hcardReal :
      (Fintype.card Domain : ℝ) = (Fintype.card Codomain : ℝ) *
        ((Finset.univ.filter fun input : Domain => transform input = 0).card : ℝ) := by
    exact_mod_cast hcardNat
  have hcodomain : (Fintype.card Codomain : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Codomain ≠ 0)
  have hcount :
      (∑ input : Domain, if transform input = 0 then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun input : Domain => transform input = 0).card : ℝ) := by
    simp
  rw [hcount]
  field_simp [hcodomain]
  nlinarith

/-- Without surjectivity, the zero fiber of a finite additive homomorphism can only be larger
than the uniform-fiber baseline. -/
theorem card_div_le_zeroFiberCount_addHom
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    (transform : Domain →+ Codomain) :
    (Fintype.card Domain : ℝ) / (Fintype.card Codomain : ℝ) ≤
      ∑ input : Domain, if transform input = 0 then (1 : ℝ) else 0 := by
  classical
  have hzeroRange : (0 : Codomain) ∈ Set.range transform := ⟨0, map_zero transform⟩
  have hfiberLe (value : Codomain) :
      (Finset.univ.filter fun input : Domain => transform input = value).card ≤
        (Finset.univ.filter fun input : Domain => transform input = 0).card := by
    by_cases hvalue : value ∈ Set.range transform
    · exact le_of_eq (AddMonoidHom.card_fiber_eq_of_mem_range
        transform hvalue hzeroRange)
    · have hempty :
      (Finset.univ.filter fun input : Domain => transform input = value) = ∅ := by
        ext input
        constructor
        · intro hinput
          have heq := (Finset.mem_filter.1 hinput).2
          exact (hvalue ⟨input, heq⟩).elim
        · intro hinput
          simp at hinput
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset Domain))
    (t := (Finset.univ : Finset Codomain)) (f := transform) (by simp)
  have hcardNat :
      Fintype.card Domain ≤ Fintype.card Codomain *
        (Finset.univ.filter fun input : Domain => transform input = 0).card := by
    calc
      Fintype.card Domain =
          ∑ value : Codomain,
            (Finset.univ.filter fun input : Domain => transform input = value).card := by
              simpa only [Finset.card_univ] using hpartition
      _ ≤ ∑ _value : Codomain,
          (Finset.univ.filter fun input : Domain => transform input = 0).card :=
            Finset.sum_le_sum fun value _ => hfiberLe value
      _ = _ := by simp
  have hcardReal :
      (Fintype.card Domain : ℝ) ≤ (Fintype.card Codomain : ℝ) *
        ((Finset.univ.filter fun input : Domain => transform input = 0).card : ℝ) := by
    exact_mod_cast hcardNat
  have hcodomain : 0 < (Fintype.card Codomain : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Codomain)
  have hcount :
      (∑ input : Domain, if transform input = 0 then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun input : Domain => transform input = 0).card : ℝ) := by
    simp
  rw [hcount]
  exact (div_le_iff₀ hcodomain).2 (by nlinarith)

/-- Exact collision-pair normal form of the conditional Pearson divergence. -/
theorem conditionalFiberChiSquare_eq_secondMoment
    {Input Side Output : Type}
    [Fintype Input] [Fintype Side] [Fintype Output]
    [Nonempty Input] [Nonempty Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output) :
    conditionalFiberChiSquare side output =
      (Fintype.card Output : ℝ) / (Fintype.card Input : ℝ) *
          conditionalFiberSecondMoment side output - 1 := by
  classical
  let N : ℝ := Fintype.card Input
  let M : ℝ := Fintype.card Output
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Input ≠ 0)
  have hM : M ≠ 0 := by
    dsimp [M]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Output ≠ 0)
  have hSide (sideValue : Side) :
      (∑ outputValue : Output,
          let realMass :=
            N⁻¹ * (jointFiberCard side output sideValue outputValue : ℝ)
          let idealMass :=
            N⁻¹ * (sideFiberCard side sideValue : ℝ) * M⁻¹
          if idealMass = 0 then 0 else (realMass - idealMass) ^ 2 / idealMass) =
        M / N *
            (if sideFiberCard side sideValue = 0 then 0
            else
              (∑ outputValue : Output,
                  (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) /
                (sideFiberCard side sideValue : ℝ)) -
          (sideFiberCard side sideValue : ℝ) / N := by
    by_cases hzero : sideFiberCard side sideValue = 0
    · simp [hzero]
    · have hsideReal : (sideFiberCard side sideValue : ℝ) ≠ 0 := by
        exact_mod_cast hzero
      have hideal :
          N⁻¹ * (sideFiberCard side sideValue : ℝ) * M⁻¹ ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (inv_ne_zero hN) hsideReal) (inv_ne_zero hM)
      simp only [hideal, if_false, hzero]
      have hterm (jointCard : ℕ) :
          (N⁻¹ * (jointCard : ℝ) -
                N⁻¹ * (sideFiberCard side sideValue : ℝ) * M⁻¹) ^ 2 /
              (N⁻¹ * (sideFiberCard side sideValue : ℝ) * M⁻¹) =
            M / N * ((jointCard : ℝ) ^ 2 /
              (sideFiberCard side sideValue : ℝ)) -
              2 * (jointCard : ℝ) / N +
              (sideFiberCard side sideValue : ℝ) / (N * M) := by
        field_simp [hN, hM, hsideReal]
        ring
      simp_rw [hterm]
      have hjoint :
          (∑ outputValue : Output,
              (jointFiberCard side output sideValue outputValue : ℝ)) =
            (sideFiberCard side sideValue : ℝ) := by
        exact_mod_cast sum_jointFiberCard side output sideValue
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      have hfirst :
          (∑ outputValue : Output,
              (jointFiberCard side output sideValue outputValue : ℝ) ^ 2 /
                (sideFiberCard side sideValue : ℝ)) =
            (∑ outputValue : Output,
                (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) /
              (sideFiberCard side sideValue : ℝ) := by
        rw [Finset.sum_div]
      have hsecond :
          (∑ outputValue : Output,
              2 * (jointFiberCard side output sideValue outputValue : ℝ) / N) =
            2 * (sideFiberCard side sideValue : ℝ) / N := by
        rw [← Finset.sum_div, ← Finset.mul_sum, hjoint]
      rw [hfirst, hsecond]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change
        M / N *
              ((∑ outputValue : Output,
                  (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) /
                (sideFiberCard side sideValue : ℝ)) -
            2 * (sideFiberCard side sideValue : ℝ) / N +
            M * ((sideFiberCard side sideValue : ℝ) / (N * M)) =
          M / N *
              ((∑ outputValue : Output,
                  (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) /
                (sideFiberCard side sideValue : ℝ)) -
            (sideFiberCard side sideValue : ℝ) / N
      field_simp [hN, hM, hsideReal]
      ring
  unfold conditionalFiberChiSquare conditionalFiberSecondMoment
  change
    (∑ sideValue : Side,
      ∑ outputValue : Output,
        let realMass :=
          N⁻¹ * (jointFiberCard side output sideValue outputValue : ℝ)
        let idealMass :=
          N⁻¹ * (sideFiberCard side sideValue : ℝ) * M⁻¹
        if idealMass = 0 then 0 else (realMass - idealMass) ^ 2 / idealMass) =
      M / N *
          (∑ sideValue : Side,
            if sideFiberCard side sideValue = 0 then 0
            else
              (∑ outputValue : Output,
                  (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) /
                (sideFiberCard side sideValue : ℝ)) - 1
  simp_rw [hSide]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsideSum :
      (∑ sideValue : Side, (sideFiberCard side sideValue : ℝ)) = N := by
    dsimp [N]
    exact_mod_cast sum_sideFiberCard side
  rw [← Finset.sum_div, hsideSum]
  field_simp [hN]

/-- A pointwise conditional collision bound on every retained-side fiber controls the complete
conditional Pearson divergence.  The hypothesis compares the squared joint-fiber counts with
the uniform-output baseline inside each side fiber. -/
theorem conditionalFiberChiSquare_le_of_secondMoment
    {Input Side Output : Type}
    [Fintype Input] [Fintype Side] [Fintype Output]
    [Nonempty Input] [Nonempty Output]
    [DecidableEq Side] [DecidableEq Output]
    (side : Input → Side) (output : Input → Output) (ε : ℝ)
    (hsecond : ∀ sideValue : Side,
      (Fintype.card Output : ℝ) *
          ∑ outputValue : Output,
            (jointFiberCard side output sideValue outputValue : ℝ) ^ 2 ≤
        (1 + ε) * (sideFiberCard side sideValue : ℝ) ^ 2) :
    conditionalFiberChiSquare side output ≤ ε := by
  classical
  let N : ℝ := Fintype.card Input
  let M : ℝ := Fintype.card Output
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Input)
  have hlocal (sideValue : Side) :
      M / N *
          (if sideFiberCard side sideValue = 0 then 0
          else
            (∑ outputValue : Output,
                (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) /
              (sideFiberCard side sideValue : ℝ)) ≤
        (1 + ε) * (sideFiberCard side sideValue : ℝ) / N := by
    by_cases hzero : sideFiberCard side sideValue = 0
    · simp [hzero]
    · have hsidePos : 0 < (sideFiberCard side sideValue : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      let S : ℝ := ∑ outputValue : Output,
        (jointFiberCard side output sideValue outputValue : ℝ) ^ 2
      have hbound : M * S ≤
          (1 + ε) * (sideFiberCard side sideValue : ℝ) ^ 2 := by
        simpa only [M, S] using hsecond sideValue
      rw [if_neg hzero]
      calc
        M / N * (S / (sideFiberCard side sideValue : ℝ)) =
            (M * S) / (N * (sideFiberCard side sideValue : ℝ)) := by
              field_simp [hNpos.ne', hsidePos.ne']
        _ ≤ ((1 + ε) * (sideFiberCard side sideValue : ℝ) ^ 2) /
              (N * (sideFiberCard side sideValue : ℝ)) :=
          (div_le_div_iff_of_pos_right (mul_pos hNpos hsidePos)).2 hbound
        _ = (1 + ε) * (sideFiberCard side sideValue : ℝ) / N := by
          field_simp [hNpos.ne', hsidePos.ne']
  rw [conditionalFiberChiSquare_eq_secondMoment]
  unfold conditionalFiberSecondMoment
  change
    M / N *
          (∑ sideValue : Side,
            if sideFiberCard side sideValue = 0 then 0
            else
              (∑ outputValue : Output,
                  (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) /
                (sideFiberCard side sideValue : ℝ)) - 1 ≤ ε
  rw [Finset.mul_sum]
  calc
    (∑ sideValue : Side,
          M / N *
            (if sideFiberCard side sideValue = 0 then 0
            else
              (∑ outputValue : Output,
                  (jointFiberCard side output sideValue outputValue : ℝ) ^ 2) /
                (sideFiberCard side sideValue : ℝ))) - 1 ≤
        (∑ sideValue : Side,
          (1 + ε) * (sideFiberCard side sideValue : ℝ) / N) - 1 :=
      sub_le_sub_right (Finset.sum_le_sum fun sideValue _ => hlocal sideValue) 1
    _ = ε := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
      have hsideSum :
          (∑ sideValue : Side, (sideFiberCard side sideValue : ℝ)) = N := by
        dsimp [N]
        exact_mod_cast sum_sideFiberCard side
      rw [hsideSum]
      field_simp [hNpos.ne']
      ring

/-- The real uniform-input joint image is automatically absolutely continuous with respect to
the experiment retaining its side marginal and refreshing the output uniformly. -/
theorem uniformJointImage_absolutelyContinuous_sideIndependent
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Side] [DecidableEq Side]
    [Fintype Output] [DecidableEq Output] [SampleableType Output]
    (side : Input → Side) (output : Input → Output) :
    ∀ value : Side × Output,
      Pr[= value | uniformSideIndependentOutput side].toReal = 0 →
        Pr[= value | uniformJointImage side output].toReal = 0 := by
  rintro ⟨sideValue, outputValue⟩ hideal
  rw [probOutput_uniformSideIndependentOutput_eq_sideFiberCard] at hideal
  rw [probOutput_uniformJointImage_eq_jointFiberCard]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast] at hideal ⊢
  have hInput : (Fintype.card Input : ℝ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Input ≠ 0))
  have hOutput : (Fintype.card Output : ℝ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Output ≠ 0))
  have hSideReal : (sideFiberCard side sideValue : ℝ) = 0 := by
    rcases mul_eq_zero.mp hideal with hleft | hright
    · rcases mul_eq_zero.mp hleft with hinput | hside
      · exact (hInput hinput).elim
      · exact hside
    · exact (hOutput hright).elim
  have hSideNat : sideFiberCard side sideValue = 0 := by
    exact_mod_cast hSideReal
  have hJointNat : jointFiberCard side output sideValue outputValue = 0 :=
    Nat.eq_zero_of_le_zero
      ((jointFiberCard_le_sideFiberCard side output sideValue outputValue).trans_eq
        hSideNat)
  simp [hJointNat]

/-- The probability-level Pearson divergence is exactly the explicit conditional-fiber
chi-square quantity. -/
theorem pearsonChiSquare_uniformJointImage_eq_conditionalFiberChiSquare
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Side] [DecidableEq Side]
    [Fintype Output] [DecidableEq Output] [SampleableType Output]
    (side : Input → Side) (output : Input → Output) :
    pearsonChiSquare (uniformJointImage side output)
        (uniformSideIndependentOutput side) =
      conditionalFiberChiSquare side output := by
  unfold pearsonChiSquare conditionalFiberChiSquare
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro sideValue _
  apply Finset.sum_congr rfl
  intro outputValue _
  rw [probOutput_uniformJointImage_eq_jointFiberCard,
    probOutput_uniformSideIndependentOutput_eq_sideFiberCard]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

/-- Global retained-side chi-square theorem.  This relaxation of the side-wise square-root
bound is often easier to estimate by rank, codimension, or Fourier counting. -/
theorem tvDist_uniformJointImage_sideIndependent_le_chiSquare
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Side] [DecidableEq Side]
    [Fintype Output] [DecidableEq Output] [SampleableType Output]
    (side : Input → Side) (output : Input → Output) :
    tvDist (uniformJointImage side output)
        (uniformSideIndependentOutput side) ≤
      Real.sqrt (conditionalFiberChiSquare side output) / 2 := by
  rw [← pearsonChiSquare_uniformJointImage_eq_conditionalFiberChiSquare side output]
  exact tvDist_le_sqrt_pearsonChiSquare_div_two _ _
    (uniformJointImage_absolutelyContinuous_sideIndependent side output)

/-- Pointwise conditional second-moment control gives a direct total-variation bound for the
retained-side extractor. -/
theorem tvDist_uniformJointImage_sideIndependent_le_of_secondMoment
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Side] [DecidableEq Side]
    [Fintype Output] [DecidableEq Output] [SampleableType Output]
    (side : Input → Side) (output : Input → Output) (ε : ℝ)
    (hsecond : ∀ sideValue : Side,
      (Fintype.card Output : ℝ) *
          ∑ outputValue : Output,
            (jointFiberCard side output sideValue outputValue : ℝ) ^ 2 ≤
        (1 + ε) * (sideFiberCard side sideValue : ℝ) ^ 2) :
    tvDist (uniformJointImage side output)
        (uniformSideIndependentOutput side) ≤ Real.sqrt ε / 2 := by
  calc
    tvDist (uniformJointImage side output)
        (uniformSideIndependentOutput side) ≤
        Real.sqrt (conditionalFiberChiSquare side output) / 2 :=
      tvDist_uniformJointImage_sideIndependent_le_chiSquare side output
    _ ≤ Real.sqrt ε / 2 := by
      gcongr
      exact conditionalFiberChiSquare_le_of_secondMoment side output ε hsecond

theorem conditionalFiberChiSquare_nonneg
    {Input Side Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Side] [DecidableEq Side]
    [Fintype Output] [DecidableEq Output] [SampleableType Output]
    (side : Input → Side) (output : Input → Output) :
    0 ≤ conditionalFiberChiSquare side output := by
  rw [← pearsonChiSquare_uniformJointImage_eq_conditionalFiberChiSquare side output]
  exact pearsonChiSquare_nonneg _ _

end

end FormalProof4FHE.ConditionalCollision
