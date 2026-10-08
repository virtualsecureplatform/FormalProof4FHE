/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct

/-!
# Total variation of finite independent products

The product discrepancy is at most the sum of coordinate discrepancies.
The comparison is on complete PMFs and can then be transported through a
shared randomized observation. The ideal coordinates need not be executable
finite `ProbComp` samplers. Boolean game-advantage lemmas retain the reference
computational gap and charge a replacement error in each challenge branch.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.FiniteProductTV

variable {α β : Type}

/-- Shared sampling preserves a uniform bound on the discrepancy of two continuations. -/
theorem etvDist_bind_left_le (seed : PMF α) (left right : α → PMF β) :
    (seed.bind left).etvDist (seed.bind right) ≤
      ∑' value, seed value * (left value).etvDist (right value) := by
  have hright : (∑' value, seed value * (left value).etvDist (right value)) =
      (∑' output, ∑' value, seed value * ENNReal.absDiff (left value output) (right value output)) / 2 := by
    simp only [PMF.etvDist, div_eq_mul_inv, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left,
      mul_assoc]
    exact ENNReal.tsum_comm
  rw [hright]
  simp only [PMF.etvDist, PMF.bind_apply]
  apply ENNReal.div_le_div_right
  apply ENNReal.tsum_le_tsum
  intro output
  calc
    _ ≤ ∑' value, ENNReal.absDiff (seed value * left value output) (seed value * right value output) :=
      ENNReal.absDiff_tsum_le _ _
    _ ≤ _ := ENNReal.tsum_le_tsum fun value ↦ by
      simpa only [mul_comm] using
        ENNReal.absDiff_mul_right_le (left value output) (right value output) (seed value)

/-- Uniform continuation TV bounds lift through arbitrary common side information. -/
theorem etvDist_bind_left_le_const (seed : PMF α) (left right : α → PMF β) (bound : ℝ≥0∞)
    (hbound : ∀ value, (left value).etvDist (right value) ≤ bound) :
    (seed.bind left).etvDist (seed.bind right) ≤ bound := by
  calc
    _ ≤ ∑' value, seed value * (left value).etvDist (right value) := etvDist_bind_left_le seed left right
    _ ≤ ∑' value, seed value * bound := ENNReal.tsum_le_tsum fun value ↦ mul_le_mul' le_rfl (hbound value)
    _ = (∑' value, seed value) * bound := ENNReal.tsum_mul_right
    _ = bound := by rw [seed.tsum_coe, one_mul]

/-- The exact full finite-product TV loss is bounded by the sum of scalar losses. -/
theorem etvDist_fin_mOfFn_le (count : ℕ) (left right : Fin count → PMF α) :
    (Fin.mOfFn count left).etvDist (Fin.mOfFn count right) ≤
      ∑ coordinate, (left coordinate).etvDist (right coordinate) := by
  induction count with
  | zero => simp [Fin.mOfFn]
  | succ count ih =>
    let firstTail : PMF (Fin count → α) := Fin.mOfFn count fun coordinate ↦ left coordinate.succ
    let secondTail : PMF (Fin count → α) := Fin.mOfFn count fun coordinate ↦ right coordinate.succ
    let join (value : α) (rest : Fin count → α) : Fin (count + 1) → α :=
      @Fin.cons count (fun _ : Fin (count + 1) ↦ α) value rest
    let firstNext : α → PMF (Fin (count + 1) → α) := fun value ↦ join value <$> firstTail
    let secondNext : α → PMF (Fin (count + 1) → α) := fun value ↦ join value <$> secondTail
    have htail : firstTail.etvDist secondTail ≤
        ∑ coordinate : Fin count, (left coordinate.succ).etvDist (right coordinate.succ) := ih _ _
    have hfirst : ((left 0).bind firstNext).etvDist ((right 0).bind firstNext) ≤
        (left 0).etvDist (right 0) := PMF.etvDist_bind_right_le firstNext _ _
    have hsecond : ((right 0).bind firstNext).etvDist ((right 0).bind secondNext) ≤
        ∑ coordinate : Fin count, (left coordinate.succ).etvDist (right coordinate.succ) := by
      refine etvDist_bind_left_le_const (α := α) (β := Fin (count + 1) → α)
        (right 0) firstNext secondNext _ (fun value ↦ ?_)
      have hmap := PMF.etvDist_map_le (α' := Fin count → α) (β := Fin (count + 1) → α)
        (join value) firstTail secondTail
      exact hmap.trans htail
    have h := (PMF.etvDist_triangle ((left 0).bind firstNext) ((right 0).bind firstNext)
      ((right 0).bind secondNext)).trans (add_le_add hfirst hsecond)
    have hleft : Fin.mOfFn (count + 1) left = (left 0).bind firstNext := by
      simp only [Fin.mOfFn, firstNext, firstTail, join, map_eq_bind_pure_comp, PMF.monad_bind_eq_bind, Function.comp_def]
    have hright : Fin.mOfFn (count + 1) right = (right 0).bind secondNext := by
      simp only [Fin.mOfFn, secondNext, secondTail, join, map_eq_bind_pure_comp, PMF.monad_bind_eq_bind, Function.comp_def]
    rw [hleft, hright, Fin.sum_univ_succ]
    exact h

/-- Identical scalar coordinates cost at most their scalar discrepancy times the number drawn. -/
theorem etvDist_iid_le (count : ℕ) (left right : PMF α) :
    (Fin.mOfFn count (fun _ ↦ left)).etvDist (Fin.mOfFn count (fun _ ↦ right)) ≤
      count * left.etvDist right := by
  simpa using etvDist_fin_mOfFn_le count (fun _ ↦ left) (fun _ ↦ right)

/-- The PMF model of the actual finite independent product uses the same coordinates. -/
theorem liftM_fin_mOfFn (count : ℕ) (samplers : Fin count → ProbComp α) :
    (liftM (Fin.mOfFn count samplers) : PMF (Fin count → α)) =
      Fin.mOfFn count (fun coordinate ↦ (liftM (samplers coordinate) : PMF α)) := by
  induction count with
  | zero => simp [Fin.mOfFn]
  | succ count ih =>
    simp only [Fin.mOfFn, liftM_bind, liftM_pure, ih]

/-- Exact bridge for the executable IID sampler and arbitrary scalar PMF reference. -/
theorem liftM_sampleIID (count : ℕ) (sampler : ProbComp α) :
    (liftM (ProbComp.sampleIID count sampler) : PMF (Fin count → α)) =
      Fin.mOfFn count (fun _ ↦ (liftM sampler : PMF α)) := by
  exact liftM_fin_mOfFn count (fun _ ↦ sampler)

/-- Probability-gap convention for a pair of Boolean distinguishing games. -/
noncomputable def booleanAdvantage (left right : PMF Bool) : ℝ≥0∞ :=
  ENNReal.absDiff (left true) (right true)

/-- The extended probability gap denotes the usual absolute real acceptance-probability gap. -/
theorem booleanAdvantage_toReal (left right : PMF Bool) :
    (booleanAdvantage left right).toReal = |(left true).toReal - (right true).toReal| :=
  ENNReal.absDiff_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

/-- A Boolean acceptance-probability gap is bounded by total variation. -/
theorem booleanAdvantage_le_etvDist (left right : PMF Bool) :
    booleanAdvantage left right ≤ left.etvDist right := by
  let mark : Bool → Option PUnit := fun value ↦ if value then some () else none
  have hmark (distribution : PMF Bool) :
      (mark <$> distribution) (some ()) = distribution true := by
    simp [PMF.monad_map_eq_map, PMF.map_apply, tsum_fintype, mark]
  have h := PMF.etvDist_map_le mark left right
  rw [PMF.etvDist_option_punit, hmark, hmark] at h
  exact h

/-- Replacing the implementation in both challenge branches adds their two statistical losses.
The reference distinguishing gap remains explicit and must be bounded computationally. -/
theorem booleanAdvantage_le_reference (leftReal rightReal leftReference rightReference : PMF Bool) :
    booleanAdvantage leftReal rightReal ≤
      leftReal.etvDist leftReference + booleanAdvantage leftReference rightReference +
        rightReal.etvDist rightReference := by
  have h := (ENNReal.absDiff_triangle (leftReal true) (leftReference true) (rightReal true)).trans
    (add_le_add le_rfl (ENNReal.absDiff_triangle (leftReference true) (rightReference true) (rightReal true)))
  have hright : ENNReal.absDiff (rightReference true) (rightReal true) ≤
      rightReal.etvDist rightReference := by
    rw [ENNReal.absDiff_comm]
    exact booleanAdvantage_le_etvDist rightReal rightReference
  have hleft := booleanAdvantage_le_etvDist leftReal leftReference
  exact h.trans (by
    simpa only [booleanAdvantage, add_assoc] using
      add_le_add hleft (add_le_add le_rfl hright))

/-- A common pair of randomized game continuations costs at most twice the source TV.
Each continuation may inspect and reuse the whole original source value. -/
theorem booleanAdvantage_bind_le_reference (real reference : PMF α)
    (observe : Bool → α → PMF Bool) :
    booleanAdvantage (real.bind (observe false)) (real.bind (observe true)) ≤
      2 * real.etvDist reference +
        booleanAdvantage (reference.bind (observe false)) (reference.bind (observe true)) := by
  have h := booleanAdvantage_le_reference (real.bind (observe false)) (real.bind (observe true))
    (reference.bind (observe false)) (reference.bind (observe true))
  apply h.trans
  calc
    _ ≤ real.etvDist reference +
        booleanAdvantage (reference.bind (observe false)) (reference.bind (observe true)) +
          real.etvDist reference :=
      add_le_add (add_le_add (PMF.etvDist_bind_right_le (observe false) _ _) le_rfl)
        (PMF.etvDist_bind_right_le (observe true) _ _)
    _ = _ := by ring

end FormalProof4FHE.FiniteProductTV
