/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FinitePMFCompiler

/-!
# Canonical Finite Approximations of Finite PMFs

This module constructs a ticket table for an arbitrary PMF on a nonempty finite type.  For a
positive denominator `D`, every ideal mass is rounded down to a multiple of `1 / D`; the unused
tickets are assigned to one distinguished output.  The resulting table has exactly `D` tickets
and admits a uniform, fully proved approximation bound.

The construction is noncomputable because the ideal PMF may contain irrational masses.  Its
result is nevertheless an ordinary finite `TicketTable`, so all downstream sampler semantics and
certificate checks use the existing finite interface.  This is a mathematical existence
construction, not an efficient table-generation algorithm.
-/

open BigOperators
open scoped ENNReal

namespace FormalProof4FHE.FinitePMFCompiler

namespace TicketTable

variable {Output : Type}

/-- Expand prescribed multiplicities into one finite ticket list. -/
noncomputable def listOfCounts [Fintype Output] (counts : Output → ℕ) : List Output :=
  (Finset.univ : Finset Output).1.toList.flatMap
    (fun value ↦ List.replicate (counts value) value)

theorem length_listOfCounts [Fintype Output] (counts : Output → ℕ) :
    (listOfCounts counts).length = ∑ value, counts value := by
  rw [listOfCounts, List.length_flatMap, Multiset.sum_map_toList]
  simp

theorem count_listOfCounts [Fintype Output] [DecidableEq Output]
    (counts : Output → ℕ) (value : Output) :
    (listOfCounts counts).count value = counts value := by
  rw [listOfCounts, List.count_flatMap, Multiset.sum_map_toList]
  change (∑ candidate ∈ (Finset.univ : Finset Output),
    (List.replicate (counts candidate) candidate).count value) = counts value
  simp [List.count_replicate]

/-- The real masses of a PMF on a finite type sum to one. -/
theorem sum_toReal_eq_one [Fintype Output] (target : PMF Output) :
    ∑ value, (target value).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun value _ ↦ target.apply_ne_top value)]
  have hsum : ∑ value : Output, target value = 1 := by
    simpa only [tsum_fintype] using target.tsum_coe
  rw [hsum]
  simp

/-- Downward-rounded ticket multiplicity before the leftover tickets are assigned. -/
noncomputable def floorCount [Fintype Output]
    (target : PMF Output) (denominator : ℕ) (value : Output) : ℕ :=
  ⌊(denominator : ℝ) * (target value).toReal⌋₊

theorem floorCount_le_scaled [Fintype Output]
    (target : PMF Output) (denominator : ℕ) (value : Output) :
    (floorCount target denominator value : ℝ) ≤
      denominator * (target value).toReal := by
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg denominator) ENNReal.toReal_nonneg)

theorem scaled_lt_floorCount_add_one [Fintype Output]
    (target : PMF Output) (denominator : ℕ) (value : Output) :
    (denominator : ℝ) * (target value).toReal <
      floorCount target denominator value + 1 := by
  exact Nat.lt_floor_add_one _

/-- Total number of downward-rounded tickets. -/
noncomputable def floorTotal [Fintype Output]
    (target : PMF Output) (denominator : ℕ) : ℕ :=
  ∑ value, floorCount target denominator value

theorem floorTotal_le [Fintype Output]
    (target : PMF Output) (denominator : ℕ) :
    floorTotal target denominator ≤ denominator := by
  have hreal : (floorTotal target denominator : ℝ) ≤ denominator := by
    calc
      (floorTotal target denominator : ℝ) =
          ∑ value, (floorCount target denominator value : ℝ) := by
            simp [floorTotal]
      _ ≤ ∑ value, (denominator : ℝ) * (target value).toReal := by
        exact Finset.sum_le_sum fun value _ ↦
          floorCount_le_scaled target denominator value
      _ = (denominator : ℝ) * ∑ value, (target value).toReal := by
        rw [Finset.mul_sum]
      _ = denominator := by rw [sum_toReal_eq_one]; ring
  exact_mod_cast hreal

/-- At most one additional ticket per output is needed to cover all fractional parts. -/
theorem denominator_le_floorTotal_add_card [Fintype Output]
    (target : PMF Output) (denominator : ℕ) :
    denominator ≤ floorTotal target denominator + Fintype.card Output := by
  have hreal : (denominator : ℝ) ≤
      floorTotal target denominator + Fintype.card Output := by
    calc
      (denominator : ℝ) =
          (denominator : ℝ) * ∑ value, (target value).toReal := by
            rw [sum_toReal_eq_one]
            ring
      _ = ∑ value, (denominator : ℝ) * (target value).toReal := by
        rw [Finset.mul_sum]
      _ ≤ ∑ value, ((floorCount target denominator value : ℕ) + 1 : ℝ) := by
        exact Finset.sum_le_sum fun value _ ↦
          (scaled_lt_floorCount_add_one target denominator value).le
      _ = (∑ value, (floorCount target denominator value : ℝ)) +
          ∑ _value : Output, (1 : ℝ) := Finset.sum_add_distrib
      _ = floorTotal target denominator + Fintype.card Output := by
        simp [floorTotal]
  exact_mod_cast hreal

/-- Number of tickets left after downward rounding. -/
noncomputable def leftoverCount [Fintype Output]
    (target : PMF Output) (denominator : ℕ) : ℕ :=
  denominator - floorTotal target denominator

theorem leftoverCount_le_card [Fintype Output]
    (target : PMF Output) (denominator : ℕ) :
    leftoverCount target denominator ≤ Fintype.card Output := by
  have h := denominator_le_floorTotal_add_card target denominator
  unfold leftoverCount
  omega

/-- Rounded multiplicities with every unused ticket assigned to `defaultValue`. -/
noncomputable def roundedCount [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ)
    (value : Output) : ℕ :=
  floorCount target denominator value +
    if value = defaultValue then leftoverCount target denominator else 0

theorem sum_roundedCount [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ) :
    ∑ value, roundedCount target defaultValue denominator value = denominator := by
  have hfloor := floorTotal_le target denominator
  simp only [roundedCount, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  change floorTotal target denominator + leftoverCount target denominator = denominator
  simp only [leftoverCount]
  omega

/-- Canonical denominator-`D` ticket table obtained by downward rounding and leftover assignment. -/
noncomputable def roundedTable [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ)
    (hdenominator : 0 < denominator) : TicketTable Output where
  sizePred := denominator - 1
  tickets := ⟨listOfCounts (roundedCount target defaultValue denominator), by
    rw [length_listOfCounts, sum_roundedCount]
    exact (Nat.sub_add_cancel hdenominator).symm⟩

@[simp]
theorem roundedTable_ticketCount [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ)
    (hdenominator : 0 < denominator) :
    (roundedTable target defaultValue denominator hdenominator).ticketCount = denominator := by
  simp [roundedTable, ticketCount, Nat.sub_add_cancel hdenominator]

@[simp]
theorem roundedTable_count [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ)
    (hdenominator : 0 < denominator) (value : Output) :
    (roundedTable target defaultValue denominator hdenominator).tickets.toList.count value =
      roundedCount target defaultValue denominator value := by
  exact count_listOfCounts _ _

/-- Before leftover assignment, every rounded mass differs from its target by less than one
ticket. -/
theorem abs_floorCount_div_sub_toReal_lt [Fintype Output]
    (target : PMF Output) (denominator : ℕ) (hdenominator : 0 < denominator)
    (value : Output) :
    |(floorCount target denominator value : ℝ) / denominator -
        (target value).toReal| < 1 / denominator := by
  have hdenominatorReal : 0 < (denominator : ℝ) := by exact_mod_cast hdenominator
  have hlower := floorCount_le_scaled target denominator value
  have hupper := scaled_lt_floorCount_add_one target denominator value
  have hdivLower :
      (floorCount target denominator value : ℝ) / denominator ≤
        (target value).toReal := by
    rw [div_le_iff₀ hdenominatorReal]
    simpa [mul_comm] using hlower
  have hdivUpper :
      (target value).toReal <
        (floorCount target denominator value : ℝ) / denominator +
          1 / denominator := by
    rw [← add_div, lt_div_iff₀ hdenominatorReal]
    simpa [mul_comm] using hupper
  have hinversePos : 0 < 1 / (denominator : ℝ) := one_div_pos.mpr hdenominatorReal
  rw [abs_lt]
  constructor <;> linarith

/-- After assigning the leftovers, every empirical mass is within
`(card(Output) + 1) / denominator` of its target mass. -/
theorem abs_roundedCount_div_sub_toReal_le [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ)
    (hdenominator : 0 < denominator) (value : Output) :
    |(roundedCount target defaultValue denominator value : ℝ) / denominator -
        (target value).toReal| ≤
      (Fintype.card Output + 1 : ℕ) / denominator := by
  have hdenominatorReal : 0 < (denominator : ℝ) := by exact_mod_cast hdenominator
  have hfloor :=
    abs_floorCount_div_sub_toReal_lt target denominator hdenominator value
  have hfloorLower :
      -(1 / (denominator : ℝ)) <
        (floorCount target denominator value : ℝ) / denominator -
          (target value).toReal := (abs_lt.mp hfloor).1
  have hfloorUpper :
      (floorCount target denominator value : ℝ) / denominator -
          (target value).toReal ≤ 0 := by
    apply sub_nonpos.mpr
    apply (div_le_iff₀ hdenominatorReal).2
    simpa [mul_comm] using floorCount_le_scaled target denominator value
  have honeLeBound :
      1 / (denominator : ℝ) ≤
        ((Fintype.card Output + 1 : ℕ) : ℝ) / denominator := by
    apply div_le_div_of_nonneg_right _ hdenominatorReal.le
    exact_mod_cast Nat.le_add_left 1 (Fintype.card Output)
  by_cases hvalue : value = defaultValue
  · subst value
    have hleftoverNonneg :
        0 ≤ (leftoverCount target denominator : ℝ) / denominator := by positivity
    have hleftoverLe :
        (leftoverCount target denominator : ℝ) / denominator ≤
          (Fintype.card Output : ℝ) / denominator := by
      apply div_le_div_of_nonneg_right _ hdenominatorReal.le
      exact_mod_cast leftoverCount_le_card target denominator
    have hcardLeBound :
        (Fintype.card Output : ℝ) / denominator ≤
          ((Fintype.card Output + 1 : ℕ) : ℝ) / denominator := by
      apply div_le_div_of_nonneg_right _ hdenominatorReal.le
      exact_mod_cast Nat.le_add_right (Fintype.card Output) 1
    simp only [roundedCount, if_pos]
    have heq :
        ((floorCount target denominator defaultValue +
              leftoverCount target denominator : ℕ) : ℝ) /
              denominator - (target defaultValue).toReal =
          ((floorCount target denominator defaultValue : ℝ) / denominator -
              (target defaultValue).toReal) +
            (leftoverCount target denominator : ℝ) / denominator := by
      push_cast
      field_simp
      ring
    rw [heq, abs_le]
    constructor
    · calc
        -(((Fintype.card Output + 1 : ℕ) : ℝ) / denominator) ≤
            -(1 / (denominator : ℝ)) := neg_le_neg honeLeBound
        _ ≤ (floorCount target denominator defaultValue : ℝ) / denominator -
            (target defaultValue).toReal := hfloorLower.le
        _ ≤ (floorCount target denominator defaultValue : ℝ) / denominator -
              (target defaultValue).toReal +
            (leftoverCount target denominator : ℝ) / denominator :=
          le_add_of_nonneg_right hleftoverNonneg
    · calc
        (floorCount target denominator defaultValue : ℝ) / denominator -
              (target defaultValue).toReal +
            (leftoverCount target denominator : ℝ) / denominator ≤
            0 + (Fintype.card Output : ℝ) / denominator :=
          add_le_add hfloorUpper hleftoverLe
        _ = (Fintype.card Output : ℝ) / denominator := zero_add _
        _ ≤ ((Fintype.card Output + 1 : ℕ) : ℝ) / denominator := hcardLeBound
  · simp only [roundedCount, if_neg hvalue, add_zero]
    exact hfloor.le.trans honeLeBound

/-- Uniform extended-real pointwise bound used by the generic certificate checker. -/
noncomputable def roundedPointwiseBound [Fintype Output] (denominator : ℕ) : ℝ≥0∞ :=
  (Fintype.card Output + 1 : ℕ) / (denominator : ℝ≥0∞)

theorem roundedTable_pointwise [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ)
    (hdenominator : 0 < denominator) (value : Output) :
    ENNReal.absDiff
        (((roundedTable target defaultValue denominator hdenominator).tickets.toList.count value :
            ℝ≥0∞) /
          ((roundedTable target defaultValue denominator hdenominator).ticketCount : ℝ≥0∞))
        (target value) ≤ roundedPointwiseBound (Output := Output) denominator := by
  rw [roundedTable_count, roundedTable_ticketCount]
  have hdenominatorNe : (denominator : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdenominator
  have hempirical :
      ((roundedCount target defaultValue denominator value : ℝ≥0∞) /
          (denominator : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hdenominatorNe
  have habsDiff :
      ENNReal.absDiff
          ((roundedCount target defaultValue denominator value : ℝ≥0∞) /
            (denominator : ℝ≥0∞)) (target value) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hempirical, target.apply_ne_top value⟩)
      (ENNReal.absDiff_le_add _ _)
  have hbound : roundedPointwiseBound (Output := Output) denominator ≠ ⊤ := by
    unfold roundedPointwiseBound
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hdenominatorNe
  apply (ENNReal.toReal_le_toReal habsDiff hbound).mp
  rw [ENNReal.absDiff_toReal hempirical (target.apply_ne_top value)]
  simpa [roundedPointwiseBound, ENNReal.toReal_div, ENNReal.toReal_add] using
    abs_roundedCount_div_sub_toReal_le
      target defaultValue denominator hdenominator value

/-- Canonical proof-carrying denominator-`D` approximation of a finite PMF. -/
noncomputable def roundedCertificate [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ)
    (hdenominator : 0 < denominator) : Certificate target :=
  Certificate.ofPointwise
    (roundedTable target defaultValue denominator hdenominator)
    (roundedPointwiseBound (Output := Output) denominator)
    (by
      unfold roundedPointwiseBound
      exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
        (by exact_mod_cast Nat.ne_of_gt hdenominator))
    (roundedTable_pointwise target defaultValue denominator hdenominator)

@[simp]
theorem roundedCertificate_bound [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ)
    (hdenominator : 0 < denominator) :
    (roundedCertificate target defaultValue denominator hdenominator).bound =
      (Fintype.card Output : ℝ≥0∞) *
        roundedPointwiseBound (Output := Output) denominator / 2 := rfl

@[simp]
theorem roundedCertificate_table [Fintype Output] [DecidableEq Output]
    (target : PMF Output) (defaultValue : Output) (denominator : ℕ)
    (hdenominator : 0 < denominator) :
    (roundedCertificate target defaultValue denominator hdenominator).table =
      roundedTable target defaultValue denominator hdenominator := rfl

end TicketTable

end FormalProof4FHE.FinitePMFCompiler
