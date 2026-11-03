module

public import FormalProof4FHE.HasteBoots.CompletedObservationLimit
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-!
# Expectations under the completed-observation limit

Every nonnegative observable, including unbounded retained work, integrates
to the supremum of its completion-gated finite expectations. This does not
replace gated costs by unconditional approximants work: that extra equality needs
a proof controlling the costs of incomplete prefixes.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.CompletedExpectation

noncomputable section

variable {A : Type}
local instance : MeasurableSpace A := ⊤

/-- Simple observables commute with an increasing setwise measure limit. -/
theorem simple (approximants : ℕ → Measure A) (limit : Measure A) (grows : Monotone approximants)
    (sets : ∀ event, limit event = ⨆ n, approximants n event) (cost : SimpleFunc A ENNReal) :
    cost.lintegral limit = ⨆ n, cost.lintegral (approximants n) := by
  simp only [SimpleFunc.lintegral, sets, ENNReal.mul_iSup]
  refine ENNReal.finsetSum_iSup fun i j => ⟨max i j, fun value => ?_⟩
  exact ⟨mul_le_mul' le_rfl (grows (le_max_left i j) _),
    mul_le_mul' le_rfl (grows (le_max_right i j) _)⟩

/-- The integral of any nonnegative observable commutes with the increasing
measure limit. In particular no finite mean or bounded cost is assumed. -/
theorem integral (approximants : ℕ → Measure A) (limit : Measure A) (grows : Monotone approximants)
    (sets : ∀ event, limit event = ⨆ n, approximants n event) (cost : A → ENNReal) :
    (∫⁻ outcome, cost outcome ∂limit) = ⨆ n, ∫⁻ outcome, cost outcome ∂approximants n := by
  simp only [MeasureTheory.lintegral, simple approximants limit grows sets]
  simp_rw [iSup_comm (ι := ℕ)]

/-- Applied to actual completed approximants measures, this identifies the mean of
the retained work observable in the countably additive unbounded law. -/
theorem completed (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete)
    (cost : A → ENNReal) :
    (∫⁻ outcome, cost outcome ∂CompletedObservationLimit.measure steps complete grows) =
      ⨆ n, ∫⁻ outcome, cost outcome ∂CompletedObservationLimit.prefixMeasure (steps n) complete := by
  apply integral
  · intro i j h
    exact CompletedObservationLimit.prefix_mono (grows i j h)
  · intro event
    rw [CompletedObservationLimit.measure, toMeasure_apply _ _ MeasurableSet.of_discrete,
      CompletedObservationLimit.outer_apply]

/-- Finite costs remain completion-gated; no partial work is silently erased
from an unconditional cost theorem or identified with the complete law. -/
theorem gated (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete)
    (cost : A → ENNReal) :
    (∫⁻ outcome, cost outcome ∂CompletedObservationLimit.measure steps complete grows) =
      ⨆ n, ∫⁻ value, value ∂𝒟[(fun outcome => if complete outcome then cost outcome else 0) <$> steps n] := by
  rw [completed]
  apply iSup_congr
  intro n
  rw [lintegral_id_evalDist_map, CompletedObservationLimit.prefixMeasure]
  rw [← lintegral_indicator MeasurableSet.of_discrete]
  rfl

end

end FormalProof4FHE.HasteBoots.CompletedExpectation
