module

public import FormalProof4FHE.HasteBoots.CompletedPrefixMixture

@[expose] public section

/-!
# Transferring unconditional prefix work to the completed trace law

Finite work splits into completed and incomplete contributions. Increasing
complete-observation laws give convergence of the first contribution. An
actual proof that the second tends to zero identifies the completed mean
with the unconditional work limit; completion probability alone is not used
as a replacement for that work argument.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.CompletedCostTransfer

noncomputable section

variable {A : Type}
local instance : MeasurableSpace A := ⊤

/-- Constant cost on an event has its exact probability-weighted mean. -/
theorem indicator (step : ProbComp A) (event : A → Prop) [DecidablePred event] (cost : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun outcome => if event outcome then cost else 0) <$> step]) =
      Pr{let outcome ← step}[event outcome] * cost := by
  rw [lintegral_id_evalDist_map, prEvent_eq_evalDist_of_discrete]
  have same : (fun outcome => if event outcome then cost else 0) =
      {outcome | event outcome}.indicator (fun _ => cost) := by
    funext outcome
    by_cases present : event outcome <;> simp [present, Set.indicator]
  rw [same, lintegral_indicator_const MeasurableSet.of_discrete, mul_comm]

/-- No finite-prefix work is lost in the completed/incomplete partition. -/
theorem split (step : ProbComp A) (complete : A → Prop) (cost : A → ENNReal) :
    (∫⁻ value, value ∂𝒟[cost <$> step]) =
      (∫⁻ value, value ∂𝒟[(fun outcome => if complete outcome then cost outcome else 0) <$> step]) +
      ∫⁻ value, value ∂𝒟[(fun outcome => if complete outcome then 0 else cost outcome) <$> step] := by
  rw [← lintegral_id_evalDist_map_add]
  have same : cost = (fun outcome => (if complete outcome then cost outcome else 0) +
      (if complete outcome then 0 else cost outcome)) := by
    funext outcome
    by_cases done : complete outcome <;> simp [done]
  rw [← same]

/-- Every nonnegative completed cost converges to its actual limit-law mean. -/
theorem gated_tends (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) (cost : A → ENNReal) :
    Filter.Tendsto
      (fun n => ∫⁻ value, value ∂𝒟[(fun outcome => if complete outcome then cost outcome else 0) <$> steps n])
      Filter.atTop (nhds (∫⁻ outcome, cost outcome ∂CompletedObservationLimit.measure steps complete grows)) := by
  rw [CompletedExpectation.gated]
  apply tendsto_atTop_iSup
  intro i j h
  dsimp only
  rw [← CompletedPrefixMixture.prefix_integral (steps i) complete cost,
    ← CompletedPrefixMixture.prefix_integral (steps j) complete cost]
  exact lintegral_mono' (CompletedObservationLimit.prefix_mono (grows i j h)) le_rfl

/-- A proved vanishing incomplete-work mean transfers the unconditional cost
limit exactly, without finite-mean or bounded-cost assumptions. -/
theorem of_partial_tends_zero (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) (cost : A → ENNReal)
    (target : ENNReal)
    (total_tends : Filter.Tendsto (fun n => ∫⁻ value, value ∂𝒟[cost <$> steps n]) Filter.atTop (nhds target))
    (partial_tends : Filter.Tendsto
      (fun n => ∫⁻ value, value ∂𝒟[(fun outcome => if complete outcome then 0 else cost outcome) <$> steps n])
      Filter.atTop (nhds 0)) :
    (∫⁻ outcome, cost outcome ∂CompletedObservationLimit.measure steps complete grows) = target := by
  have added := (gated_tends steps complete grows cost).add partial_tends
  simp_rw [← split] at added
  simpa only [add_zero] using tendsto_nhds_unique added total_tends

end

end FormalProof4FHE.HasteBoots.CompletedCostTransfer
