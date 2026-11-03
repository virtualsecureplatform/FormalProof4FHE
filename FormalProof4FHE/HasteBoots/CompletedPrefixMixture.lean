module

public import FormalProof4FHE.HasteBoots.CompletedExpectation

@[expose] public section

/-!
# Actual earlier work before an increasing completed continuation

The prefix is sampled once before the continuation and retained in every
outcome. Each continuation may depend on the complete prefix observation,
including its actual shared state and recorded work. Nonnegative means
compose over this real prefix without moving it after completion.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.CompletedPrefixMixture

noncomputable section

variable {First Later : Type}
local instance : MeasurableSpace First := ⊤
local instance : MeasurableSpace Later := ⊤
local instance : MeasurableSpace (First × Later) := ⊤

def program (before : ProbComp First) (tails : First → ℕ → ProbComp Later) (n : ℕ) : ProbComp (First × Later) := do
  let first ← before
  (fun last => (first, last)) <$> tails first n

def finished (complete : First → Later → Prop) (outcome : First × Later) : Prop := complete outcome.1 outcome.2

variable (before : ProbComp First) (tails : First → ℕ → ProbComp Later) (complete : First → Later → Prop)
  (grows : ∀ first i j, i ≤ j → CompletedObservation.LE (tails first i) (tails first j) (complete first))

include grows in
/-- Completed outcome order is preserved through the actual earlier prefix. -/
theorem ordered {i j : ℕ} (h : i ≤ j) :
    CompletedObservation.LE (program before tails i) (program before tails j) (finished complete) := by
  unfold program
  apply CompletedObservation.bind_same
  intro first
  exact CompletedObservation.map (grows first i j h) _ _ (fun _ => Iff.rfl)

def measure : Measure (First × Later) :=
  CompletedObservationLimit.measure (program before tails) (finished complete)
    (fun _ _ h => ordered before tails complete grows h)

/-- Prefix-restricted means are the actual completion-gated finite means. -/
theorem prefix_integral (step : ProbComp Later) (done : Later → Prop) (cost : Later → ENNReal) :
    (∫⁻ last, cost last ∂CompletedObservationLimit.prefixMeasure step done) =
      ∫⁻ value, value ∂𝒟[(fun last => if done last then cost last else 0) <$> step] := by
  rw [lintegral_id_evalDist_map, CompletedObservationLimit.prefixMeasure,
    ← lintegral_indicator MeasurableSet.of_discrete]
  rfl

include grows in
/-- The inner gated means increase for every actual prefix observation. -/
theorem inner_monotone (cost : First → Later → ENNReal) (first : First) :
    Monotone (fun n => ∫⁻ value, value ∂𝒟[(fun last => if complete first last then cost first last else 0) <$> tails first n]) := by
  intro i j h
  dsimp only
  rw [← prefix_integral (tails first i) (complete first) (cost first),
    ← prefix_integral (tails first j) (complete first) (cost first)]
  exact lintegral_mono' (CompletedObservationLimit.prefix_mono (grows first i j h)) le_rfl

/-- Finite gated expectation is averaged over the actual original prefix. -/
theorem finite_integral (cost : First → Later → ENNReal) (n : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun outcome => if finished complete outcome then cost outcome.1 outcome.2 else 0) <$>
      program before tails n]) =
      ∫⁻ value, value ∂𝒟[(fun first => ∫⁻ value, value ∂𝒟[(fun last =>
        if complete first last then cost first last else 0) <$> tails first n]) <$> before] := by
  rw [program, lintegral_id_evalDist_map_bind]
  simp only [Functor.map_map, finished]
  rfl

/-- The full completed joint mean equals the actual prefix average of the
conditional completed means. All observables may be unbounded or infinite. -/
theorem integral (cost : First → Later → ENNReal) :
    (∫⁻ outcome, cost outcome.1 outcome.2 ∂measure before tails complete grows) =
      ∫⁻ value, value ∂𝒟[(fun first => ∫⁻ last, cost first last ∂CompletedObservationLimit.measure
        (tails first) (complete first) (grows first)) <$> before] := by
  rw [measure, CompletedExpectation.gated, lintegral_id_evalDist_map]
  simp_rw [CompletedExpectation.gated]
  rw [lintegral_iSup (fun _ => Measurable.of_discrete)
    (fun i j h first => inner_monotone tails complete grows cost first h)]
  apply iSup_congr
  intro n
  rw [finite_integral, lintegral_id_evalDist_map]

/-- A probability measure results when every actual prefix's continuation
completes almost surely. No conditioning of the prefix distribution occurs. -/
theorem probability (total : ∀ first, (⨆ n, Pr{let last ← tails first n}[complete first last]) = 1) :
    IsProbabilityMeasure (measure before tails complete grows) := by
  constructor
  rw [← lintegral_one]
  rw [integral before tails complete grows (fun _ _ => 1)]
  have mass (first : First) : (∫⁻ last, (1 : ENNReal) ∂CompletedObservationLimit.measure
      (tails first) (complete first) (grows first)) = 1 := by
    let _ := CompletedObservationLimit.probability (tails first) (complete first) (grows first) (total first)
    simp only [lintegral_one, measure_univ]
  simp only [mass, OracleComp.evalDist_map_const, lintegral_dirac]

end

end FormalProof4FHE.HasteBoots.CompletedPrefixMixture
