module

public import FormalProof4FHE.HasteBoots.CompletedObservation
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-!
# A genuine measure from all increasing completed-observation laws

Completed prefixes are subprobability measures, not distributions normalized
by successful mass. Their increasing outer-measure supremum is a measure;
its countable additivity is proved through Carathéodory measurability. Eventual
completion mass one then makes it a probability measure on full observations.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.CompletedObservationLimit

noncomputable section

variable {A : Type}
local instance : MeasurableSpace A := ⊤

def prefixMeasure (step : ProbComp A) (complete : A → Prop) : Measure A :=
  (𝒟[step]).restrict {value | complete value}

theorem prefix_apply (step : ProbComp A) (complete : A → Prop) (event : Set A) :
    prefixMeasure step complete event = Pr{let value ← step}[complete value ∧ value ∈ event] := by
  rw [prefixMeasure, Measure.restrict_apply MeasurableSet.of_discrete, prEvent_eq_evalDist_of_discrete]
  congr 1
  ext value
  simp [and_comm]

theorem prefix_mono {left right : ProbComp A} {complete : A → Prop}
    (ordered : CompletedObservation.LE left right complete) :
    prefixMeasure left complete ≤ prefixMeasure right complete := by
  intro event
  rw [prefix_apply, prefix_apply]
  exact ordered _

def outer (steps : ℕ → ProbComp A) (complete : A → Prop) : OuterMeasure A :=
  ⨆ n, (prefixMeasure (steps n) complete).toOuterMeasure

theorem outer_apply (steps : ℕ → ProbComp A) (complete : A → Prop) (event : Set A) :
    outer steps complete event = ⨆ n, prefixMeasure (steps n) complete event := by
  simp only [outer, OuterMeasure.iSup_apply, Measure.coe_toOuterMeasure]

/-- Increasing completed laws give the finite partition identity needed for
a countably additive measure. No finite observation-space assumption enters. -/
theorem measurable_outer (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) :
    (⊤ : MeasurableSpace A) ≤ (outer steps complete).caratheodory := by
  intro event _
  apply (OuterMeasure.isCaratheodory_iff_le _).mpr
  intro whole
  simp_rw [outer_apply]
  rw [ENNReal.iSup_add]
  simp_rw [ENNReal.add_iSup]
  apply iSup_le
  intro first
  apply iSup_le
  intro second
  have left := prefix_mono (grows first (max first second) (le_max_left _ _)) (whole ∩ event)
  have right := prefix_mono (grows second (max first second) (le_max_right _ _)) (whole \ event)
  calc _ ≤ prefixMeasure (steps (max first second)) complete (whole ∩ event) +
          prefixMeasure (steps (max first second)) complete (whole \ event) := add_le_add left right
       _ = prefixMeasure (steps (max first second)) complete whole :=
          measure_inter_add_sdiff (μ := prefixMeasure (steps (max first second)) complete) whole
            (MeasurableSet.of_discrete : MeasurableSet event)
       _ ≤ _ := le_iSup (fun n => prefixMeasure (steps n) complete whole) _

/-- The full observation measure uses all operational approximations. -/
def measure (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) : Measure A :=
  (outer steps complete).toMeasure (measurable_outer steps complete grows)

theorem measure_apply (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) (event : Set A) :
    measure steps complete grows event = ⨆ n, Pr{let value ← steps n}[complete value ∧ value ∈ event] := by
  rw [measure, toMeasure_apply _ _ MeasurableSet.of_discrete, outer_apply]
  simp_rw [prefix_apply]

/-- Arbitrary events on the complete trace are limits of their actual finite
prefix probabilities, including events used by adaptive later code. -/
theorem event_tends (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) (event : A → Prop) :
    Filter.Tendsto (fun n => Pr{let value ← steps n}[complete value ∧ event value]) Filter.atTop
      (nhds (measure steps complete grows {value | event value})) := by
  rw [measure_apply]
  exact tendsto_atTop_iSup (fun i j ordered => grows i j ordered event)

/-- Completion mass one is established in the limit, without postselection
or a successful-mass normalization at any finite depth. -/
theorem probability (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete)
    (total : (⨆ n, Pr{let value ← steps n}[complete value]) = 1) :
    IsProbabilityMeasure (measure steps complete grows) := by
  constructor
  rw [measure_apply]
  simpa only [Set.mem_univ, and_true] using total

/-- Partial observations are not fabricated completed outputs of the limit. -/
theorem incomplete_zero (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) :
    measure steps complete grows {value | ¬complete value} = 0 := by
  rw [measure_apply]
  simp

/-- Uniform prefix security bounds pass to the actual full-trace measure. -/
theorem event_bound (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete)
    (event : A → Prop) (epsilon : ENNReal)
    (bounded : ∀ n, Pr{let value ← steps n}[complete value ∧ event value] ≤ epsilon) :
    measure steps complete grows {value | event value} ≤ epsilon := by
  rw [measure_apply]
  exact iSup_le bounded

end

end FormalProof4FHE.HasteBoots.CompletedObservationLimit
