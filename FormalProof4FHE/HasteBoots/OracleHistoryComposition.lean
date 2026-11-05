module

public import FormalProof4FHE.HasteBoots.OracleHistoryCharge

@[expose] public section

/-! Exact averaging and refinement of complete oracle-history conditionals.
All attainable histories remain present, including zero-mass fibers under a
further restriction. No query cutoff or successful-completion floor is used. -/
namespace FormalProof4FHE.HasteBoots.OracleHistoryComposition

open MeasureTheory ProbabilityTheory
open InputIndexedOracle (World law)
open NativeTranscript (Execution Observation)
open OracleHistoryCharge (Histories fiber)

noncomputable section

/-- The actual complete histories partition any measure on the original world
sigma algebra, not only its initial product measure. -/
theorem measure_sum_fibers {A : Type} {past : World → Execution A}
    (replay : ObservationReplay.Replayable past) (measure : Measure World) :
    measure = Measure.sum (fun history : Histories past => measure.restrict (fiber past history)) := by
  let := OracleHistoryCharge.histories_countable replay
  have partition := Measure.restrict_iUnion (μ := measure) (OracleHistoryCharge.fibers_disjoint past)
    (OracleHistoryCharge.fiber_measurable replay)
  rw [OracleHistoryCharge.fibers_cover,Measure.restrict_univ] at partition
  exact partition

/-- Exact total probability over full finite histories. Finiteness is required
of the measure, not of the history space, computation or response type. -/
theorem average_event {A : Type} {past : World → Execution A}
    (replay : ObservationReplay.Replayable past) (measure : Measure World) [IsFiniteMeasure measure]
    (event : Set World) (measurable : MeasurableSet event) :
    measure event = ∫⁻ world,
      (measure[|{other | (past other).run = (past world).run}]) event ∂measure := by
  let := OracleHistoryCharge.histories_countable replay
  have integral (history : Histories past) :
      (∫⁻ world, (measure[|{other | (past other).run = (past world).run}]) event
        ∂measure.restrict (fiber past history)) =
      measure (fiber past history) * (measure[|fiber past history]) event := by
    calc _ = ∫⁻ _, (measure[|fiber past history]) event ∂measure.restrict (fiber past history) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem (OracleHistoryCharge.fiber_measurable replay history)] with world same
          change (past world).run = history.val at same
          rw [same]
          rfl
         _ = _ := by simp [mul_comm]
  calc measure event = ∑' history : Histories past, measure (fiber past history ∩ event) := by
          conv_lhs => rw [measure_sum_fibers replay measure]
          rw [Measure.sum_apply _ measurable]
          congr 1
          funext history
          rw [Measure.restrict_apply measurable,Set.inter_comm]
       _ = ∑' history : Histories past,
          ∫⁻ world, (measure[|{other | (past other).run = (past world).run}]) event
            ∂measure.restrict (fiber past history) := by
          congr 1
          funext history
          rw [integral,← cond_mul_eq_inter (OracleHistoryCharge.fiber_measurable replay history) event measure,
            mul_comm]
       _ = _ := by rw [← lintegral_sum_measure,← measure_sum_fibers replay measure]

/-- A later full history determines the earlier one. Conditioning on the
later history therefore composes exactly inside the earlier posterior. -/
theorem refinement_event {A B : Type} {past : World → Execution A} {later : World → Execution B}
    (pastReplay : ObservationReplay.Replayable past) (laterReplay : ObservationReplay.Replayable later)
    (earlier : B × List Observation → A × List Observation)
    (refines : ∀ world, earlier (later world).run = (past world).run)
    (world : World) (event : Set World) (measurable : MeasurableSet event) :
    (law[|{other | (past other).run = (past world).run}]) event =
      ∫⁻ current, (law[|{other | (later other).run = (later current).run}]) event
        ∂law[|{other | (past other).run = (past world).run}] := by
  rw [average_event laterReplay _ event measurable]
  apply lintegral_congr_ae
  filter_upwards [ae_cond_mem (μ := law) (ObservationReplay.fiber_measurable pastReplay world)] with current same
  have subset : {other | (later other).run = (later current).run} ⊆
      {other | (past other).run = (past world).run} := by
    intro other equal
    change (past other).run = (past world).run
    rw [← refines other,equal,refines current]
    exact same
  rw [cond_cond_eq_cond_inter (ObservationReplay.fiber_measurable pastReplay world)
    (ObservationReplay.fiber_measurable laterReplay current) law,Set.inter_eq_right.mpr subset]

end
end FormalProof4FHE.HasteBoots.OracleHistoryComposition
