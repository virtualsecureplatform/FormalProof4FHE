module
public import FormalProof4FHE.HasteBoots.OracleHistoryComposition
@[expose] public section

/-! Upper bounds on arbitrary events follow from the countable partition of
attainable oracle histories. Event measurability and a measurable reference
chooser are not required for this outer-measure inequality. -/
namespace FormalProof4FHE.HasteBoots.OracleFiberOuterBound
open InputIndexedOracle (World law)
open OracleHistoryCharge (Histories fiber)
open NativeTranscript (Execution)
open MeasureTheory ProbabilityTheory
noncomputable section

theorem sum_bound {T : Type} {past : World → Execution T} (replay : ObservationReplay.Replayable past)
    (event : Set World) (risk : Histories past → ENNReal)
    (localBound : ∀ history, (law[|fiber past history]) event ≤ risk history) :
    law event ≤ ∑' history, risk history * law (fiber past history) := by
  let := OracleHistoryCharge.histories_countable replay
  have cover : event = ⋃ history : Histories past, fiber past history ∩ event := by
    rw [← Set.iUnion_inter,OracleHistoryCharge.fibers_cover,Set.univ_inter]
  rw [cover]
  apply (measure_iUnion_le _).trans
  apply ENNReal.tsum_le_tsum
  intro history
  rw [← cond_mul_eq_inter (OracleHistoryCharge.fiber_measurable replay history) event law]
  exact mul_le_mul' (localBound history) le_rfl

theorem uniform {T : Type} {past : World → Execution T} (replay : ObservationReplay.Replayable past)
    (event : Set World) (risk : ENNReal)
    (localBound : ∀ world, (law[|{other | (past other).run = (past world).run}]) event ≤ risk) : law event ≤ risk := by
  let := OracleHistoryCharge.histories_countable replay
  have bound := sum_bound replay event (fun _ => risk) (by
    intro history
    obtain ⟨world,same⟩ := history.property
    have pointwise := localBound world
    simpa only [fiber,same] using pointwise)
  have total : (∑' history : Histories past, law (fiber past history)) = 1 := by
    have applied := congrArg (fun measure : Measure World => measure Set.univ) (OracleHistoryCharge.law_sum_fibers replay)
    simpa only [Measure.sum_apply _ MeasurableSet.univ,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,measure_univ] using applied.symm
  simpa only [ENNReal.tsum_mul_left,total,mul_one] using bound


/-- Scores are functions of the same actual selecting packet. This upper
bound holds even for a nonmeasurable existential event. -/
theorem score_bound {T : Type} {past : World → Execution T} (replay : ObservationReplay.Replayable past)
    (event : Set World) (score : T × List NativeTranscript.Observation → ENNReal)
    (localBound : ∀ world, (law[|{other | (past other).run = (past world).run}]) event ≤ score (past world).run) :
    law event ≤ ∫⁻ world, score (past world).run ∂law := by
  let := OracleHistoryCharge.histories_countable replay
  have bounded := sum_bound replay event (fun history => score history.val) (by
    intro history
    obtain ⟨world,same⟩ := history.property
    have pointwise := localBound world
    simpa only [fiber,same] using pointwise)
  have integral : (∫⁻ world, score (past world).run ∂law) =
      ∑' history : Histories past, score history.val * law (fiber past history) := by
    calc
      _ = ∑' history : Histories past, ∫⁻ world, score (past world).run ∂law.restrict (fiber past history) := by
        conv_lhs => rw [OracleHistoryCharge.law_sum_fibers replay]
        rw [lintegral_sum_measure]
      _ = _ := by
        congr 1
        funext history
        calc
          _ = ∫⁻ _, score history.val ∂law.restrict (fiber past history) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem (OracleHistoryCharge.fiber_measurable replay history)] with world same
            change (past world).run = history.val at same
            rw [same]
          _ = _ := by simp
  rw [integral]
  exact bounded

end
end FormalProof4FHE.HasteBoots.OracleFiberOuterBound
