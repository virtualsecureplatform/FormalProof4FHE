module
public import FormalProof4FHE.HasteBoots.ReferenceRiskBudget
@[expose] public section

/-! History-selected analysis masks preserve conditional event bounds,
including after a completed replay that retains the original packet. -/
namespace FormalProof4FHE.HasteBoots.MaskedOracleBound
open InputIndexedOracle (World law)
open NativeTranscript (Execution Observation)
open MeasureTheory ProbabilityTheory
noncomputable section

theorem bound {T P : Type} {past : World → Execution T} (replay : ObservationReplay.Replayable past)
    (project : T × List Observation → P) (gate : P → Prop) [DecidablePred gate]
    (event : Set World) (risk : P → ENNReal)
    (conditional : ∀ world, (law[|{other | (past other).run = (past world).run}]) event ≤ risk (project (past world).run)) :
    law {world | gate (project (past world).run) ∧ world ∈ event} ≤
      ∫⁻ world, (if gate (project (past world).run) then risk (project (past world).run) else 0) ∂law := by
  apply OracleFiberOuterBound.score_bound replay _ (fun packet => if gate (project packet) then risk (project packet) else 0)
  intro world
  by_cases eligible : gate (project (past world).run)
  · simp only [eligible,ite_true]
    exact (measure_mono (fun _ occurred => occurred.2)).trans (conditional world)
  · simp only [eligible,ite_false]
    have equal := NativeShakeProjection.conditional_event_congr replay world
      (fun other => gate (project (past other).run) ∧ other ∈ event) (fun _ => False) (by
        intro other same
        rw [same]
        simp only [eligible,false_and])
    simpa only [Set.ofPred_false,measure_empty] using le_of_eq equal

end
end FormalProof4FHE.HasteBoots.MaskedOracleBound
