module

public import FormalProof4FHE.HasteBoots.ExpectedHazard
@[expose] public section

/-! Adding an actual continuation cannot decrease accumulated expected nonnegative hazard, including state-dependent charges and all return branches. -/
open OracleSpec OracleComp MeasureTheory
namespace FormalProof4FHE.HasteBoots.ExpectedHazardMonotone
noncomputable section
variable {ι : Type} {spec : OracleSpec ι} {State A B : Type}

theorem charge_bind (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (program : OracleComp spec A)
    (next : A → OracleComp spec B) (state : State) :
    ExpectedHazard.charge impl loss program state ≤ ExpectedHazard.charge impl loss (program >>= next) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [ExpectedHazard.charge_pure,pure_bind]; exact bot_le
  | query_bind query tail ih =>
    rw [bind_assoc,ExpectedHazard.charge_query_bind,ExpectedHazard.charge_query_bind]
    exact add_le_add le_rfl (lintegral_id_evalDist_map_mono _ (fun outcome => ih outcome.1 outcome.2))
end
end FormalProof4FHE.HasteBoots.ExpectedHazardMonotone
