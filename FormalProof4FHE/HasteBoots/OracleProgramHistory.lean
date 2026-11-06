module
public import FormalProof4FHE.HasteBoots.OracleHistorySnapshot
public import FormalProof4FHE.HasteBoots.OracleProgram
@[expose] public section

/-! Retain the entire selecting history alongside a history-selected native
program result. This analysis boundary composes posterior laws without losing
old prequeries or replacing the native observation log. -/
namespace FormalProof4FHE.HasteBoots.OracleProgramHistory
open InputIndexedOracle (World)
open NativeTranscript (Execution Observation)
open MeasureTheory
noncomputable section

def extend {A B : Type} (past : World → Execution A) (program : A × List Observation → OracleProgram.Program B) (world : World) :
    Execution ((A × List Observation) × B) :=
  let before := (past world).run
  let after := (OracleProgram.run (program before) world).run
  WriterT.mk ((before,after.1),before.2++after.2)

theorem run_extend {A B : Type} (past : World → Execution A) (program : A × List Observation → OracleProgram.Program B) (world : World) :
    (extend past program world).run = (((past world).run,(OracleProgram.run (program (past world).run) world).run.1),
      (past world).run.2++(OracleProgram.run (program (past world).run) world).run.2) := rfl

theorem replay {A B : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past)
    (program : A × List Observation → OracleProgram.Program B) : ObservationReplay.Replayable (extend past program) := by
  constructor
  · intro world
    exact (ObservationReplay.agrees_append _ _ _).mpr ⟨old.truthful world,(OracleProgram.run_replay _).truthful world⟩
  · intro world other truthful
    obtain ⟨first,later⟩ := (ObservationReplay.agrees_append _ _ _).mp truthful
    have before := old.replay world other first
    have after := (OracleProgram.run_replay (program (past world).run)).replay world other later
    simp only [run_extend,before,after]

/-- A replayable finite history has a countable attainable range, even when
its state type is not countable. World-dependent predicates can be assembled
from measurable predicates at each fixed attainable packet. -/
theorem event_measurable {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (event : A × List Observation → World → Prop) (fixed : ∀ packet, MeasurableSet {world | event packet world}) :
    MeasurableSet {world | event (past world).run world} := by
  let := OracleHistoryCharge.histories_countable replay
  have union : {world | event (past world).run world} = ⋃ packet : OracleHistoryCharge.Histories past,
      OracleHistoryCharge.fiber past packet ∩ {world | event packet.val world} := by
    ext world
    constructor
    · intro yes
      exact Set.mem_iUnion.mpr ⟨⟨(past world).run,⟨world,rfl⟩⟩,rfl,yes⟩
    · intro yes
      obtain ⟨packet,same,yes⟩ := Set.mem_iUnion.mp yes
      change (past world).run = packet.val at same
      change event (past world).run world
      rw [same]
      exact yes
  rw [union]
  exact MeasurableSet.iUnion (fun packet => (OracleHistoryCharge.fiber_measurable replay packet).inter (fixed packet.val))
end
end FormalProof4FHE.HasteBoots.OracleProgramHistory
