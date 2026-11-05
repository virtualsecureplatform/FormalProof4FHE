module

public import FormalProof4FHE.HasteBoots.NativeShakeProjection
public import FormalProof4FHE.HasteBoots.OracleHistoryComposition

@[expose] public section

/-! Analysis snapshots retain the complete earlier result and log alongside
an actual read/hash response. Their replay certificates give exact posterior
refinement without discarding rejected branches or earlier prequeries. -/
namespace FormalProof4FHE.HasteBoots.OracleHistorySnapshot
open InputIndexedOracle (Input World)
open NativeTranscript (Execution Observation)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
open InputIndexedOracle (law)

noncomputable section

def snapshot {A : Type} (past : World → Execution A) (world : World) : Execution (A × List Observation) :=
  WriterT.mk ((past world).run,(past world).run.2)

theorem snapshot_replay {A : Type} {past : World → Execution A}
    (replay : ObservationReplay.Replayable past) : ObservationReplay.Replayable (snapshot past) := by
  constructor
  · exact replay.truthful
  · intro world other agree
    have same := replay.replay world other agree
    simp only [snapshot,WriterT.run_mk,same]

def read {A : Type} (past : World → Execution A) (input : Input) (offset count : ℕ) (world : World) :
    Execution ((A × List Observation) × Input) := do
  let before ← snapshot past world
  let bytes ← ObservationReplay.read world input offset count
  pure (before,bytes)

theorem read_replay {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (input : Input) (offset count : ℕ) : ObservationReplay.Replayable (read past input offset count) := by
  apply ObservationReplay.bind_replay (snapshot_replay replay)
  intro before
  exact ObservationReplay.bind_replay (ObservationReplay.read_replay input offset count)
    (fun bytes => ObservationReplay.pure_replay (before,bytes))

theorem read_run {A : Type} (past : World → Execution A) (input : Input) (offset count : ℕ) (world : World) :
    (read past input offset count world).run =
      (((past world).run,InputIndexedOracle.bytes world input offset count),
        (past world).run.2 ++ [.output input offset (InputIndexedOracle.bytes world input offset count)]) := rfl


def hash {A : Type} (past : World → Execution A) (input : Input) (world : World) :
    Execution ((A × List Observation) × Digest) := do
  let before ← snapshot past world
  let digest ← ObservationReplay.hash world input
  pure (before,digest)

theorem hash_replay {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (input : Input) : ObservationReplay.Replayable (hash past input) := by
  apply ObservationReplay.bind_replay (snapshot_replay replay)
  intro before
  exact ObservationReplay.bind_replay (ObservationReplay.hash_replay input)
    (fun digest => ObservationReplay.pure_replay (before,digest))

theorem hash_run {A : Type} (past : World → Execution A) (input : Input) (world : World) :
    (hash past input world).run =
      (((past world).run,InputIndexedOracle.sha512 world input),
        (past world).run.2 ++ [.hash input (List.ofFn (InputIndexedOracle.sha512 world input))]) := rfl

theorem read_average {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world : World) (input : Input) (offset count : ℕ) (event : Set World) (measurable : MeasurableSet event) :
    (law[|{other | (past other).run = (past world).run}]) event =
      ∫⁻ current, (law[|{other | (read past input offset count other).run =
        (read past input offset count current).run}]) event
        ∂law[|{other | (past other).run = (past world).run}] :=
  OracleHistoryComposition.refinement_event replay (read_replay replay input offset count)
    (fun history => history.1.1) (fun _ => rfl) world event measurable

theorem hash_average {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world : World) (input : Input) (event : Set World) (measurable : MeasurableSet event) :
    (law[|{other | (past other).run = (past world).run}]) event =
      ∫⁻ current, (law[|{other | (hash past input other).run = (hash past input current).run}]) event
        ∂law[|{other | (past other).run = (past world).run}] :=
  OracleHistoryComposition.refinement_event replay (hash_replay replay input)
    (fun history => history.1.1) (fun _ => rfl) world event measurable

end
end FormalProof4FHE.HasteBoots.OracleHistorySnapshot
