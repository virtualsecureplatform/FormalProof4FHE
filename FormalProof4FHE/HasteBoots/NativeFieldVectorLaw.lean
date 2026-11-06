module
public import FormalProof4FHE.HasteBoots.NativeFieldVectorFresh
@[expose] public section

/-! Conditional value laws of the actual native collector after any replayable
mixed-oracle past, when its unread stream tail is fresh in the observed cache.
All candidate budgets are analysis prefixes. Their increasing union supplies
an unbounded successful-event bound without a retry cap or success floor.
Supplying freshness from complete causal lineage remains a separate obligation. -/
namespace FormalProof4FHE.HasteBoots.NativeFieldVectorLaw
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeTranscript (FieldPhase Observation)
open OracleProgram (run)
open NativeFieldVectorValues (project)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open scoped Classical
noncomputable section

def values (p fuel count : ℕ) (phase : FieldPhase) (world : World) :=
  project p count 0 (NativeFieldVector.execute p fuel (NativeFieldVector.initial phase count) world).1

theorem program_values (p fuel count : ℕ) (phase : FieldPhase) (world : World) :
    values p fuel count phase world = (run (NativeFieldVectorProgram.program p fuel count phase) world).run.1 := by
  have same := NativeFieldVectorProgram.collect_projection p fuel count phase world
  rw [NativeFieldVector.run_collect] at same
  exact congrArg Prod.fst same

/-- Native finalization emits a receipt without changing the completed
coefficient state produced by the same collector. -/
theorem finished_values (p fuel count : ℕ) (transcript : NativeTranscript.Transcript)
    (label : Input) (world : World) (state : NativeFieldVector.State) (result : NativeTranscript.Transcript)
    (finished : (run (NativeFieldVector.request p fuel transcript label count) world).run.1 = .finished state result) :
    values p fuel count (NativeTranscript.beginField transcript label p count).run.1 world =
      some (fun index : Fin count => (state.values[index.val]?.getD 0 : ZMod p)) := by
  have same := congrArg NativeFieldVector.stateOf finished
  rw [NativeFieldVector.run_request] at same
  change NativeFieldVector.stateOf (NativeFieldVector.finishExecute world
    (NativeFieldVector.execute p fuel (NativeFieldVector.initial (NativeTranscript.beginField transcript label p count).run.1 count) world).1).1 = state at same
  rw [NativeFieldVector.finish_state] at same
  have complete := NativeFieldVector.request_status p fuel transcript label count world
  rw [finished] at complete
  change state.remaining = 0 at complete
  unfold values
  rw [same]
  simp only [project,complete,ite_true,Nat.zero_add]

/-- The native values event is evaluated in the actual posterior of a whole
mixed history. Cache entries outside the fresh unread tail are unrestricted. -/
theorem conditional_uniform {Cfg Payload P : Type}
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (p : ℕ) (valid : 1 < p) [NeZero p] (fuel count : ℕ) (phase : FieldPhase)
    (fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) phase.pending.input phase.consumed.length)
    (event : (Fin count → ZMod p) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (values p fuel count phase other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar p 1) fuel count *
        Pr{let value ← $ᵗ (Fin count → ZMod p)}[event value] := by
  have same : {other | (values p fuel count phase other).elim False event} =
      {other | ((run (NativeFieldVectorProgram.program p fuel count phase) other).run.1).elim False event} := by
    ext other
    change (values p fuel count phase other).elim False event ↔ _
    rw [program_values]
    rfl
  rw [same]
  have transferred := NativeLazyExecutionLaw.execute_law (NativeFieldVectorProgram.program p fuel count phase) replay world enc dummy shape state hashStart
    (fun result => result.1.elim False event)
  exact transferred.trans (NativeFieldVectorFresh.lazy_uniform enc dummy shape state p valid fuel count phase _ fresh event)

theorem conditional_le_uniform {Cfg Payload P : Type}
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (p : ℕ) (valid : 1 < p) [NeZero p] (fuel count : ℕ) (phase : FieldPhase)
    (fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) phase.pending.input phase.consumed.length)
    (event : (Fin count → ZMod p) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (values p fuel count phase other).elim False event} ≤
        Pr{let value ← $ᵗ (Fin count → ZMod p)}[event value] := by
  rw [conditional_uniform replay world enc dummy shape state hashStart p valid fuel count phase fresh event]
  exact mul_le_of_le_one_left' (BudgetedUniformSequence.completion_le_one _ fuel count)

/-- Once a native prefix completes, no later analysis prefix changes its
values. This is resumption of the same reader, not a fresh sampler. -/
theorem event_monotone (p count : ℕ) (phase : FieldPhase) (event : (Fin count → ZMod p) → Prop) :
    Monotone (fun fuel => {world | (values p fuel count phase world).elim False event}) := by
  intro first second ordered world member
  have complete : (NativeFieldVector.execute p first (NativeFieldVector.initial phase count) world).1.remaining = 0 := by
    change (project p count 0 _).elim False event at member
    unfold project at member
    split at member
    · assumption
    · contradiction
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  have same : (NativeFieldVector.execute p (first+extra) (NativeFieldVector.initial phase count) world).1 =
      (NativeFieldVector.execute p first (NativeFieldVector.initial phase count) world).1 := by
    rw [NativeFieldVector.execute_add]
    dsimp only
    rw [NativeFieldVector.execute_complete p extra _ world complete]
  change (project p count 0 _).elim False event
  rw [same]
  exact member

/-- Any eventual successful native values event has at most its joint
uniform probability. Every finite analysis prefix is included, without
conditioning on completion or limiting the native number of attempts. -/
theorem eventual_le_uniform {Cfg Payload P : Type}
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (p : ℕ) (valid : 1 < p) [NeZero p] (count : ℕ) (phase : FieldPhase)
    (fresh : FreshShakeTail.Fresh (NativeShakeKernel.observed (past world).run.2 world) phase.pending.input phase.consumed.length)
    (event : (Fin count → ZMod p) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, (values p fuel count phase other).elim False event} ≤
        Pr{let value ← $ᵗ (Fin count → ZMod p)}[event value] := by
  have same : {other | ∃ fuel, (values p fuel count phase other).elim False event} =
      ⋃ fuel, {other | (values p fuel count phase other).elim False event} := by ext other; simp
  rw [same,(event_monotone p count phase event).measure_iUnion]
  exact iSup_le (fun fuel => conditional_le_uniform replay world enc dummy shape state hashStart p valid fuel count phase fresh event)
end
end FormalProof4FHE.HasteBoots.NativeFieldVectorLaw
