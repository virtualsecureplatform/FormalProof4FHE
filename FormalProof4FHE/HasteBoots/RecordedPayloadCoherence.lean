module
public import FormalProof4FHE.HasteBoots.CheckpointAvailability
public import FormalProof4FHE.HasteBoots.CheckpointHistory
@[expose] public section

/-! One common drift event for all recorded contexts and tree shapes. Payload
agreement is independent of field, code height, lane width and query; any fixed
typed interpretation preserves it. Native owner identity and immutable decoder
parameters still have to supply the same-context/same-root structural facts. -/
namespace FormalProof4FHE.HasteBoots.RecordedPayloadCoherence
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
noncomputable section
variable {Cfg Input Digest Payload : Type} [DecidableEq Digest]

def source (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (tag : Cfg) (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag) :
    SkeletonLeafIndex (shape tag) → Option Payload :=
  fun index => MerkleAvailability.payloadAt enc dummy checkpoint.cumulativeLog checkpoint.root index

theorem source_eq_of_stable (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (state : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (stable : MerklePayloadCheckpoints.StableAt enc dummy shape state log)
    (tag : Cfg) (first second : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints) (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints)
    (sameRoot : first.root = second.root) : source enc dummy shape tag first = source enc dummy shape tag second := by
  funext index
  exact MerklePayloadCheckpoints.same_root_payloads enc dummy shape state log stable tag first second firstRecorded secondRecorded sameRoot index

def Drift (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) : Prop :=
  ∃ (tag : Cfg) (first second : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag),
    ⟨tag,first⟩ ∈ state.checkpoints.checkpoints ∧ ⟨tag,second⟩ ∈ state.checkpoints.checkpoints ∧
    first.root = second.root ∧ source enc dummy shape tag first ≠ source enc dummy shape tag second

variable [DecidableEq Input]

theorem drift_implies_failed (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (audited : CheckpointExecution.Audited enc dummy shape state) (drift : Drift enc dummy shape state) : state.failed = true := by
  rcases drift with ⟨tag,first,second,firstRecorded,secondRecorded,sameRoot,different⟩
  cases clear : state.failed with
  | false => exact False.elim (different (source_eq_of_stable enc dummy shape state.checkpoints state.hash.log (audited.2 clear)
      tag first second firstRecorded secondRecorded sameRoot))
  | true => rfl

variable [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

theorem interpretation_eq_or_bad_on_run {Result Value : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy shape) program).run (CheckpointExecution.empty shape)))
    (tag : Cfg) (first second : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag)
    (firstRecorded : ⟨tag,first⟩ ∈ result.2.checkpoints.checkpoints) (secondRecorded : ⟨tag,second⟩ ∈ result.2.checkpoints.checkpoints)
    (sameRoot : first.root = second.root) (interpret : (SkeletonLeafIndex (shape tag) → Option Payload) → Value) :
    interpret (source enc dummy shape tag first) = interpret (source enc dummy shape tag second) ∨ CheckpointCollision.Bad shape result.2 := by
  classical
  by_cases same : source enc dummy shape tag first = source enc dummy shape tag second
  · exact Or.inl (congrArg interpret same)
  · have initial := CheckpointExecution.good_empty enc dummy shape
    have audited := CheckpointExecution.audited_run implBase enc dummy shape program _ ⟨initial.1,fun _ => initial.2.2⟩ result supported
    exact Or.inr (Or.inl (drift_implies_failed enc dummy shape result.2 audited
      ⟨tag,first,second,firstRecorded,secondRecorded,sameRoot,same⟩))

variable [Fintype Digest]

/-- All contexts, shapes, aliases and eventual interpretations share one
exception charge; none of these selections incurs a separate union bound. -/
theorem drift_from_empty_le_charge {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result) :
    Pr{let result ← ((simulateQ (CheckpointExecution.handler implBase enc dummy shape) program).run (CheckpointExecution.empty shape))}[
      Drift enc dummy shape result.2] ≤ ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy shape)
        (CheckpointCollision.loss base shape) program (CheckpointExecution.empty shape) := by
  apply le_trans (prEvent_mono_of_support _ _ (fun result => CheckpointCollision.Bad shape result.2) ?_)
    (CheckpointCollision.failure_from_empty_le_charge implBase enc dummy shape program)
  intro result supported drift
  have initial := CheckpointExecution.good_empty enc dummy shape
  have audited := CheckpointExecution.audited_run implBase enc dummy shape program _ ⟨initial.1,fun _ => initial.2.2⟩ result supported
  exact Or.inl (drift_implies_failed enc dummy shape result.2 audited drift)

end
end FormalProof4FHE.HasteBoots.RecordedPayloadCoherence
