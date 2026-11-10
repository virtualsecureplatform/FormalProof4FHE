module
public import FormalProof4FHE.HasteBoots.JointMatrixOpening
public import FormalProof4FHE.HasteBoots.RecordedPayloadCoherence
public import FormalProof4FHE.HasteBoots.SubclaimSourceLayout
public import FormalProof4FHE.HasteBoots.CheckpointHistory
@[expose] public section

/-! Coherence of original and reused PCS sources. Same-root checkpoints keep
the same complete word and decoded matrix source when the cumulative history
is stable. Any drift on an actual run from empty exposes the existing common
checkpoint/hash exception and is bounded by one whole-run charge. Context,
code, field and layout parameters are kept fixed; query equality is irrelevant. -/
namespace FormalProof4FHE.HasteBoots.RecordedSourceCoherence
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest]
  {front suffix b m height : ℕ}

abbrev Shape (Cfg : Type) (height : ℕ) := fun _ : Cfg => Skeleton.perfect height
abbrev Snapshot (Input Digest Cfg : Type) (height : ℕ) (tag : Cfg) :=
  Checkpoint Input Digest (MerklePayloadCheckpoints.configuration (Shape Cfg height)) tag

def source (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (tag : Cfg) (checkpoint : Snapshot Input Digest Cfg height tag) : MatrixFold.Cube (front+suffix) → Fin b → F :=
  SubclaimSourceLayout.decodedSource domain capacity radius
    (word (leftCount := 2^front) (b := b) enc dummy (fun _ : Cfg => height) tag checkpoint)

omit [DecidableEq F] in
theorem word_eq_of_stable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape Cfg height))
    (stable : MerklePayloadCheckpoints.StableAt enc dummy (Shape Cfg height) state.checkpoints state.hash.log)
    (tag : Cfg) (first second : Snapshot Input Digest Cfg height tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    word (leftCount := 2^front) (b := b) enc dummy (fun _ : Cfg => height) tag first =
      word (leftCount := 2^front) (b := b) enc dummy (fun _ : Cfg => height) tag second := by
  funext position row lane
  have payloads := MerklePayloadCheckpoints.same_root_payloads enc dummy (Shape Cfg height)
    state.checkpoints state.hash.log stable tag first second firstRecorded secondRecorded sameRoot
    (SkeletonLeafIndex.perfectEquiv height position)
  exact congrArg (fun payload : Option (List F) =>
    NativeColumnLayout.unpackPayload (((2^front)*b)*b) (payload.getD [])
      (NativeColumnLayout.payloadAddress (finProdFinEquiv row) lane)) payloads

theorem source_eq_of_stable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape Cfg height))
    (stable : MerklePayloadCheckpoints.StableAt enc dummy (Shape Cfg height) state.checkpoints state.hash.log)
    (tag : Cfg) (first second : Snapshot Input Digest Cfg height tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    source (front := front) enc dummy domain capacity radius tag first = source enc dummy domain capacity radius tag second :=
  congrArg (SubclaimSourceLayout.decodedSource domain capacity radius)
    (word_eq_of_stable enc dummy state stable tag first second firstRecorded secondRecorded sameRoot)

/-- All same-context/same-root source changes, selected after the run, form
one event. There is no union over openings, aliases, checkpoints or queries. -/
def Drift (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape Cfg height)) : Prop :=
  ∃ (tag : Cfg) (first second : Snapshot Input Digest Cfg height tag),
    ⟨tag,first⟩ ∈ state.checkpoints.checkpoints ∧ ⟨tag,second⟩ ∈ state.checkpoints.checkpoints ∧
    first.root = second.root ∧
    source (front := front) enc dummy domain capacity radius tag first ≠ source enc dummy domain capacity radius tag second

theorem source_eq_of_payload_eq (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (tag : Cfg) (first second : Snapshot Input Digest Cfg height tag)
    (same : RecordedPayloadCoherence.source enc dummy (Shape Cfg height) tag first =
      RecordedPayloadCoherence.source enc dummy (Shape Cfg height) tag second) :
    source (front := front) enc dummy domain capacity radius tag first = source enc dummy domain capacity radius tag second := by
  have words : word (leftCount := 2^front) (b := b) enc dummy (fun _ : Cfg => height) tag first =
      word (leftCount := 2^front) (b := b) enc dummy (fun _ : Cfg => height) tag second := by
    funext position row lane
    have payloads := congrFun same (SkeletonLeafIndex.perfectEquiv height position)
    exact congrArg (fun payload : Option (List F) =>
      NativeColumnLayout.unpackPayload (((2^front)*b)*b) (payload.getD [])
        (NativeColumnLayout.payloadAddress (finProdFinEquiv row) lane)) payloads
  exact congrArg (SubclaimSourceLayout.decodedSource domain capacity radius) words

theorem drift_implies_payload_drift (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape Cfg height))
    (drift : Drift (front := front) enc dummy domain capacity radius state) :
    RecordedPayloadCoherence.Drift enc dummy (Shape Cfg height) state := by
  rcases drift with ⟨tag,first,second,firstRecorded,secondRecorded,sameRoot,different⟩
  exact ⟨tag,first,second,firstRecorded,secondRecorded,sameRoot,
    fun same => different (source_eq_of_payload_eq enc dummy domain capacity radius tag first second same)⟩

variable [DecidableEq Input]

theorem drift_implies_failed (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape Cfg height))
    (audited : CheckpointExecution.Audited enc dummy (Shape Cfg height) state)
    (drift : Drift (front := front) enc dummy domain capacity radius state) : state.failed = true := by
  rcases drift with ⟨tag,first,second,firstRecorded,secondRecorded,sameRoot,different⟩
  cases clear : state.failed with
  | false => exact False.elim (different (source_eq_of_stable enc dummy domain capacity radius state (audited.2 clear)
      tag first second firstRecorded secondRecorded sameRoot))
  | true => rfl

theorem source_eq_or_bad (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape Cfg height))
    (audited : CheckpointExecution.Audited enc dummy (Shape Cfg height) state)
    (tag : Cfg) (first second : Snapshot Input Digest Cfg height tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    source (front := front) enc dummy domain capacity radius tag first = source enc dummy domain capacity radius tag second ∨
      CheckpointCollision.Bad (Shape Cfg height) state := by
  classical
  by_cases same : source (front := front) enc dummy domain capacity radius tag first = source enc dummy domain capacity radius tag second
  · exact Or.inl same
  · exact Or.inr (Or.inl (drift_implies_failed enc dummy domain capacity radius state audited
      ⟨tag,first,second,firstRecorded,secondRecorded,sameRoot,same⟩))

/-- Any source predicate, including a later verifier's masked relation, can
be measured on the original owner snapshot outside the common bad event. -/
theorem predicate_transfer (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape Cfg height))
    (audited : CheckpointExecution.Audited enc dummy (Shape Cfg height) state)
    (tag : Cfg) (first second : Snapshot Input Digest Cfg height tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root)
    (predicate : (MatrixFold.Cube (front+suffix) → Fin b → F) → Prop)
    (falseOriginal : ¬predicate (source enc dummy domain capacity radius tag first)) :
    ¬predicate (source enc dummy domain capacity radius tag second) ∨ CheckpointCollision.Bad (Shape Cfg height) state := by
  rcases source_eq_or_bad enc dummy domain capacity radius state audited tag first second firstRecorded secondRecorded sameRoot with same | bad
  · exact Or.inl (fun valid => falseOriginal (same.symm ▸ valid))
  · exact Or.inr bad

variable [SampleableType Digest] [Fintype Digest] {ι : Type} {base : OracleSpec ι}

theorem drift_from_empty_le_charge {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result) :
    Pr{let result ← ((simulateQ (CheckpointExecution.handler implBase enc dummy (Shape Cfg height)) program).run
      (CheckpointExecution.empty (Shape Cfg height)))}[
        Drift (front := front) enc dummy domain capacity radius result.2] ≤
      ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy (Shape Cfg height))
        (CheckpointCollision.loss base (Shape Cfg height)) program (CheckpointExecution.empty (Shape Cfg height)) := by
  apply le_trans (prEvent_mono_of_support _ _ (fun result => CheckpointCollision.Bad (Shape Cfg height) result.2) ?_)
    (CheckpointCollision.failure_from_empty_le_charge implBase enc dummy (Shape Cfg height) program)
  intro result supported drift
  have initial := CheckpointExecution.good_empty enc dummy (Shape Cfg height)
  have audited := CheckpointExecution.audited_run implBase enc dummy (Shape Cfg height) program _
    ⟨initial.1,fun _ => initial.2.2⟩ result supported
  exact Or.inl (drift_implies_failed enc dummy domain capacity radius result.2 audited drift)

omit [Fintype Digest] in
/-- Actual support from empty initialization discharges the audit invariant;
callers need only structural recorded-owner/root facts, not safety certificates. -/
theorem predicate_transfer_on_run {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape Cfg height))
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy (Shape Cfg height)) program).run
      (CheckpointExecution.empty (Shape Cfg height))))
    (tag : Cfg) (first second : Snapshot Input Digest Cfg height tag)
    (firstRecorded : ⟨tag,first⟩ ∈ result.2.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ result.2.checkpoints.checkpoints) (sameRoot : first.root = second.root)
    (predicate : (MatrixFold.Cube (front+suffix) → Fin b → F) → Prop)
    (falseOriginal : ¬predicate (source enc dummy domain capacity radius tag first)) :
    ¬predicate (source enc dummy domain capacity radius tag second) ∨ CheckpointCollision.Bad (Shape Cfg height) result.2 := by
  have initial := CheckpointExecution.good_empty enc dummy (Shape Cfg height)
  have audited := CheckpointExecution.audited_run implBase enc dummy (Shape Cfg height) program _
    ⟨initial.1,fun _ => initial.2.2⟩ result supported
  exact predicate_transfer enc dummy domain capacity radius result.2 audited tag first second firstRecorded secondRecorded sameRoot predicate falseOriginal

end
end FormalProof4FHE.HasteBoots.RecordedSourceCoherence
