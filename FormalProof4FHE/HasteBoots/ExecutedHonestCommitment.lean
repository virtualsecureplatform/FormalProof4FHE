module
public import FormalProof4FHE.HasteBoots.HonestMerkleTranscript
public import FormalProof4FHE.HasteBoots.RecordedCheckpointQueries
public import FormalProof4FHE.HasteBoots.CheckpointHistory
@[expose] public section

/-! Execute honest payload commitments against the verifier's shared cached
oracle, then record their actual roots at the actual cumulative transcript. -/
namespace FormalProof4FHE.HasteBoots.ExecutedHonestCommitment
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {Cfg Input Digest Payload : Type} {ι : Type} {base : OracleSpec ι}

/-- The existing Merkle builder, with both leaf and node queries routed into
exactly the shared hash oracle used by verification. -/
def program (enc : MerkleOracle.Encoding Input Digest Payload) {s : Skeleton}
    (payloads : LeafData Payload s) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (FullData Digest s) :=
  AddressedMerkleTree.buildMerkleTreeAddressedM
    (fun index => (CheckpointExecution.Spec base Cfg Input Digest).query
      (.inr (.inl (enc.leaf () (payloads.get index)))))
    (fun _ left right => (CheckpointExecution.Spec base Cfg Input Digest).query
      (.inr (.inl (enc.node () (left,right)))))

/-- Freeze the computed root immediately after its actual builder execution. -/
def commit (enc : MerkleOracle.Encoding Input Digest Payload) (shape : Cfg → Skeleton)
    (tag : Cfg) (payloads : LeafData Payload (shape tag)) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (FullData Digest (shape tag)) := do
  let labels ← program enc payloads
  let _ ← (CheckpointExecution.Spec base Cfg Input Digest).query (.inr (.inr (tag,labels.getRootValue)))
  pure labels

/-- A total answer function agreeing with all actual builder queries realizes
the actual returned tree, even when distinct queries have equal responses. -/
theorem tree_of_answers (enc : MerkleOracle.Encoding Input Digest Payload) (hash : Input → Digest)
    {s : Skeleton} (payloads : LeafData Payload s) (labels : FullData Digest s)
    (answered : ∀ entry ∈ HonestMerkleTranscript.queries enc payloads labels,
      hash entry.1 = entry.2) : HonestMerkleTranscript.tree enc hash payloads = labels := by
  induction payloads with
  | leaf payload =>
      cases labels with
      | leaf label =>
          have equal := answered _ (List.mem_singleton_self _)
          change FullData.leaf (hash (enc.leaf () payload)) = FullData.leaf label
          rw [equal]
  | internal left right ihLeft ihRight =>
      cases labels with
      | internal root l r =>
          have leftEqual := ihLeft l (fun entry member =>
            answered entry (List.mem_append_left _ (List.mem_append_left _ member)))
          have rightEqual := ihRight r (fun entry member =>
            answered entry (List.mem_append_left _ (List.mem_append_right _ member)))
          have parent := answered _ (List.mem_append_right _ (List.mem_singleton_self _))
          change FullData.internal
            (hash (enc.node () ((HonestMerkleTranscript.tree enc hash left).getRootValue,
              (HonestMerkleTranscript.tree enc hash right).getRootValue)))
            (HonestMerkleTranscript.tree enc hash left)
            (HonestMerkleTranscript.tree enc hash right) = FullData.internal root l r
          rw [leftEqual, rightEqual]
          rw [parent]

section Runtime
variable [DecidableEq Input] [SampleableType Digest]

theorem hash_log (query : Input) (state : CachedHashHandler.State Input Digest)
    (result : Digest × CachedHashHandler.State Input Digest)
    (supported : result ∈ support ((CachedHashHandler.handler query).run state)) :
    result.2.log = state.log ++ [⟨query,result.1⟩] := by
  cases known : state.cache query with
  | none =>
      rw [CachedHashHandler.run_fresh state query known, support_map, Set.mem_image] at supported
      obtain ⟨answer, _, equal⟩ := supported
      subst result
      rfl
  | some answer =>
      rw [CachedHashHandler.run_cached state query answer known, mem_support_pure_iff] at supported
      subst result
      rfl

variable [DecidableEq Digest]

/-- No query disappears, including a cache hit: the trace is exactly the
builder's leaf/left/right/parent query sequence with the actual returned labels. -/
theorem transcript (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    {s : Skeleton} (payloads : LeafData Payload s)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : FullData Digest s × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (program enc payloads)).run state)) :
    result.2.hash.log = state.hash.log ++ HonestMerkleTranscript.queries enc payloads result.1 := by
  induction payloads generalizing state with
  | leaf payload =>
      simp only [program, AddressedMerkleTree.buildMerkleTreeAddressedM, simulateQ_map,
        StateT.run_map, simulateQ_spec_query, support_map, Set.mem_image] at supported
      obtain ⟨answer, answerSupported, equal⟩ := supported
      subst result
      change answer ∈ support ((fun next => (next.1, CheckpointExecution.afterHash enc dummy shape state next.2)) <$>
        (CachedHashHandler.handler (enc.leaf () payload)).run state.hash) at answerSupported
      rw [support_map, Set.mem_image] at answerSupported
      obtain ⟨next, nextSupported, equal⟩ := answerSupported
      subst answer
      exact hash_log _ _ next nextSupported
  | internal left right ihLeft ihRight =>
      simp only [program, AddressedMerkleTree.buildMerkleTreeAddressedM, simulateQ_bind,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind,
        support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
      obtain ⟨l, lSupported, r, rSupported, root, rootSupported, equal⟩ := supported
      subst result
      have leftLog := ihLeft state l lSupported
      have rightLog := ihRight l.2 r rSupported
      simp only [simulateQ_spec_query] at rootSupported
      change root ∈ support ((fun next => (next.1, CheckpointExecution.afterHash enc dummy shape r.2 next.2)) <$>
        (CachedHashHandler.handler (enc.node () (l.1.getRootValue,r.1.getRootValue))).run r.2.hash) at rootSupported
      rw [support_map, Set.mem_image] at rootSupported
      obtain ⟨next, nextSupported, equal⟩ := rootSupported
      subst root
      have rootLog := hash_log _ _ next nextSupported
      simpa only [CheckpointExecution.afterHash, HonestMerkleTranscript.queries,
        List.append_assoc, leftLog, rightLog] using rootLog

/-- Recording is tied to the computed root and exact query transcript, rather
than an independently supplied setup snapshot. -/
theorem recorded (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (tag : Cfg) (payloads : LeafData Payload (shape tag))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : FullData Digest (shape tag) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (commit enc shape tag payloads)).run state)) :
    ⟨tag, ⟨result.1.getRootValue,
      state.hash.log ++ HonestMerkleTranscript.queries enc payloads result.1⟩⟩ ∈
      result.2.checkpoints.checkpoints := by
  simp only [commit, simulateQ_bind, simulateQ_pure, simulateQ_spec_query,
    StateT.run_bind, StateT.run_pure, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at supported
  obtain ⟨built, builtSupported, recorded, recordSupported, equal⟩ := supported
  subst result
  change recorded ∈ support (pure ((), CheckpointExecution.record shape built.2 tag built.1.getRootValue) : ProbComp _) at recordSupported
  have same := eq_of_mem_support_pure _ recordSupported
  subst recorded
  have trace := transcript impl enc dummy shape payloads state built builtSupported
  rw [← trace]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Once setup records a computed commitment, arbitrary subsequent shared
execution preserves that very snapshot. -/
theorem retained {Result : Type} (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (tag : Cfg) (payloads : LeafData Payload (shape tag))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (built : FullData Digest (shape tag) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (setupSupported : built ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (commit enc shape tag payloads)).run state))
    (continuation : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      continuation).run built.2)) :
    ⟨tag, ⟨built.1.getRootValue,
      state.hash.log ++ HonestMerkleTranscript.queries enc payloads built.1⟩⟩ ∈
      result.2.checkpoints.checkpoints :=
  CheckpointHistory.recorded_run impl enc dummy shape tag _ continuation built.2
    (recorded impl enc dummy shape tag payloads state built setupSupported) result supported

end Runtime

/-- The final cache itself supplies a total hash function realizing an executed
recorded commitment. This uses cache consistency, not response injectivity. -/
theorem realized (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (tag : Cfg) (payloads : LeafData Payload (shape tag))
    (labels : FullData Digest (shape tag)) (before : MerkleTreeExtractor.QueryLog Input Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (sound : RecordedCheckpointQueries.Sound shape state)
    (recorded : ⟨tag, ⟨labels.getRootValue,
      before ++ HonestMerkleTranscript.queries enc payloads labels⟩⟩ ∈ state.checkpoints.checkpoints) :
    HonestMerkleTranscript.tree enc (fun input => (state.hash.cache input).getD dummy) payloads = labels := by
  apply tree_of_answers
  intro entry member
  have known := sound _ recorded entry (List.mem_append_right _ member)
  rw [known]
  rfl

/-- The earlier deterministic honest-commitment model is an exact representation
of a retained executed commitment, using the actual final shared cache. -/
theorem realized_recorded (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (tag : Cfg) (payloads : LeafData Payload (shape tag))
    (labels : FullData Digest (shape tag)) (before : MerkleTreeExtractor.QueryLog Input Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (sound : RecordedCheckpointQueries.Sound shape state)
    (recorded : ⟨tag, ⟨labels.getRootValue,
      before ++ HonestMerkleTranscript.queries enc payloads labels⟩⟩ ∈ state.checkpoints.checkpoints) :
    let computed := HonestMerkleTranscript.tree enc (fun input => (state.hash.cache input).getD dummy) payloads
    ⟨tag, ⟨computed.getRootValue,
      before ++ HonestMerkleTranscript.queries enc payloads computed⟩⟩ ∈ state.checkpoints.checkpoints := by
  dsimp only
  rw [realized enc dummy shape tag payloads labels before state sound recorded]
  exact recorded

end
end FormalProof4FHE.HasteBoots.ExecutedHonestCommitment
