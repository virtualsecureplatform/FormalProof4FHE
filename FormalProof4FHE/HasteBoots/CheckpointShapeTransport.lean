module

public import FormalProof4FHE.HasteBoots.CheckpointCollision

@[expose] public section

open BinaryTree MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.CheckpointShapeTransport

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]

/-- Reconfigure ghost extraction geometry without changing a recorded root or log. -/
def checkpoint (oldShape newShape : Cfg → Skeleton) (tag : Cfg)
    (saved : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration oldShape) tag) :
    Checkpoint Input Digest (MerklePayloadCheckpoints.configuration newShape) tag :=
  ⟨saved.root, saved.cumulativeLog⟩

def history (oldShape newShape : Cfg → Skeleton)
    (saved : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) oldShape) :
    MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) newShape :=
  ⟨saved.cumulativeLog, saved.checkpoints.map fun entry =>
    ⟨entry.1, checkpoint oldShape newShape entry.1 entry.2⟩⟩

/-- Only geometry at tags already present in the history must agree. -/
def Compatible (oldShape newShape : Cfg → Skeleton)
    (saved : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) oldShape) : Prop :=
  ∀ tag entry, ⟨tag, entry⟩ ∈ saved.checkpoints → oldShape tag = newShape tag

/-- The cache, full query log and persistent failure bit are copied verbatim. -/
def state (oldShape newShape : Cfg → Skeleton)
    (saved : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape) :
    CheckpointExecution.State (Input := Input) (Digest := Digest) newShape :=
  ⟨saved.hash, history oldShape newShape saved.checkpoints, saved.failed⟩

omit [DecidableEq Input] in
/-- Stability transfers only when every previously recorded context keeps its geometry. -/
theorem stable (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (oldShape newShape : Cfg → Skeleton)
    (saved : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : Compatible oldShape newShape saved)
    (log : MerkleTreeExtractor.QueryLog Input Digest)
    (valid : MerklePayloadCheckpoints.StableAt enc dummy oldShape saved log) :
    MerklePayloadCheckpoints.StableAt enc dummy newShape (history oldShape newShape saved) log := by
  constructor
  · intro tag entry member
    obtain ⟨⟨oldTag, oldEntry⟩, recorded, equal⟩ := List.mem_map.mp member
    cases equal
    have geometry := compatible oldTag oldEntry recorded
    have previous := valid.digest oldTag oldEntry recorded
    simp only [Checkpoint.extractedTree, MerklePayloadCheckpoints.configuration] at previous
    rw [geometry] at previous
    exact previous
  · intro tag entry member idx
    obtain ⟨⟨oldTag, oldEntry⟩, recorded, equal⟩ := List.mem_map.mp member
    cases equal
    have geometry := compatible oldTag oldEntry recorded
    have previous := valid.payloads oldTag oldEntry recorded
    rw [geometry] at previous
    exact previous idx

omit [DecidableEq Input] [DecidableEq Digest] in
/-- Reconfiguring back restores the entire ordered checkpoint history. -/
theorem history_roundtrip (oldShape newShape : Cfg → Skeleton)
    (saved : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) oldShape) :
    history newShape oldShape (history oldShape newShape saved) = saved := by
  cases saved
  simp [history, checkpoint, List.map_map, Function.comp_def]

omit [DecidableEq Input] [DecidableEq Digest] in
theorem compatible_reverse (oldShape newShape : Cfg → Skeleton)
    (saved : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : Compatible oldShape newShape saved) :
    Compatible newShape oldShape (history oldShape newShape saved) := by
  intro tag entry member
  obtain ⟨⟨oldTag, oldEntry⟩, recorded, equal⟩ := List.mem_map.mp member
  cases equal
  exact (compatible oldTag oldEntry recorded).symm

omit [DecidableEq Input] in
/-- Geometry changes at unrecorded tags cannot change the current monitor test. -/
theorem stable_iff (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (oldShape newShape : Cfg → Skeleton)
    (saved : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : Compatible oldShape newShape saved)
    (log : MerkleTreeExtractor.QueryLog Input Digest) :
    MerklePayloadCheckpoints.StableAt enc dummy newShape (history oldShape newShape saved) log ↔
      MerklePayloadCheckpoints.StableAt enc dummy oldShape saved log := by
  constructor
  · intro valid
    have back := stable enc dummy newShape oldShape (history oldShape newShape saved)
      (compatible_reverse oldShape newShape saved compatible) log valid
    rwa [history_roundtrip] at back
  · exact stable enc dummy oldShape newShape saved compatible log

omit [DecidableEq Input] [DecidableEq Digest] in
/-- A phase boundary preserves exact recording order and snapshot contents. -/
theorem record (oldShape newShape : Cfg → Skeleton)
    (saved : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (tag : Cfg) (root : Digest) :
    state oldShape newShape (CheckpointExecution.record oldShape saved tag root) =
      CheckpointExecution.record newShape (state oldShape newShape saved) tag root := by
  cases saved
  simp [state, history, checkpoint, CheckpointExecution.record,
    ExtractorState.recordCumulative, List.map_append]

omit [DecidableEq Input] in
/-- Hash updates commute with reconfiguration, including the persistent failure monitor. -/
theorem afterHash (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (oldShape newShape : Cfg → Skeleton)
    (saved : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : Compatible oldShape newShape saved.checkpoints)
    (next : CachedHashHandler.State Input Digest) :
    state oldShape newShape (CheckpointExecution.afterHash enc dummy oldShape saved next) =
      CheckpointExecution.afterHash enc dummy newShape (state oldShape newShape saved) next := by
  classical
  have equivalent := stable_iff enc dummy oldShape newShape saved.checkpoints compatible next.log
  simp only [state, CheckpointExecution.afterHash]
  congr 1
  exact congrArg (fun test => saved.failed || decide (¬test)) (propext equivalent).symm

omit [DecidableEq Input] [DecidableEq Digest] in
/-- Future recordings add exactly one new geometry obligation. -/
theorem compatible_record (oldShape newShape : Cfg → Skeleton)
    (saved : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) oldShape)
    (tag : Cfg) (root : Digest) (log : MerkleTreeExtractor.QueryLog Input Digest) :
    Compatible oldShape newShape (saved.recordCumulative tag log root) ↔
      Compatible oldShape newShape saved ∧ oldShape tag = newShape tag := by
  constructor
  · intro compatible
    constructor
    · intro oldTag entry member
      exact compatible oldTag entry (List.mem_append_left _ member)
    · exact compatible tag ⟨root, log⟩ (List.mem_append_right _ (List.mem_singleton_self _))
  · rintro ⟨compatible, geometry⟩ oldTag entry member
    obtain old | fresh := List.mem_append.mp member
    · exact compatible oldTag entry old
    · simp only [List.mem_singleton] at fresh
      cases fresh
      exact geometry

omit [DecidableEq Input] [DecidableEq Digest] in
/-- Original owners are retained with their exact tag, root and snapshot log. -/
theorem recorded_iff (oldShape newShape : Cfg → Skeleton)
    (saved : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) oldShape)
    (tag : Cfg)
    (entry : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration oldShape) tag) :
    ⟨tag, checkpoint oldShape newShape tag entry⟩ ∈ (history oldShape newShape saved).checkpoints ↔
      ⟨tag, entry⟩ ∈ saved.checkpoints := by
  constructor
  · intro member
    obtain ⟨⟨oldTag, oldEntry⟩, recorded, equal⟩ := List.mem_map.mp member
    have recovered := congrArg (fun item : (tag : Cfg) ×'
      Checkpoint Input Digest (MerklePayloadCheckpoints.configuration newShape) tag =>
        (⟨item.1, checkpoint newShape oldShape item.1 item.2⟩ : (tag : Cfg) ×'
          Checkpoint Input Digest (MerklePayloadCheckpoints.configuration oldShape) tag)) equal
    simpa only [checkpoint] using recovered ▸ recorded
  · intro member
    exact List.mem_map.mpr ⟨⟨tag, entry⟩, member, rfl⟩

/-- An inherited audit remains valid; no old failure is cleared. -/
theorem audited (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (oldShape newShape : Cfg → Skeleton)
    (saved : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : Compatible oldShape newShape saved.checkpoints)
    (valid : CheckpointExecution.Audited enc dummy oldShape saved) :
    CheckpointExecution.Audited enc dummy newShape (state oldShape newShape saved) :=
  ⟨valid.1, fun clear => stable enc dummy oldShape newShape saved.checkpoints compatible
    saved.hash.log (valid.2 clear)⟩

omit [DecidableEq Input] [DecidableEq Digest] in
/-- Reconfiguration neither creates nor erases the single shared collision event. -/
theorem bad_iff (oldShape newShape : Cfg → Skeleton)
    (saved : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape) :
    CheckpointCollision.Bad newShape (state oldShape newShape saved) ↔
      CheckpointCollision.Bad oldShape saved := Iff.rfl

end
end FormalProof4FHE.HasteBoots.CheckpointShapeTransport
