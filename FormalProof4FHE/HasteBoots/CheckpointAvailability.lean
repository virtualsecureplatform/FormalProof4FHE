module

public import FormalProof4FHE.HasteBoots.CheckpointCollision

@[expose] public section

/-!
# Root-wide payload availability for the adaptive shared-hash execution

One event quantifies over all recorded configurations, roots, leaf positions,
paths and whole payloads authenticated in the final shared cache. Away from the
combined collision/source-stability exception, each such payload equals its
immutable checkpoint extraction. No per-opening probability union is needed.
The execution is still a mathematical oracle program; native phase placement,
transcript compilation, concrete serialization and Rust refinement remain open.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeExtractability MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.CheckpointAvailability

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]

/-- An authentication chain in a represented collision-free cache determines
exactly the payload recovered from that same cache's complete log. -/
theorem current_payload_eq (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (state : CachedHashHandler.State Input Digest) (coherent : CachedHashHandler.Coherent state)
    (noCollision : ¬CacheHasCollision state.cache) {s : Skeleton} (root label : Digest)
    (idx : SkeletonLeafIndex s) (proof : List.Vector Digest idx.depth) (payload : Payload)
    (chain : ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) state.cache label root idx proof)
    (leafHash : state.cache (enc.leaf () payload) = some label) :
    MerkleAvailability.payloadAt enc dummy state.log root idx = some payload := by
  by_contra different
  obtain collision | ⟨target, _, query, known, missing⟩ :=
    MerkleAvailability.payload_disagreement enc dummy state.log state.cache state.cache root label idx proof
      payload (CachedHashHandler.represents_cache state coherent) le_rfl chain leafHash different
  · exact noCollision collision
  · rw [missing] at known
    cases known

/-- Every authenticated payload agrees with its recorded source in a safe state. -/
theorem frozen_payload_eq (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (safe : CheckpointCollision.Safe enc dummy shape state)
    (tag : Cfg) (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag)
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (idx : SkeletonLeafIndex (shape tag)) (proof : List.Vector Digest idx.depth) (label : Digest) (payload : Payload)
    (chain : ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) state.hash.cache label checkpoint.root idx proof)
    (leafHash : state.hash.cache (enc.leaf () payload) = some label) :
    MerkleAvailability.payloadAt enc dummy checkpoint.cumulativeLog checkpoint.root idx = some payload :=
  (safe.1.2.2.payloads tag checkpoint recorded idx).trans
    (current_payload_eq enc dummy state.hash safe.1.1 safe.2 checkpoint.root label idx proof payload chain leafHash)

/-- One existential event covers ALL cached authenticated openings of ALL
recorded roots. Proofs and payloads may be selected after the entire execution. -/
def Disagreement (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) : Prop :=
  ∃ (tag : Cfg) (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag),
    ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints ∧
    ∃ (idx : SkeletonLeafIndex (shape tag)) (proof : List.Vector Digest idx.depth) (label : Digest) (payload : Payload),
      ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) state.hash.cache label checkpoint.root idx proof ∧
      state.hash.cache (enc.leaf () payload) = some label ∧
      MerkleAvailability.payloadAt enc dummy checkpoint.cumulativeLog checkpoint.root idx ≠ some payload

/-- A disagreement cannot occur in a safe state. -/
theorem no_disagreement_of_safe (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (safe : CheckpointCollision.Safe enc dummy shape state) : ¬Disagreement enc dummy shape state := by
  rintro ⟨tag, checkpoint, recorded, idx, proof, label, payload, chain, leafHash, different⟩
  exact different (frozen_payload_eq enc dummy shape state safe tag checkpoint recorded idx proof label payload chain leafHash)

/-- The concrete execution's audit invariant reduces every disagreement to its
persistent source-failure flag or a shared-cache collision. -/
theorem disagreement_implies_bad (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (audited : CheckpointExecution.Audited enc dummy shape state)
    (different : Disagreement enc dummy shape state) : CheckpointCollision.Bad shape state := by
  by_contra noBad
  have clear : state.failed = false := by
    cases known : state.failed with
    | false => rfl
    | true => exact (noBad (Or.inl known)).elim
  have noCollision : ¬CacheHasCollision state.hash.cache := fun collision => noBad (Or.inr collision)
  exact no_disagreement_of_safe enc dummy shape state
    ⟨⟨audited.1, clear, audited.2 clear⟩, noCollision⟩ different

section Runtime

variable [SampleableType Digest] [Fintype Digest] {ι : Type} {base : OracleSpec ι}

/-- Root-wide availability bound for arbitrary adaptive private/hash/recording
interleavings. It is one bound on all cached authenticated payloads, not a sum
over selected openings. No maximum query count is assumed. -/
theorem disagreement_le_charge {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (safe : CheckpointCollision.Safe enc dummy shape state) :
    Pr{let result ← (simulateQ (CheckpointExecution.handler implBase enc dummy shape) program).run state}[
      Disagreement enc dummy shape result.2] ≤
      ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy shape)
        (CheckpointCollision.loss base shape) program state := by
  apply le_trans (prEvent_mono_of_support _ _ _ ?_)
    (CheckpointCollision.failure_le_charge implBase enc dummy shape program state safe)
  intro result supported different
  have audited := CheckpointExecution.audited_run implBase enc dummy shape program state
    ⟨safe.1.1, fun _ => safe.1.2.2⟩ result supported
  exact disagreement_implies_bad enc dummy shape result.2 audited different

/-- The empty-cache corollary has no initial safety certificate to supply. -/
theorem disagreement_from_empty_le_charge {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result) :
    Pr{let result ← (simulateQ (CheckpointExecution.handler implBase enc dummy shape) program).run
        (CheckpointExecution.empty shape)}[Disagreement enc dummy shape result.2] ≤
      ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy shape)
        (CheckpointCollision.loss base shape) program (CheckpointExecution.empty shape) :=
  disagreement_le_charge implBase enc dummy shape program (CheckpointExecution.empty shape)
    (CheckpointCollision.safe_empty enc dummy shape)

end Runtime

end

end FormalProof4FHE.HasteBoots.CheckpointAvailability
