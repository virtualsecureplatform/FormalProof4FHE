module

public import FormalProof4FHE.HasteBoots.InterleavedMerkleWorker
public import FormalProof4FHE.HasteBoots.NativeOpeningAvailability

@[expose] public section

/-!
# One availability bound for interleaved native column workers

The native column checker uses Rayon, so entire paths are not assumed atomic
and rejecting a worker need not cancel already issued calls from others.
A completed worker replays from the final shared cache. The event below even
covers any listed column whose native verifier can accept by such a replay,
whether or not the entire opening is accepted. One root-wide bound covers all
columns, configurations, positions and paths, without a per-column union loss.
The global program includes all actual calls, including work on rejection.
Native Rayon/Rust refinement and the PCS coordinate/challenge checks remain open.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeExtractability MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.ParallelColumnAvailability

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]

/-- The actual native verifier can read every required answer from this cache
and returns true. This is a deterministic condition on code and cache. -/
def Replays (enc : MerkleOracle.Encoding Input Digest Payload) (height : Cfg → ℕ)
    (request : NativeOpeningAvailability.Request (Digest := Digest) (Payload := Payload) height)
    (cache : (Input →ₒ Digest).QueryCache) : Prop :=
  simulateQ cache.toPartialImpl (NativeMerkleVerifier.verifyPayload enc (height request.tag)
    request.position.val request.payload request.leaf request.root request.siblings) = some true

/-- A listed authenticated column disagrees with an immutable matching root
snapshot. The request list and failing member can be chosen after other queries. -/
def Failure (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : Cfg → ℕ)
    (requests : List (NativeOpeningAvailability.Request (Digest := Digest) (Payload := Payload) height))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag))) : Prop :=
  ∃ request ∈ requests, Replays enc height request state.hash.cache ∧
    ∃ checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) request.tag,
      ⟨request.tag, checkpoint⟩ ∈ state.checkpoints.checkpoints ∧ checkpoint.root = request.root ∧
      MerkleAvailability.payloadAt enc dummy checkpoint.cumulativeLog checkpoint.root
        (SkeletonLeafIndex.perfectEquiv (height request.tag) request.position) ≠ some request.payload

omit [DecidableEq Input] in
/-- A wrong value of the fixed total word is included for any chosen fallback. -/
theorem failure_of_word_disagreement (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (height : Cfg → ℕ)
    (requests : List (NativeOpeningAvailability.Request (Digest := Digest) (Payload := Payload) height))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (request : NativeOpeningAvailability.Request (Digest := Digest) (Payload := Payload) height)
    (member : request ∈ requests) (read : Replays enc height request state.hash.cache)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) request.tag)
    (recorded : ⟨request.tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (root : checkpoint.root = request.root) (fallback : Payload)
    (different : MerkleAvailability.word enc dummy fallback (height request.tag)
      checkpoint.cumulativeLog checkpoint.root request.position ≠ request.payload) :
    Failure enc dummy height requests state := by
  refine ⟨request, member, read, checkpoint, recorded, root, ?_⟩
  intro recovered
  apply different
  simp only [MerkleAvailability.word, recovered, Option.getD_some]

/-- One completed worker yields the root-wide disagreement event. This
reduction requires neither independent workers nor a sequential path order. -/
theorem failure_implies_disagreement (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (height : Cfg → ℕ)
    (requests : List (NativeOpeningAvailability.Request (Digest := Digest) (Payload := Payload) height))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag))) (failure : Failure enc dummy height requests state) :
    CheckpointAvailability.Disagreement enc dummy (fun tag => Skeleton.perfect (height tag)) state := by
  obtain ⟨request, _, read, checkpoint, recorded, root, different⟩ := failure
  have authenticated := CachedVerifierReplay.payload_of_partial_acceptance enc dummy
    (height request.tag) request.position.val request.payload request.leaf request.root request.siblings
      state.hash.cache read
  refine ⟨request.tag, checkpoint, recorded,
    SkeletonLeafIndex.perfectEquiv (height request.tag) request.position,
    NativeMerklePath.typedProof (height request.tag) request.position.val request.siblings,
    request.leaf, request.payload, ?_, authenticated.1, different⟩
  rw [root]
  exact authenticated.2

theorem no_failure_of_safe (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (height : Cfg → ℕ)
    (requests : List (NativeOpeningAvailability.Request (Digest := Digest) (Payload := Payload) height))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (safe : CheckpointCollision.Safe enc dummy (fun tag => Skeleton.perfect (height tag)) state) :
    ¬Failure enc dummy height requests state :=
  fun failure => CheckpointAvailability.no_disagreement_of_safe enc dummy _ state safe
    (failure_implies_disagreement enc dummy height requests state failure)

section Runtime

variable [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

/-- Every native worker that finishes true under arbitrary intervening shared
execution satisfies the replay predicate used in the joint column event. -/
theorem replays_of_worker (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : Cfg → ℕ)
    (request : NativeOpeningAvailability.Request (Digest := Digest) (Payload := Payload) height)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (trace : InterleavedMerkleWorker.Run implBase enc dummy (fun tag => Skeleton.perfect (height tag))
      (NativeMerkleVerifier.verifyPayload enc (height request.tag) request.position.val
        request.payload request.leaf request.root request.siblings) before true after) :
    Replays enc height request after.hash.cache :=
  InterleavedMerkleWorker.replay implBase enc dummy _ trace

variable [Fintype Digest]

/-- One expected-charge bound covers every listed completed native column
worker, for any global linearization of actual shared calls. The program may
return a rejection branch and still retains all work already performed. -/
theorem failure_le_charge (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : Cfg → ℕ)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      (List (NativeOpeningAvailability.Request (Digest := Digest) (Payload := Payload) height)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (safe : CheckpointCollision.Safe enc dummy (fun tag => Skeleton.perfect (height tag)) state) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag))) program).run state}[
        Failure enc dummy height result.1 result.2] ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag))) program state := by
  apply le_trans (prEvent_mono _ _ _ ?_)
    (CheckpointAvailability.disagreement_le_charge implBase enc dummy
      (fun tag => Skeleton.perfect (height tag)) program state safe)
  intro result failure
  exact failure_implies_disagreement enc dummy height result.1 result.2 failure

/-- Empty initialization needs no externally supplied safety certificate. -/
theorem failure_from_empty_le_charge (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : Cfg → ℕ)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      (List (NativeOpeningAvailability.Request (Digest := Digest) (Payload := Payload) height))) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag))) program).run
        (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag)))}[
          Failure enc dummy height result.1 result.2] ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag))) program
        (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))) :=
  failure_le_charge implBase enc dummy height program _
    (CheckpointCollision.safe_empty enc dummy (fun tag => Skeleton.perfect (height tag)))

end Runtime

end

end FormalProof4FHE.HasteBoots.ParallelColumnAvailability
