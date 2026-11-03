module

public import FormalProof4FHE.HasteBoots.NativeMerkleExecution
public import FormalProof4FHE.HasteBoots.CachedVerifierReplay

@[expose] public section

/-!
# Native hash workers with arbitrary intervening shared execution

Rayon's column workers need not execute atomically. A worker may pause before
or after any primitive hash request while other private/hash/checkpoint actions
run. Every step uses the actual shared handler. A completed worker can replay
its result from the final cache, so acceptance yields the same authentication
chain independently of how worker calls interleave. Rejection does not erase
background work or require other workers to stop immediately.
This is an operational trace relation; native Rayon/Rust refinement is separate.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeExtractability

namespace FormalProof4FHE.HasteBoots.InterleavedMerkleWorker

noncomputable section

variable {Input Digest Payload Cfg : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

/-- Every supported shared hash call leaves its complete input/answer cached. -/
theorem hash_query_caches (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : Input) (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (answer : Digest)
    (supported : (answer, after) ∈ support ((CheckpointExecution.handler implBase enc dummy shape
      (.inr (.inl query))).run before)) :
    after.hash.cache query = some answer := by
  change (answer, after) ∈ support ((fun result =>
      (result.1, CheckpointExecution.afterHash enc dummy shape before result.2)) <$>
        (CachedHashHandler.handler query).run before.hash) at supported
  rw [support_map, Set.mem_image] at supported
  obtain ⟨next, present, equal⟩ := supported
  cases known : before.hash.cache query with
  | none =>
      rw [CachedHashHandler.run_fresh before.hash query known, support_map, Set.mem_image] at present
      obtain ⟨freshAnswer, _, returned⟩ := present
      subst next
      cases equal
      exact QueryCache.cacheQuery_self _ _ _
  | some previous =>
      rw [CachedHashHandler.run_cached before.hash query previous known, mem_support_pure_iff] at present
      subst next
      cases equal
      exact known

/-- A completed worker, allowing arbitrary actual shared execution between its
own primitive calls. The background can include fragments of other workers. -/
inductive Run (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    {Result : Type} : OracleComp (Input →ₒ Digest) Result →
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Result →
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop where
  | done (value : Result) (state) : Run implBase enc dummy shape (pure value) state value state
  | pause {Other : Type} (other : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Other)
      {worker before middle after result value}
      (supported : (value, middle) ∈ support ((simulateQ
        (CheckpointExecution.handler implBase enc dummy shape) other).run before))
      (rest : Run implBase enc dummy shape worker middle result after) :
      Run implBase enc dummy shape worker before result after
  | query {query : Input} (next : Digest → OracleComp (Input →ₒ Digest) Result)
      {before middle after answer result}
      (supported : (answer, middle) ∈ support ((CheckpointExecution.handler implBase enc dummy shape
        (.inr (.inl query))).run before))
      (rest : Run implBase enc dummy shape (next answer) middle result after) :
      Run implBase enc dummy shape (liftM ((Input →ₒ Digest).query query) >>= next) before result after

/-- Pausing a worker cannot discard any earlier shared hash answer. -/
theorem cache_monotone {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    {worker : OracleComp (Input →ₒ Digest) Result}
    {before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape} {result : Result}
    (trace : Run implBase enc dummy shape worker before result after) :
    before.hash.cache ≤ after.hash.cache := by
  induction trace with
  | done => exact le_rfl
  | pause other supported rest ih =>
      exact (CheckpointCollision.cache_monotone_run implBase enc dummy shape other _ _ supported).trans ih
  | query next supported rest ih =>
      exact (CheckpointCollision.cache_monotone_step implBase enc dummy shape (.inr (.inl _)) _ _ supported).trans ih

/-- All of a completed worker's own query answers are settled in the final
cache, even though intervening activity can add arbitrarily many other entries. -/
theorem replay {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    {worker : OracleComp (Input →ₒ Digest) Result}
    {before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape} {result : Result}
    (trace : Run implBase enc dummy shape worker before result after) :
    simulateQ after.hash.cache.toPartialImpl worker = some result := by
  induction trace with
  | done => rfl
  | pause other supported rest ih => exact ih
  | query next supported rest ih =>
      have known := hash_query_caches implBase enc dummy shape _ _ _ _ supported
      have monotone := cache_monotone implBase enc dummy shape rest
      rw [simulateQ_bind, simulateQ_spec_query, QueryCache.toPartialImpl_apply, monotone known]
      exact ih

/-- An accepted interleaved native verifier establishes its leaf entry and
path chain in the final shared cache, without serializing entire workers. -/
theorem payload_of_accepted (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (height index : ℕ) (payload : Payload) (claimedLeaf root : Digest) (siblings : List.Vector Digest height)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (trace : Run implBase enc dummy shape
      (NativeMerkleVerifier.verifyPayload enc height index payload claimedLeaf root siblings) before true after) :
    after.hash.cache (enc.leaf () payload) = some claimedLeaf ∧
      ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) after.hash.cache claimedLeaf root
        (SkeletonLeafIndex.ofNat height index) (NativeMerklePath.typedProof height index siblings) :=
  CachedVerifierReplay.payload_of_partial_acceptance enc dummy height index payload claimedLeaf root siblings
    after.hash.cache (replay implBase enc dummy shape trace)

end

end FormalProof4FHE.HasteBoots.InterleavedMerkleWorker
