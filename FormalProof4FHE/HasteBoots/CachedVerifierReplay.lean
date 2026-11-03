module

public import FormalProof4FHE.HasteBoots.NativeMerkleVerifier
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

@[expose] public section

/-!
# Reading completed native verifiers from a final shared cache

A successful partial-cache evaluation fixes the complete verifier result and
needs no further hash samples. It induces an execution of the nondeterministic
cached verifier with unchanged cache, hence the checked leaf entry and typed
path chain. This interface permits concurrent workers to replay from the final
cache even when their own hash requests were interleaved with other workers.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeExtractability

namespace FormalProof4FHE.HasteBoots.CachedVerifierReplay

noncomputable section

variable {Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]

omit [DecidableEq Digest] in
/-- A successful reading uses only cached answers and returns the same result
under nondeterministic caching, without changing any existing entry. -/
theorem run_caching_of_partial {Result : Type} (program : OracleComp (Input →ₒ Digest) Result)
    (cache : (Input →ₒ Digest).QueryCache) (result : Result)
    (read : simulateQ cache.toPartialImpl program = some result) :
    (simulateQ (Input →ₒ Digest).cachingOracle program).run cache = pure (result, cache) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      have equal : value = result := Option.some.inj read
      subst result
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query] at read
      obtain ⟨answer, known, remaining⟩ := Option.bind_eq_some_iff.mp read
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, cachingOracle.run_some known, pure_bind]
      exact ih answer remaining

/-- Replay acceptance of the actual whole-column and bottom-up path verifier
establishes its leaf query and authentication chain in that very cache. -/
theorem payload_of_partial_acceptance (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (height index : ℕ) (payload : Payload) (claimedLeaf root : Digest) (siblings : List.Vector Digest height)
    (cache : (Input →ₒ Digest).QueryCache)
    (read : simulateQ cache.toPartialImpl
      (NativeMerkleVerifier.verifyPayload enc height index payload claimedLeaf root siblings) = some true) :
    cache (enc.leaf () payload) = some claimedLeaf ∧
      ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) cache claimedLeaf root
        (SkeletonLeafIndex.ofNat height index) (NativeMerklePath.typedProof height index siblings) := by
  apply NativeMerkleVerifier.payload_of_accepted enc dummy height index payload claimedLeaf root siblings cache cache
  rw [run_caching_of_partial _ cache true read, mem_support_pure_iff]

end

end FormalProof4FHE.HasteBoots.CachedVerifierReplay
