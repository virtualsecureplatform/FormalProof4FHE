module

public import FormalProof4FHE.HasteBoots.NativeMerklePathM
public import VCVio.CryptoFoundations.MerkleTree.Addressed.QueryBound

@[expose] public section

/-!
# Cached native Merkle verification and frozen payloads

The verifier first checks the supplied leaf digest against the hash of the
whole column payload, then evaluates bottom-up siblings in native order.
Acceptance induces both the leaf-query cache entry and the typed cache chain.
Consequently the frozen-prefix availability reduction no longer requires a
caller-supplied chain premise. Byte parsing and Rust execution refinement remain
separate; all leaf and node calls share the same complete-query oracle.
-/

open BinaryTree OracleSpec OracleComp MerkleTreeExtractability

namespace FormalProof4FHE.HasteBoots.NativeMerkleVerifier

noncomputable section

variable {Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]

def nodeHash (enc : MerkleOracle.Encoding Input Digest Payload) (left right : Digest) :
    OracleComp (Input →ₒ Digest) Digest :=
  liftM ((Input →ₒ Digest).query (enc.node () (left, right)))

/-- Siblings are in native leaf-to-root order; the first path element is given separately. -/
def verifyNodes (enc : MerkleOracle.Encoding Input Digest Payload) (height index : ℕ)
    (leaf root : Digest) (siblings : List.Vector Digest height) : OracleComp (Input →ₒ Digest) Bool := do
  let computed ← NativeMerklePathM.loopFrom (nodeHash enc) index 0 leaf siblings.toList
  pure (computed == root)

/-- Native whole-column leaf-hash check followed by native sibling-path verification. -/
def verifyPayload (enc : MerkleOracle.Encoding Input Digest Payload) (height index : ℕ)
    (payload : Payload) (claimedLeaf root : Digest) (siblings : List.Vector Digest height) :
    OracleComp (Input →ₒ Digest) Bool := do
  let observed ← liftM ((Input →ₒ Digest).query (enc.leaf () payload))
  if observed = claimedLeaf then verifyNodes enc height index claimedLeaf root siblings else pure false

omit [DecidableEq Input] in
/-- The native sibling loop is exactly VCVio's typed verifier computation. -/
theorem verifyNodes_eq_typed (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (height index : ℕ) (leaf root : Digest) (siblings : List.Vector Digest height) :
    verifyNodes enc height index leaf root siblings =
      MerkleTreeExtractability.verifyOpening (MerkleOracle.model enc dummy) (fun _ => ())
        (SkeletonLeafIndex.ofNat height index) leaf root (NativeMerklePath.typedProof height index siblings) := by
  unfold verifyNodes MerkleTreeExtractability.verifyOpening
  rw [NativeMerklePathM.loop_eq_root, NativeMerklePathM.root_native_eq_typed]
  rfl

/-- Every accepted native sibling run induces an authentication chain in its final cache. -/
theorem chain_of_accepted (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (height index : ℕ) (leaf root : Digest) (siblings : List.Vector Digest height)
    (cacheStart cacheFinal : (Input →ₒ Digest).QueryCache)
    (accepted : (true, cacheFinal) ∈ support ((simulateQ (Input →ₒ Digest).cachingOracle
      (verifyNodes enc height index leaf root siblings)).run cacheStart)) :
    ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) cacheFinal leaf root
      (SkeletonLeafIndex.ofNat height index) (NativeMerklePath.typedProof height index siblings) := by
  rw [verifyNodes_eq_typed enc dummy] at accepted
  exact chainInCache_of_mem_support_verifyOpening (MerkleOracle.model enc dummy) (fun _ => ())
    (SkeletonLeafIndex.ofNat height index) leaf root (NativeMerklePath.typedProof height index siblings)
    cacheStart cacheFinal accepted

/-- Payload verification establishes the complete leaf query as well as the node chain. -/
theorem payload_of_accepted (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (height index : ℕ) (payload : Payload) (claimedLeaf root : Digest)
    (siblings : List.Vector Digest height) (cacheStart cacheFinal : (Input →ₒ Digest).QueryCache)
    (accepted : (true, cacheFinal) ∈ support ((simulateQ (Input →ₒ Digest).cachingOracle
      (verifyPayload enc height index payload claimedLeaf root siblings)).run cacheStart)) :
    cacheFinal (enc.leaf () payload) = some claimedLeaf ∧
      ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) cacheFinal claimedLeaf root
        (SkeletonLeafIndex.ofNat height index) (NativeMerklePath.typedProof height index siblings) := by
  unfold verifyPayload at accepted
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at accepted
  obtain ⟨⟨observed, cacheMid⟩, queried, remaining⟩ := accepted
  by_cases equal : observed = claimedLeaf
  · subst observed
    rw [ite_eq_left rfl] at remaining
    have leafEntry : cacheMid (enc.leaf () payload) = some claimedLeaf :=
      cachingOracle_query_caches (enc.leaf () payload) cacheStart claimedLeaf cacheMid (by
        simpa only [HasQuery.instOfMonadLift_query, cachingOracle.simulateQ_query] using queried)
    have monotone := simulateQ_cachingOracle_cache_le
      (verifyNodes enc height index claimedLeaf root siblings) cacheMid (true, cacheFinal) remaining
    exact ⟨monotone leafEntry,
      chain_of_accepted enc dummy height index claimedLeaf root siblings cacheMid cacheFinal remaining⟩
  · rw [ite_eq_right equal] at remaining
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
      Bool.true_eq_false, false_and] at remaining

/-- A native accepted payload can disagree with the prechallenge frozen word
only through the same prefix-collision or later target-hit exceptions. -/
theorem frozen_word_disagreement (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (fallback : Payload) (height : ℕ) (log : MerkleTreeExtractor.QueryLog Input Digest)
    (cacheCommit cacheStart cacheFinal : (Input →ₒ Digest).QueryCache)
    (represented : LogRepresentsCache log cacheCommit) (beforeStart : cacheCommit ≤ cacheStart)
    (position : Fin (2 ^ height)) (payload : Payload) (claimedLeaf root : Digest)
    (siblings : List.Vector Digest height)
    (accepted : (true, cacheFinal) ∈ support ((simulateQ (Input →ₒ Digest).cachingOracle
      (verifyPayload enc height position.val payload claimedLeaf root siblings)).run cacheStart))
    (different : MerkleAvailability.word enc dummy fallback height log root position ≠ payload) :
    CacheHasCollision cacheCommit ∨
      ∃ target ∈ MerkleAvailability.targets enc dummy (Skeleton.perfect height) log root,
        CacheAddsValue cacheCommit cacheFinal target := by
  have authenticated := payload_of_accepted enc dummy height position.val payload claimedLeaf root
    siblings cacheStart cacheFinal accepted
  have monotone := beforeStart.trans (simulateQ_cachingOracle_cache_le
    (verifyPayload enc height position.val payload claimedLeaf root siblings) cacheStart (true, cacheFinal) accepted)
  exact MerkleAvailability.word_disagreement enc dummy fallback height log cacheCommit cacheFinal
    root claimedLeaf position (NativeMerklePath.typedProof height position.val siblings) payload
    represented monotone authenticated.2 authenticated.1 different

omit [DecidableEq Input] in
/-- Root verification makes at most one node query per supplied sibling. This
counts every issued query, including cache hits. -/
theorem nodes_query_bound (enc : MerkleOracle.Encoding Input Digest Payload)
    (height index : ℕ) (leaf root : Digest) (siblings : List.Vector Digest height) :
    IsTotalQueryBound (verifyNodes enc height index leaf root siblings) height := by
  have rootBound : IsTotalQueryBound
      (NativeMerklePathM.loopFrom (nodeHash enc) index 0 leaf siblings.toList) height := by
    rw [NativeMerklePathM.loop_eq_root, NativeMerklePathM.root_native_eq_typed]
    have bound := AddressedMerkleTree.isTotalQueryBound_getPutativeRootAddressedM
      (fun _ => nodeHash enc) 1 (SkeletonLeafIndex.ofNat height index) leaf
      (NativeMerklePath.typedProof height index siblings) (fun _ left right =>
        (isQueryBound_query_iff (enc.node () (left, right)) 1 _ _).mpr Nat.one_pos)
    simpa only [SkeletonLeafIndex.depth_ofNat, Nat.mul_one] using bound
  unfold verifyNodes
  exact (isTotalQueryBound_bind rootBound (fun _ => (show IsTotalQueryBound (pure _) 0 from trivial)))

omit [DecidableEq Input] in
/-- Whole-payload authentication adds one leaf hash, even if it rejects before
the node loop. This bounds checker overhead, not the adversary's query budget. -/
theorem payload_query_bound (enc : MerkleOracle.Encoding Input Digest Payload)
    (height index : ℕ) (payload : Payload) (claimedLeaf root : Digest)
    (siblings : List.Vector Digest height) :
    IsTotalQueryBound (verifyPayload enc height index payload claimedLeaf root siblings) (height + 1) := by
  have bound : IsTotalQueryBound (verifyPayload enc height index payload claimedLeaf root siblings) (1 + height) := by
    unfold verifyPayload
    apply isTotalQueryBound_bind
      ((isQueryBound_query_iff (enc.leaf () payload) 1 _ _).mpr Nat.one_pos)
    intro observed
    by_cases equal : observed = claimedLeaf
    · rw [ite_eq_left equal]
      exact nodes_query_bound enc height index claimedLeaf root siblings
    · rw [ite_eq_right equal]
      trivial
  simpa only [Nat.add_comm] using bound

end

end FormalProof4FHE.HasteBoots.NativeMerkleVerifier
