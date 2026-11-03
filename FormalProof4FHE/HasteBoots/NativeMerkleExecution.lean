module

public import FormalProof4FHE.HasteBoots.CheckpointAvailability
public import FormalProof4FHE.HasteBoots.NativeMerkleVerifier
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

@[expose] public section

/-!
# Native Merkle verification inside the shared checkpoint execution

The native verifier's leaf and node queries are routed to the same cached hash
as the surrounding private/hash/checkpoint program. Projecting its actual run
recovers the canonical lazy oracle, whose supported outcomes are supported by
the nondeterministic caching semantics used by the checked native path theorem.
Acceptance therefore establishes a leaf entry and authentication chain in the
actual final shared cache. No caller-supplied path-semantics premise is needed.
Byte decoding, machine-size bounds and Rust execution refinement remain open.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeExtractability MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.NativeMerkleExecution

noncomputable section

variable {Input Digest Payload Cfg : Type} [DecidableEq Input] [DecidableEq Digest]

section CanonicalSupport

variable [SampleableType Digest]

omit [DecidableEq Digest] in
/-- Every actual lazy-oracle step is allowed by the nondeterministic cached
semantics; a fresh answer is not interpreted as a repeated independent query. -/
theorem random_step_support (query : Input) (cache : (Input →ₒ Digest).QueryCache)
    (result : Digest × (Input →ₒ Digest).QueryCache)
    (supported : result ∈ support (((Input →ₒ Digest).randomOracle query).run cache)) :
    result ∈ support (((Input →ₒ Digest).cachingOracle query).run cache) := by
  cases known : cache query with
  | none =>
      rw [randomOracle.run_eq, known, mem_support_bind_iff] at supported
      obtain ⟨answer, _, returned⟩ := supported
      have equal := eq_of_mem_support_pure _ returned
      subst result
      rw [cachingOracle.run_none known, support_map, Set.mem_image]
      exact ⟨answer, mem_support_query query answer, rfl⟩
  | some answer =>
      rw [randomOracle.run_eq, known] at supported
      rw [cachingOracle.run_some known]
      exact supported

omit [DecidableEq Digest] in
/-- The support inclusion respects arbitrary adaptive continuations and the
whole cache. It imposes no query bound and no finite-input-domain premise. -/
theorem random_run_support {Result : Type} (program : OracleComp (Input →ₒ Digest) Result)
    (cache : (Input →ₒ Digest).QueryCache) (result : Result × (Input →ₒ Digest).QueryCache)
    (supported : result ∈ support ((simulateQ (Input →ₒ Digest).randomOracle program).run cache)) :
    result ∈ support ((simulateQ (Input →ₒ Digest).cachingOracle program).run cache) := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported ⊢
      obtain ⟨middle, queried, remaining⟩ := supported
      exact ⟨middle, random_step_support query cache middle queried, ih middle.1 middle.2 remaining⟩

end CanonicalSupport

variable {ι : Type} {base : OracleSpec ι}

/-- Route every native verifier hash to the unique shared hash summand. -/
def embed (base : OracleSpec ι) (Cfg : Type) {Result : Type}
    (program : OracleComp (Input →ₒ Digest) Result) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result :=
  simulateQ (fun query => liftM ((CheckpointExecution.Spec base Cfg Input Digest).query
    (.inr (.inl query)))) program

section Runtime

variable [SampleableType Digest]

/-- The restriction of the actual full handler to native verifier hash calls. -/
def hashHandler (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton) :
    QueryImpl (Input →ₒ Digest)
      (StateT (CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ProbComp) :=
  fun query => CheckpointExecution.handler implBase enc dummy shape (.inr (.inl query))

theorem simulate_embed {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (Input →ₒ Digest) Result) :
    simulateQ (CheckpointExecution.handler implBase enc dummy shape) (embed base Cfg program) =
      simulateQ (hashHandler implBase enc dummy shape) program := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro query
  exact simulateQ_spec_query _ _

/-- Erasing the ghost state recovers precisely the canonical hash run of the
native verifier, including all cached repeats and the order of primitive calls. -/
theorem project_embed {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (Input →ₒ Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Prod.map id (fun state => state.hash.cache) <$>
        (simulateQ (CheckpointExecution.handler implBase enc dummy shape) (embed base Cfg program)).run state =
      (simulateQ (Input →ₒ Digest).randomOracle program).run state.hash.cache := by
  rw [simulate_embed]
  apply map_run_simulateQ_eq_of_query_map_eq
  intro query current
  exact CheckpointExecution.project_step implBase enc dummy shape (.inr (.inl query)) current

/-- An embedded native accepted payload establishes authentication in the
actual final shared cache, rather than in a separate idealized verifier cache. -/
theorem payload_of_accepted (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (height index : ℕ) (payload : Payload) (claimedLeaf root : Digest) (siblings : List.Vector Digest height)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (accepted : (true, after) ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy shape)
      (embed base Cfg (NativeMerkleVerifier.verifyPayload enc height index payload claimedLeaf root siblings))).run before)) :
    after.hash.cache (enc.leaf () payload) = some claimedLeaf ∧
      ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) after.hash.cache claimedLeaf root
        (SkeletonLeafIndex.ofNat height index) (NativeMerklePath.typedProof height index siblings) := by
  have projected : (true, after.hash.cache) ∈ support
      ((simulateQ (Input →ₒ Digest).randomOracle
        (NativeMerkleVerifier.verifyPayload enc height index payload claimedLeaf root siblings)).run before.hash.cache) := by
    rw [← project_embed implBase enc dummy shape _ before, support_map, Set.mem_image]
    exact ⟨(true, after), accepted, rfl⟩
  exact NativeMerkleVerifier.payload_of_accepted enc dummy height index payload claimedLeaf root siblings
    before.hash.cache after.hash.cache (random_run_support _ _ _ projected)

/-- The chain and leaf entry survive an arbitrary further adaptive execution. -/
theorem payload_after_continuation {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (height index : ℕ) (payload : Payload) (claimedLeaf root : Digest) (siblings : List.Vector Digest height)
    (before middle after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (accepted : (true, middle) ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy shape)
      (embed base Cfg (NativeMerkleVerifier.verifyPayload enc height index payload claimedLeaf root siblings))).run before))
    (rest : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result) (result : Result)
    (remaining : (result, after) ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy shape) rest).run middle)) :
    after.hash.cache (enc.leaf () payload) = some claimedLeaf ∧
      ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) after.hash.cache claimedLeaf root
        (SkeletonLeafIndex.ofNat height index) (NativeMerklePath.typedProof height index siblings) := by
  have authenticated := payload_of_accepted implBase enc dummy shape height index payload claimedLeaf root siblings
    before middle accepted
  have monotone := CheckpointCollision.cache_monotone_run implBase enc dummy shape rest middle (result, after) remaining
  exact ⟨monotone authenticated.1, chainInCache_mono _ _ _ monotone authenticated.2⟩

end Runtime

end

end FormalProof4FHE.HasteBoots.NativeMerkleExecution
