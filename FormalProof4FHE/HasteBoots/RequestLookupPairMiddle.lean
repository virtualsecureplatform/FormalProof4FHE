module
public import FormalProof4FHE.HasteBoots.RequestLookupPairs
public import FormalProof4FHE.HasteBoots.PrivateSampling
public import FormalProof4FHE.HasteBoots.SharedContinuation
@[expose] public section

/-! Request-specific private pair vectors are retained through adaptive helper
construction. The trusted wrapper stores the actual sampled dependent vector;
helper builders supply roots and opaque memory, not replacement challenges.
The bound uses one selected false request and retains all later shared work. -/
open OracleSpec OracleComp BinaryTree
open scoped Classical BigOperators
namespace FormalProof4FHE.HasteBoots.RequestLookupPairMiddle
noncomputable section
variable {F K Cfg Input Digest Payload HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq K] [Fintype K] [SampleableType K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {requests : ℕ} {widths sizes repetitions : Fin requests → ℕ}

abbrev Memory (K HelperMemory : Type) [Zero K] {requests : ℕ} (repetitions : Fin requests → ℕ) :=
  RequestLookupPairs.Vector K repetitions × HelperMemory
abbrev Emission (K Digest HelperMemory : Type) [Zero K] {requests : ℕ} (repetitions : Fin requests → ℕ) :=
  StagedSharedLookup.HelperEmission (∑ request, repetitions request) Digest (Memory K HelperMemory repetitions)

def pairs (emission : Emission K Digest HelperMemory repetitions) :
    Fin (∑ request, repetitions request) → StagedSharedLookup.Pair K := RequestLookupPairs.flatten emission.2.1

def program (tables : (request : Fin requests) → Fin (sizes request) → Fin (widths request) → F)
    (enough : ∀ request, sizes request + 1 < Fintype.card K)
    (build : RequestLookupPairs.Vector K repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (StagedSharedLookup.HelperEmission (∑ request, repetitions request) Digest HelperMemory)) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Emission K Digest HelperMemory repetitions) :=
  (fun result => (result.2.1,(result.1,result.2.2))) <$>
    SharedContinuation.program
      (PrivateSampling.embed Cfg Input Digest (RequestLookupPairs.sample (K := K) requests widths sizes repetitions tables enough)) build

omit [Field F] [Algebra F K] [DecidableEq K] [Fintype K] [SampleableType K]
    [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] in
theorem pairs_job (emission : Emission K Digest HelperMemory repetitions) (request : Fin requests)
    (repetition : Fin (repetitions request)) :
    pairs emission (finSigmaFinEquiv ⟨request,repetition⟩) = emission.2.1 request repetition :=
  RequestLookupPairs.flatten_job _ _ _

/-- The full repeated hash/reciprocal error survives adaptive helper work;
other requests may have different tables and repetition counts. -/
theorem retained_bound {p active : ℕ} [CharP K p]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (tables : (request : Fin requests) → Fin (sizes request) → Fin (widths request) → F)
    (enough : ∀ request, sizes request + 1 < Fintype.card K) (selected : Fin requests)
    (sources : Fin active → Fin (widths selected) → F) (multiplicities : Fin (sizes selected) → K)
    (bad : ∃ i, ∀ j, sources i ≠ tables selected j) (small : active < p)
    (build : RequestLookupPairs.Vector K repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (StagedSharedLookup.HelperEmission (∑ request, repetitions request) Digest HelperMemory))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program tables enough build)).run state}[
        LookupPairVector.AllPass sources (tables selected) multiplicities (outcome.1.2.1 selected)] ≤
      TupleLookupPair.error (Fintype.card K) (widths selected) active (sizes selected) ^ repetitions selected := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest (RequestLookupPairs.sample (K := K) requests widths sizes repetitions tables enough)) build state
    (fun pairs => LookupPairVector.AllPass sources (tables selected) multiplicities (pairs selected))
  have arithmetic := RequestLookupPairs.selected_bound requests widths sizes repetitions tables enough selected sources multiplicities bad small
  have bound := retained.trans (by simpa only [PrivateSampling.run_probComp,prEvent_norm] using arithmetic)
  simpa only [program,simulateQ_map,StateT.run_map,prEvent_map] using bound

/-- A deterministic upper bound over request-specific repeated errors. This
is a maximum, not a probability union or a request-count multiplier. -/
def errorBudget (q : ℕ) (widths sizes active repetitions : Fin requests → ℕ) : ENNReal :=
  Finset.univ.sup (fun request => TupleLookupPair.error q (widths request) (active request) (sizes request) ^ repetitions request)

/-- Average over the actual source prefix. One false request is selected
before all pair draws, and its event is retained through the complete later
execution, including adaptive helper construction and rejecting callbacks. -/
theorem staged_bound {First Result : Type} {p : ℕ} [CharP K p]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest))
    (helperRequests : First → Emission K Digest HelperMemory repetitions → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (tables : (request : Fin requests) → Fin (sizes request) → Fin (widths request) → F)
    (enough : ∀ request, sizes request + 1 < Fintype.card K)
    (build : First → RequestLookupPairs.Vector K repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (StagedSharedLookup.HelperEmission (∑ request, repetitions request) Digest HelperMemory))
    (next : First → Emission K Digest HelperMemory repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (active : Fin requests → ℕ)
    (sources : First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape →
      (request : Fin requests) → Fin (active request) → Fin (widths request) → F)
    (multiplicities : First → (request : Fin requests) → Fin (sizes request) → K)
    (small : ∀ request, active request < p)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy shape sourceRequests helperRequests sourceCommit
      (fun first => program tables enough (build first)) next initial)}[
        (∃ request i, ∀ j, sources outcome.1 request i ≠ tables request j) ∧
        ∀ request, LookupPairVector.AllPass (sources outcome.1 request) (tables request) (multiplicities outcome.1.1 request)
          (outcome.2.1.1.2.1 request)] ≤ errorBudget (Fintype.card K) widths sizes active repetitions := by
  unfold StagedCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases bad : ∃ request i, ∀ j, sources first request i ≠ tables request j
  · let selected := Classical.choose bad
    have outside := Classical.choose_spec bad
    have middle := retained_bound enc dummy shape tables enough selected (sources first selected) (multiplicities first.1 selected)
      outside (small selected) (build first.1) (RecordRoots.state shape (sourceRequests first.1) first.2)
    have retained := prEvent_bind_le_prEvent_of_forall_eq_zero
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program tables enough (build first.1))).run (RecordRoots.state shape (sourceRequests first.1) first.2))
      (fun second => do
        let last ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (next first.1 second.1)).run (RecordRoots.state shape (helperRequests first.1 second.1) second.2)
        pure (first,second,last))
      (fun second => LookupPairVector.AllPass (sources first selected) (tables selected) (multiplicities first.1 selected) (second.1.2.1 selected))
      (fun outcome => (∃ request i, ∀ j, sources outcome.1 request i ≠ tables request j) ∧
        ∀ request, LookupPairVector.AllPass (sources outcome.1 request) (tables request) (multiplicities outcome.1.1 request)
          (outcome.2.1.1.2.1 request)) ?_
    · exact (retained.trans middle).trans (Finset.le_sup (s := Finset.univ)
        (f := fun request => TupleLookupPair.error (Fintype.card K) (widths request) (active request) (sizes request) ^ repetitions request)
        (Finset.mem_univ selected))
    · intro second failed
      simp only [prEvent_norm]
      exact prEvent_eq_zero_of_forall_not _ _ (fun _ event => failed (event.2 selected))
  · apply prEvent_bind_le_of_forall_le
    intro second
    simp only [prEvent_norm]
    exact (prEvent_eq_zero_of_forall_not _ _ (fun _ event => bad event.1)).le.trans zero_le
end
end FormalProof4FHE.HasteBoots.RequestLookupPairMiddle
