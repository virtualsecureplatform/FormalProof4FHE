module

public import FormalProof4FHE.HasteBoots.LookupPairVector
public import FormalProof4FHE.HasteBoots.PrivateSampling
public import FormalProof4FHE.HasteBoots.SharedContinuation

@[expose] public section

/-!
# Fresh pair vectors retained by the helper-commit phase

The middle program draws its private vector before arbitrary helper work and
stores that exact vector alongside the returned roots and opaque memory. The
helper builder cannot replace it. All helper hashes, aborts and checkpoints
remain in the shared execution. This models the ideal accepted-domain law;
native rejection-loop coins, transcript binding and work remain open.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.LookupPairVectorMiddle

noncomputable section

variable {F K Cfg Input Digest Payload HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq K] [Fintype K] [SampleableType K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {width count size repetitions : ℕ}

abbrev Memory (K HelperMemory : Type) [Zero K] (repetitions : ℕ) :=
  (Fin repetitions → StagedRepeatedLookup.Pair K) × HelperMemory

abbrev Emission (K Digest HelperMemory : Type) [Zero K] (repetitions : ℕ) :=
  StagedRepeatedLookup.HelperEmission repetitions Digest (Memory K HelperMemory repetitions)

def pairs (emission : Emission K Digest HelperMemory repetitions) : Fin repetitions → StagedRepeatedLookup.Pair K :=
  emission.2.1

/-- The trusted wrapper attaches the actual vector after helper construction;
only roots and opaque memory come from the helper builder. -/
def program (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K)
    (build : (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory)) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Emission K Digest HelperMemory repetitions) :=
  (fun result => (result.2.1, (result.1, result.2.2))) <$>
    SharedContinuation.program
      (PrivateSampling.embed Cfg Input Digest (LookupPairVector.vector (K := K) table enough repetitions)) build

variable {p : ℕ} [CharP K p]

/-- Later helper work cannot increase the all-pass probability of the stored
vector, even if it makes adaptive shared-oracle queries or aborts. -/
theorem retained_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ i, ∀ j, sources i ≠ table j) (small : count < p)
    (build : (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program table enough build)).run state}[
        LookupPairVector.AllPass sources table multiplicities (pairs outcome.1)] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest (LookupPairVector.vector (K := K) table enough repetitions)) build state
    (LookupPairVector.AllPass sources table multiplicities)
  have arithmetic := LookupPairVector.vector_bound sources table multiplicities enough bad small repetitions
  have bound := retained.trans (by
    simpa only [PrivateSampling.run_probComp, prEvent_norm] using arithmetic)
  simpa only [program, simulateQ_map, StateT.run_map, prEvent_map, pairs] using bound

/-- Average over the actual source prefix and retain the middle event through
all later work. Source tuples and multiplicities are fixed at the first saved
state, before the entire private vector. False prefixes alone incur the bound. -/
theorem staged_bound {First Result : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest))
    (helperRequests : First → Emission K Digest HelperMemory repetitions → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K)
    (build : First → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (next : First → Emission K Digest HelperMemory repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (sources : First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Fin count → Fin width → F)
    (multiplicities : First → Fin size → K) (small : count < p)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy shape sourceRequests helperRequests sourceCommit
      (fun first => program table enough (build first)) next initial)}[
        (∃ i, ∀ j, sources outcome.1 i ≠ table j) ∧
        LookupPairVector.AllPass (sources outcome.1) table (multiplicities outcome.1.1) (pairs outcome.2.1.1)] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  unfold StagedCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases bad : ∃ i, ∀ j, sources first i ≠ table j
  · have middle := retained_bound enc dummy shape (sources first) table (multiplicities first.1) enough bad small
      (build first.1) (RecordRoots.state shape (sourceRequests first.1) first.2)
    have retained := prEvent_bind_le_prEvent_of_forall_eq_zero
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program table enough (build first.1))).run (RecordRoots.state shape (sourceRequests first.1) first.2))
      (fun second => do
        let last ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (next first.1 second.1)).run (RecordRoots.state shape (helperRequests first.1 second.1) second.2)
        pure (first, second, last))
      (fun second => LookupPairVector.AllPass (sources first) table (multiplicities first.1) (pairs second.1))
      (fun outcome => (∃ i, ∀ j, sources outcome.1 i ≠ table j) ∧
        LookupPairVector.AllPass (sources outcome.1) table (multiplicities outcome.1.1) (pairs outcome.2.1.1)) ?_
    · exact retained.trans middle
    · intro second failed
      simp only [prEvent_norm]
      exact prEvent_eq_zero_of_forall_not _ _ (fun _ event => failed event.2)
  · apply prEvent_bind_le_of_forall_le
    intro second
    simp only [prEvent_norm]
    exact (prEvent_eq_zero_of_forall_not _ _ (fun _ event => bad event.1)).le.trans zero_le

end

end FormalProof4FHE.HasteBoots.LookupPairVectorMiddle
