module
public import FormalProof4FHE.HasteBoots.SharedLookupBatchSequence
@[expose] public section

/-! Concrete lookup obstructions on the shared-challenge batch. Each job keeps
its own literal public table, multiplicities, tuple width and pair. A fixed
nonpassing job yields the degree-four partial / degree-three full arithmetic
bound with no job-count multiplier. Pair sampling and PCS remain to compose. -/
open OracleSpec OracleComp BinaryTree
open scoped BigOperators Classical
namespace FormalProof4FHE.HasteBoots.SharedLookupBatchArithmetic
noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {jobs n active inactive : ℕ} {columns sizes : Fin jobs → ℕ}

def totals (pairs : Fin jobs → K × K)
    (tables : (job : Fin jobs) → Fin (sizes job) → Fin (columns job) → F)
    (multiplicities : (job : Fin jobs) → Fin (sizes job) → F) : Fin jobs → K :=
  fun job => LookupPairArithmetic.tableSum (pairs job).2 (pairs job).1 (tables job) (multiplicities job)

variable {Message Memory Cfg Input Digest Payload : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [DecidableEq K] [Fintype K] [SampleableType K]
  [SampleableType (Fin 1 → K)] [SampleableType (Fin n → K)]

theorem partial_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : SharedLookupBatchSequence.Schedule K Message Memory Cfg Input Digest jobs n)
    (selected : Fin jobs) (pairs : Fin jobs → K × K)
    (tables : (job : Fin jobs) → Fin (sizes job) → Fin (columns job) → F)
    (multiplicities : (job : Fin jobs) → Fin (sizes job) → F)
    (logicalShape : active + inactive = 2 ^ n)
    (sources : Fin (columns selected) → MatrixFold.Cube n → F) (helpers : MatrixFold.Cube n → K)
    (rNonzero : (pairs selected).2 ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes (LookupPairArithmetic.activeTuples logicalShape sources) (tables selected)
      (fun i => algebraMap F K (multiplicities selected i)) (pairs selected))
    (sumDegree : ∀ points message, (schedule.interpret points message (selected,false)).natDegree ≤ 1)
    (identityDegree : ∀ points message, (schedule.interpret points message (selected,true)).natDegree ≤ 4)
    (memory : Memory) (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedLookupBatchSequence.program p small schedule (totals pairs tables multiplicities) memory)).run before}[
        SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.partialArity
          (ExtensionLookupIdentity.partialCoefficient (pairs selected).2) ExtensionLookupIdentity.partialIndices
          (fun eqPoint => ExtensionLookupIdentity.factors eqPoint (pairs selected).1 sources helpers active) helpers outcome.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * (4 / Fintype.card K) := by
  apply SharedLookupBatchSequence.soundness_bound enc dummy shape p small schedule _ memory selected
    ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (pairs selected).2)
    ExtensionLookupIdentity.partialIndices _ helpers 4 ExtensionLookupIdentity.partial_degree sumDegree identityDegree _ before
  by_cases correctSum : totals pairs tables multiplicities selected = ∑ cell, helpers cell
  · right
    exact LookupReciprocalEnforcement.equality_bound logicalShape (pairs selected).2 (pairs selected).1 sources helpers
      (fun i => TupleHash.hash (pairs selected).1 (tables selected i))
      (fun i => algebraMap F K (multiplicities selected i)) rNonzero notPasses correctSum.symm
  · exact Or.inl correctSum

theorem full_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : SharedLookupBatchSequence.Schedule K Message Memory Cfg Input Digest jobs n)
    (selected : Fin jobs) (pairs : Fin jobs → K × K)
    (tables : (job : Fin jobs) → Fin (sizes job) → Fin (columns job) → F)
    (multiplicities : (job : Fin jobs) → Fin (sizes job) → F)
    (sources : Fin (columns selected) → MatrixFold.Cube n → F) (helpers : MatrixFold.Cube n → K)
    (rNonzero : (pairs selected).2 ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes
      (LookupPairArithmetic.activeTuples (active := 2 ^ n) (inactive := 0) (by omega) sources) (tables selected)
      (fun i => algebraMap F K (multiplicities selected i)) (pairs selected))
    (sumDegree : ∀ points message, (schedule.interpret points message (selected,false)).natDegree ≤ 1)
    (identityDegree : ∀ points message, (schedule.interpret points message (selected,true)).natDegree ≤ 3)
    (memory : Memory) (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedLookupBatchSequence.program p small schedule (totals pairs tables multiplicities) memory)).run before}[
        SharedLookupBatchSequence.JointTruthful selected ExtensionLookupIdentity.fullArity
          (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
          (fun eqPoint => LookupPairArithmetic.fullTables eqPoint (pairs selected).2 (pairs selected).1 sources helpers) helpers outcome.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * (3 / Fintype.card K) := by
  apply SharedLookupBatchSequence.soundness_bound enc dummy shape p small schedule _ memory selected
    ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
    _ helpers 3 ExtensionLookupIdentity.full_degree sumDegree identityDegree _ before
  by_cases correctSum : totals pairs tables multiplicities selected = ∑ cell, helpers cell
  · right
    have bound := LookupReciprocalEnforcement.equality_bound (count := 2 ^ n) (padding := 0) (by omega)
      (pairs selected).2 (pairs selected).1 sources helpers
      (fun i => TupleHash.hash (pairs selected).1 (tables selected i))
      (fun i => algebraMap F K (multiplicities selected i)) rNonzero notPasses correctSum.symm
    simpa only [LookupPairArithmetic.full_sum_eq_partial] using bound
  · exact Or.inl correctSum
end
end FormalProof4FHE.HasteBoots.SharedLookupBatchArithmetic
