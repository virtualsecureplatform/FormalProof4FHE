module

public import FormalProof4FHE.HasteBoots.LookupPairSequence
public import FormalProof4FHE.HasteBoots.TupleLookupPair

@[expose] public section

/-!
# Concrete partial/full lookup pair arithmetic on the shared execution

The public total uses actual tuple hashing and embedded base-field
multiplicities. A nonpassing pair supplies the false-sum/EQ obstruction
internally. The partial degree-four and full degree-three programs inherit
n/card(K)+n*D/card(K) for both truthful subclaims on one shared run. No EQ or
sumcheck soundness certificate is supplied by the caller. This event still
needs actual terminal/PCS enforcement before it is an acceptance theorem.
-/

open OracleSpec OracleComp BinaryTree
open scoped BigOperators Classical

namespace FormalProof4FHE.HasteBoots.LookupPairArithmetic

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] {n active inactive width size : ℕ}

def activeTuples (shape : active + inactive = 2 ^ n) (sources : Fin width → MatrixFold.Cube n → F) :
    Fin active → Fin width → F := fun i j => sources j (LookupReciprocalEnforcement.cells shape (i.castAdd inactive))

def tableSum (r y : K) (table : Fin size → Fin width → F) (multiplicities : Fin size → F) : K :=
  ∑ i, algebraMap F K (multiplicities i) * (r + TupleHash.hash y (table i))⁻¹

def fullTables (eqPoint : Fin n → K) (r y : K) (sources : Fin width → MatrixFold.Cube n → F)
    (helpers : MatrixFold.Cube n → K) : ExtensionLookupIdentity.Factor → MatrixFold.Cube n → K :=
  fun factor cell => if factor = .hash then ExtensionLookupIdentity.hashTable y sources cell + r else
    ExtensionLookupIdentity.factors eqPoint y sources helpers (2 ^ n) factor cell

/-- The full grammar agrees with the masked grammar on Boolean cells, while
retaining the smaller full-table round degree. -/
theorem full_sum_eq_partial (eqPoint : Fin n → K) (r y : K) (sources : Fin width → MatrixFold.Cube n → F)
    (helpers : MatrixFold.Cube n → K) :
    (∑ cell, PackedSumcheckRound.expression ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun factor => fullTables eqPoint r y sources helpers factor cell)) =
    ∑ cell, PackedSumcheckRound.expression ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
      (fun factor => ExtensionLookupIdentity.factors eqPoint y sources helpers (2 ^ n) factor cell) := by
  apply Finset.sum_congr rfl
  intro cell _
  change PackedSumcheckRound.expression ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
    ExtensionLookupIdentity.fullIndices (fun factor => if factor = .hash then
      ExtensionLookupIdentity.factors eqPoint y sources helpers (2 ^ n) .hash cell + r else
      ExtensionLookupIdentity.factors eqPoint y sources helpers (2 ^ n) factor cell) = _
  rw [ExtensionLookupIdentity.full_expression r
    (fun factor => ExtensionLookupIdentity.factors eqPoint y sources helpers (2 ^ n) factor cell),
    ExtensionLookupIdentity.partial_expression]
  simp only [ExtensionLookupIdentity.factors, ExtensionLookupIdentity.maskTable,
    (FlatMatrixFold.index n cell).isLt, ite_true, one_mul]

variable {Memory Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [DecidableEq K] [Fintype K] [SampleableType K] [SampleableType (Fin 1 → K)] [SampleableType (Fin n → K)]

/-- Native partial-table pair arithmetic. The two helper-sum cases are
exclusive: the false-sum loss is covered by the displayed EQ-plus-identity
bound rather than silently omitted or assumed independent. -/
theorem partial_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 4 + 1 ≤ p)
    (schedule : LookupPairSequence.Schedule K Memory Cfg Input Digest n 4)
    (shape : active + inactive = 2 ^ n) (r y : K) (table : Fin size → Fin width → F) (multiplicities : Fin size → F)
    (sources : Fin width → MatrixFold.Cube n → F) (helpers : MatrixFold.Cube n → K)
    (rNonzero : r ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes (activeTuples shape sources) table
      (fun i => algebraMap F K (multiplicities i)) (y, r))
    (claimed : K) (memory : Memory) (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (LookupPairSequence.program p small (by decide) schedule (tableSum r y table multiplicities) claimed memory)).run before}[
        LookupPairSequence.JointTruthful ExtensionLookupIdentity.partialArity
          (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
          (fun eqPoint => ExtensionLookupIdentity.factors eqPoint y sources helpers active) helpers outcome.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * (4 / Fintype.card K) := by
  apply LookupPairSequence.soundness_bound enc dummy workerShape p small (by decide) schedule _ claimed memory
    ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
    (fun eqPoint => ExtensionLookupIdentity.factors eqPoint y sources helpers active) ExtensionLookupIdentity.partial_degree helpers
  by_cases correctSum : tableSum r y table multiplicities = ∑ cell, helpers cell
  · right
    exact LookupReciprocalEnforcement.equality_bound shape r y sources helpers
      (fun i => TupleHash.hash y (table i)) (fun i => algebraMap F K (multiplicities i)) rNonzero notPasses correctSum.symm
  · exact Or.inl correctSum

/-- Native full-table pair arithmetic, with the actual degree-three affine
identity and the full active prefix. -/
theorem full_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 3 + 1 ≤ p)
    (schedule : LookupPairSequence.Schedule K Memory Cfg Input Digest n 3)
    (r y : K) (table : Fin size → Fin width → F) (multiplicities : Fin size → F)
    (sources : Fin width → MatrixFold.Cube n → F) (helpers : MatrixFold.Cube n → K)
    (rNonzero : r ≠ 0)
    (notPasses : ¬TupleLookupPair.Passes (activeTuples (active := 2 ^ n) (inactive := 0) (by omega) sources) table
      (fun i => algebraMap F K (multiplicities i)) (y, r))
    (claimed : K) (memory : Memory) (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (LookupPairSequence.program p small (by decide) schedule (tableSum r y table multiplicities) claimed memory)).run before}[
        LookupPairSequence.JointTruthful ExtensionLookupIdentity.fullArity
          (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
          (fun eqPoint => fullTables eqPoint r y sources helpers) helpers outcome.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * (3 / Fintype.card K) := by
  apply LookupPairSequence.soundness_bound enc dummy workerShape p small (by decide) schedule _ claimed memory
    ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
    (fun eqPoint => fullTables eqPoint r y sources helpers) ExtensionLookupIdentity.full_degree helpers
  by_cases correctSum : tableSum r y table multiplicities = ∑ cell, helpers cell
  · right
    have bound := LookupReciprocalEnforcement.equality_bound (count := 2 ^ n) (padding := 0) (by omega)
      r y sources helpers (fun i => TupleHash.hash y (table i)) (fun i => algebraMap F K (multiplicities i))
      rNonzero notPasses correctSum.symm
    simpa only [full_sum_eq_partial] using bound
  · exact Or.inl correctSum

end

end FormalProof4FHE.HasteBoots.LookupPairArithmetic
