module

public import FormalProof4FHE.HasteBoots.ScalarSumcheckQuery
public import FormalProof4FHE.HasteBoots.SharedBatchSumcheckSoundness

@[expose] public section

/-!
# One scalar point for every equation in a batch

Every supported batch result has scalar MLE query form and the same query
for every equation. This follows from execution; the prover supplies neither
certificate. Each round binds all messages before drawing a common challenge.
Rejected executions retain their work. Native refinement remains separate.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.SharedScalarBatchQuery

noncomputable section

open scoped Classical

variable {K Equation Memory Message Cfg Input Digest Payload : Type} [Field K] {n : ℕ}

def Valid : Option ((Equation → Subclaim K 1 n) × Memory) → Prop
  | none => True
  | some entry => (∀ equation, ScalarSumcheckQuery.Scalar (entry.1 equation).query) ∧
      ∀ left right, (entry.1 left).query = (entry.1 right).query

theorem valid_prepend (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (challenge : Fin 1 → K)
    (result : Option ((Equation → Subclaim K 1 n) × Memory)) (valid : Valid result) :
    Valid (SharedBatchSumcheckOracle.prependResult
      (PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes p small) challenge) result) := by
  cases result with
  | none => trivial
  | some entry =>
    constructor
    · intro equation
      exact ScalarSumcheckQuery.scalar_prepend p small challenge (entry.1 equation).query (valid.1 equation)
    · intro left right
      exact congrArg (Query.cons _) (valid.2 left right)

variable [SampleableType (Fin 1 → K)] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Query form follows from the operational verifier, not from a supplied
source-dependent certificate. This holds for every supported shared state. -/
theorem valid_result (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (interpret : Message → Equation → Polynomial K)
    (send : ℕ → Memory → (Equation → Fin 1 → K) → OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) (Message × Memory))
    (afterChallenge : Memory → (Fin 1 → K) → OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) Memory)
    (n : ℕ) (claimed : Equation → Fin 1 → K) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Option ((Equation → Subclaim K 1 n) × Memory) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedBatchSumcheckOracle.program (NativePackedInterpolation.nodes p small) interpret send afterChallenge n claimed memory)).run before)) :
    Valid outcome.1 := by
  induction n generalizing claimed memory before with
  | zero =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    exact ⟨fun _ => ScalarSumcheckQuery.scalar_nil, fun _ _ => rfl⟩
  | succ n ih =>
    rw [SharedBatchSumcheckOracle.run_succ, mem_support_bind_iff] at supported
    obtain ⟨packet, _, rest⟩ := supported
    by_cases checked : ∀ equation, PackedSumcheckProbability.Checks (NativePackedInterpolation.nodes p small) (claimed equation) (interpret packet.1.1 equation)
    · simp only [checked, implies_true, reduceIte, mem_support_bind_iff] at rest
      obtain ⟨challenge, _, callback, _, result, resultSupported, returned⟩ := rest
      have equal := eq_of_mem_support_pure _ returned
      subst outcome
      exact valid_prepend p small challenge result.1 (ih _ _ _ _ resultSupported)
    · simp only [checked, reduceIte] at rest
      have equal := eq_of_mem_support_pure _ rest
      subst outcome
      trivial

variable {Factor Term : Type} [Fintype Term]

def MLETruthful (equation : Equation) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor) (tables : Factor → MatrixFold.Cube n → K) :
    Option ((Equation → Subclaim K 1 n) × Memory) → Prop
  | none => False
  | some entry => (entry.1 equation).expected 0 = PackedSumcheckRound.expression arity coefficient indices
      (fun factor => ExtensionQuery.evaluate n (ScalarSumcheckQuery.point (entry.1 equation).query) (tables factor))

omit [SampleableType (Fin 1 → K)] in
theorem truthful_iff (equation : Equation) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor) (tables : Factor → MatrixFold.Cube n → K)
    (result : Option ((Equation → Subclaim K 1 n) × Memory)) (valid : Valid result) :
    MLETruthful equation arity coefficient indices tables result ↔
      SharedBatchSumcheckOracle.TruthfulResult equation arity coefficient indices (fun factor cell _ => tables factor cell) result := by
  cases result with
  | none => rfl
  | some entry => exact (ScalarSumcheckQuery.truthful_iff arity coefficient indices tables (entry.1 equation) (valid.1 equation)).symm

variable [Fintype K] [DecidableEq K]

/-- The ordinary scalar-MLE event inherits the full shared arithmetic bound,
including arbitrary adaptive messages/callbacks and rejecting executions. -/
theorem soundness_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor) (interpret : Message → Equation → Polynomial K) (equation : Equation)
    (degree : ℕ) (bounded : ∀ term, arity term ≤ degree) (messageDegree : ∀ message, (interpret message equation).natDegree ≤ degree)
    (send : ℕ → Memory → (Equation → Fin 1 → K) → OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) (Message × Memory))
    (afterChallenge : Memory → (Fin 1 → K) → OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) Memory)
    (n : ℕ) (tables : Factor → MatrixFold.Cube n → K) (claimed : Equation → Fin 1 → K) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed equation ≠ PackedSumcheckExecution.sum arity coefficient indices (fun factor cell _ => tables factor cell)) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedBatchSumcheckOracle.program (NativePackedInterpolation.nodes p small) interpret send afterChallenge n claimed memory)).run before}[
        MLETruthful equation arity coefficient indices tables outcome.1] ≤ (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
  have comparison := prEvent_mono_of_support
    ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedBatchSumcheckOracle.program (NativePackedInterpolation.nodes p small) interpret send afterChallenge n claimed memory)).run before)
    (fun outcome => MLETruthful equation arity coefficient indices tables outcome.1)
    (fun outcome => SharedBatchSumcheckOracle.TruthfulResult equation arity coefficient indices
      (fun factor cell _ => tables factor cell) outcome.1)
    (fun outcome supported => (truthful_iff equation arity coefficient indices tables outcome.1
      (valid_result enc dummy shape p small interpret send afterChallenge n claimed memory before outcome supported)).mp)
  have bound := SharedBatchSumcheckSoundness.soundness_bound enc dummy shape
    (NativePackedInterpolation.nodes p small) arity coefficient indices interpret equation degree bounded
    (by simpa only [Nat.reduceMul, Nat.reduceSub, one_mul] using messageDegree)
    send afterChallenge n (fun factor cell _ => tables factor cell) claimed memory before falseClaim
  exact comparison.trans (by simpa only [Nat.reduceMul, Nat.reduceSub, one_mul, pow_one] using bound)

end

end FormalProof4FHE.HasteBoots.SharedScalarBatchQuery
