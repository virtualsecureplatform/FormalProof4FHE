module

public import FormalProof4FHE.HasteBoots.LookupScalarSubclaim
public import FormalProof4FHE.HasteBoots.LookupReciprocalEnforcement

@[expose] public section

/-!
# Native lookup pair: helper sum, fresh EQ, identity sumcheck

The source-independent operational schedule validates the public-table sum
claim, runs the scalar helper-sum verifier, samples EQ only after success,
and runs the identity verifier on the same shared state. A failed sum skips
all EQ/identity work. Identity failure retains the actual earlier work.
Returned subclaims are not a supplied acceptance flag. Authentication and the
complete lookup repetition/root schedule remain separate obligations.
-/

open OracleSpec OracleComp BinaryTree
open scoped BigOperators Classical
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.LookupPairSequence

noncomputable section

abbrev SumResult (K Memory : Type) (n : ℕ) := Option (Subclaim K 1 n × Memory)
abbrev IdentityResult (K Memory : Type) (n : ℕ) := Option ((Fin n → K) × SumResult K Memory n)
abbrev Result (K Memory : Type) (n : ℕ) := SumResult K Memory n × IdentityResult K Memory n

variable {K Memory Cfg Input Digest : Type} [Field K] {n degree : ℕ}

structure Schedule (K Memory Cfg Input Digest : Type) (n degree : ℕ) where
  sumSend : ℕ → Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) ((Fin 2 → K) × Memory)
  sumAfter : Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory
  zeroSend : Subclaim K 1 n → (Fin n → K) → ℕ → Memory → (Fin 1 → K) →
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) ((Fin (degree + 1) → K) × Memory)
  zeroAfter : Subclaim K 1 n → (Fin n → K) → Memory → (Fin 1 → K) →
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin n → K)]

def sumProgram (p : ℕ) [CharP K p] (nodesEnough : 2 ≤ p)
    (schedule : Schedule K Memory Cfg Input Digest n degree) (claimed : K) (memory : Memory) :
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (SumResult K Memory n) :=
  PackedSumcheckOracle.program (NativePackedInterpolation.nodes p nodesEnough)
    (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p nodesEnough))
    schedule.sumSend schedule.sumAfter n (fun _ => claimed) memory

def zeroProgram (p : ℕ) [CharP K p] (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : Schedule K Memory Cfg Input Digest n degree) (earlier : Subclaim K 1 n) (eqPoint : Fin n → K) (memory : Memory) :
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (SumResult K Memory n) :=
  PackedSumcheckOracle.program (NativePackedInterpolation.nodes p (show 2 * 1 ≤ p by omega))
    (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small))
    (schedule.zeroSend earlier eqPoint) (schedule.zeroAfter earlier eqPoint) n (fun _ => 0) memory

def afterSum (p : ℕ) [CharP K p] (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : Schedule K Memory Cfg Input Digest n degree) (earlier : SumResult K Memory n) :
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (IdentityResult K Memory n) :=
  match earlier with
  | none => pure none
  | some entry => do
    let eqPoint ← PrivateSampling.embed Cfg Input Digest ($ᵗ (Fin n → K))
    let result ← zeroProgram p small positive schedule entry.1 eqPoint entry.2
    pure (some (eqPoint, result))

/-- The sum claim is compared before either sumcheck. The old sum result is
retained for the joint event; erasing it does not issue or remove any calls. -/
def program (p : ℕ) [CharP K p] (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : Schedule K Memory Cfg Input Digest n degree) (publicTotal claimed : K) (memory : Memory) :
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Result K Memory n) :=
  if claimed = publicTotal then
    SharedContinuation.program (sumProgram p (by omega) schedule claimed memory) (afterSum p small positive schedule)
  else pure (none, none)

def SumTruthful (helpers : MatrixFold.Cube n → K) (result : SumResult K Memory n) : Prop :=
  ScalarSumcheckOracle.MLETruthful LookupScalarSubclaim.sumArity (LookupScalarSubclaim.sumCoefficient (K := K))
    LookupScalarSubclaim.sumIndices (fun _ => helpers) result

/-- The identity relation is analysis-only. It is never passed to the
operational verifier or used to choose a different original source. -/
def IdentityTruthful {Factor Term : Type} [Fintype Term] (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor) (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K) :
    IdentityResult K Memory n → Prop
  | none => False
  | some entry => ScalarSumcheckOracle.MLETruthful arity coefficient indices (tables entry.1) entry.2

def JointTruthful {Factor Term : Type} [Fintype Term] (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor) (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K)
    (helpers : MatrixFold.Cube n → K) (result : Result K Memory n) : Prop :=
  SumTruthful helpers result.1 ∧ IdentityTruthful arity coefficient indices tables result.2

variable {Payload : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- EQ and the identity verifier share precisely the state left by sumcheck. -/
theorem afterSum_run_some (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : Schedule K Memory Cfg Input Digest n degree) (earlier : Subclaim K 1 n) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (afterSum p small positive schedule (some (earlier, memory)))).run before =
      (do
        let eqPoint ← $ᵗ (Fin n → K)
        let result ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (zeroProgram p small positive schedule earlier eqPoint memory)).run before
        pure (some (eqPoint, result.1), result.2)) := by
  simp only [afterSum, simulateQ_bind, StateT.run_bind, PrivateSampling.run_probComp,
    bind_map_left, simulateQ_pure, StateT.run_pure]

variable [Fintype K] [DecidableEq K]

/-- A false helper sum cannot yield both truthful terminals except for the
helper-sum soundness error. Every later EQ/identity call is retained. -/
theorem false_sum_bound {Factor Term : Type} [Fintype Term]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : Schedule K Memory Cfg Input Digest n degree) (publicTotal claimed : K) (memory : Memory)
    (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K) (helpers : MatrixFold.Cube n → K)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseSum : publicTotal ≠ ∑ cell, helpers cell) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program p small positive schedule publicTotal claimed memory)).run before}[
        JointTruthful arity coefficient indices tables helpers outcome.1] ≤ (n : ENNReal) / Fintype.card K := by
  by_cases checked : claimed = publicTotal
  · subst claimed
    rw [program, ite_eq_left rfl]
    have retained := SharedContinuation.earlier_event_le enc dummy shape
      (sumProgram p (by omega) schedule publicTotal memory)
      (afterSum p small positive schedule) before (SumTruthful helpers)
    have bound := ScalarSumcheckOracle.native_soundness_bound enc dummy shape p 1 (show 1 + 1 ≤ p by omega) (by decide)
      LookupScalarSubclaim.sumArity (LookupScalarSubclaim.sumCoefficient (K := K)) LookupScalarSubclaim.sumIndices
      (fun _ => le_rfl) schedule.sumSend schedule.sumAfter n (fun _ => helpers) publicTotal memory before
      (by simpa only [LookupScalarSubclaim.sum_expression] using falseSum)
    exact (prEvent_mono _ _ _ (fun _ event => event.1)).trans
      (retained.trans (by simpa only [sumProgram, SumTruthful, Nat.cast_one, div_eq_mul_inv, one_mul] using bound))
  · simp only [program, checked, ite_false, simulateQ_pure, StateT.run_pure, prEvent_pure,
      JointTruthful, SumTruthful, ScalarSumcheckOracle.MLETruthful, false_and, ite_false, zero_le]

/-- A fresh EQ draw followed by the actual native identity verifier. The
analysis miss bound is instantiated by concrete lookup arithmetic below. -/
theorem identity_bound {Factor Term : Type} [Fintype Term]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : Schedule K Memory Cfg Input Digest n degree) (earlier : Subclaim K 1 n) (memory : Memory)
    (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K) (bounded : ∀ term, arity term ≤ degree)
    (miss : Pr{let eqPoint ← $ᵗ (Fin n → K)}[
      (∑ cell, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables eqPoint factor cell)) = 0] ≤
        (n : ENNReal) / Fintype.card K)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (afterSum p small positive schedule (some (earlier, memory)))).run before}[
        IdentityTruthful arity coefficient indices tables outcome.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
  let stage := fun eqPoint => (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
    (zeroProgram p small positive schedule earlier eqPoint memory)).run before
  let tail := fun eqPoint => (fun outcome => (eqPoint, outcome)) <$> stage eqPoint
  let healed := fun eqPoint =>
    (∑ cell, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables eqPoint factor cell)) = 0
  have conditional : ∀ eqPoint, ¬healed eqPoint →
      Pr{let entry ← tail eqPoint}[ScalarSumcheckOracle.MLETruthful arity coefficient indices (tables entry.1) entry.2.1] ≤
        (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
    intro eqPoint notHealed
    rw [prEvent_map]
    exact ScalarSumcheckOracle.native_soundness_bound enc dummy shape p degree small positive arity coefficient indices bounded
      (schedule.zeroSend earlier eqPoint) (schedule.zeroAfter earlier eqPoint) n (tables eqPoint) 0 memory before (Ne.symm notHealed)
  have composed := prEvent_bind_le_prEvent_add ($ᵗ (Fin n → K)) tail healed
    (fun entry => ScalarSumcheckOracle.MLETruthful arity coefficient indices (tables entry.1) entry.2.1) conditional
  rw [afterSum_run_some]
  have translated : Pr{let eqPoint ← $ᵗ (Fin n → K); let outcome ← stage eqPoint}[
      ScalarSumcheckOracle.MLETruthful arity coefficient indices (tables eqPoint) outcome.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
    simpa only [tail, prEvent_norm] using composed.trans (add_le_add miss le_rfl)
  simpa only [prEvent_norm, IdentityTruthful] using translated

/-- The joint event requires both sumcheck terminals. A false helper sum is
handled by the sum verifier; otherwise the fresh-EQ/identity bound applies.
The two cases share one execution and do not assume independence. -/
theorem soundness_bound {Factor Term : Type} [Fintype Term]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (schedule : Schedule K Memory Cfg Input Digest n degree) (publicTotal claimed : K) (memory : Memory)
    (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K) (bounded : ∀ term, arity term ≤ degree)
    (helpers : MatrixFold.Cube n → K)
    (obstruction : publicTotal ≠ ∑ cell, helpers cell ∨
      Pr{let eqPoint ← $ᵗ (Fin n → K)}[
        (∑ cell, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables eqPoint factor cell)) = 0] ≤
          (n : ENNReal) / Fintype.card K)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program p small positive schedule publicTotal claimed memory)).run before}[
        JointTruthful arity coefficient indices tables helpers outcome.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
  rcases obstruction with falseSum | miss
  · exact (false_sum_bound enc dummy shape p small positive schedule publicTotal claimed memory
      arity coefficient indices tables helpers before falseSum).trans (le_add_of_nonneg_right zero_le)
  · by_cases checked : claimed = publicTotal
    · rw [program, ite_eq_left checked]
      have later := SharedContinuation.later_event_le enc dummy shape
        (sumProgram p (by omega) schedule claimed memory) (afterSum p small positive schedule) before
        (fun _ outcome => IdentityTruthful arity coefficient indices tables outcome.1)
        ((n : ENNReal) / Fintype.card K + (n : ENNReal) * ((degree : ENNReal) / Fintype.card K)) (by
          intro earlier initial
          cases earlier with
          | none => simp [afterSum, IdentityTruthful]
          | some entry =>
            exact identity_bound enc dummy shape p small positive schedule entry.1 entry.2
              arity coefficient indices tables bounded miss initial)
      exact (prEvent_mono _ _ _ (fun _ event => event.2)).trans later
    · simp only [program, checked, ite_false, simulateQ_pure, StateT.run_pure, prEvent_pure,
        JointTruthful, SumTruthful, ScalarSumcheckOracle.MLETruthful, false_and, ite_false, zero_le]

end

end FormalProof4FHE.HasteBoots.LookupPairSequence
