module
public import FormalProof4FHE.HasteBoots.OrderedPrivateDraws
public import FormalProof4FHE.HasteBoots.SharedScalarBatchQuery
public import FormalProof4FHE.HasteBoots.LookupPairArithmetic
@[expose] public section

/-! All job equality points precede a common-challenge scalar sumcheck batch.
Each job contributes [helper sum, identity], with initial claims fixed to the
computed public total and zero. Callbacks preserve the actual shared work.
The source/helper tables appear only in analysis, after their fixed prefixes.
Production Fiat--Shamir and native message refinement remain separate. -/
open OracleSpec OracleComp BinaryTree
open scoped BigOperators Classical
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
namespace FormalProof4FHE.HasteBoots.SharedLookupBatchSequence
noncomputable section
abbrev Equation (jobs : ℕ) := Fin jobs × Bool
abbrev Points (K : Type) (jobs n : ℕ) := Fin jobs → Fin n → K
abbrev Shared (Cfg Input Digest : Type) := CheckpointExecution.Spec unifSpec Cfg Input Digest
abbrev Result (K Memory : Type) (jobs n : ℕ) :=
  ((Points K jobs n) × Memory) × Option ((Equation jobs → Subclaim K 1 n) × Memory)

structure Schedule (K Message Memory Cfg Input Digest : Type) (jobs n : ℕ) [Field K] where
  beforeEquality : ℕ → Memory → OracleComp (Shared Cfg Input Digest) Memory
  afterEquality : ℕ → Memory → (Fin n → K) → OracleComp (Shared Cfg Input Digest) Memory
  interpret : Points K jobs n → Message → Equation jobs → Polynomial K
  send : Points K jobs n → ℕ → Memory → (Equation jobs → Fin 1 → K) →
    OracleComp (Shared Cfg Input Digest) (Message × Memory)
  afterChallenge : Points K jobs n → Memory → (Fin 1 → K) → OracleComp (Shared Cfg Input Digest) Memory

variable {K Message Memory Cfg Input Digest Payload : Type} [Field K] {jobs n : ℕ}

def initialClaims (totals : Fin jobs → K) (equation : Equation jobs) (_ : Fin 1) : K :=
  if equation.2 then 0 else totals equation.1

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin n → K)]

def batch (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : Schedule K Message Memory Cfg Input Digest jobs n) (totals : Fin jobs → K)
    (earlier : Points K jobs n × Memory) :=
  SharedBatchSumcheckOracle.program (NativePackedInterpolation.nodes p small)
    (schedule.interpret earlier.1) (schedule.send earlier.1) (schedule.afterChallenge earlier.1)
    n (initialClaims totals) earlier.2

def program (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : Schedule K Message Memory Cfg Input Digest jobs n) (totals : Fin jobs → K) (memory : Memory) :
    OracleComp (Shared Cfg Input Digest) (Result K Memory jobs n) :=
  SharedContinuation.program
    (OrderedPrivateDraws.program schedule.beforeEquality schedule.afterEquality jobs 0 memory)
    (batch p small schedule totals)

def SumTruthful (selected : Fin jobs) (helpers : MatrixFold.Cube n → K)
    (result : Result K Memory jobs n) : Prop :=
  SharedScalarBatchQuery.MLETruthful (selected,false) LookupScalarSubclaim.sumArity
    (LookupScalarSubclaim.sumCoefficient (K := K)) LookupScalarSubclaim.sumIndices (fun _ => helpers) result.2

def IdentityTruthful {Factor Term : Type} [Fintype Term] (selected : Fin jobs)
    (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K) (result : Result K Memory jobs n) : Prop :=
  SharedScalarBatchQuery.MLETruthful (selected,true) arity coefficient indices (tables (result.1.1 selected)) result.2

def JointTruthful {Factor Term : Type} [Fintype Term] (selected : Fin jobs)
    (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K) (helpers : MatrixFold.Cube n → K)
    (result : Result K Memory jobs n) : Prop :=
  SumTruthful selected helpers result ∧ IdentityTruthful selected arity coefficient indices tables result

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- The real ordered-draw/batch execution supplies common scalar query
validity. This is the invariant used to extract opening packets later. -/
theorem valid_result (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : Schedule K Message Memory Cfg Input Digest jobs n) (totals : Fin jobs → K) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Result K Memory jobs n × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program p small schedule totals memory)).run before)) :
    SharedScalarBatchQuery.Valid outcome.1.2 := by
  obtain ⟨earlier,_,later,laterSupported,equal⟩ :=
    (SharedContinuation.support_program enc dummy shape
      (OrderedPrivateDraws.program schedule.beforeEquality schedule.afterEquality jobs 0 memory)
      (batch p small schedule totals) before outcome).mp supported
  subst outcome
  exact SharedScalarBatchQuery.valid_result enc dummy shape p small
    (schedule.interpret earlier.1.1) (schedule.send earlier.1.1) (schedule.afterChallenge earlier.1.1)
    n (initialClaims totals) earlier.1.2 earlier.2 later laterSupported

/-- All equality-point work is retained before the batch. A fixed false
helper sum needs only its degree-one scalar batch bound. -/
theorem false_sum_bound {Factor Term : Type} [Fintype Term]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : Schedule K Message Memory Cfg Input Digest jobs n) (totals : Fin jobs → K) (memory : Memory)
    (selected : Fin jobs) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K) (helpers : MatrixFold.Cube n → K)
    (sumDegree : ∀ points message, (schedule.interpret points message (selected,false)).natDegree ≤ 1)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseSum : totals selected ≠ ∑ cell, helpers cell) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program p small schedule totals memory)).run before}[
        JointTruthful selected arity coefficient indices tables helpers outcome.1] ≤ (n : ENNReal) / Fintype.card K := by
  have later := SharedContinuation.later_event_le enc dummy shape
    (OrderedPrivateDraws.program schedule.beforeEquality schedule.afterEquality jobs 0 memory)
    (batch p small schedule totals) before
    (fun _ outcome => SharedScalarBatchQuery.MLETruthful (selected,false) LookupScalarSubclaim.sumArity
      (LookupScalarSubclaim.sumCoefficient (K := K)) LookupScalarSubclaim.sumIndices (fun _ => helpers) outcome.1)
    ((n : ENNReal) / Fintype.card K) (by
      intro earlier initial
      have bound := SharedScalarBatchQuery.soundness_bound enc dummy shape p small
        LookupScalarSubclaim.sumArity (LookupScalarSubclaim.sumCoefficient (K := K)) LookupScalarSubclaim.sumIndices
        (schedule.interpret earlier.1) (selected,false) 1 (fun _ => le_rfl) (sumDegree earlier.1)
        (schedule.send earlier.1) (schedule.afterChallenge earlier.1) n (fun _ => helpers)
        (initialClaims totals) earlier.2 initial (by
          intro equal
          apply falseSum
          have equalZero := congrFun equal 0
          change totals selected = ∑ cell, PackedSumcheckRound.expression LookupScalarSubclaim.sumArity
            LookupScalarSubclaim.sumCoefficient LookupScalarSubclaim.sumIndices (fun _ => helpers cell) at equalZero
          simpa only [LookupScalarSubclaim.sum_expression] using equalZero)
      simpa only [batch,Nat.cast_one,div_eq_mul_inv,one_mul] using bound)
  exact (prEvent_mono _ _ _ (fun _ event => event.1)).trans later
/-- A selected fresh equality point precedes the shared batch. Outside its
Boolean-identity miss event, that job's initial zero claim is false. -/
theorem identity_bound {Factor Term : Type} [Fintype Term]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : Schedule K Message Memory Cfg Input Digest jobs n) (totals : Fin jobs → K) (memory : Memory)
    (selected : Fin jobs) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K)
    (degree : ℕ) (bounded : ∀ term, arity term ≤ degree)
    (messageDegree : ∀ points message, (schedule.interpret points message (selected,true)).natDegree ≤ degree)
    (miss : Pr{let eqPoint ← $ᵗ (Fin n → K)}[
      (∑ cell, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables eqPoint factor cell)) = 0] ≤
        (n : ENNReal) / Fintype.card K)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program p small schedule totals memory)).run before}[
        IdentityTruthful selected arity coefficient indices tables outcome.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
  let drawsLaw := (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
    (OrderedPrivateDraws.program schedule.beforeEquality schedule.afterEquality jobs 0 memory)).run before
  let next := fun earlier : (Points K jobs n × Memory) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape => do
    let result ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (batch p small schedule totals earlier.1)).run earlier.2
    pure ((earlier.1,result.1),result.2)
  let healed := fun earlier : (Points K jobs n × Memory) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape =>
    (∑ cell, PackedSumcheckRound.expression arity coefficient indices
      (fun factor => tables (earlier.1.1 selected) factor cell)) = 0
  have missPrefix : Pr{let earlier ← drawsLaw}[healed earlier] ≤ (n : ENNReal) / Fintype.card K :=
    (OrderedPrivateDraws.selected_event_le enc dummy shape schedule.beforeEquality schedule.afterEquality jobs 0 memory before
      selected (fun eqPoint => (∑ cell, PackedSumcheckRound.expression arity coefficient indices
        (fun factor => tables eqPoint factor cell)) = 0)).trans miss
  have conditional : ∀ earlier, ¬healed earlier →
      Pr{let outcome ← next earlier}[IdentityTruthful selected arity coefficient indices tables outcome.1] ≤
        (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
    intro earlier outside
    have bound := SharedScalarBatchQuery.soundness_bound enc dummy shape p small arity coefficient indices
      (schedule.interpret earlier.1.1) (selected,true) degree bounded (messageDegree earlier.1.1)
      (schedule.send earlier.1.1) (schedule.afterChallenge earlier.1.1) n (tables (earlier.1.1 selected))
      (initialClaims totals) earlier.1.2 earlier.2 (by
        intro equal
        apply outside
        have equalZero := congrFun equal 0
        change 0 = ∑ cell, PackedSumcheckRound.expression arity coefficient indices
          (fun factor => tables (earlier.1.1 selected) factor cell) at equalZero
        exact equalZero.symm)
    simpa only [next,batch,prEvent_norm,IdentityTruthful] using bound
  have composed := (prEvent_bind_le_prEvent_add drawsLaw next healed
    (fun outcome => IdentityTruthful selected arity coefficient indices tables outcome.1) conditional).trans
      (add_le_add missPrefix le_rfl)
  simpa only [program,SharedContinuation.program,simulateQ_bind,StateT.run_bind,simulateQ_pure,
    StateT.run_pure,drawsLaw,next] using composed

/-- A fixed nonpassing job yields a false helper sum or a fresh-EQ obstruction.
Both terminals are measured on the same batch: there is no job-count factor
and no separate sum/identity challenge experiment. -/
theorem soundness_bound {Factor Term : Type} [Fintype Term]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : Schedule K Message Memory Cfg Input Digest jobs n) (totals : Fin jobs → K) (memory : Memory)
    (selected : Fin jobs) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K) (helpers : MatrixFold.Cube n → K)
    (degree : ℕ) (bounded : ∀ term, arity term ≤ degree)
    (sumDegree : ∀ points message, (schedule.interpret points message (selected,false)).natDegree ≤ 1)
    (messageDegree : ∀ points message, (schedule.interpret points message (selected,true)).natDegree ≤ degree)
    (obstruction : totals selected ≠ ∑ cell, helpers cell ∨
      Pr{let eqPoint ← $ᵗ (Fin n → K)}[
        (∑ cell, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables eqPoint factor cell)) = 0] ≤
          (n : ENNReal) / Fintype.card K)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program p small schedule totals memory)).run before}[
        JointTruthful selected arity coefficient indices tables helpers outcome.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
  rcases obstruction with falseSum | miss
  · exact (false_sum_bound enc dummy shape p small schedule totals memory selected arity coefficient indices tables helpers
      sumDegree before falseSum).trans (le_add_of_nonneg_right zero_le)
  · exact (prEvent_mono _ _ _ (fun _ event => event.2)).trans
      (identity_bound enc dummy shape p small schedule totals memory selected arity coefficient indices tables degree bounded
        messageDegree miss before)

/-- Later terminal reception, binding, and PCS work use the actual returned
state and retain this arithmetic event, including rejecting continuations. -/
theorem continued_soundness_bound {Later Factor Term : Type} [Fintype Term]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : Schedule K Message Memory Cfg Input Digest jobs n) (totals : Fin jobs → K) (memory : Memory)
    (selected : Fin jobs) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : (Fin n → K) → Factor → MatrixFold.Cube n → K) (helpers : MatrixFold.Cube n → K)
    (degree : ℕ) (bounded : ∀ term, arity term ≤ degree)
    (sumDegree : ∀ points message, (schedule.interpret points message (selected,false)).natDegree ≤ 1)
    (messageDegree : ∀ points message, (schedule.interpret points message (selected,true)).natDegree ≤ degree)
    (obstruction : totals selected ≠ ∑ cell, helpers cell ∨
      Pr{let eqPoint ← $ᵗ (Fin n → K)}[
        (∑ cell, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables eqPoint factor cell)) = 0] ≤
          (n : ENNReal) / Fintype.card K)
    (next : Result K Memory jobs n → OracleComp (Shared Cfg Input Digest) Later)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (program p small schedule totals memory) next)).run before}[
        JointTruthful selected arity coefficient indices tables helpers outcome.1.1] ≤
      (n : ENNReal) / Fintype.card K + (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) :=
  (SharedContinuation.earlier_event_le enc dummy shape (program p small schedule totals memory) next before
    (JointTruthful selected arity coefficient indices tables helpers)).trans
      (soundness_bound enc dummy shape p small schedule totals memory selected arity coefficient indices tables helpers
        degree bounded sumDegree messageDegree obstruction before)

end
end FormalProof4FHE.HasteBoots.SharedLookupBatchSequence
