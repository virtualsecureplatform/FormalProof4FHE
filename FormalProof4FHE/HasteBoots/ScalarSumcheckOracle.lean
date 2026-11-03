module

public import FormalProof4FHE.HasteBoots.ScalarSumcheckQuery

@[expose] public section

/-!
# Scalar-point subclaims on the existing shared execution

Every supported result of the actual width-one sumcheck verifier has the
ordinary scalar query form. Rejection is allowed, and send/callback programs
retain their real shared work. The MLE terminal event inherits the checked
sumcheck bound directly, without a caller-supplied query-form certificate.
This remains the private-coin arithmetic stage; lookup PCS composition and
production Fiat--Shamir/Rust refinement are separate obligations.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.ScalarSumcheckOracle

noncomputable section

open scoped Classical

variable {K Memory Message Cfg Input Digest Payload : Type} [Field K] {n : ℕ}

def Valid : Option (Subclaim K 1 n × Memory) → Prop
  | none => True
  | some entry => ScalarSumcheckQuery.Scalar entry.1.query

theorem valid_prepend (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (challenge : Fin 1 → K)
    (result : Option (Subclaim K 1 n × Memory)) (valid : Valid result) :
    Valid (PackedSumcheckOracle.prependResult
      (PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes p small) challenge) result) := by
  cases result with
  | none => trivial
  | some entry => exact ScalarSumcheckQuery.scalar_prepend p small challenge entry.1.query valid

variable [SampleableType (Fin 1 → K)] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Query form follows from the operational verifier, not from a supplied
source-dependent certificate. This holds for every supported shared state. -/
theorem valid_result (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (interpret : Message → Polynomial K)
    (send : ℕ → Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message × Memory))
    (afterChallenge : Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (n : ℕ) (claimed : Fin 1 → K) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Option (Subclaim K 1 n × Memory) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PackedSumcheckOracle.program (NativePackedInterpolation.nodes p small) interpret send afterChallenge n claimed memory)).run before)) :
    Valid outcome.1 := by
  induction n generalizing claimed memory before with
  | zero =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    exact ScalarSumcheckQuery.scalar_nil
  | succ n ih =>
    rw [PackedSumcheckOracle.run_succ, mem_support_bind_iff] at supported
    obtain ⟨packet, _, rest⟩ := supported
    by_cases checked : PackedSumcheckProbability.Checks (NativePackedInterpolation.nodes p small) claimed (interpret packet.1.1)
    · simp only [checked, reduceIte, mem_support_bind_iff] at rest
      obtain ⟨challenge, _, callback, _, result, resultSupported, returned⟩ := rest
      have equal := eq_of_mem_support_pure _ returned
      subst outcome
      exact valid_prepend p small challenge result.1 (ih _ _ _ _ resultSupported)
    · simp only [checked, reduceIte] at rest
      have equal := eq_of_mem_support_pure _ rest
      subst outcome
      trivial

variable {Factor Term : Type} [Fintype Term]

def MLETruthful (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor) (tables : Factor → MatrixFold.Cube n → K) :
    Option (Subclaim K 1 n × Memory) → Prop
  | none => False
  | some entry => entry.1.expected 0 = PackedSumcheckRound.expression arity coefficient indices
      (fun factor => ExtensionQuery.evaluate n (ScalarSumcheckQuery.point entry.1.query) (tables factor))

omit [SampleableType (Fin 1 → K)] in
theorem truthful_iff (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor) (tables : Factor → MatrixFold.Cube n → K)
    (result : Option (Subclaim K 1 n × Memory)) (valid : Valid result) :
    MLETruthful arity coefficient indices tables result ↔
      PackedSumcheckOracle.TruthfulResult arity coefficient indices (fun factor cell _ => tables factor cell) result := by
  cases result with
  | none => rfl
  | some entry => exact (ScalarSumcheckQuery.truthful_iff arity coefficient indices tables entry.1 valid).symm

variable [Fintype K] [DecidableEq K]

/-- The ordinary scalar-MLE event inherits the full shared arithmetic bound,
including arbitrary adaptive messages/callbacks and rejecting executions. -/
theorem soundness_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor) (interpret : Message → Polynomial K)
    (degree : ℕ) (bounded : ∀ term, arity term ≤ degree) (messageDegree : ∀ message, (interpret message).natDegree ≤ degree)
    (send : ℕ → Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message × Memory))
    (afterChallenge : Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (n : ℕ) (tables : Factor → MatrixFold.Cube n → K) (claimed : Fin 1 → K) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ PackedSumcheckExecution.sum arity coefficient indices (fun factor cell _ => tables factor cell)) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PackedSumcheckOracle.program (NativePackedInterpolation.nodes p small) interpret send afterChallenge n claimed memory)).run before}[
        MLETruthful arity coefficient indices tables outcome.1] ≤ (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
  have comparison := prEvent_mono_of_support
    ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PackedSumcheckOracle.program (NativePackedInterpolation.nodes p small) interpret send afterChallenge n claimed memory)).run before)
    (fun outcome => MLETruthful arity coefficient indices tables outcome.1)
    (fun outcome => PackedSumcheckOracle.TruthfulResult arity coefficient indices
      (fun factor cell _ => tables factor cell) outcome.1)
    (fun outcome supported => (truthful_iff arity coefficient indices tables outcome.1
      (valid_result enc dummy shape p small interpret send afterChallenge n claimed memory before outcome supported)).mp)
  have bound := PackedSumcheckSharedSoundness.soundness_bound enc dummy shape
    (NativePackedInterpolation.nodes p small) arity coefficient indices interpret degree bounded
    (by simpa only [Nat.reduceMul, Nat.reduceSub, one_mul] using messageDegree)
    send afterChallenge n (fun factor cell _ => tables factor cell) claimed memory before falseClaim
  exact comparison.trans (by simpa only [Nat.reduceMul, Nat.reduceSub, one_mul, pow_one] using bound)

/-- Native scalar evaluation-vector messages automatically have the required
round degree. The supplied initial claim is an ordinary field element. -/
theorem native_soundness_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (degree : ℕ) (small : degree + 1 ≤ p) (positive : 1 ≤ degree)
    (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (bounded : ∀ term, arity term ≤ degree)
    (send : ℕ → Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Fin (degree + 1) → K) × Memory))
    (afterChallenge : Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (n : ℕ) (tables : Factor → MatrixFold.Cube n → K) (claimed : K) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ ∑ cell, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables factor cell)) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PackedSumcheckOracle.program (NativePackedInterpolation.nodes p (show 2 * 1 ≤ p by omega))
        (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small))
        send afterChallenge n (fun _ => claimed) memory)).run before}[
        MLETruthful arity coefficient indices tables outcome.1] ≤ (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) := by
  apply soundness_bound enc dummy shape p (show 2 * 1 ≤ p by omega) arity coefficient indices _ degree bounded
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) send afterChallenge n tables (fun _ => claimed) memory before
  intro equal
  exact falseClaim (congrFun equal 0)

/-- Later preparation/opening work retains this MLE event and every issued
shared call, including a rejecting continuation. -/
theorem continued_soundness_bound {Later : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor) (interpret : Message → Polynomial K)
    (degree : ℕ) (bounded : ∀ term, arity term ≤ degree) (messageDegree : ∀ message, (interpret message).natDegree ≤ degree)
    (send : ℕ → Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message × Memory))
    (afterChallenge : Memory → (Fin 1 → K) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (n : ℕ) (tables : Factor → MatrixFold.Cube n → K) (claimed : Fin 1 → K) (memory : Memory)
    (next : Option (Subclaim K 1 n × Memory) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Later)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ PackedSumcheckExecution.sum arity coefficient indices (fun factor cell _ => tables factor cell)) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program
        (PackedSumcheckOracle.program (NativePackedInterpolation.nodes p small) interpret send afterChallenge n claimed memory)
        next)).run before}[MLETruthful arity coefficient indices tables outcome.1.1] ≤
      (n : ENNReal) * ((degree : ENNReal) / Fintype.card K) :=
  (SharedContinuation.earlier_event_le enc dummy shape _ next before (MLETruthful arity coefficient indices tables)).trans
    (soundness_bound enc dummy shape p small arity coefficient indices interpret degree bounded messageDegree
      send afterChallenge n tables claimed memory before falseClaim)

end

end FormalProof4FHE.HasteBoots.ScalarSumcheckOracle
