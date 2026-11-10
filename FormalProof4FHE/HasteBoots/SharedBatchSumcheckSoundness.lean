module

public import FormalProof4FHE.HasteBoots.SharedBatchSumcheckOracle
public import FormalProof4FHE.HasteBoots.SharedContinuation

@[expose] public section

/-!
# Shared-challenge batch soundness

A fixed false equation suffices: all equations are checked before each shared
draw, so no equation-count multiplier is required. Other equations may reject
and terminate the execution. The selected source tables are analysis only;
all adaptive messages and callbacks use one actual cache and checkpoint log.
For k = 1 the error is n * productDegree / card F. This is an interactive
arithmetic theorem, not yet a native transcript or PCS refinement.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.SharedBatchSumcheckSoundness

noncomputable section

variable {F Equation Factor Term Message ProverState Cfg Input Digest Payload : Type}
  [Field F] [Fintype F] [DecidableEq F] [Fintype Term] {k : ℕ} [SampleableType (Fin k → F)]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- The operational verifier never receives the fixed source tables: they
appear only in the returned-subclaim event. No initial hash safety premise or
adversarial query cutoff is needed for this arithmetic bound. -/
theorem soundness_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (interpret : Message → Equation → Polynomial F) (equation : Equation) (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (messageDegree : ∀ message, (interpret message equation).natDegree ≤ (2 * k - 1) * productDegree)
    (send : ℕ → ProverState → (Equation → Fin k → F) →
      OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) →
      OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) ProverState)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Equation → Fin k → F)
    (privateState : ProverState)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed equation ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedBatchSumcheckOracle.program nodes interpret send afterChallenge n claimed privateState)).run state}[
        SharedBatchSumcheckOracle.TruthfulResult equation arity coefficient indices tables result.1] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
  classical
  induction n generalizing claimed privateState state with
  | zero =>
    rw [SharedBatchSumcheckOracle.program, simulateQ_pure, StateT.run_pure, prEvent_pure]
    simp only [SharedBatchSumcheckOracle.TruthfulResult, Subclaim.truthful_zero_iff, falseClaim,
      ite_false, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    rw [SharedBatchSumcheckOracle.run_succ]
    apply prEvent_bind_le_of_forall_le
    intro packet
    by_cases checked : ∀ eq, PackedSumcheckProbability.Checks nodes (claimed eq) (interpret packet.1.1 eq)
    · simp only [checked, implies_true, reduceIte]
      let honest := PackedSumcheckExecution.roundPolynomial nodes arity coefficient indices tables
      let healed := fun challenge : Fin k → F =>
        ∀ lane, (interpret packet.1.1 equation).eval (challenge lane) = honest.eval (challenge lane)
      have different := PackedSumcheckProbability.checked_distinct nodes (claimed equation)
        (PackedSumcheckExecution.sum arity coefficient indices tables) (interpret packet.1.1 equation) honest falseClaim (checked equation)
        (PackedSumcheckExecution.roundPolynomial_check nodes arity coefficient indices tables)
      have roots := PackedSumcheckProbability.all_agree_bound (interpret packet.1.1 equation) honest
        ((2 * k - 1) * productDegree) k different (messageDegree packet.1.1)
        (PackedSumcheckRound.polynomial_degree nodes arity coefficient indices
          (fun factor bit suffix lane => tables factor (bit, suffix) lane) productDegree bounded)
      have tailBound : ∀ challenge, ¬healed challenge →
          Pr{let result ← (do
            let nextState ← (simulateQ
              (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
                (afterChallenge packet.1.2 challenge)).run packet.2
            let result ← (simulateQ
              (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
              (SharedBatchSumcheckOracle.program nodes interpret send afterChallenge n
                (fun eq lane => (interpret packet.1.1 eq).eval (challenge lane)) nextState.1)).run nextState.2
            pure (SharedBatchSumcheckOracle.prependResult (PackedSumcheckRound.challengePair nodes challenge) result.1, result.2))}[
              SharedBatchSumcheckOracle.TruthfulResult equation arity coefficient indices tables result.1] ≤
            (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
        intro challenge outside
        have falseNext : (fun lane => (interpret packet.1.1 equation).eval (challenge lane)) ≠
            PackedSumcheckExecution.sum arity coefficient indices (PackedSumcheckExecution.fold nodes tables challenge) := by
          intro equal
          apply outside
          intro lane
          exact (congrFun equal lane).trans (PackedSumcheckExecution.sum_fold nodes arity coefficient indices tables challenge lane)
        apply prEvent_bind_le_of_forall_le
        intro nextState
        have bound := ih (fun factor => MatrixFold.foldFirst (PackedSumcheckRound.challengePair nodes challenge) (tables factor))
          (fun eq lane => (interpret packet.1.1 eq).eval (challenge lane)) nextState.1 nextState.2 falseNext
        simpa only [prEvent_norm, SharedBatchSumcheckOracle.truthful_prepend_iff] using bound
      exact (prEvent_bind_le_prEvent_add ($ᵗ (Fin k → F)) _ healed _ tailBound).trans
        ((add_le_add roots le_rfl).trans_eq (by
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]))
    · simp only [checked, prEvent_pure, SharedBatchSumcheckOracle.TruthfulResult, ite_false, zero_le]

/-- Native evaluation-vector messages provide their degree bounds without a
PCS or transcript security certificate. The oracle program and state remain
exactly those of the preceding theorem. -/
theorem native_soundness_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) (bounded : ∀ term, arity term ≤ productDegree)
    (send : ℕ → ProverState → (Equation → Fin k → F) → OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest)
      ((Equation → Fin ((2 * k - 1) * productDegree + 1) → F) × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) ProverState)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Equation → Fin k → F) (equation : Equation)
    (privateState : ProverState)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed equation ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedBatchSumcheckOracle.program (NativePackedInterpolation.nodes p (enough.trans small))
        (fun (message : Equation → Fin ((2 * k - 1) * productDegree + 1) → F) equation => NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small) (message equation))
        send afterChallenge n claimed privateState)).run state}[
          SharedBatchSumcheckOracle.TruthfulResult equation arity coefficient indices tables result.1] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) :=
  soundness_bound (Equation := Equation) (Message := Equation → Fin ((2 * k - 1) * productDegree + 1) → F)
    enc dummy shape (NativePackedInterpolation.nodes p (enough.trans small)) arity coefficient indices
    (fun message eq => NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small) (message eq))
    equation productDegree bounded
    (fun message => NativePackedInterpolation.messagePolynomial_degree (NativePackedInterpolation.consecutive p small) (message equation)) send afterChallenge n tables claimed privateState state falseClaim

/-- Arbitrary later opening work runs on the actual returned cache and logs.
Retaining the subclaim keeps the same arithmetic bound while all later calls
remain present in the complete execution and its expected work charge. -/
theorem continued_soundness_bound {Later : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (interpret : Message → Equation → Polynomial F) (equation : Equation) (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (messageDegree : ∀ message, (interpret message equation).natDegree ≤ (2 * k - 1) * productDegree)
    (send : ℕ → ProverState → (Equation → Fin k → F) →
      OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) ProverState)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Equation → Fin k → F)
    (privateState : ProverState)
    (next : Option ((Equation → Subclaim F k n) × ProverState) → OracleComp (SharedBatchSumcheckOracle.Shared Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed equation ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (SharedBatchSumcheckOracle.program nodes interpret send afterChallenge n claimed privateState)
        next)).run state}[SharedBatchSumcheckOracle.TruthfulResult equation arity coefficient indices tables result.1.1] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) :=
  (SharedContinuation.earlier_event_le enc dummy shape _ next state
    (SharedBatchSumcheckOracle.TruthfulResult equation arity coefficient indices tables)).trans
      (soundness_bound enc dummy shape nodes arity coefficient indices interpret equation productDegree bounded messageDegree
        send afterChallenge n tables claimed privateState state falseClaim)

end

end FormalProof4FHE.HasteBoots.SharedBatchSumcheckSoundness
