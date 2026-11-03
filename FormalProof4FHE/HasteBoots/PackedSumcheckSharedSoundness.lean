module

public import FormalProof4FHE.HasteBoots.PackedSumcheckOracle
public import FormalProof4FHE.HasteBoots.SharedContinuation

@[expose] public section

/-!
# Packed-sumcheck arithmetic bound on the same shared hash execution

The actual verifier returns a source-independent matrix-opening subclaim.
Against any fixed false source sum, the probability that this returned claim
is truthful is bounded by the packed-round arithmetic error. All message and
callback programs use the actual shared cache/log/checkpoint state, including
calls on rejected executions. The analysis does not reset or sample a second
hash experiment. Authentication of the returned subclaim and production
Fiat--Shamir remain separate obligations.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.PackedSumcheckSharedSoundness

noncomputable section

variable {F Factor Term Message ProverState Cfg Input Digest Payload : Type}
  [Field F] [Fintype F] [DecidableEq F] [Fintype Term] {k : ℕ} [SampleableType (Fin k → F)]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- The operational verifier never receives the fixed source tables: they
appear only in the returned-subclaim event. No initial hash safety premise or
adversarial query cutoff is needed for this arithmetic bound. -/
theorem soundness_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (interpret : Message → Polynomial F) (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (messageDegree : ∀ message, (interpret message).natDegree ≤ (2 * k - 1) * productDegree)
    (send : ℕ → ProverState → (Fin k → F) →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) ProverState)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F)
    (privateState : ProverState)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PackedSumcheckOracle.program nodes interpret send afterChallenge n claimed privateState)).run state}[
        PackedSumcheckOracle.TruthfulResult arity coefficient indices tables result.1] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
  classical
  induction n generalizing claimed privateState state with
  | zero =>
    rw [PackedSumcheckOracle.program, simulateQ_pure, StateT.run_pure, prEvent_pure]
    simp only [PackedSumcheckOracle.TruthfulResult, Subclaim.truthful_zero_iff, falseClaim,
      ite_false, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    rw [PackedSumcheckOracle.run_succ]
    apply prEvent_bind_le_of_forall_le
    intro packet
    by_cases checked : PackedSumcheckProbability.Checks nodes claimed (interpret packet.1.1)
    · simp only [checked, reduceIte]
      let honest := PackedSumcheckExecution.roundPolynomial nodes arity coefficient indices tables
      let healed := fun challenge : Fin k → F =>
        ∀ lane, (interpret packet.1.1).eval (challenge lane) = honest.eval (challenge lane)
      have different := PackedSumcheckProbability.checked_distinct nodes claimed
        (PackedSumcheckExecution.sum arity coefficient indices tables) (interpret packet.1.1) honest falseClaim checked
        (PackedSumcheckExecution.roundPolynomial_check nodes arity coefficient indices tables)
      have roots := PackedSumcheckProbability.all_agree_bound (interpret packet.1.1) honest
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
              (PackedSumcheckOracle.program nodes interpret send afterChallenge n
                (fun lane => (interpret packet.1.1).eval (challenge lane)) nextState.1)).run nextState.2
            pure (PackedSumcheckOracle.prependResult (PackedSumcheckRound.challengePair nodes challenge) result.1, result.2))}[
              PackedSumcheckOracle.TruthfulResult arity coefficient indices tables result.1] ≤
            (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
        intro challenge outside
        have falseNext : (fun lane => (interpret packet.1.1).eval (challenge lane)) ≠
            PackedSumcheckExecution.sum arity coefficient indices (PackedSumcheckExecution.fold nodes tables challenge) := by
          intro equal
          apply outside
          intro lane
          exact (congrFun equal lane).trans (PackedSumcheckExecution.sum_fold nodes arity coefficient indices tables challenge lane)
        apply prEvent_bind_le_of_forall_le
        intro nextState
        have bound := ih (fun factor => MatrixFold.foldFirst (PackedSumcheckRound.challengePair nodes challenge) (tables factor))
          (fun lane => (interpret packet.1.1).eval (challenge lane)) nextState.1 nextState.2 falseNext
        simpa only [prEvent_norm, PackedSumcheckOracle.truthful_prepend_iff] using bound
      exact (prEvent_bind_le_prEvent_add ($ᵗ (Fin k → F)) _ healed _ tailBound).trans
        ((add_le_add roots le_rfl).trans_eq (by
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]))
    · simp only [checked, prEvent_pure, PackedSumcheckOracle.TruthfulResult, ite_false, zero_le]

/-- Native evaluation-vector messages provide their degree bounds without a
PCS or transcript security certificate. The oracle program and state remain
exactly those of the preceding theorem. -/
theorem native_soundness_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) (bounded : ∀ term, arity term ≤ productDegree)
    (send : ℕ → ProverState → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Fin ((2 * k - 1) * productDegree + 1) → F) × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) ProverState)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F)
    (privateState : ProverState)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PackedSumcheckOracle.program (NativePackedInterpolation.nodes p (enough.trans small))
        (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small))
        send afterChallenge n claimed privateState)).run state}[
          PackedSumcheckOracle.TruthfulResult arity coefficient indices tables result.1] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) :=
  soundness_bound enc dummy shape _ arity coefficient indices _ productDegree bounded
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) send afterChallenge n tables claimed privateState state falseClaim

/-- Arbitrary later opening work runs on the actual returned cache and logs.
Retaining the subclaim keeps the same arithmetic bound while all later calls
remain present in the complete execution and its expected work charge. -/
theorem continued_soundness_bound {Later : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (interpret : Message → Polynomial F) (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (messageDegree : ∀ message, (interpret message).natDegree ≤ (2 * k - 1) * productDegree)
    (send : ℕ → ProverState → (Fin k → F) →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) ProverState)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F)
    (privateState : ProverState)
    (next : Option (Subclaim F k n × ProverState) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (PackedSumcheckOracle.program nodes interpret send afterChallenge n claimed privateState)
        next)).run state}[PackedSumcheckOracle.TruthfulResult arity coefficient indices tables result.1.1] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) :=
  (SharedContinuation.earlier_event_le enc dummy shape _ next state
    (PackedSumcheckOracle.TruthfulResult arity coefficient indices tables)).trans
      (soundness_bound enc dummy shape nodes arity coefficient indices interpret productDegree bounded messageDegree
        send afterChallenge n tables claimed privateState state falseClaim)

end

end FormalProof4FHE.HasteBoots.PackedSumcheckSharedSoundness
