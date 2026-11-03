module

public import FormalProof4FHE.HasteBoots.PackedZeroOracle
public import FormalProof4FHE.HasteBoots.PackedSumcheckSharedSoundness

@[expose] public section

/-!
# Shared-execution arithmetic soundness of packed ZeroCheck

A false original zero relation yields a truthful returned subclaim only within
the equality-point, first-mixing and remaining packed-sumcheck error terms.
All first messages and challenge callbacks are actual shared-oracle programs.
The same original factor sources and public mixed EQ source are retained.
The operational verifier rejects before sampling first mixing coins or running
callbacks; this proof adds no discarded hash work or safe-state certificate.
Authenticated original-factor openings and production Fiat--Shamir/Rust remain
composition obligations.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.PackedZeroSharedSoundness

noncomputable section

variable {F Factor Term FirstMessage RoundMessage Memory Cfg Input Digest Payload : Type}
  [Field F] [Fintype F] [DecidableEq F] [Fintype Term]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] {n k : ℕ}
  [SampleableType F] [SampleableType (Fin k → F)] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n k)] [SampleableType (Fin k → Fin k → F)]
  [SampleableType (Fin k → ((Fin k → F) × F))]

/-- All arithmetic errors are measured on the actual shared handler, with no
source-dependent operational checks or assumed terminal authentication. -/
theorem soundness_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (interpretFirst : FirstMessage → Fin k → Polynomial F) (interpretRound : RoundMessage → Polynomial F)
    (firstDegree : ∀ message point, (interpretFirst message point).natDegree ≤ (2 * k - 1) * productDegree)
    (roundDegree : ∀ message, (interpretRound message).natDegree ≤ (2 * k - 1) * (productDegree + 1))
    (firstRespond : PackedZeroReduction.Points F n k → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (FirstMessage × Memory))
    (afterFirst : PackedZeroReduction.Points F n k → FirstMessage × Memory → PackedZeroReduction.Coins F k →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (send : ℕ → Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (RoundMessage × Memory))
    (afterChallenge : Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseRelation : ¬PackedZeroCube.Vanishes arity coefficient indices tables) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PackedZeroOracle.program nodes interpretFirst interpretRound firstRespond afterFirst send afterChallenge memory)).run state}[
        PackedZeroOracle.TruthfulResult nodes arity coefficient indices tables outcome.1] ≤
      ((((n : ENNReal) / Fintype.card F) ^ k) +
        ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k))) +
      (n : ENNReal) * ((((((2 * k - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
  classical
  let honest := fun points => PackedZeroCube.firstPolynomials nodes arity coefficient indices tables points
  let pointBad := fun points => PackedZeroFirst.Boundary nodes (honest points)
  have falseCells : ¬PackedZeroFirst.Vanishes arity coefficient indices (PackedZeroCube.onCells tables) :=
    fun zero => falseRelation ((PackedZeroCube.vanishes_onCells_iff arity coefficient indices tables).mp zero)
  have pointBound : Pr{let points ← $ᵗ (PackedZeroReduction.Points F n k)}[pointBad points] ≤
      (((n : ENNReal) / Fintype.card F) ^ k) := by
    simpa only [pointBad, honest, PackedZeroCube.firstPolynomials_eq] using
      PackedZeroEquality.boundary_miss_bound nodes arity coefficient indices (PackedZeroCube.onCells tables) falseCells
  rw [PackedZeroOracle.run_program]
  apply le_trans (prEvent_bind_le_prEvent_add ($ᵗ (PackedZeroReduction.Points F n k)) _ pointBad _ ?_)
  · exact (add_le_add pointBound le_rfl).trans_eq (add_assoc _ _ _).symm
  · intro points outside
    apply prEvent_bind_le_of_forall_le
    intro first
    by_cases checked : PackedZeroFirst.Boundary nodes (interpretFirst first.1.1)
    · simp only [checked, reduceIte]
      let healed := fun coins : PackedZeroReduction.Coins F k =>
        PackedZeroFirst.reduce (interpretFirst first.1.1) coins.1 coins.2 =
          PackedSumcheckExecution.sum (fun term => arity term + 1) coefficient
            (PackedZeroFirst.reducedIndices arity indices) (PackedZeroCube.reducedTables nodes tables points coins)
      have mixingBound : Pr{let coins ← $ᵗ (PackedZeroReduction.Coins F k)}[healed coins] ≤
          ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
        have distinct := PackedZeroFirst.boundary_distinct nodes (interpretFirst first.1.1) (honest points) checked outside
        have honestDegree (point : Fin k) : (honest points point).natDegree ≤ (2 * k - 1) * productDegree :=
          PackedZeroFirst.polynomial_degree nodes arity coefficient indices
            (fun factor bit suffix lane => tables factor (bit, suffix) lane)
            (fun point => PackedEqualityCube.weight (points point)) productDegree bounded point
        simpa only [healed, PackedZeroCube.reducedSum_eq, honest] using
          PackedZeroMixing.mixing_bound (interpretFirst first.1.1) (honest points) ((2 * k - 1) * productDegree)
            distinct (firstDegree first.1.1) honestDegree
      have tailBound : ∀ coins, ¬healed coins →
          Pr{let outcome ← (do
              let nextState ← (simulateQ
                (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
                (afterFirst points first.1 coins)).run first.2
              let result ← (simulateQ
                (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
                (PackedSumcheckOracle.program nodes interpretRound send afterChallenge n
                  (PackedZeroFirst.reduce (interpretFirst first.1.1) coins.1 coins.2) nextState.1)).run nextState.2
              pure (PackedZeroOracle.wrapResult points coins result.1, result.2))}[
            PackedZeroOracle.TruthfulResult nodes arity coefficient indices tables outcome.1] ≤
            (n : ENNReal) * ((((((2 * k - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
        intro coins falseClaim
        apply prEvent_bind_le_of_forall_le
        intro nextState
        have bound := PackedSumcheckSharedSoundness.soundness_bound enc dummy shape nodes (fun term => arity term + 1)
          coefficient (PackedZeroFirst.reducedIndices arity indices) interpretRound (productDegree + 1)
          (fun term => Nat.add_le_add_right (bounded term) 1) roundDegree send afterChallenge n
          (PackedZeroCube.reducedTables nodes tables points coins)
          (PackedZeroFirst.reduce (interpretFirst first.1.1) coins.1 coins.2) nextState.1 nextState.2 falseClaim
        simpa only [prEvent_norm, PackedZeroOracle.truthful_wrap_iff] using bound
      exact (prEvent_bind_le_prEvent_add ($ᵗ (PackedZeroReduction.Coins F k)) _ healed _ tailBound).trans
        (add_le_add mixingBound le_rfl)
    · simp [checked, PackedZeroOracle.TruthfulResult, prEvent_norm]


/-- Native first and ordinary evaluation-vector messages discharge both degree
obligations. The equality points and every callback still use the shared run. -/
theorem native_soundness_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP F p] (productDegree : ℕ)
    (firstSmall : (2 * k - 1) * productDegree + 1 ≤ p)
    (roundSmall : (2 * k - 1) * (productDegree + 1) + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) (bounded : ∀ term, arity term ≤ productDegree)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (firstRespond : PackedZeroReduction.Points F n k → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
        ((Fin k → Fin ((2 * k - 1) * productDegree + 1) → F) × Memory))
    (afterFirst : PackedZeroReduction.Points F n k →
      (Fin k → Fin ((2 * k - 1) * productDegree + 1) → F) × Memory → PackedZeroReduction.Coins F k →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (send : ℕ → Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Fin ((2 * k - 1) * (productDegree + 1) + 1) → F) × Memory))
    (afterChallenge : Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseRelation : ¬PackedZeroCube.Vanishes arity coefficient indices tables) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PackedZeroOracle.program (NativePackedInterpolation.nodes p (enough.trans firstSmall))
        (fun message point => NativePackedInterpolation.messagePolynomial
          (NativePackedInterpolation.consecutive p firstSmall) (message point))
        (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p roundSmall))
        firstRespond afterFirst send afterChallenge memory)).run state}[
        PackedZeroOracle.TruthfulResult (NativePackedInterpolation.nodes p (enough.trans firstSmall))
          arity coefficient indices tables outcome.1] ≤
      ((((n : ENNReal) / Fintype.card F) ^ k) +
        ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k))) +
      (n : ENNReal) * ((((((2 * k - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ k)) :=
  soundness_bound enc dummy shape _ arity coefficient indices tables productDegree bounded _ _
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    firstRespond afterFirst send afterChallenge memory state falseRelation

/-- Later work retains the arithmetic bound and runs on the returned actual
cache, so its hash work remains available to the final availability charge. -/
theorem continued_soundness_bound {Later : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (interpretFirst : FirstMessage → Fin k → Polynomial F) (interpretRound : RoundMessage → Polynomial F)
    (firstDegree : ∀ message point, (interpretFirst message point).natDegree ≤ (2 * k - 1) * productDegree)
    (roundDegree : ∀ message, (interpretRound message).natDegree ≤ (2 * k - 1) * (productDegree + 1))
    (firstRespond : PackedZeroReduction.Points F n k → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (FirstMessage × Memory))
    (afterFirst : PackedZeroReduction.Points F n k → FirstMessage × Memory → PackedZeroReduction.Coins F k →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (send : ℕ → Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (RoundMessage × Memory))
    (afterChallenge : Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (memory : Memory)
    (next : Option (PackedZeroOracle.Subclaim F k n × Memory) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseRelation : ¬PackedZeroCube.Vanishes arity coefficient indices tables) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program
        (PackedZeroOracle.program nodes interpretFirst interpretRound firstRespond afterFirst send afterChallenge memory)
        next)).run state}[PackedZeroOracle.TruthfulResult nodes arity coefficient indices tables outcome.1.1] ≤
      ((((n : ENNReal) / Fintype.card F) ^ k) +
        ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k))) +
      (n : ENNReal) * ((((((2 * k - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ k)) :=
  (SharedContinuation.earlier_event_le enc dummy shape _ next state
    (PackedZeroOracle.TruthfulResult nodes arity coefficient indices tables)).trans
      (soundness_bound enc dummy shape nodes arity coefficient indices tables productDegree bounded
        interpretFirst interpretRound firstDegree roundDegree firstRespond afterFirst send afterChallenge memory state falseRelation)

end

end FormalProof4FHE.HasteBoots.PackedZeroSharedSoundness
