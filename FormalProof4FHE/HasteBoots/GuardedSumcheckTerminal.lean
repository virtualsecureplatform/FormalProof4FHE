module

public import FormalProof4FHE.HasteBoots.PackedSumcheckTerminalOracle
public import FormalProof4FHE.HasteBoots.ShortCircuitSequence

@[expose] public section

/-!
# Terminal checks before short-circuit factor verification

The typed values are checked against the returned subclaim before binding them
or opening any factor. Only a passing check invokes the binding callback and
factor loop. The first rejected opening stops that loop. All earlier calls and
private memory survive rejection in the actual shared handler.
This is a source-independent terminal adapter. Its arithmetic theorem retains
an explicit accepted wrong-factor event; concrete PCS/ZeroCheck composition,
Fiat--Shamir and Rust refinement remain separate obligations.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.GuardedSumcheckTerminal

noncomputable section

variable {F Factor Term Message Memory Opening Cfg Input Digest Payload : Type}
  [Field F] [DecidableEq F] [Fintype Term] {k n : ℕ}

abbrev Outcome (F Factor Memory Opening : Type) (k n : ℕ) :=
  Option (Subclaim F k n × Memory) ×
    Option (((Factor → Fin k → F) × Memory) × Option (ShortCircuitSequence.Outcome Factor Opening Memory))

def terminalView (outcome : Outcome F Factor Memory Opening k n) :
    PackedSumcheckTerminalOracle.Outcome F Factor Memory k n :=
  (outcome.1, outcome.2.map (fun proposal => proposal.1.1))

def accepted (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) : Outcome F Factor Memory Opening k n → Bool
  | (some entry, some ((values, _memory), some opened)) =>
      opened.accepted && PackedSumcheckTerminalOracle.check arity coefficient indices values entry.1.expected
  | _ => false

/-- Acceptance retains both the checked terminal identity and successful factor
verification; a supplied wrong value on a rejected path is not a PCS failure. -/
def WrongAcceptedFactor (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor n k) (outcome : Outcome F Factor Memory Opening k n) : Prop :=
  accepted arity coefficient indices outcome = true ∧
    PackedSumcheckTerminalOracle.WrongFactor tables (terminalView outcome)

theorem accepted_terminalView (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) (outcome : Outcome F Factor Memory Opening k n)
    (passes : accepted arity coefficient indices outcome = true) :
    PackedSumcheckTerminalOracle.accepted arity coefficient indices (terminalView outcome) = true := by
  rcases outcome with ⟨earlier, later⟩
  cases earlier with
  | none => simp only [accepted, Bool.false_eq_true] at passes
  | some entry =>
    cases later with
    | none => simp only [accepted, Bool.false_eq_true] at passes
    | some proposal =>
      rcases proposal with ⟨⟨values, _memory⟩, opening⟩
      cases opening with
      | none => simp only [accepted, Bool.false_eq_true] at passes
      | some opened => exact (Bool.and_eq_true_iff.mp passes).2

/-- The same sources occur in the arithmetic subclaim and the actual accepted
wrong-opening event. No commitment-security certificate is supplied. -/
theorem accepted_implies_truthful_or_wrong (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor n k) (outcome : Outcome F Factor Memory Opening k n)
    (passes : accepted arity coefficient indices outcome = true) :
    PackedSumcheckOracle.TruthfulResult arity coefficient indices tables outcome.1 ∨
      WrongAcceptedFactor arity coefficient indices tables outcome := by
  obtain truthful | wrong := PackedSumcheckTerminalOracle.accepted_implies_truthful_or_wrong
    arity coefficient indices tables (terminalView outcome)
      (accepted_terminalView arity coefficient indices outcome passes)
  · exact Or.inl truthful
  · exact Or.inr ⟨passes, wrong⟩

/-- Values are checked before the binding callback and before the first opening.
The callbacks are actual shared-oracle programs, not discarded prover tapes. -/
def finish (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (openOne : Subclaim F k n → (Factor → Fin k → F) → Factor → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult Opening Memory))
    (factors : List Factor) : Option (Subclaim F k n × Memory) →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
        (Option (((Factor → Fin k → F) × Memory) × Option (ShortCircuitSequence.Outcome Factor Opening Memory)))
  | none => pure none
  | some entry => do
      let proposal ← receiveValues entry.1 entry.2
      if PackedSumcheckTerminalOracle.check arity coefficient indices proposal.1 entry.1.expected then
        let memory ← bindValues entry.1 proposal.1 proposal.2
        let opened ← ShortCircuitSequence.program (openOne entry.1 proposal.1) factors memory
        pure (some ((proposal.1, opened.memory), some opened))
      else pure (some (proposal, none))

variable [SampleableType (Fin k → F)]

def program (nodes : PackedSumcheckRound.Node k ↪ F) (interpret : Message → Polynomial F)
    (send : ℕ → Memory → (Fin k → F) →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message × Memory))
    (afterChallenge : Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (openOne : Subclaim F k n → (Factor → Fin k → F) → Factor → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult Opening Memory))
    (factors : List Factor) (claimed : Fin k → F) (memory : Memory) :
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Outcome F Factor Memory Opening k n) :=
  SharedContinuation.program (PackedSumcheckOracle.program nodes interpret send afterChallenge n claimed memory)
    (finish arity coefficient indices receiveValues bindValues openOne factors)

variable [Fintype F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- False-sum acceptance is bounded on this exact guarded execution. The
residual event requires successful terminal checking and successful openings. -/
theorem false_sum_acceptance_bound
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (interpret : Message → Polynomial F) (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (messageDegree : ∀ message, (interpret message).natDegree ≤ (2 * k - 1) * productDegree)
    (send : ℕ → Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message × Memory))
    (afterChallenge : Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F) (memory : Memory)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (openOne : Subclaim F k n → (Factor → Fin k → F) → Factor → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult Opening Memory))
    (factors : List Factor)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes interpret send afterChallenge arity coefficient indices receiveValues bindValues openOne factors claimed memory)).run state}[
        accepted arity coefficient indices result.1 = true] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) +
      Pr{let result ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program nodes interpret send afterChallenge arity coefficient indices receiveValues bindValues openOne factors claimed memory)).run state}[
          WrongAcceptedFactor arity coefficient indices tables result.1] := by
  apply le_trans (prEvent_mono _ _ (fun result =>
    PackedSumcheckOracle.TruthfulResult arity coefficient indices tables result.1.1 ∨
      WrongAcceptedFactor arity coefficient indices tables result.1) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add
      (PackedSumcheckSharedSoundness.continued_soundness_bound enc dummy shape nodes arity coefficient indices
        interpret productDegree bounded messageDegree send afterChallenge n tables claimed memory _ state falseClaim) le_rfl)
  · intro result passes
    exact accepted_implies_truthful_or_wrong arity coefficient indices tables result.1 passes

/-- Native evaluation-vector messages supply their proved degree bound. The
terminal gate and early-return hash schedule are unchanged. -/
theorem native_false_sum_acceptance_bound
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (bounded : ∀ term, arity term ≤ productDegree)
    (send : ℕ → Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) ((Fin ((2 * k - 1) * productDegree + 1) → F) × Memory))
    (afterChallenge : Memory → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F) (memory : Memory)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (openOne : Subclaim F k n → (Factor → Fin k → F) → Factor → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult Opening Memory))
    (factors : List Factor)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program (NativePackedInterpolation.nodes p (enough.trans small))
          (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small)) send afterChallenge arity coefficient indices receiveValues bindValues openOne factors claimed memory)).run state}[
        accepted arity coefficient indices result.1 = true] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) +
      Pr{let result ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program (NativePackedInterpolation.nodes p (enough.trans small))
          (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small)) send afterChallenge arity coefficient indices receiveValues bindValues openOne factors claimed memory)).run state}[
          WrongAcceptedFactor arity coefficient indices tables result.1] :=
  false_sum_acceptance_bound enc dummy shape _ arity coefficient indices _ productDegree bounded
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) send afterChallenge tables claimed memory
      receiveValues bindValues openOne factors state falseClaim

end

end FormalProof4FHE.HasteBoots.GuardedSumcheckTerminal
