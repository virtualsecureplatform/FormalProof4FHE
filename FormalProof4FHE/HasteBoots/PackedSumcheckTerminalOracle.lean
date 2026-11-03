module

public import FormalProof4FHE.HasteBoots.PackedSumcheckSharedSoundness

@[expose] public section

/-!
# Terminal factor openings after the shared-oracle sumcheck verifier

The opener receives the returned matrix subclaim and uses the same cache and
logs. It returns no values on rejection. The native typed terminal expression
then compares the supplied factor vectors with the subclaim's expected value.
False-sum acceptance implies the earlier arithmetic event or an incorrectly
opened factor on this exact complete execution. The remaining opening-error
probability is explicit: no PCS security certificate is assumed or set to zero.
Its cryptographic bound, production Fiat--Shamir and Rust refinement remain open.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.PackedSumcheckTerminalOracle

noncomputable section

variable {F Factor Term Message ProverState Cfg Input Digest Payload : Type}
  [Field F] [DecidableEq F] [Fintype Term] {k n : ℕ}

abbrev Outcome (F Factor ProverState : Type) (k n : ℕ) :=
  Option (Subclaim F k n × ProverState) × Option (Factor → Fin k → F)

def check (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (values : Factor → Fin k → F) (expected : Fin k → F) : Bool :=
  (List.ofFn fun lane : Fin k => decide
    (PackedSumcheckRound.expression arity coefficient indices (fun factor => values factor lane) = expected lane)).all id

theorem check_iff (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (values : Factor → Fin k → F) (expected : Fin k → F) :
    check arity coefficient indices values expected = true ↔
      ∀ lane, PackedSumcheckRound.expression arity coefficient indices (fun factor => values factor lane) = expected lane := by
  simp [check, List.mem_ofFn, List.all_eq_true]

def accepted (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) : Outcome F Factor ProverState k n → Bool
  | (some entry, some values) => check arity coefficient indices values entry.1.expected
  | _ => false

def WrongFactor (tables : PackedSumcheckExecution.Tables F Factor n k)
    (outcome : Outcome F Factor ProverState k n) : Prop :=
  ∃ entry values, outcome = (some entry, some values) ∧
    ∃ factor, values factor ≠ entry.1.query.fold (tables factor)

/-- Every accepting terminal check is either a truthful returned subclaim or
has at least one factor vector differing from that same source's query fold. -/
theorem accepted_implies_truthful_or_wrong (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor n k) (outcome : Outcome F Factor ProverState k n)
    (passes : accepted arity coefficient indices outcome = true) :
    PackedSumcheckOracle.TruthfulResult arity coefficient indices tables outcome.1 ∨ WrongFactor tables outcome := by
  classical
  by_cases wrong : WrongFactor tables outcome
  · exact Or.inr wrong
  left
  rcases outcome with ⟨earlier, later⟩
  cases earlier with
  | none => simp only [accepted, Bool.false_eq_true] at passes
  | some entry =>
    cases later with
    | none => simp only [accepted, Bool.false_eq_true] at passes
    | some values =>
      have correct : values = fun factor => entry.1.query.fold (tables factor) := by
        funext factor
        by_contra different
        exact wrong ⟨entry, values, rfl, factor, different⟩
      have checked := (check_iff arity coefficient indices values entry.1.expected).mp passes
      rw [correct] at checked
      exact funext (fun lane => (checked lane).symm)

variable [SampleableType (Fin k → F)]

/-- Both phases are source-independent operational code; failed sumchecks do
not invoke an opener, and failed openings retain their actual final hash state. -/
def program (nodes : PackedSumcheckRound.Node k ↪ F) (interpret : Message → Polynomial F)
    (send : ℕ → ProverState → (Fin k → F) →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) ProverState)
    (n : ℕ) (claimed : Fin k → F) (privateState : ProverState)
    (openFactors : Subclaim F k n → ProverState →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Factor → Fin k → F))) :
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Outcome F Factor ProverState k n) :=
  SharedContinuation.program (PackedSumcheckOracle.program nodes interpret send afterChallenge n claimed privateState)
    (fun earlier => match earlier with | none => pure none | some entry => openFactors entry.1 entry.2)

section Runtime

variable [Fintype F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- The arithmetic loss and the actual joint wrong-opening event are bounded
on one complete execution, including every message, callback and opener call. -/
theorem false_sum_acceptance_bound
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (interpret : Message → Polynomial F) (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (messageDegree : ∀ message, (interpret message).natDegree ≤ (2 * k - 1) * productDegree)
    (send : ℕ → ProverState → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) ProverState)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F) (privateState : ProverState)
    (openFactors : Subclaim F k n → ProverState →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Factor → Fin k → F)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes interpret send afterChallenge n claimed privateState openFactors)).run state}[
        accepted arity coefficient indices result.1 = true] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) +
      Pr{let result ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program nodes interpret send afterChallenge n claimed privateState openFactors)).run state}[
          WrongFactor tables result.1] := by
  apply le_trans (prEvent_mono _ _ (fun result =>
    PackedSumcheckOracle.TruthfulResult arity coefficient indices tables result.1.1 ∨ WrongFactor tables result.1) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add
      (PackedSumcheckSharedSoundness.continued_soundness_bound enc dummy shape nodes arity coefficient indices
        interpret productDegree bounded messageDegree send afterChallenge n tables claimed privateState _ state falseClaim) le_rfl)
  · intro result passes
    exact accepted_implies_truthful_or_wrong arity coefficient indices tables result.1 passes

/-- Native messages discharge the round-degree premise while the genuine
joint wrong-opening probability remains visible on the complete shared run. -/
theorem native_false_sum_acceptance_bound
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) (bounded : ∀ term, arity term ≤ productDegree)
    (send : ℕ → ProverState → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Fin ((2 * k - 1) * productDegree + 1) → F) × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) ProverState)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F) (privateState : ProverState)
    (openFactors : Subclaim F k n → ProverState →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Factor → Fin k → F)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : claimed ≠ PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program (NativePackedInterpolation.nodes p (enough.trans small))
        (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small))
        send afterChallenge n claimed privateState openFactors)).run state}[
          accepted arity coefficient indices result.1 = true] ≤
      (n : ENNReal) * ((((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k)) +
      Pr{let result ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program (NativePackedInterpolation.nodes p (enough.trans small))
          (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small))
          send afterChallenge n claimed privateState openFactors)).run state}[WrongFactor tables result.1] :=
  false_sum_acceptance_bound enc dummy shape _ arity coefficient indices _ productDegree bounded
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) send afterChallenge n tables claimed privateState
      openFactors state falseClaim

end Runtime

end

end FormalProof4FHE.HasteBoots.PackedSumcheckTerminalOracle
