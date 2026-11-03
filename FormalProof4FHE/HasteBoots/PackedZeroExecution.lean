module

public import FormalProof4FHE.HasteBoots.PackedZeroTerminal

@[expose] public section

/-!
# Composed private-coin packed ZeroCheck soundness

The special first round and all remaining packed-sumcheck rounds operate on
one fixed original source, with its once-folded original factors and appended
mixed EQ source. Arbitrary probabilistic prover state may follow the first
challenge and every later challenge. Acceptance here discharges the truthful
terminal factor obligation. `PackedZeroTerminal` identifies that obligation
with the native original-factor/public-EQ check when those factors are correct.

This is an interactive mathematical experiment. Actual shared-oracle scheduling,
authenticated factor values, transcript sampling and Rust refinement remain
open. Sampling unused private coins on rejected paths is allowed here; no
physical-cost equivalence is claimed.
-/

namespace FormalProof4FHE.HasteBoots.PackedZeroExecution

noncomputable section

variable {F Factor Term FirstMessage RoundMessage ProverState : Type}
  [Field F] [Fintype F] [DecidableEq F] [Fintype Term] {n k : ℕ}
  [SampleableType F] [SampleableType (Fin k → F)] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n k)] [SampleableType (Fin k → Fin k → F)]
  [SampleableType (Fin k → ((Fin k → F) × F))]

def run (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (interpretFirst : FirstMessage → Fin k → Polynomial F) (interpretRound : RoundMessage → Polynomial F)
    (firstRespond : PackedZeroReduction.Points F n k → ProbComp (FirstMessage × ProverState))
    (afterFirst : PackedZeroReduction.Points F n k → FirstMessage × ProverState →
      PackedZeroReduction.Coins F k → ProbComp ProverState)
    (send : ℕ → ProverState → (Fin k → F) → ProbComp (RoundMessage × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → ProbComp ProverState) : ProbComp Bool := by
  classical
  exact do
    let outcome ← PackedZeroReduction.experiment firstRespond
    if PackedZeroFirst.Boundary nodes (interpretFirst outcome.1.2.1) then
      let state ← afterFirst outcome.1.1 outcome.1.2 outcome.2
      PackedSumcheckExecution.run nodes (fun term => arity term + 1) coefficient
        (PackedZeroFirst.reducedIndices arity indices) interpretRound send afterChallenge n
        (PackedZeroCube.reducedTables nodes tables outcome.1.1 outcome.2)
        (PackedZeroFirst.reduce (interpretFirst outcome.1.2.1) outcome.2.1 outcome.2.2) state
    else pure false

/-- A false relation over n+1 Boolean variables has the special-round error
plus n ordinary packed-round errors, with exactly the native increased arity. -/
theorem soundness_bound (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (interpretFirst : FirstMessage → Fin k → Polynomial F) (interpretRound : RoundMessage → Polynomial F)
    (firstDegree : ∀ message point, (interpretFirst message point).natDegree ≤ (2 * k - 1) * productDegree)
    (roundDegree : ∀ message, (interpretRound message).natDegree ≤ (2 * k - 1) * (productDegree + 1))
    (firstRespond : PackedZeroReduction.Points F n k → ProbComp (FirstMessage × ProverState))
    (afterFirst : PackedZeroReduction.Points F n k → FirstMessage × ProverState →
      PackedZeroReduction.Coins F k → ProbComp ProverState)
    (send : ℕ → ProverState → (Fin k → F) → ProbComp (RoundMessage × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → ProbComp ProverState)
    (falseRelation : ¬PackedZeroCube.Vanishes arity coefficient indices tables) :
    Pr{let accepted ← (run nodes arity coefficient indices tables interpretFirst interpretRound
      firstRespond afterFirst send afterChallenge)}[accepted = true] ≤
      ((((n : ENNReal) / Fintype.card F) ^ k) +
        ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k))) +
      (n : ENNReal) *
        ((((((2 * k - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
  classical
  let healed := fun outcome :
      (PackedZeroReduction.Points F n k × (FirstMessage × ProverState)) × PackedZeroReduction.Coins F k =>
    PackedZeroFirst.Boundary nodes (interpretFirst outcome.1.2.1) ∧
      PackedZeroFirst.reduce (interpretFirst outcome.1.2.1) outcome.2.1 outcome.2.2 =
        PackedSumcheckExecution.sum (fun term => arity term + 1) coefficient
          (PackedZeroFirst.reducedIndices arity indices) (PackedZeroCube.reducedTables nodes tables outcome.1.1 outcome.2)
  have firstBound := PackedZeroCube.healing_bound nodes arity coefficient indices tables productDegree bounded
    firstRespond (fun response => interpretFirst response.1) (fun response => firstDegree response.1) falseRelation
  unfold run
  apply le_trans (prEvent_bind_le_prEvent_add (PackedZeroReduction.experiment firstRespond) _ healed _ ?_)
  · exact add_le_add firstBound le_rfl
  · intro outcome outside
    by_cases checked : PackedZeroFirst.Boundary nodes (interpretFirst outcome.1.2.1)
    · simp only [checked, reduceIte]
      apply prEvent_bind_le_of_forall_le
      intro state
      apply PackedSumcheckExecution.soundness_bound nodes (fun term => arity term + 1) coefficient
        (PackedZeroFirst.reducedIndices arity indices) interpretRound (productDegree + 1)
        (fun term => Nat.add_le_add_right (bounded term) 1) roundDegree send afterChallenge
      intro equal
      exact outside ⟨checked, equal⟩
    · simp only [checked, prEvent_pure, Bool.false_eq_true, ite_false, zero_le]

/-- Native first and ordinary evaluation vectors supply both degree bounds
automatically; neither is an adversarial security certificate. -/
theorem native_soundness_bound (p : ℕ) [CharP F p] (productDegree : ℕ)
    (firstSmall : (2 * k - 1) * productDegree + 1 ≤ p)
    (roundSmall : (2 * k - 1) * (productDegree + 1) + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (bounded : ∀ term, arity term ≤ productDegree)
    (firstRespond : PackedZeroReduction.Points F n k →
      ProbComp ((Fin k → Fin ((2 * k - 1) * productDegree + 1) → F) × ProverState))
    (afterFirst : PackedZeroReduction.Points F n k →
      (Fin k → Fin ((2 * k - 1) * productDegree + 1) → F) × ProverState →
        PackedZeroReduction.Coins F k → ProbComp ProverState)
    (send : ℕ → ProverState → (Fin k → F) →
      ProbComp ((Fin ((2 * k - 1) * (productDegree + 1) + 1) → F) × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → ProbComp ProverState)
    (falseRelation : ¬PackedZeroCube.Vanishes arity coefficient indices tables) :
    Pr{let accepted ← (run (NativePackedInterpolation.nodes p (enough.trans firstSmall)) arity coefficient indices tables
      (fun message point => NativePackedInterpolation.messagePolynomial
        (NativePackedInterpolation.consecutive p firstSmall) (message point))
      (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p roundSmall))
      firstRespond afterFirst send afterChallenge)}[accepted = true] ≤
      ((((n : ENNReal) / Fintype.card F) ^ k) +
        ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k))) +
      (n : ENNReal) *
        ((((((2 * k - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ k)) :=
  soundness_bound (NativePackedInterpolation.nodes p (enough.trans firstSmall)) arity coefficient indices tables
    productDegree bounded _ _ (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
      (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) firstRespond afterFirst send afterChallenge falseRelation

end

end FormalProof4FHE.HasteBoots.PackedZeroExecution
