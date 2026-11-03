module

public import FormalProof4FHE.HasteBoots.NativePackedInterpolation

@[expose] public section

/-!
# Adaptive interactive packed-sumcheck composition

The prover chooses each message before that round's independent lane vector.
Arbitrary probabilistic state updates may follow the challenge, matching the
per-challenge callback schedule. At termination the factors are read from the
same repeatedly folded source tables. This ideal terminal obligation still
needs the authenticated-opening and full-stage adapters; no production
Fiat--Shamir or Rust refinement is asserted.
-/

open scoped BigOperators
open Polynomial

namespace FormalProof4FHE.HasteBoots.PackedSumcheckExecution

noncomputable section

variable {F Factor Term Message ProverState : Type} [Field F] [DecidableEq F] [Fintype F]
  [Fintype Term] {k : ℕ} [SampleableType (Fin k → F)]

abbrev Tables (F Factor : Type) (n k : ℕ) := Factor → MatrixFold.Cube n → Fin k → F

/-- The statement asserted by a sumcheck at its current Boolean dimension. -/
def sum (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) {n : ℕ}
    (tables : Tables F Factor n k) (lane : Fin k) : F :=
  ∑ cell, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables factor cell lane)

def roundPolynomial (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor) {n : ℕ}
    (tables : Tables F Factor (n + 1) k) : F[X] :=
  PackedSumcheckRound.polynomial nodes arity coefficient indices
    (fun factor bit suffix lane => tables factor (bit, suffix) lane)

def fold (nodes : PackedSumcheckRound.Node k ↪ F) {n : ℕ} (tables : Tables F Factor (n + 1) k)
    (challenge : Fin k → F) : Tables F Factor n k :=
  fun factor => MatrixFold.foldFirst (PackedSumcheckRound.challengePair nodes challenge) (tables factor)

omit [DecidableEq F] [Fintype F] [SampleableType (Fin k → F)] in
/-- The correct current sum is exactly what the honest round node checks test. -/
theorem roundPolynomial_check (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor) {n : ℕ}
    (tables : Tables F Factor (n + 1) k) :
    PackedSumcheckProbability.Checks nodes (sum arity coefficient indices tables)
      (roundPolynomial nodes arity coefficient indices tables) := by
  intro lane
  rw [roundPolynomial, PackedSumcheckRound.polynomial_check]
  change (∑ suffix : MatrixFold.Cube n,
    (PackedSumcheckRound.expression arity coefficient indices (fun factor => tables factor (false, suffix) lane) +
    PackedSumcheckRound.expression arity coefficient indices (fun factor => tables factor (true, suffix) lane))) =
      ∑ cell : Bool × MatrixFold.Cube n,
        PackedSumcheckRound.expression arity coefficient indices (fun factor => tables factor cell lane)
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib, add_comm]

omit [DecidableEq F] [Fintype F] [SampleableType (Fin k → F)] in
/-- The truthful next claim is the honest polynomial evaluated at the fresh
lane challenges, for the same source tables and matrix pair. -/
theorem sum_fold (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor) {n : ℕ}
    (tables : Tables F Factor (n + 1) k) (challenge : Fin k → F) (lane : Fin k) :
    sum arity coefficient indices (fold nodes tables challenge) lane =
      (roundPolynomial nodes arity coefficient indices tables).eval (challenge lane) := by
  exact (PackedSumcheckRound.polynomial_fold nodes arity coefficient indices
    (fun factor bit suffix inLane => tables factor (bit, suffix) inLane) challenge lane).symm

/-- Adaptive messages and callback state are unrestricted probabilistic
procedures; every verifier lane vector is sampled only after its message. -/
def run (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (interpret : Message → F[X])
    (send : ℕ → ProverState → (Fin k → F) → ProbComp (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → ProbComp ProverState) :
    (n : ℕ) → Tables F Factor n k → (Fin k → F) → ProverState → ProbComp Bool
  | 0, tables, claimed, _state => by
    classical
    exact pure (decide (claimed = sum arity coefficient indices tables))
  | n + 1, tables, claimed, state => by
    classical
    exact do
      let packet ← send (n + 1) state claimed
      if PackedSumcheckProbability.Checks nodes claimed (interpret packet.1) then
        let challenge ← $ᵗ (Fin k → F)
        let nextState ← afterChallenge packet.2 challenge
        run nodes arity coefficient indices interpret send afterChallenge n (fold nodes tables challenge)
          (fun lane => (interpret packet.1).eval (challenge lane)) nextState
      else pure false

/-- A false initial sum can pass n packed rounds and the truthful terminal
factor obligation with probability at most n*(D/card(F))^k. No finite prover
state, fixed response tape, independent callback, or losslessness is assumed. -/
theorem soundness_bound (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (interpret : Message → F[X]) (productDegree : ℕ)
    (bounded : ∀ term, arity term ≤ productDegree)
    (messageDegree : ∀ message, (interpret message).natDegree ≤ (2 * k - 1) * productDegree)
    (send : ℕ → ProverState → (Fin k → F) → ProbComp (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → ProbComp ProverState)
    (n : ℕ) (tables : Tables F Factor n k) (claimed : Fin k → F) (state : ProverState)
    (falseClaim : claimed ≠ sum arity coefficient indices tables) :
    Pr{let accepted ← run nodes arity coefficient indices interpret send afterChallenge n tables claimed state}[
      accepted = true] ≤ (n : ENNReal) *
        (((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k) := by
  classical
  induction n generalizing claimed state with
  | zero => simp only [run, falseClaim, decide_false, prEvent_pure, Bool.false_eq_true, ite_false, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    simp only [run]
    apply prEvent_bind_le_of_forall_le
    rintro ⟨message, privateState⟩
    by_cases checked : PackedSumcheckProbability.Checks nodes claimed (interpret message)
    · simp only [checked, reduceIte]
      let honest := roundPolynomial nodes arity coefficient indices tables
      let healed := fun challenge : Fin k → F =>
        ∀ lane, (interpret message).eval (challenge lane) = honest.eval (challenge lane)
      have different := PackedSumcheckProbability.checked_distinct nodes claimed
        (sum arity coefficient indices tables) (interpret message) honest falseClaim checked
          (roundPolynomial_check nodes arity coefficient indices tables)
      have roots := PackedSumcheckProbability.all_agree_bound (interpret message) honest
        ((2 * k - 1) * productDegree) k different (messageDegree message)
        (PackedSumcheckRound.polynomial_degree nodes arity coefficient indices
          (fun factor bit suffix lane => tables factor (bit, suffix) lane) productDegree bounded)
      have tailBound : ∀ challenge, ¬healed challenge →
          Pr{let accepted ← (do
            let nextState ← afterChallenge privateState challenge
            run nodes arity coefficient indices interpret send afterChallenge n (fold nodes tables challenge)
              (fun lane => (interpret message).eval (challenge lane)) nextState)}[accepted = true] ≤
            (n : ENNReal) *
              (((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k) := by
        intro challenge notHealed
        apply prEvent_bind_le_of_forall_le
        intro nextState
        apply ih
        intro equal
        apply notHealed
        intro lane
        exact (congrFun equal lane).trans (sum_fold nodes arity coefficient indices tables challenge lane)
      exact (prEvent_bind_le_prEvent_add ($ᵗ (Fin k → F)) _ healed _ tailBound).trans
        ((add_le_add roots le_rfl).trans_eq (by
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]))
    · simp only [checked, prEvent_pure, Bool.false_eq_true, ite_false, zero_le]

/-- Native evaluation-vector specialization: received messages automatically
have the validated round degree; their node checks are the array checks proved
by `NativePackedInterpolation.checks_iff`. -/
theorem native_soundness_bound (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (bounded : ∀ term, arity term ≤ productDegree)
    (send : ℕ → ProverState → (Fin k → F) →
      ProbComp ((Fin ((2 * k - 1) * productDegree + 1) → F) × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → ProbComp ProverState)
    (n : ℕ) (tables : Tables F Factor n k) (claimed : Fin k → F) (state : ProverState)
    (falseClaim : claimed ≠ sum arity coefficient indices tables) :
    Pr{let accepted ← (run (NativePackedInterpolation.nodes p (enough.trans small)) arity coefficient indices
      (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small))
      send afterChallenge n tables claimed state)}[accepted = true] ≤ (n : ENNReal) *
        (((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k) :=
  soundness_bound (NativePackedInterpolation.nodes p (enough.trans small)) arity coefficient indices
    _ productDegree bounded (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    send afterChallenge n tables claimed state falseClaim

end

end FormalProof4FHE.HasteBoots.PackedSumcheckExecution
