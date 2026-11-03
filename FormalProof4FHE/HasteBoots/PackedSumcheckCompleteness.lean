module

public import FormalProof4FHE.HasteBoots.PackedHonestMessages

@[expose] public section

/-!
# Honest packed sumcheck in the existing verifier experiment

The honest prover stores its remaining dimension and factor tables. Sending
encodes their actual round polynomial; after each challenge it folds exactly
those tables. Every supported run of `PackedSumcheckExecution.run` with this
prover accepts a correct sum, hence acceptance has probability one. The native
evaluation-vector specialization proves the codec premise from interpolation.
Cryptographic factor authentication and Rust implementation refinement remain
separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.PackedSumcheckCompleteness

noncomputable section

variable {F Factor Term Message : Type} [Field F] [DecidableEq F] [Fintype Term] {k : ℕ}
  [SampleableType (Fin k → F)]

abbrev State (F Factor : Type) (k : ℕ) := (n : ℕ) × PackedSumcheckExecution.Tables F Factor n k

/-- The honest sender uses its stored tables; zero-dimensional sends are
defined for totality and are never used by the zero-round verifier branch. -/
def send (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (encode : Polynomial F → Message) (_round : ℕ) (state : State F Factor k) (_claimed : Fin k → F) :
    ProbComp (Message × State F Factor k) :=
  match state with
  | ⟨0, _⟩ => pure (encode 0, state)
  | ⟨n + 1, tables⟩ => pure (encode (PackedSumcheckExecution.roundPolynomial (n := n) nodes arity coefficient indices tables), state)

def afterChallenge (nodes : PackedSumcheckRound.Node k ↪ F) (state : State F Factor k) (challenge : Fin k → F) :
    ProbComp (State F Factor k) :=
  match state with
  | ⟨0, _⟩ => pure state
  | ⟨n + 1, tables⟩ => pure ⟨n, PackedSumcheckExecution.fold nodes tables challenge⟩

omit [DecidableEq F] [SampleableType (Fin k → F)] in
/-- The literal native adjacent-entry round check accepts an honestly encoded
round, for every current source and not just with high probability. -/
theorem native_round_checks (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) (bounded : ∀ term, arity term ≤ productDegree)
    {n : ℕ} (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) :
    NativePackedInterpolation.Checks enough (PackedSumcheckExecution.sum arity coefficient indices tables)
      (PackedHonestMessages.encode (NativePackedInterpolation.consecutive p small)
        (PackedSumcheckExecution.roundPolynomial (NativePackedInterpolation.nodes p (enough.trans small))
          arity coefficient indices tables)) := by
  have decoded := PackedHonestMessages.decode_encode (NativePackedInterpolation.consecutive p small)
    (PackedSumcheckExecution.roundPolynomial (NativePackedInterpolation.nodes p (enough.trans small))
      arity coefficient indices tables)
    (PackedSumcheckRound.polynomial_degree (NativePackedInterpolation.nodes p (enough.trans small))
      arity coefficient indices (fun factor bit suffix lane => tables factor (bit, suffix) lane) productDegree bounded)
  rw [NativePackedInterpolation.checks_iff p small enough, decoded]
  exact PackedSumcheckExecution.roundPolynomial_check _ arity coefficient indices tables

/-- The stored-table prover has no rejecting supported execution when the
initial claim is the true sum of those same source tables. -/
theorem supported_accepts (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (encode : Polynomial F → Message) (interpret : Message → Polynomial F)
    (codec : ∀ polynomial, polynomial.natDegree ≤ (2 * k - 1) * productDegree →
      interpret (encode polynomial) = polynomial)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F)
    (truthful : claimed = PackedSumcheckExecution.sum arity coefficient indices tables)
    (accepted : Bool)
    (supported : accepted ∈ support (PackedSumcheckExecution.run nodes arity coefficient indices interpret
      (send nodes arity coefficient indices encode) (afterChallenge nodes) n tables claimed ⟨n, tables⟩)) :
    accepted = true := by
  classical
  induction n generalizing claimed with
  | zero =>
    simpa only [PackedSumcheckExecution.run, truthful, decide_true, mem_support_pure_iff] using supported
  | succ n ih =>
    have decoded := codec (PackedSumcheckExecution.roundPolynomial nodes arity coefficient indices tables)
      (PackedSumcheckRound.polynomial_degree nodes arity coefficient indices
        (fun factor bit suffix lane => tables factor (bit, suffix) lane) productDegree bounded)
    have checked : PackedSumcheckProbability.Checks nodes claimed
        (PackedSumcheckExecution.roundPolynomial nodes arity coefficient indices tables) := by
      rw [truthful]
      exact PackedSumcheckExecution.roundPolynomial_check nodes arity coefficient indices tables
    simp only [PackedSumcheckExecution.run, send, pure_bind, decoded, checked, reduceIte,
      afterChallenge] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨challenge, _, supported⟩ := supported
    apply ih (PackedSumcheckExecution.fold nodes tables challenge)
      (fun lane => (PackedSumcheckExecution.roundPolynomial nodes arity coefficient indices tables).eval (challenge lane))
      ?_ supported
    funext lane
    exact (PackedSumcheckExecution.sum_fold nodes arity coefficient indices tables challenge lane).symm

/-- Perfect completeness of the same typed verifier used by soundness, with
the concrete honest sender and challenge-dependent folded-table state. -/
theorem probability_one (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (encode : Polynomial F → Message) (interpret : Message → Polynomial F)
    (codec : ∀ polynomial, polynomial.natDegree ≤ (2 * k - 1) * productDegree →
      interpret (encode polynomial) = polynomial)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F)
    (truthful : claimed = PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let accepted ← (PackedSumcheckExecution.run nodes arity coefficient indices interpret
      (send nodes arity coefficient indices encode) (afterChallenge nodes) n tables claimed ⟨n, tables⟩)}[
      accepted = true] = 1 :=
  (OracleComp.prEvent_eq_one_iff _ _).mpr
    (supported_accepts nodes arity coefficient indices productDegree bounded encode interpret codec n tables claimed truthful)

/-- Native evaluation vectors instantiate the honest codec without any extra
interpolation premise. -/
theorem native_probability_one (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) (bounded : ∀ term, arity term ≤ productDegree)
    (n : ℕ) (tables : PackedSumcheckExecution.Tables F Factor n k) (claimed : Fin k → F)
    (truthful : claimed = PackedSumcheckExecution.sum arity coefficient indices tables) :
    Pr{let accepted ← (PackedSumcheckExecution.run (NativePackedInterpolation.nodes p (enough.trans small))
      arity coefficient indices (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small))
      (send (NativePackedInterpolation.nodes p (enough.trans small)) arity coefficient indices
        (PackedHonestMessages.encode (NativePackedInterpolation.consecutive p small)))
      (afterChallenge (NativePackedInterpolation.nodes p (enough.trans small))) n tables claimed ⟨n, tables⟩)}[
      accepted = true] = 1 :=
  probability_one _ arity coefficient indices productDegree bounded _ _
    (PackedHonestMessages.decode_encode _) n tables claimed truthful

end

end FormalProof4FHE.HasteBoots.PackedSumcheckCompleteness
