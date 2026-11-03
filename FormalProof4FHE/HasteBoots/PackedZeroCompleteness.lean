module

public import FormalProof4FHE.HasteBoots.PackedSumcheckCompleteness

@[expose] public section

/-!
# Honest packed ZeroCheck in the existing composed verifier experiment

The first message contains the real equality-weighted polynomials. A valid
source relation makes every boundary entry zero. After the first challenge the
honest state stores exactly the once-folded original factors and public EQ
source; its remaining rounds use the stored-table sumcheck prover. All
supported executions accept, and native evaluation-vector encodings give
probability-one completeness without an assumed message codec certificate.
The truthful terminal factor obligation, production transcript, native prover
optimization and Rust refinement remain separate composition obligations.
-/

namespace FormalProof4FHE.HasteBoots.PackedZeroCompleteness

noncomputable section

variable {F Factor Term FirstMessage RoundMessage : Type}
  [Field F] [DecidableEq F] [Fintype Term] {n k : ℕ}
  [SampleableType (Fin k → F)] [SampleableType (PackedZeroReduction.Points F n k)]
  [SampleableType (Fin k → Fin k → F)]

def firstMessage (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (encode : Polynomial F → FirstMessage) (points : PackedZeroReduction.Points F n k) : Fin k → FirstMessage :=
  fun point => encode (PackedZeroCube.firstPolynomials nodes arity coefficient indices tables points point)

def firstRespond (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (encode : Polynomial F → FirstMessage) (points : PackedZeroReduction.Points F n k) :
    ProbComp ((Fin k → FirstMessage) × PackedSumcheckCompleteness.State F (Factor ⊕ Unit) k) :=
  pure (firstMessage nodes arity coefficient indices tables encode points, ⟨0, fun _ _ _ => 0⟩)

def afterFirst (nodes : PackedSumcheckRound.Node k ↪ F)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (points : PackedZeroReduction.Points F n k)
    (_packet : (Fin k → FirstMessage) × PackedSumcheckCompleteness.State F (Factor ⊕ Unit) k)
    (coins : PackedZeroReduction.Coins F k) : ProbComp (PackedSumcheckCompleteness.State F (Factor ⊕ Unit) k) :=
  pure ⟨n, PackedZeroCube.reducedTables nodes tables points coins⟩

omit [DecidableEq F] [SampleableType (Fin k → F)]
  [SampleableType (PackedZeroReduction.Points F n k)] [SampleableType (Fin k → Fin k → F)] in
/-- The first encoded polynomial family is exactly the one used by the
special-round source identity, for every possible equality-point vector. -/
theorem first_decoded (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (encode : Polynomial F → FirstMessage) (interpret : FirstMessage → Polynomial F)
    (codec : ∀ polynomial, polynomial.natDegree ≤ (2 * k - 1) * productDegree →
      interpret (encode polynomial) = polynomial)
    (points : PackedZeroReduction.Points F n k) :
    (fun point => interpret (firstMessage nodes arity coefficient indices tables encode points point)) =
      PackedZeroCube.firstPolynomials nodes arity coefficient indices tables points := by
  funext point
  exact codec _ (PackedZeroFirst.polynomial_degree nodes arity coefficient indices
    (fun factor bit suffix lane => tables factor (bit, suffix) lane)
    (fun point => PackedEqualityCube.weight (points point)) productDegree bounded point)

omit [SampleableType (Fin k → F)] [SampleableType (PackedZeroReduction.Points F n k)]
  [SampleableType (Fin k → Fin k → F)] in
/-- Every honestly generated native first message passes the actual Boolean
boundary loop, for every equality-point vector of a valid source. -/
theorem native_first_check (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (bounded : ∀ term, arity term ≤ productDegree)
    (zero : PackedZeroCube.Vanishes arity coefficient indices tables)
    (points : PackedZeroReduction.Points F n k) :
    NativePackedZeroFirst.checkFirst enough
      (firstMessage (NativePackedInterpolation.nodes p (enough.trans small)) arity coefficient indices tables
        (PackedHonestMessages.encode (NativePackedInterpolation.consecutive p small)) points) = true := by
  rw [NativePackedZeroFirst.checkFirst_boundary_iff p small enough,
    first_decoded _ arity coefficient indices tables productDegree bounded _ _
      (PackedHonestMessages.decode_encode _)]
  exact PackedZeroFirst.boundary_of_vanishes _ arity coefficient indices
    (fun factor bit suffix lane => tables factor (bit, suffix) lane)
    (fun point => PackedEqualityCube.weight (points point)) (fun bit suffix lane => zero (bit, suffix) lane)

/-- Concrete honest messages and state transitions have no rejecting
supported run for a source satisfying every original zero constraint. -/
theorem supported_accepts (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (encodeFirst : Polynomial F → FirstMessage) (interpretFirst : FirstMessage → Polynomial F)
    (encodeRound : Polynomial F → RoundMessage) (interpretRound : RoundMessage → Polynomial F)
    (firstCodec : ∀ polynomial, polynomial.natDegree ≤ (2 * k - 1) * productDegree →
      interpretFirst (encodeFirst polynomial) = polynomial)
    (roundCodec : ∀ polynomial, polynomial.natDegree ≤ (2 * k - 1) * (productDegree + 1) →
      interpretRound (encodeRound polynomial) = polynomial)
    (zero : PackedZeroCube.Vanishes arity coefficient indices tables) (accepted : Bool)
    (supported : accepted ∈ support (PackedZeroExecution.run nodes arity coefficient indices tables
      (fun message point => interpretFirst (message point)) interpretRound
      (firstRespond nodes arity coefficient indices tables encodeFirst) (afterFirst nodes tables)
      (PackedSumcheckCompleteness.send nodes (fun term => arity term + 1) coefficient
        (PackedZeroFirst.reducedIndices arity indices) encodeRound)
      (PackedSumcheckCompleteness.afterChallenge nodes))) : accepted = true := by
  classical
  simp only [PackedZeroExecution.run, PackedZeroReduction.experiment, firstRespond, pure_bind, bind_assoc] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨points, _, supported⟩ := supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨coins, _, supported⟩ := supported
  rw [first_decoded nodes arity coefficient indices tables productDegree bounded encodeFirst interpretFirst firstCodec] at supported
  have boundary : PackedZeroFirst.Boundary nodes
      (PackedZeroCube.firstPolynomials nodes arity coefficient indices tables points) :=
    PackedZeroFirst.boundary_of_vanishes nodes arity coefficient indices
      (fun factor bit suffix lane => tables factor (bit, suffix) lane)
      (fun point => PackedEqualityCube.weight (points point)) (fun bit suffix lane => zero (bit, suffix) lane)
  simp only [boundary, reduceIte, afterFirst, pure_bind] at supported
  apply PackedSumcheckCompleteness.supported_accepts nodes (fun term => arity term + 1) coefficient
    (PackedZeroFirst.reducedIndices arity indices) (productDegree + 1)
    (fun term => Nat.add_le_add_right (bounded term) 1) encodeRound interpretRound roundCodec
    n (PackedZeroCube.reducedTables nodes tables points coins) _ ?_ accepted supported
  exact (PackedZeroCube.reducedSum_eq nodes arity coefficient indices tables points coins).symm

/-- Perfect completeness of the same composed ZeroCheck verifier used by the
soundness theorem, with the explicit stored-source honest prover. -/
theorem probability_one (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (encodeFirst : Polynomial F → FirstMessage) (interpretFirst : FirstMessage → Polynomial F)
    (encodeRound : Polynomial F → RoundMessage) (interpretRound : RoundMessage → Polynomial F)
    (firstCodec : ∀ polynomial, polynomial.natDegree ≤ (2 * k - 1) * productDegree →
      interpretFirst (encodeFirst polynomial) = polynomial)
    (roundCodec : ∀ polynomial, polynomial.natDegree ≤ (2 * k - 1) * (productDegree + 1) →
      interpretRound (encodeRound polynomial) = polynomial)
    (zero : PackedZeroCube.Vanishes arity coefficient indices tables) :
    Pr{let accepted ← (PackedZeroExecution.run nodes arity coefficient indices tables
      (fun message point => interpretFirst (message point)) interpretRound
      (firstRespond nodes arity coefficient indices tables encodeFirst) (afterFirst nodes tables)
      (PackedSumcheckCompleteness.send nodes (fun term => arity term + 1) coefficient
        (PackedZeroFirst.reducedIndices arity indices) encodeRound)
      (PackedSumcheckCompleteness.afterChallenge nodes))}[accepted = true] = 1 :=
  (OracleComp.prEvent_eq_one_iff _ _).mpr (supported_accepts nodes arity coefficient indices tables productDegree bounded
    encodeFirst interpretFirst encodeRound interpretRound firstCodec roundCodec zero)

/-- Native evaluation vectors provide both honest codecs by the proved
degree-bounded interpolation identity. -/
theorem native_probability_one (p : ℕ) [CharP F p] (productDegree : ℕ)
    (firstSmall : (2 * k - 1) * productDegree + 1 ≤ p)
    (roundSmall : (2 * k - 1) * (productDegree + 1) + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (bounded : ∀ term, arity term ≤ productDegree)
    (zero : PackedZeroCube.Vanishes arity coefficient indices tables) :
    Pr{let accepted ← (PackedZeroExecution.run (NativePackedInterpolation.nodes p (enough.trans firstSmall))
      arity coefficient indices tables
      (fun message point => NativePackedInterpolation.messagePolynomial
        (NativePackedInterpolation.consecutive p firstSmall) (message point))
      (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p roundSmall))
      (firstRespond (NativePackedInterpolation.nodes p (enough.trans firstSmall)) arity coefficient indices tables
        (PackedHonestMessages.encode (NativePackedInterpolation.consecutive p firstSmall)))
      (afterFirst (NativePackedInterpolation.nodes p (enough.trans firstSmall)) tables)
      (PackedSumcheckCompleteness.send (NativePackedInterpolation.nodes p (enough.trans firstSmall))
        (fun term => arity term + 1) coefficient (PackedZeroFirst.reducedIndices arity indices)
        (PackedHonestMessages.encode (NativePackedInterpolation.consecutive p roundSmall)))
      (PackedSumcheckCompleteness.afterChallenge (NativePackedInterpolation.nodes p (enough.trans firstSmall))))}[
      accepted = true] = 1 :=
  probability_one _ arity coefficient indices tables productDegree bounded _ _ _ _
    (PackedHonestMessages.decode_encode _) (PackedHonestMessages.decode_encode _) zero

end

end FormalProof4FHE.HasteBoots.PackedZeroCompleteness
