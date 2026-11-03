module

public import FormalProof4FHE.HasteBoots.PackedZeroExecution

@[expose] public section

/-!
# Honest native evaluation messages recover their polynomial meanings

The prover sends evaluations at D+1 distinct consecutive field nodes. Decoding
recovers every polynomial of degree at most D exactly. This supplies the honest
encoding side of the same message interpretation used by soundness; it does
not assume an interpolation or commitment correctness certificate.
The optimized Rust interpolation and forward-difference implementation remain
separate refinement obligations.
-/

namespace FormalProof4FHE.HasteBoots.PackedHonestMessages

noncomputable section

variable {F : Type} [Field F] {degree : ℕ}

def encode (points : Fin (degree + 1) ↪ F) (polynomial : Polynomial F) : Fin (degree + 1) → F :=
  fun index => polynomial.eval (points index)

/-- Encoding followed by the verifier's interpolation is the identity on its
validated degree space, including constant and zero polynomials. -/
theorem decode_encode (points : Fin (degree + 1) ↪ F) (polynomial : Polynomial F)
    (bounded : polynomial.natDegree ≤ degree) :
    NativePackedInterpolation.messagePolynomial points (encode points polynomial) = polynomial := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ polynomial points.injective
  · intro index
    exact NativePackedInterpolation.messagePolynomial_node points (encode points polynomial) index
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le
      (max_le (NativePackedInterpolation.messagePolynomial_degree points _) bounded)

/-- Consecutive native nodes satisfy the codec theorem under the same
characteristic check already used for message soundness. -/
theorem native_decode_encode (p : ℕ) [CharP F p] (small : degree + 1 ≤ p)
    (polynomial : Polynomial F) (bounded : polynomial.natDegree ≤ degree) :
    NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive p small)
      (encode (NativePackedInterpolation.consecutive p small) polynomial) = polynomial :=
  decode_encode _ polynomial bounded

end

end FormalProof4FHE.HasteBoots.PackedHonestMessages
