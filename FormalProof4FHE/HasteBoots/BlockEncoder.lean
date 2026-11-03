module

public import FormalProof4FHE.HasteBoots.BlockCode

@[expose] public section

/-!
# Coordinate polynomial encoding

The input is coefficient-block-major, coordinate-minor, as in the Rust row
encoder. This is direct polynomial evaluation; equality with the bit-reversed
negacyclic NTT implementation remains a separate refinement obligation.
-/

open scoped BigOperators
open Polynomial

namespace FormalProof4FHE.HasteBoots.BlockEncoder

variable {F Position : Type*} [Field F] {m b : ℕ}

/-- The polynomial for one symbol coordinate. -/
noncomputable def polynomial (input : Fin m → Fin b → F) (lane : Fin b) : F[X] :=
  ∑ j : Fin m, C (input j lane) * X ^ (j : ℕ)

/-- Direct encoder with the same coordinate layout as `encode_row`. -/
def encode (domain : Position → F) (input : Fin m → Fin b → F) :
    Position → Fin b → F :=
  fun pos lane => ∑ j : Fin m, input j lane * domain pos ^ (j : ℕ)

theorem degree_polynomial_lt (input : Fin m → Fin b → F) (lane : Fin b) :
    (polynomial input lane).degree < m :=
  Polynomial.degree_sum_fin_lt _

theorem encode_eq_eval (domain : Position → F) (input : Fin m → Fin b → F)
    (pos : Position) (lane : Fin b) :
    encode domain input pos lane = (polynomial input lane).eval (domain pos) := by
  simp [encode, polynomial, Polynomial.eval_finsetSum]

theorem coeff_polynomial (input : Fin m → Fin b → F) (lane : Fin b) (j : Fin m) :
    (polynomial input lane).coeff (j : ℕ) = input j lane := by
  classical
  simp [polynomial, Polynomial.finsetSum_coeff, Fin.val_inj]

/-- Distinct coefficient tables cannot have the same word on a sufficiently large domain. -/
theorem encode_injective [Fintype Position] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) :
    Function.Injective (encode domain : (Fin m → Fin b → F) → Position → Fin b → F) := by
  intro input other heq
  funext j lane
  have hm : 0 < m := Nat.zero_lt_of_lt j.isLt
  have bound (t : Fin m → Fin b → F) : (polynomial t lane).natDegree < m := by
    by_cases h : polynomial t lane = 0
    · simpa [h] using hm
    · exact (Polynomial.natDegree_lt_iff_degree_lt h).2 (degree_polynomial_lt t lane)
  have hp : polynomial input lane = polynomial other lane :=
    Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ domain.injective
      (fun pos => by
        rw [← encode_eq_eval, ← encode_eq_eval]
        exact congrFun (congrFun heq pos) lane)
      ((max_lt_iff.mpr ⟨bound input, bound other⟩).trans_le enough)
  have hc := congrArg (fun p : F[X] => p.coeff (j : ℕ)) hp
  simpa only [coeff_polynomial] using hc

/-- The semantic row encoder lands in precisely the code whose distance was proved. -/
theorem encode_mem_code [Fintype Position] [NeZero b]
    (domain : Position ↪ F) (input : Fin m → Fin b → F) :
    encode domain input ∈ BlockCode.code domain m b := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  change ∀ lane : Fin b, (fun pos => encode domain input pos lane) ∈
    ReedSolomon.code domain ((b * m) / b)
  rw [Nat.mul_div_right _ hb]
  intro lane
  exact ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    (polynomial input lane) (degree_polynomial_lt input lane)
    (fun pos => encode_eq_eval domain input pos lane)

/-- Encoding is base-linear, including the actual order of the symbol coordinates. -/
theorem encode_add (domain : Position → F) (input other : Fin m → Fin b → F) :
    encode domain (input + other) = encode domain input + encode domain other := by
  classical
  ext pos lane
  simp [encode, add_mul, Finset.sum_add_distrib]

theorem encode_smul (domain : Position → F) (a : F) (input : Fin m → Fin b → F) :
    encode domain (a • input) = a • encode domain input := by
  classical
  ext pos lane
  simp [encode, mul_assoc, Finset.mul_sum]

end FormalProof4FHE.HasteBoots.BlockEncoder
