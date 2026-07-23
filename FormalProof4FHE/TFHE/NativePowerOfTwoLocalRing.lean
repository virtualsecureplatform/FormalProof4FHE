/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalDeterminantObstruction
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Local-Ring Foundation for Native Power-of-Two Negacyclic Rings

This file isolates the algebraic lift behind the rectangular binary rank argument.  First, any
ring map to `ZMod 2` whose kernel consists of nilpotent elements reflects units.  Second, for the
binary negacyclic ring of degree `2^d`, parity evaluation has nilpotent kernel: over characteristic
two the defining modulus is `(X - 1)^(2^d)`.  Finally, coefficient reduction from `ZMod (2^k)`
has nilpotent kernel for `k > 0`; composing the two arguments proves that parity evaluation on the
production ring `ZMod (2^k)[X]/(X^(2^d) + 1)` reflects units.
-/

namespace FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing

noncomputable section

open Polynomial
open FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

/-- A map to the binary field reflects units whenever every element of its kernel is nilpotent. -/
theorem isLocalHom_toZModTwo_of_nilpotent_kernel
    {R : Type} [CommRing R] (hom : R →+* ZMod 2)
    (kernel_nilpotent : ∀ value : R, hom value = 0 → IsNilpotent value) :
    IsLocalHom hom := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  intro value mapped_unit
  have mapped_ne_zero : hom value ≠ 0 :=
    isUnit_iff_ne_zero.mp mapped_unit
  have mapped_eq_one : hom value = 1 := by
    have fermat := ZMod.pow_card_sub_one_eq_one mapped_ne_zero
    simpa using fermat
  have difference_nilpotent : IsNilpotent (1 - value) := by
    apply kernel_nilpotent
    rw [map_sub, map_one, mapped_eq_one, sub_self]
  have lifted_unit := difference_nilpotent.isUnit_one_sub
  convert lifted_unit using 1
  ring

/-- In characteristic two, the degree-`2^d` negacyclic modulus is a pure power of `X - 1`. -/
theorem binary_negacyclicModulus_eq_X_sub_one_pow (exponent : ℕ) :
    LatticeCrypto.negacyclicModulus (ZMod 2) (2 ^ exponent) =
      (X - C 1) ^ (2 ^ exponent) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sub_pow_char_pow (p := 2)]
  simp only [map_one, one_pow, LatticeCrypto.negacyclicModulus]
  have neg_one_eq_one : -(1 : Polynomial (ZMod 2)) = 1 := by
    ext coefficient
    simp [ZMod.neg_eq_self_mod_two]
  rw [sub_eq_add_neg, neg_one_eq_one]

/-- Reduce coefficients modulo two in a semantic negacyclic quotient.  Mapping the defining
polynomial preserves `X^N + 1`, so coefficient reduction descends to the quotient. -/
noncomputable def quotientCoefficientReduce {q ringDegree : ℕ} (heven : 2 ∣ q) :
    FormalProof4FHE.RLWE.QuotientRq q ringDegree →+*
      FormalProof4FHE.RLWE.QuotientRq 2 ringDegree :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp
      (Polynomial.mapRingHom (ZMod.castHom heven (ZMod 2)))) (by
        intro polynomial polynomial_mem
        rw [RingHom.comp_apply, Polynomial.coe_mapRingHom]
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [Ideal.mem_span_singleton] at polynomial_mem ⊢
        obtain ⟨factor, rfl⟩ := polynomial_mem
        refine ⟨factor.map (ZMod.castHom heven (ZMod 2)), ?_⟩
        have modulus_map :
            (LatticeCrypto.negacyclicModulus (ZMod q) ringDegree).map
                (ZMod.castHom heven (ZMod 2)) =
              LatticeCrypto.negacyclicModulus (ZMod 2) ringDegree := by
          simp [LatticeCrypto.negacyclicModulus]
        rw [Polynomial.map_mul, modulus_map])

@[simp]
theorem quotientCoefficientReduce_mk {q ringDegree : ℕ} (heven : 2 ∣ q)
    (polynomial : Polynomial (ZMod q)) :
    quotientCoefficientReduce (ringDegree := ringDegree) heven
        (Ideal.Quotient.mk _ polynomial) =
      Ideal.Quotient.mk _
        (polynomial.map (ZMod.castHom heven (ZMod 2))) := by
  rw [quotientCoefficientReduce, Ideal.Quotient.lift_mk]
  rfl

/-- Reducing a semantic negacyclic class coefficientwise and then evaluating parity agrees with
evaluating parity directly. -/
theorem quotientParityEval_quotientCoefficientReduce {q ringDegree : ℕ}
    (heven : 2 ∣ q)
    (value : FormalProof4FHE.RLWE.QuotientRq q ringDegree) :
    quotientParityEval dvd_rfl (quotientCoefficientReduce heven value) =
      quotientParityEval heven value := by
  obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective value
  rw [quotientCoefficientReduce_mk]
  simp only [quotientParityEval, Ideal.Quotient.lift_mk]
  simp [polynomialParityEval]

/-- An element of `ZMod (2^k)` killed by reduction modulo two is nilpotent. -/
theorem zmod_powerOfTwo_isNilpotent_of_castHom_eq_zero
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (value : ZMod (2 ^ modulusExponent))
    (parity_zero :
      ZMod.castHom (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) (ZMod 2) value = 0) :
    IsNilpotent value := by
  letI : NeZero (2 ^ modulusExponent) :=
    ⟨pow_ne_zero modulusExponent (by omega)⟩
  have value_even : 2 ∣ value.val := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at parity_zero
    exact (CharP.cast_eq_zero_iff (ZMod 2) 2 value.val).mp parity_zero
  obtain ⟨half, value_val_eq⟩ := value_even
  have value_eq : value = (2 : ZMod (2 ^ modulusExponent)) * half := by
    calc
      value = (value.val : ZMod (2 ^ modulusExponent)) :=
        value.natCast_zmod_val.symm
      _ = (2 * half : ℕ) := congrArg (fun natural : ℕ ↦
        (natural : ZMod (2 ^ modulusExponent))) value_val_eq
      _ = (2 : ZMod (2 ^ modulusExponent)) * half := by
        norm_num
  refine ⟨modulusExponent, ?_⟩
  calc
    value ^ modulusExponent =
        (2 : ZMod (2 ^ modulusExponent)) ^ modulusExponent *
          (half : ZMod (2 ^ modulusExponent)) ^ modulusExponent := by
      rw [value_eq, mul_pow]
    _ = (2 ^ modulusExponent : ℕ) *
          (half : ZMod (2 ^ modulusExponent)) ^ modulusExponent := by
      congr 1
      exact (Nat.cast_pow 2 modulusExponent).symm
    _ = 0 := by rw [ZMod.natCast_self, zero_mul]

/-- The kernel of semantic coefficient reduction from modulus `2^k` to modulus two consists of
nilpotent elements.  A representative that vanishes in the binary quotient differs from a lifted
multiple of the negacyclic modulus by a polynomial whose coefficients are all even, hence all
nilpotent. -/
theorem quotientCoefficientReduce_kernel_isNilpotent_powerOfTwo
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (ringDegree : ℕ)
    (value : FormalProof4FHE.RLWE.QuotientRq (2 ^ modulusExponent) ringDegree)
    (reduction_zero :
      quotientCoefficientReduce
        (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) value = 0) :
    IsNilpotent value := by
  let coefficientReduce : ZMod (2 ^ modulusExponent) →+* ZMod 2 :=
    ZMod.castHom (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) (ZMod 2)
  obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective value
  rw [quotientCoefficientReduce_mk,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at reduction_zero
  obtain ⟨binaryFactor, mapped_polynomial_eq⟩ := reduction_zero
  obtain ⟨liftedFactor, liftedFactor_spec⟩ :=
    Polynomial.map_surjective coefficientReduce
      (ZMod.castHom_surjective
        (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent))) binaryFactor
  let remainder : Polynomial (ZMod (2 ^ modulusExponent)) :=
    polynomial -
      LatticeCrypto.negacyclicModulus
        (ZMod (2 ^ modulusExponent)) ringDegree * liftedFactor
  have modulus_map :
      (LatticeCrypto.negacyclicModulus
          (ZMod (2 ^ modulusExponent)) ringDegree).map coefficientReduce =
        LatticeCrypto.negacyclicModulus (ZMod 2) ringDegree := by
    simp [coefficientReduce, LatticeCrypto.negacyclicModulus]
  have remainder_map : remainder.map coefficientReduce = 0 := by
    dsimp only [remainder]
    rw [Polynomial.map_sub, Polynomial.map_mul, modulus_map,
      liftedFactor_spec, mapped_polynomial_eq, sub_self]
  have remainder_nilpotent : IsNilpotent remainder := by
    rw [Polynomial.isNilpotent_iff]
    intro coefficient
    apply zmod_powerOfTwo_isNilpotent_of_castHom_eq_zero
      modulusExponent modulusExponent_positive
    have coefficient_zero := congrArg
      (fun mapped : Polynomial (ZMod 2) ↦ mapped.coeff coefficient)
      remainder_map
    simpa [coefficientReduce] using coefficient_zero
  have quotient_eq :
      Ideal.Quotient.mk
          (Ideal.span {LatticeCrypto.negacyclicModulus
            (ZMod (2 ^ modulusExponent)) ringDegree}) polynomial =
        Ideal.Quotient.mk
          (Ideal.span {LatticeCrypto.negacyclicModulus
            (ZMod (2 ^ modulusExponent)) ringDegree}) remainder := by
    dsimp only [remainder]
    simp [map_sub, map_mul]
  rw [quotient_eq]
  exact remainder_nilpotent.map (Ideal.Quotient.mk _)

/-- The kernel of parity evaluation on the semantic binary degree-`2^d` negacyclic quotient is
nilpotent elementwise, with exponent `2^d`. -/
theorem quotientParityEval_kernel_isNilpotent_binary_powerOfTwo
    (exponent : ℕ)
    (value : FormalProof4FHE.RLWE.QuotientRq 2 (2 ^ exponent))
    (parity_zero : quotientParityEval (q := 2) dvd_rfl value = 0) :
    IsNilpotent value := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective value
  have eval_zero : Polynomial.eval 1 polynomial = 0 := by
    change polynomialParityEval (q := 2) dvd_rfl polynomial = 0 at parity_zero
    simpa [polynomialParityEval] using parity_zero
  have polynomial_mem : polynomial ∈ Ideal.span {X - C (1 : ZMod 2)} := by
    rw [← Polynomial.ker_evalRingHom]
    exact RingHom.mem_ker.mpr eval_zero
  obtain ⟨factor, polynomial_eq⟩ :=
    Ideal.mem_span_singleton.mp polynomial_mem
  refine ⟨2 ^ exponent, ?_⟩
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [polynomial_eq, mul_pow,
    ← binary_negacyclicModulus_eq_X_sub_one_pow]
  exact Ideal.mem_span_singleton.mpr ⟨factor ^ (2 ^ exponent), rfl⟩

/-- For power-of-two coefficient modulus and power-of-two negacyclic degree, the semantic parity
kernel is nilpotent.  Binary nilpotence first puts a power into the coefficient-reduction kernel;
nilpotence of that kernel then lifts back through the power. -/
theorem quotientParityEval_kernel_isNilpotent_powerOfTwo
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (degreeExponent : ℕ)
    (value : FormalProof4FHE.RLWE.QuotientRq
      (2 ^ modulusExponent) (2 ^ degreeExponent))
    (parity_zero :
      quotientParityEval
        (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) value = 0) :
    IsNilpotent value := by
  let heven : 2 ∣ 2 ^ modulusExponent :=
    pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)
  let reduced := quotientCoefficientReduce heven value
  have reduced_parity_zero : quotientParityEval dvd_rfl reduced = 0 := by
    rw [quotientParityEval_quotientCoefficientReduce]
    exact parity_zero
  obtain ⟨binaryExponent, reduced_pow_zero⟩ :=
    quotientParityEval_kernel_isNilpotent_binary_powerOfTwo
      degreeExponent reduced reduced_parity_zero
  have source_pow_reduces_to_zero :
      quotientCoefficientReduce heven (value ^ binaryExponent) = 0 := by
    rw [map_pow, reduced_pow_zero]
  have source_pow_nilpotent :=
    quotientCoefficientReduce_kernel_isNilpotent_powerOfTwo
      modulusExponent modulusExponent_positive (2 ^ degreeExponent)
      (value ^ binaryExponent) source_pow_reduces_to_zero
  exact IsNilpotent.of_pow source_pow_nilpotent

/-- Executable binary degree-`2^d` parity evaluation also has nilpotent kernel. -/
theorem rqParityEval_kernel_isNilpotent_binary_powerOfTwo
    (exponent : ℕ)
    (value : FormalProof4FHE.RLWE.Rq 2 (2 ^ exponent))
    (parity_zero : rqParityEval dvd_rfl (pow_pos (by omega) exponent) value = 0) :
    IsNilpotent value := by
  have semantic_nilpotent : IsNilpotent
      (FormalProof4FHE.RLWE.quotientRingHom
        (q := 2) (pow_pos (by omega) exponent) value) := by
    apply quotientParityEval_kernel_isNilpotent_binary_powerOfTwo
    exact parity_zero
  obtain ⟨nilpotenceExponent, semantic_pow_zero⟩ := semantic_nilpotent
  refine ⟨nilpotenceExponent, ?_⟩
  apply FormalProof4FHE.RLWE.quotientRingHom_injective
    (pow_pos (by omega) exponent)
  rw [map_pow, semantic_pow_zero]
  change 0 = FormalProof4FHE.RLWE.quotientOf
    (pow_pos (by omega) exponent) 0
  rw [FormalProof4FHE.RLWE.quotientOf_zero]

/-! ## Production power-of-two coefficient modulus -/

/-- The executable parity kernel is nilpotent for coefficient modulus `2^k`, `k > 0`, and
negacyclic degree `2^d`. -/
theorem rqParityEval_kernel_isNilpotent_powerOfTwo
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (degreeExponent : ℕ)
    (value : FormalProof4FHE.RLWE.Rq
      (2 ^ modulusExponent) (2 ^ degreeExponent))
    (parity_zero :
      rqParityEval
        (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent))
        (pow_pos (by omega) degreeExponent) value = 0) :
    IsNilpotent value := by
  have semantic_nilpotent : IsNilpotent
      (FormalProof4FHE.RLWE.quotientRingHom
        (q := 2 ^ modulusExponent)
        (pow_pos (by omega) degreeExponent) value) := by
    apply quotientParityEval_kernel_isNilpotent_powerOfTwo
      modulusExponent modulusExponent_positive degreeExponent
    exact parity_zero
  obtain ⟨nilpotenceExponent, semantic_pow_zero⟩ := semantic_nilpotent
  refine ⟨nilpotenceExponent, ?_⟩
  apply FormalProof4FHE.RLWE.quotientRingHom_injective
    (pow_pos (by omega) degreeExponent)
  rw [map_pow, semantic_pow_zero]
  change 0 = FormalProof4FHE.RLWE.quotientOf
    (pow_pos (by omega) degreeExponent) 0
  rw [FormalProof4FHE.RLWE.quotientOf_zero]

private theorem rqPositive_zero_eq_bundled {q ringDegree : ℕ}
    (ringDegree_positive : 0 < ringDegree) :
    @Zero.zero (FormalProof4FHE.RLWE.Rq q ringDegree)
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod q) ringDegree).toZero =
      (FormalProof4FHE.RLWE.negacyclicRing q ringDegree).zero := by
  cases ringDegree with
  | zero => omega
  | succ ringDegree => rfl

/-- Binary power-of-two negacyclic parity evaluation reflects units unconditionally. -/
theorem rqParityEval_isLocalHom_binary_powerOfTwo (exponent : ℕ) :
    IsLocalHom
      (rqParityEval dvd_rfl (pow_pos (by omega) exponent) :
        FormalProof4FHE.RLWE.Rq 2 (2 ^ exponent) →+* ZMod 2) := by
  apply isLocalHom_toZModTwo_of_nilpotent_kernel
  intro value parity_zero
  obtain ⟨nilpotenceExponent, nilpotence⟩ :=
    rqParityEval_kernel_isNilpotent_binary_powerOfTwo exponent value parity_zero
  refine ⟨nilpotenceExponent, ?_⟩
  convert nilpotence using 1
  exact rqPositive_zero_eq_bundled (pow_pos (by omega) exponent)

/-- Equality-transported form of the binary local-ring theorem, convenient when a caller stores
the positive ring degree as `degree + 1`. -/
theorem rqParityEval_isLocalHom_binary_powerOfTwo_of_degree_eq
    {ringDegree exponent : ℕ} (degree_eq : ringDegree = 2 ^ exponent)
    (degree_positive : 0 < ringDegree) :
    IsLocalHom
      (rqParityEval dvd_rfl degree_positive :
        FormalProof4FHE.RLWE.Rq 2 ringDegree →+* ZMod 2) := by
  subst ringDegree
  exact rqParityEval_isLocalHom_binary_powerOfTwo exponent

/-- Production power-of-two negacyclic parity evaluation reflects units: both the coefficient
modulus and ring degree may be arbitrary positive powers of two. -/
theorem rqParityEval_isLocalHom_powerOfTwo
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (degreeExponent : ℕ) :
    IsLocalHom
      (rqParityEval
        (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent))
        (pow_pos (by omega) degreeExponent) :
          FormalProof4FHE.RLWE.Rq
            (2 ^ modulusExponent) (2 ^ degreeExponent) →+* ZMod 2) := by
  apply isLocalHom_toZModTwo_of_nilpotent_kernel
  intro value parity_zero
  obtain ⟨nilpotenceExponent, nilpotence⟩ :=
    rqParityEval_kernel_isNilpotent_powerOfTwo
      modulusExponent modulusExponent_positive degreeExponent value parity_zero
  refine ⟨nilpotenceExponent, ?_⟩
  convert nilpotence using 1
  exact rqPositive_zero_eq_bundled (pow_pos (by omega) degreeExponent)

/-- Equality-transported production local-ring theorem for callers storing the ring degree in a
different but propositionally equal form. -/
theorem rqParityEval_isLocalHom_powerOfTwo_of_degree_eq
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    {ringDegree degreeExponent : ℕ}
    (degree_eq : ringDegree = 2 ^ degreeExponent)
    (ringDegree_positive : 0 < ringDegree) :
    IsLocalHom
      (rqParityEval
        (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) ringDegree_positive :
          FormalProof4FHE.RLWE.Rq (2 ^ modulusExponent) ringDegree →+* ZMod 2) := by
  subst ringDegree
  exact rqParityEval_isLocalHom_powerOfTwo
    modulusExponent modulusExponent_positive degreeExponent

/-- Fully equality-transported production theorem.  This form accepts a named coefficient
modulus together with a proof that it is a positive power of two, while retaining the caller's
chosen proof that the modulus is even. -/
theorem rqParityEval_isLocalHom_of_modulus_eq_powerOfTwo_of_degree_eq
    {q ringDegree : ℕ} (heven : 2 ∣ q)
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (modulus_eq : q = 2 ^ modulusExponent)
    (degreeExponent : ℕ) (degree_eq : ringDegree = 2 ^ degreeExponent)
    (ringDegree_positive : 0 < ringDegree) :
    IsLocalHom
      (rqParityEval heven ringDegree_positive :
        FormalProof4FHE.RLWE.Rq q ringDegree →+* ZMod 2) := by
  subst q
  exact rqParityEval_isLocalHom_powerOfTwo_of_degree_eq
    modulusExponent modulusExponent_positive degree_eq ringDegree_positive

end

end FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing
