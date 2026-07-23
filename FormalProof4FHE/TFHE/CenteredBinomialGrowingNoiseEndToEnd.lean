/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialDivisibleRefresh
import FormalProof4FHE.TFHE.CenteredBinomialFiniteViewSecurity
import FormalProof4FHE.TFHE.CoefficientStructuredLWE
import FormalProof4FHE.RLWE.PowerOfTwoCyclotomicGame
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IrreducibleDef

/-!
# Growing-Noise Centered-Binomial TFHE Family

The unit-width large-modulus family proves that nonzero finite noise is compatible with the
checked TFHE refresh circuit, but a constant error width is not an asymptotically meaningful LWE
noise regime.  This module strengthens that witness to a linearly growing centered-binomial
width.

At security parameter `λ`, let `w = λ + 1` and let `N` be the least power of two at least `8w`.
The scalar dimension and ring degree are both `N`, every ring, key-switch, and fresh-input error
has centered-binomial width `w`, and the coefficient modulus is

`q = 64 N^6 = (2N)^6`.

Six base-`2N` digits reconstruct `q` exactly.  The quotient `ZMod q → ZMod (2N)` therefore gives
exact native phase reduction, the supported input errors stay strictly inside the anti-periodic
Boolean region, and the fully checked worst-case BRK budget fits the quarter-modulus output
distance for every `λ`.  Fresh Boolean refresh consequently succeeds with probability one with no
arithmetic premise left to the caller.

The accompanying confidentiality theorem retains the exact native auxiliary-input CircLWE
premise.  The supplied circular-security references do not reduce TFHE's heterogeneous bilinear
BRK/KSK cycle to ordinary LWE or RLWE; this module strengthens parameters without obscuring that
open computational boundary.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd

open Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView

noncomputable section

/-- Centered-binomial width `w = λ + 1`. -/
def errorWidth (securityParameter : ℕ) : ℕ := securityParameter + 1

/-- Linear lower target `8(λ+1)` for the cyclotomic ring degree. -/
def targetDegree (securityParameter : ℕ) : ℕ := 8 * errorWidth securityParameter

/-- Exponent of the least power-of-two ring degree. -/
def ringExponent (securityParameter : ℕ) : ℕ :=
  Nat.clog 2 (targetDegree securityParameter)

/-- Ring degree and scalar LWE dimension: the least power of two at least `8(λ+1)`.

It is opaque so downstream typeclass search treats the dimension as an atomic positive natural;
the exact formula is exposed by `ringDegree_eq_two_pow`. -/
irreducible_def ringDegree (securityParameter : ℕ) : ℕ :=
  2 ^ Nat.clog 2 (targetDegree securityParameter)

/-- Polynomial index `N - 1` of the native negacyclic rotation ring. -/
def rotationDegree (securityParameter : ℕ) : ℕ := ringDegree securityParameter - 1

/-- The chosen ring degree is literally a power of two. -/
theorem ringDegree_eq_two_pow (securityParameter : ℕ) :
    ringDegree securityParameter =
      2 ^ Nat.clog 2 (targetDegree securityParameter) := by
  exact ringDegree_def securityParameter

theorem ringDegree_eq_two_pow_ringExponent (securityParameter : ℕ) :
    ringDegree securityParameter = 2 ^ ringExponent securityParameter := by
  simpa [ringExponent] using ringDegree_eq_two_pow securityParameter

/-- The ring degree is a power of two, as required for the usual power-of-two cyclotomic
presentation `Z[X] / (X^N + 1)`. -/
theorem ringDegree_isPowerOfTwo (securityParameter : ℕ) :
    ∃ exponent : ℕ, ringDegree securityParameter = 2 ^ exponent :=
  ⟨Nat.clog 2 (targetDegree securityParameter), ringDegree_eq_two_pow securityParameter⟩

theorem ringDegree_pos (securityParameter : ℕ) :
    0 < ringDegree securityParameter := by
  simp [ringDegree_def]

/-- The target linear dimension is below the rounded power-of-two degree. -/
theorem targetDegree_le_ringDegree (securityParameter : ℕ) :
    targetDegree securityParameter ≤ ringDegree securityParameter := by
  rw [ringDegree_eq_two_pow]
  exact Nat.le_pow_clog (b := 2) (by norm_num) (targetDegree securityParameter)

/-- Every member of the family has a nontrivial power-of-two cyclotomic degree. -/
theorem eight_le_ringDegree (securityParameter : ℕ) :
    8 ≤ ringDegree securityParameter := by
  apply (show 8 ≤ targetDegree securityParameter by
    simp [targetDegree, errorWidth]).trans
  exact targetDegree_le_ringDegree securityParameter

/-- The defining negacyclic polynomial of this family is exactly the cyclotomic polynomial of
order twice the ring degree. -/
theorem cyclotomic_two_mul_ringDegree_eq {R : Type*} [CommRing R]
    (securityParameter : ℕ) :
    Polynomial.cyclotomic (2 * ringDegree securityParameter) R =
      Polynomial.X ^ ringDegree securityParameter + 1 := by
  rw [ringDegree_eq_two_pow]
  simpa [pow_succ, Nat.mul_comm] using
    (RLWE.PowerOfTwoCyclotomic.cyclotomic_two_pow_succ_eq
      (R := R) (Nat.clog 2 (targetDegree securityParameter)))

/-- The proof-facing negacyclic quotient used by the family is canonically the cyclotomic
quotient of order `2N`. -/
noncomputable def ringQuotientEquivCyclotomic {R : Type*} [CommRing R]
    (securityParameter : ℕ) :
    LatticeCrypto.NegacyclicQuotient R (ringDegree securityParameter) ≃+*
      RLWE.PowerOfTwoCyclotomic.CyclotomicQuotient R
        (2 * ringDegree securityParameter) := by
  unfold LatticeCrypto.NegacyclicQuotient
    RLWE.PowerOfTwoCyclotomic.CyclotomicQuotient
  exact Ideal.quotEquivOfEq (by
    rw [cyclotomic_two_mul_ringDegree_eq]
    rfl)

/-- Rounding up to a power of two costs strictly less than a factor of two. -/
theorem ringDegree_lt_two_mul_targetDegree (securityParameter : ℕ) :
    ringDegree securityParameter < 2 * targetDegree securityParameter := by
  have htarget : 1 < targetDegree securityParameter := by
    simp [targetDegree, errorWidth]
    omega
  have hclog : 0 < Nat.clog 2 (targetDegree securityParameter) :=
    Nat.clog_pos (by norm_num) htarget
  have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) htarget
  calc
    ringDegree securityParameter =
        2 ^ (Nat.clog 2 (targetDegree securityParameter)).pred * 2 := by
      rw [ringDegree_def, ← Nat.pow_succ]
      congr 1
    _ < targetDegree securityParameter * 2 :=
      Nat.mul_lt_mul_of_pos_right hpred (by norm_num)
    _ = 2 * targetDegree securityParameter := by omega

/-- The cyclotomic degree still has a simple linear polynomial upper bound. -/
theorem ringDegree_le_sixteen_mul_errorWidth (securityParameter : ℕ) :
    ringDegree securityParameter ≤ 16 * errorWidth securityParameter := by
  have := ringDegree_lt_two_mul_targetDegree securityParameter
  simp [targetDegree] at this
  omega

@[simp]
theorem rotationDegree_add_one (securityParameter : ℕ) :
    rotationDegree securityParameter + 1 = ringDegree securityParameter := by
  unfold rotationDegree
  exact Nat.sub_add_cancel (ringDegree_pos securityParameter)

/-- Coefficient modulus `q = 64N^6 = (2N)^6`. -/
def coefficientModulus (securityParameter : ℕ) : ℕ :=
  64 * ringDegree securityParameter ^ 6

/-- The concrete coefficient modulus is larger than one, so its residue ring is nontrivial. -/
theorem one_lt_coefficientModulus (securityParameter : ℕ) :
    1 < coefficientModulus securityParameter := by
  unfold coefficientModulus
  have hpower : 0 < ringDegree securityParameter ^ 6 :=
    Nat.pow_pos (ringDegree_pos securityParameter)
  omega

instance instCoefficientModulusOneLt (securityParameter : ℕ) :
    Fact (1 < coefficientModulus securityParameter) :=
  ⟨one_lt_coefficientModulus securityParameter⟩

/-- Interpret an executable ring element of the concrete family in its exact order-`2N`
cyclotomic quotient. -/
noncomputable def coefficientCyclotomicQuotientOf (securityParameter : ℕ)
    (value : RLWE.Rq (coefficientModulus securityParameter)
      (ringDegree securityParameter)) :
    RLWE.PowerOfTwoCyclotomic.CyclotomicQuotient
      (ZMod (coefficientModulus securityParameter))
      (2 * ringDegree securityParameter) :=
  ringQuotientEquivCyclotomic securityParameter
    (RLWE.quotientOf (ringDegree_pos securityParameter) value)

/-- The concrete executable-to-cyclotomic interpretation is injective. -/
theorem coefficientCyclotomicQuotientOf_injective (securityParameter : ℕ) :
    Function.Injective (coefficientCyclotomicQuotientOf securityParameter) :=
  (ringQuotientEquivCyclotomic securityParameter).injective.comp
    (RLWE.quotientOf_injective
      (q := coefficientModulus securityParameter) (ringDegree_pos securityParameter))

/-- Every class in the exact order-`2N` cyclotomic quotient has a concrete executable
coefficient representative. -/
theorem coefficientCyclotomicQuotientOf_surjective (securityParameter : ℕ) :
    Function.Surjective (coefficientCyclotomicQuotientOf securityParameter) :=
  (ringQuotientEquivCyclotomic securityParameter).surjective.comp
    (RLWE.quotientOf_surjective
      (q := coefficientModulus securityParameter) (ringDegree_pos securityParameter))

/-- The concrete executable carrier and the exact order-`2N` cyclotomic quotient are in
bijection. -/
theorem coefficientCyclotomicQuotientOf_bijective (securityParameter : ℕ) :
    Function.Bijective (coefficientCyclotomicQuotientOf securityParameter) :=
  ⟨coefficientCyclotomicQuotientOf_injective securityParameter,
    coefficientCyclotomicQuotientOf_surjective securityParameter⟩

/-- Carrier equivalence for the concrete growing-noise TFHE ring family.  Multiplication
preservation is recorded separately below. -/
noncomputable def coefficientCyclotomicEquiv (securityParameter : ℕ) :
    RLWE.Rq (coefficientModulus securityParameter) (ringDegree securityParameter) ≃
      RLWE.PowerOfTwoCyclotomic.CyclotomicQuotient
        (ZMod (coefficientModulus securityParameter))
        (2 * ringDegree securityParameter) :=
  Equiv.ofBijective (coefficientCyclotomicQuotientOf securityParameter)
    (coefficientCyclotomicQuotientOf_bijective securityParameter)

/-- Concrete executable negacyclic multiplication agrees with multiplication in the exact
cyclotomic quotient. -/
theorem coefficientCyclotomicQuotientOf_mul (securityParameter : ℕ)
    (left right : RLWE.Rq (coefficientModulus securityParameter)
      (ringDegree securityParameter)) :
    coefficientCyclotomicQuotientOf securityParameter
        ((RLWE.negacyclicRing (coefficientModulus securityParameter)
          (ringDegree securityParameter)).mul left right) =
      coefficientCyclotomicQuotientOf securityParameter left *
        coefficientCyclotomicQuotientOf securityParameter right := by
  unfold coefficientCyclotomicQuotientOf
  rw [RLWE.quotientOf_mul]
  exact map_mul (ringQuotientEquivCyclotomic securityParameter) _ _

/-- Explicit polynomial upper bound witnessing that the coefficient modulus has polynomial
growth despite power-of-two rounding. -/
def coefficientModulusPolynomial : Polynomial ℕ :=
  64 * (16 * (Polynomial.X + 1)) ^ 6

theorem coefficientModulus_le_polynomial_eval (securityParameter : ℕ) :
    coefficientModulus securityParameter ≤
      coefficientModulusPolynomial.eval securityParameter := by
  have hdegree := ringDegree_le_sixteen_mul_errorWidth securityParameter
  simp only [errorWidth] at hdegree
  simp [coefficientModulus, coefficientModulusPolynomial]
  gcongr

instance instCoefficientModulusNeZero (securityParameter : ℕ) :
    NeZero (coefficientModulus securityParameter) :=
  ⟨Nat.ne_of_gt (Nat.mul_pos (by norm_num)
    (Nat.pow_pos (ringDegree_pos securityParameter)))⟩

/-- Six base-`2N` digits reconstruct the coefficient modulus exactly. -/
def decomposition (securityParameter : ℕ) :
    Gadget.Base.Parameters (coefficientModulus securityParameter) where
  base := 2 * ringDegree securityParameter
  levels := 6
  one_lt_base := by
    have := ringDegree_pos securityParameter
    omega
  modulus_le_capacity := by
    change 64 * ringDegree securityParameter ^ 6 ≤
      (2 * ringDegree securityParameter) ^ 6
    ring_nf
    rfl

/-- The native signed-rotation order divides the larger coefficient modulus. -/
theorem rotationOrder_dvd_coefficientModulus (securityParameter : ℕ) :
    2 * (rotationDegree securityParameter + 1) ∣
      coefficientModulus securityParameter := by
  rw [rotationDegree_add_one]
  refine ⟨32 * ringDegree securityParameter ^ 5, ?_⟩
  simp [coefficientModulus]
  ring

/-- Centered-binomial Boolean family with a linearly growing error width in every component. -/
def family : CenteredBinomial.Family Bool where
  q := coefficientModulus
  degree := ringDegree
  ringRank := fun _ ↦ 1
  lweDimension := ringDegree
  ringEta := errorWidth
  keySwitchEta := errorWidth
  inputEta := errorWidth
  tgswDecomposition := decomposition
  keySwitchDecomposition := decomposition
  encode := fun securityParameter ↦
    CenteredBinomialDivisibleRefresh.inputCode
      (coefficientModulus securityParameter) (rotationDegree securityParameter)

instance instFamilyNeZero :
    ∀ securityParameter, NeZero (family.q securityParameter) :=
  fun securityParameter ↦
    ⟨by
      change coefficientModulus securityParameter ≠ 0
      exact NeZero.ne (coefficientModulus securityParameter)⟩

/-! ## Concrete nonlinear circular-KDM boundary -/

/-- The first level of the concrete six-level base-`2N` TGSW gadget. -/
def firstTGSWLevel (securityParameter : ℕ) :
    Fin (family.parameters.tgswLevels securityParameter) :=
  ⟨0, by simp [family, CenteredBinomial.Family.parameters, decomposition]⟩

/-- The concrete first TGSW gadget coordinate is nonzero in every member of the growing family. -/
theorem firstTGSWGadget_ne_zero (securityParameter : ℕ) :
    family.parameters.tgswGadget securityParameter
        (firstTGSWLevel securityParameter) ≠ 0 := by
  change Gadget.Base.ringGadget (decomposition securityParameter)
      ⟨0, by simp [decomposition]⟩ ≠ 0
  exact Gadget.Base.ringGadget_zero_ne_zero
    (decomposition securityParameter) (ringDegree_pos securityParameter) (by simp [decomposition])

/-- The selected native TFHE mask-block phase is genuinely degree two for the exact growing
parameters.  Consequently an affine-KDM theorem cannot discharge the intact bootstrap-key cycle
without an additional transformation or a stronger circular/KDM assumption. -/
theorem nativeMaskBlockPhase_not_affine (securityParameter : ℕ) :
    ¬ TGSW.MonomialKDM.ScaledProductAffine
      (family.parameters.tgswGadget securityParameter
        (firstTGSWLevel securityParameter)) := by
  apply TGSW.MonomialKDM.not_scaledProductAffine
  intro hzero
  apply firstTGSWGadget_ne_zero securityParameter
  rw [hzero]
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change Gadget.Base.coefficientAddHom
      (family.parameters.degree securityParameter) coefficient _ =
    (RLWE.negacyclicRing (family.parameters.q securityParameter)
      (family.parameters.degree securityParameter)).backend.coeff _ coefficient
  exact ((Gadget.Base.coefficientAddHom
    (family.parameters.degree securityParameter) coefficient).map_zero).trans
      (LatticeCrypto.NegacyclicRing.coeff_zero
        (RLWE.negacyclicRing (family.parameters.q securityParameter)
          (family.parameters.degree securityParameter)) coefficient).symm

/-- The same obstruction already holds on the actual Boolean support of the selected ring/scalar
secret coordinates.  Hence it is not enough for an affine expression merely to agree with the
native mask-block phase on valid binary keys. -/
theorem nativeBinaryMaskBlockPhase_not_affine (securityParameter : ℕ) :
    ¬ TGSW.MonomialKDM.BinaryScaledProductAffine
      (family.parameters.tgswGadget securityParameter
        (firstTGSWLevel securityParameter)) := by
  apply TGSW.MonomialKDM.not_binaryScaledProductAffine
  intro hzero
  apply firstTGSWGadget_ne_zero securityParameter
  rw [hzero]
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change Gadget.Base.coefficientAddHom
      (family.parameters.degree securityParameter) coefficient _ =
    (RLWE.negacyclicRing (family.parameters.q securityParameter)
      (family.parameters.degree securityParameter)).backend.coeff _ coefficient
  exact ((Gadget.Base.coefficientAddHom
    (family.parameters.degree securityParameter) coefficient).map_zero).trans
      (LatticeCrypto.NegacyclicRing.coeff_zero
        (RLWE.negacyclicRing (family.parameters.q securityParameter)
          (family.parameters.degree securityParameter)) coefficient).symm

/-- Coordinate zero in both the rank-one binary ring key and scalar binary key. -/
def firstBinaryKeyCoordinate (securityParameter : ℕ) : Fin (ringDegree securityParameter) :=
  ⟨0, ringDegree_pos securityParameter⟩

/-- A binary polynomial supported at coefficient zero embeds as the corresponding constant ring
bit.  Positivity of the polynomial degree is the only required shape condition. -/
theorem embedBinaryPolynomial_singleBit_zero {q degree : ℕ} [NeZero q]
    (hdegree : 0 < degree) (bit : Bool) :
    embedBinaryPolynomial q degree
        (TGSW.MonomialKDM.singleBit ⟨0, hdegree⟩ bit) =
      (embedBit bit : RLWE.Rq q degree) := by
  cases degree with
  | zero => omega
  | succ degree =>
      have hconstant :
          embedBinaryPolynomial q (degree + 1)
              (TGSW.MonomialKDM.singleBit ⟨0, hdegree⟩ bit) =
            embedConstantBit q (degree + 1) bit := by
        apply LatticeCrypto.Poly.ext_get_eq
        intro coefficient
        change LatticeCrypto.Poly.toPi
            (embedBinaryPolynomial q (degree + 1)
              (TGSW.MonomialKDM.singleBit ⟨0, hdegree⟩ bit)) coefficient =
          LatticeCrypto.Poly.toPi
            (embedConstantBit q (degree + 1) bit) coefficient
        simp only [embedBinaryPolynomial, embedConstantBit,
          LatticeCrypto.Poly.toPi_ofPi]
        cases bit with
        | false =>
            simp only [TGSW.MonomialKDM.singleBit, Bool.and_false, ite_self]
        | true =>
            congr 1
            by_cases hcoefficient : coefficient = ⟨0, hdegree⟩
            · subst coefficient
              rfl
            · have hvalue : coefficient.val ≠ 0 := by
                intro hzero
                apply hcoefficient
                exact Fin.ext hzero
              rw [TGSW.MonomialKDM.singleBit, if_neg hcoefficient]
              simp only [hvalue, decide_false, Bool.false_and]
      exact hconstant.trans (BlindRotation.embedConstantBit_eq_embedBit bit)

/-- Reconcile the executable carrier's bundled bit embedding with the abstract `CommRing`
embedding used by the affine-support predicate. -/
theorem embedBit_eq_commRingEmbedBit {q degree : ℕ} [NeZero q]
    (hdegree : 0 < degree) (bit : Bool) :
    (embedBit bit : RLWE.Rq q degree) =
      TGSW.MonomialKDM.commRingEmbedBit
        (R := RLWE.Rq q degree) bit := by
  cases degree with
  | zero => omega
  | succ degree =>
      cases bit <;> rfl

/-- Even allowing arbitrary affine coefficients on every bit of both complete native keys cannot
represent the selected degree-two cross coordinate.  This is the vector-key notion relevant to
the affine LWE-KDM and subspace-LWE references, specialized to the exact TFHE parameters. -/
theorem nativeBinaryKeyCoordinateProduct_not_affine (securityParameter : ℕ) :
    ¬ TGSW.MonomialKDM.BinaryVectorScaledProductAffine
      (firstBinaryKeyCoordinate securityParameter)
      (firstBinaryKeyCoordinate securityParameter)
      (family.parameters.tgswGadget securityParameter
        (firstTGSWLevel securityParameter)) := by
  apply TGSW.MonomialKDM.not_binaryVectorScaledProductAffine
  intro hzero
  apply firstTGSWGadget_ne_zero securityParameter
  rw [hzero]
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change Gadget.Base.coefficientAddHom
      (family.parameters.degree securityParameter) coefficient _ =
    (RLWE.negacyclicRing (family.parameters.q securityParameter)
      (family.parameters.degree securityParameter)).backend.coeff _ coefficient
  exact ((Gadget.Base.coefficientAddHom
    (family.parameters.degree securityParameter) coefficient).map_zero).trans
      (LatticeCrypto.NegacyclicRing.coeff_zero
        (RLWE.negacyclicRing (family.parameters.q securityParameter)
          (family.parameters.degree securityParameter)) coefficient).symm

/-- The complete selected native mask-block function is non-affine on its actual key support: the
first argument is an arbitrary binary polynomial (the rank-one ring key), the second is the full
binary scalar key, and an alleged affine representation may use every bit of both keys. -/
theorem nativePolynomialMaskBlockPhase_not_affine_on_binaryKeys
    (securityParameter : ℕ) :
    ¬ TGSW.MonomialKDM.BinaryPolynomialScaledProductAffine
      (embedBinaryPolynomial (coefficientModulus securityParameter)
        (ringDegree securityParameter))
      (firstBinaryKeyCoordinate securityParameter)
      (family.parameters.tgswGadget securityParameter
        (firstTGSWLevel securityParameter)) := by
  apply TGSW.MonomialKDM.not_binaryPolynomialScaledProductAffine
  · intro bit
    exact (embedBinaryPolynomial_singleBit_zero
      (q := coefficientModulus securityParameter)
      (ringDegree_pos securityParameter) bit).trans
        (embedBit_eq_commRingEmbedBit
          (q := coefficientModulus securityParameter)
          (ringDegree_pos securityParameter) bit)
  · intro hzero
    apply firstTGSWGadget_ne_zero securityParameter
    rw [hzero]
    apply LatticeCrypto.Poly.ext_get_eq
    intro coefficient
    change Gadget.Base.coefficientAddHom
        (family.parameters.degree securityParameter) coefficient _ =
      (RLWE.negacyclicRing (family.parameters.q securityParameter)
        (family.parameters.degree securityParameter)).backend.coeff _ coefficient
    exact ((Gadget.Base.coefficientAddHom
      (family.parameters.degree securityParameter) coefficient).map_zero).trans
        (LatticeCrypto.NegacyclicRing.coeff_zero
          (RLWE.negacyclicRing (family.parameters.q securityParameter)
            (family.parameters.degree securityParameter)) coefficient).symm

/-! ## Exact coefficient structured-LWE premise -/

/-- Coefficient-level attacks on the exact rank-one post-cut problem at one security parameter. -/
abbrev PostCutCoefficientStructuredLWEAdversaryAt (securityParameter : ℕ) :=
  LearningWithErrors.Adversary
    (Native.CoefficientStructuredLWE.problem
      (family.parameters.q securityParameter)
      (family.parameters.degree securityParameter) 1
      (family.parameters.lweDimension securityParameter *
        TGSW.rowCount 1 (family.parameters.tgswLevels securityParameter))
      (family.parameters.ringErrorSampler securityParameter))

/-- Parameter-indexed attacks on the exact coefficient negacyclic structured-LWE problem. -/
abbrev PostCutCoefficientStructuredLWEAdversaryFamily :=
  (securityParameter : ℕ) →
    PostCutCoefficientStructuredLWEAdversaryAt securityParameter

/-- The post-cut hardness premise stated directly on coefficient matrices, explicit negacyclic
convolution, independently uniform Boolean secret coefficients, and centered-binomial errors. -/
noncomputable def postCutCoefficientStructuredLWESecurityGame :
    SecurityGame PostCutCoefficientStructuredLWEAdversaryFamily where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (Native.CoefficientStructuredLWE.problem
        (family.parameters.q securityParameter)
        (family.parameters.degree securityParameter) 1
        (family.parameters.lweDimension securityParameter *
          TGSW.rowCount 1 (family.parameters.tgswLevels securityParameter))
        (family.parameters.ringErrorSampler securityParameter))
      (adversary securityParameter))

/-- In this concrete family the coefficient image of the ring-error law is the direct sampler of
independent signed sums of `2(λ+1)` uniform bits, reduced modulo `(2N)^6`. -/
theorem postCutCoefficientErrorSampler_eq_centeredBinomial
    (securityParameter : ℕ) :
    Native.CoefficientStructuredLWE.coefficientErrorSampler
        (family.parameters.q securityParameter)
        (family.parameters.degree securityParameter)
        (family.parameters.ringErrorSampler securityParameter) =
      Native.CoefficientStructuredLWE.centeredBinomialErrorSampler
        (coefficientModulus securityParameter)
        (ringDegree securityParameter) (errorWidth securityParameter) := by
  simpa [family, CenteredBinomial.Family.parameters] using
    (Native.CoefficientStructuredLWE.coefficientErrorSampler_centeredBinomial
      (coefficientModulus securityParameter)
      (ringDegree securityParameter) (errorWidth securityParameter))

/-- The concrete rank-one post-cut secret has exactly `ringDegree λ` bits of min-entropy,
expressed as its exact point probability. -/
theorem postCutRingSecret_pointProbability (securityParameter : ℕ)
    (secret : RingBinarySecret 1 (ringDegree securityParameter)) :
    Pr[= secret | Native.sampleRingSecret 1 (ringDegree securityParameter)] =
      ((2 ^ ringDegree securityParameter : ℕ) : ENNReal)⁻¹ := by
  simpa using
    (Native.CoefficientStructuredLWE.probOutput_sampleRingSecret
      1 (ringDegree securityParameter) secret)

/-- Pull a post-cut ring-carrier adversary back along the coefficient transcript equivalence. -/
noncomputable def postCutRingToCoefficientReduction
    (adversary :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters) :
    PostCutCoefficientStructuredLWEAdversaryFamily :=
  fun securityParameter ↦
    Native.CoefficientStructuredLWE.ofRingAdversary
      (q := family.parameters.q securityParameter)
      (degree := family.parameters.degree securityParameter)
      (rank := 1)
      (sampleCount := family.parameters.lweDimension securityParameter *
        TGSW.rowCount 1 (family.parameters.tgswLevels securityParameter))
      (errorSampler := family.parameters.ringErrorSampler securityParameter)
      (adversary securityParameter)

/-- The ring-carrier and coefficient presentations have pointwise identical advantage. -/
theorem ringBatchLWESecurityGame_advantage_eq_coefficientStructuredLWE
    (adversary :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).advantage adversary securityParameter =
      postCutCoefficientStructuredLWESecurityGame.advantage
        (postCutRingToCoefficientReduction adversary) securityParameter := by
  exact congrArg ENNReal.ofReal
    (Native.CoefficientStructuredLWE.advantage_ofRingAdversary_eq
      (family.parameters.q securityParameter)
      (family.parameters.degree securityParameter) 1
      (family.parameters.lweDimension securityParameter *
        TGSW.rowCount 1 (family.parameters.tgswLevels securityParameter))
      (family.parameters.ringErrorSampler securityParameter)
      (adversary securityParameter)).symm

/-- Coefficient structured-LWE security transfers without loss to the ring presentation used by
the native TFHE reductions. -/
theorem ringBatchLWESecurityGame_secureAgainst_of_coefficientStructuredLWE
    (coefficientIsPPT : PostCutCoefficientStructuredLWEAdversaryFamily → Prop)
    (hCoefficient :
      postCutCoefficientStructuredLWESecurityGame.secureAgainst coefficientIsPPT) :
    (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
      family.parameters).secureAgainst
        (fun adversary ↦ coefficientIsPPT
          (postCutRingToCoefficientReduction adversary)) := by
  exact SecurityGame.secureAgainst_of_reduction
    (fun _ hEfficient ↦ hEfficient)
    (fun adversary securityParameter ↦ le_of_eq
      (ringBatchLWESecurityGame_advantage_eq_coefficientStructuredLWE
        adversary securityParameter))
    hCoefficient

/-! ## Exact post-cut RLWE identification -/

/-- Adversary families for the binary-secret rank-one RLWE problem whose row count is exactly the
native post-cut BRK row count of this family. -/
abbrev PostCutBinarySecretRLWEAdversaryFamily :=
  Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
    family.parameters

/-- Binary-secret RLWE security game on the same public-adversary carrier used by the concrete
post-cut reductions.  Rank one makes the two carriers definitionally coincide. -/
noncomputable def postCutBinarySecretRLWESecurityGame :
    SecurityGame PostCutBinarySecretRLWEAdversaryFamily where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (Native.BootstrapCutSecurity.binarySecretRLWEProblem
        (family.parameters.q securityParameter)
        (family.parameters.degree securityParameter)
        (family.parameters.lweDimension securityParameter *
          TGSW.rowCount 1 (family.parameters.tgswLevels securityParameter))
        (family.parameters.ringErrorSampler securityParameter))
      (adversary securityParameter))

/-- For the concrete rank-one family, the asymptotic post-cut ring-batch game and the explicitly
named binary-secret RLWE game have pointwise identical advantage. -/
theorem binarySecretRLWESecurityGame_advantage_eq_ringBatchLWE
    (adversary : PostCutBinarySecretRLWEAdversaryFamily)
    (securityParameter : ℕ) :
    postCutBinarySecretRLWESecurityGame.advantage adversary securityParameter =
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).advantage adversary securityParameter := by
  exact congrArg ENNReal.ofReal
    (Native.BootstrapCutSecurity.batchModuleLweProblem_one_advantage_eq_binarySecretRLWE
      (family.parameters.q securityParameter)
      (family.parameters.degree securityParameter)
      (family.parameters.tgswLevels securityParameter)
      (family.parameters.lweDimension securityParameter)
      (family.parameters.ringErrorSampler securityParameter)
      (adversary securityParameter)).symm

/-- For this rank-one family, the named binary-secret RLWE game is the existing post-cut
ring-batch game as a complete asymptotic security game, not only up to a bound. -/
theorem postCutBinarySecretRLWESecurityGame_eq_ringBatchLWE :
    postCutBinarySecretRLWESecurityGame =
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters := by
  apply congrArg SecurityGame.mk
  funext adversary securityParameter
  exact binarySecretRLWESecurityGame_advantage_eq_ringBatchLWE adversary securityParameter

/-! ## Exact cyclotomic presentation of the post-cut RLWE premise -/

/-- Number of rank-one RLWE samples exposed by the native post-cut BRK batch. -/
def postCutSampleCount (securityParameter : ℕ) : ℕ :=
  family.parameters.lweDimension securityParameter *
    TGSW.rowCount 1 (family.parameters.tgswLevels securityParameter)

/-- The same binary-secret centered-binomial post-cut problem, now stated over the exact
order-`2N` cyclotomic quotient rather than the executable coefficient-vector carrier. -/
noncomputable def postCutCyclotomicRLWEProblem (securityParameter : ℕ) :=
  RLWE.PowerOfTwoCyclotomic.problem
    (coefficientModulus securityParameter)
    (ringExponent securityParameter)
    (postCutSampleCount securityParameter)
    (Native.BootstrapCutSecurity.binarySecretRLWESampler
      (coefficientModulus securityParameter)
      (2 ^ ringExponent securityParameter))
    (RLWE.CenteredBinomial.sampler
      (coefficientModulus securityParameter)
      (2 ^ ringExponent securityParameter)
      (errorWidth securityParameter))

/-- Pointwise adversaries against the exact cyclotomic post-cut problem. -/
abbrev PostCutCyclotomicRLWEAdversaryAt (securityParameter : ℕ) :=
  LearningWithErrors.Adversary (postCutCyclotomicRLWEProblem securityParameter)

/-- Parameter-indexed adversaries against the exact cyclotomic post-cut family. -/
abbrev PostCutCyclotomicRLWEAdversaryFamily :=
  (securityParameter : ℕ) → PostCutCyclotomicRLWEAdversaryAt securityParameter

/-- Asymptotic security game for the exact order-`2N` cyclotomic presentation. -/
noncomputable def postCutCyclotomicRLWESecurityGame :
    SecurityGame PostCutCyclotomicRLWEAdversaryFamily where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (postCutCyclotomicRLWEProblem securityParameter)
      (adversary securityParameter))

/-- The executable binary-secret RLWE problem at an explicit degree. -/
noncomputable def postCutExecutableRLWEProblem
    (securityParameter degree : ℕ) :=
  Native.BootstrapCutSecurity.binarySecretRLWEProblem
    (coefficientModulus securityParameter) degree
    (postCutSampleCount securityParameter)
    (RLWE.CenteredBinomial.sampler
      (coefficientModulus securityParameter) degree
      (errorWidth securityParameter))

/-- View the existing rank-one ring-batch adversary as an adversary against the explicitly named
binary-secret RLWE problem at the same opaque degree. -/
noncomputable def postCutRingBatchAsExecutable
    (securityParameter : ℕ)
    (adversary :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryAt
        family.parameters securityParameter) :
    LearningWithErrors.Adversary
      (postCutExecutableRLWEProblem securityParameter
        (ringDegree securityParameter)) := by
  simpa [postCutExecutableRLWEProblem, postCutSampleCount, family,
    CenteredBinomial.Family.parameters] using adversary

/-- The inverse carrier-level view from explicitly named binary-secret RLWE back to the existing
rank-one ring-batch adversary type. -/
noncomputable def postCutExecutableAsRingBatch
    (securityParameter : ℕ)
    (adversary : LearningWithErrors.Adversary
      (postCutExecutableRLWEProblem securityParameter
        (ringDegree securityParameter))) :
    Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryAt
      family.parameters securityParameter := by
  simpa [postCutExecutableRLWEProblem, postCutSampleCount, family,
    CenteredBinomial.Family.parameters] using adversary

/-- Reindex an executable post-cut adversary along an equality of degrees. -/
noncomputable def reindexPostCutExecutableAdversary
    (securityParameter : ℕ) {sourceDegree targetDegree : ℕ}
    (hdegree : sourceDegree = targetDegree)
    (adversary : LearningWithErrors.Adversary
      (postCutExecutableRLWEProblem securityParameter sourceDegree)) :
    LearningWithErrors.Adversary
      (postCutExecutableRLWEProblem securityParameter targetDegree) :=
  cast (congrArg (fun degree ↦ LearningWithErrors.Adversary
    (postCutExecutableRLWEProblem securityParameter degree)) hdegree) adversary

/-- Degree reindexing changes only the presentation type and preserves advantage exactly. -/
theorem advantage_reindexPostCutExecutableAdversary
    (securityParameter : ℕ) {sourceDegree targetDegree : ℕ}
    (hdegree : sourceDegree = targetDegree)
    (adversary : LearningWithErrors.Adversary
      (postCutExecutableRLWEProblem securityParameter sourceDegree)) :
    LearningWithErrors.advantage
        (postCutExecutableRLWEProblem securityParameter sourceDegree) adversary =
      LearningWithErrors.advantage
        (postCutExecutableRLWEProblem securityParameter targetDegree)
        (reindexPostCutExecutableAdversary securityParameter hdegree adversary) := by
  subst targetDegree
  rfl

/-- Reindex an existing post-cut adversary along the proved equality
`ringDegree λ = 2 ^ ringExponent λ`. -/
noncomputable def postCutBinaryAdversaryAtPower
    (securityParameter : ℕ)
    (adversary :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryAt
        family.parameters securityParameter) :
    LearningWithErrors.Adversary
      (postCutExecutableRLWEProblem securityParameter
        (2 ^ ringExponent securityParameter)) :=
  reindexPostCutExecutableAdversary securityParameter
    (ringDegree_eq_two_pow_ringExponent securityParameter)
    (postCutRingBatchAsExecutable securityParameter adversary)

/-- Reindex a degree-`2^k` executable adversary back to the family's opaque ring-degree
presentation. -/
noncomputable def postCutPowerAdversaryToBinary
    (securityParameter : ℕ)
    (adversary : LearningWithErrors.Adversary
      (postCutExecutableRLWEProblem securityParameter
        (2 ^ ringExponent securityParameter))) :
    Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryAt
      family.parameters securityParameter :=
  postCutExecutableAsRingBatch securityParameter
    (reindexPostCutExecutableAdversary securityParameter
      (ringDegree_eq_two_pow_ringExponent securityParameter).symm adversary)

/-- Transport an executable post-cut adversary to the exact cyclotomic presentation. -/
noncomputable def postCutBinaryToCyclotomicReduction
    (adversary : PostCutBinarySecretRLWEAdversaryFamily) :
    PostCutCyclotomicRLWEAdversaryFamily :=
  fun securityParameter ↦ by
    exact RLWE.PowerOfTwoCyclotomic.ofExecutableAdversary
      (postCutBinaryAdversaryAtPower securityParameter (adversary securityParameter))

/-- Transport a cyclotomic post-cut adversary to the executable presentation. -/
noncomputable def postCutCyclotomicToBinaryReduction
    (adversary : PostCutCyclotomicRLWEAdversaryFamily) :
    PostCutBinarySecretRLWEAdversaryFamily :=
  fun securityParameter ↦ by
    exact postCutPowerAdversaryToBinary securityParameter
      (RLWE.PowerOfTwoCyclotomic.reduction (adversary securityParameter))

/-- The existing executable binary-secret post-cut game and its exact cyclotomic presentation
have pointwise identical distinguishing advantage. -/
theorem postCutBinarySecretRLWE_advantage_eq_cyclotomic
    (adversary : PostCutBinarySecretRLWEAdversaryFamily)
    (securityParameter : ℕ) :
    postCutBinarySecretRLWESecurityGame.advantage adversary securityParameter =
      postCutCyclotomicRLWESecurityGame.advantage
        (postCutBinaryToCyclotomicReduction adversary) securityParameter := by
  calc
    _ = ENNReal.ofReal (LearningWithErrors.advantage
        (postCutExecutableRLWEProblem securityParameter
          (ringDegree securityParameter))
        (postCutRingBatchAsExecutable securityParameter
          (adversary securityParameter))) := by
      rfl
    _ = ENNReal.ofReal (LearningWithErrors.advantage
        (postCutExecutableRLWEProblem securityParameter
          (2 ^ ringExponent securityParameter))
        (postCutBinaryAdversaryAtPower securityParameter
          (adversary securityParameter))) :=
      congrArg ENNReal.ofReal
        (advantage_reindexPostCutExecutableAdversary securityParameter
          (ringDegree_eq_two_pow_ringExponent securityParameter)
          (postCutRingBatchAsExecutable securityParameter
            (adversary securityParameter)))
    _ = _ := by
      exact congrArg ENNReal.ofReal
        (RLWE.PowerOfTwoCyclotomic.ofExecutableAdversary_advantage_eq
          (coefficientModulus securityParameter)
          (ringExponent securityParameter)
          (postCutSampleCount securityParameter)
          (Native.BootstrapCutSecurity.binarySecretRLWESampler
            (coefficientModulus securityParameter)
            (2 ^ ringExponent securityParameter))
          (RLWE.CenteredBinomial.sampler
            (coefficientModulus securityParameter)
            (2 ^ ringExponent securityParameter)
            (errorWidth securityParameter))
          (postCutBinaryAdversaryAtPower securityParameter
            (adversary securityParameter))).symm

/-- Security of the exact cyclotomic post-cut game transfers without advantage loss to the
executable binary-secret post-cut game.  The source efficiency predicate is precisely the
pullback of the chosen cyclotomic efficiency predicate along the exact carrier transport. -/
theorem postCutBinarySecretRLWESecurityGame_secureAgainst_of_cyclotomic
    (cyclotomicIsPPT : PostCutCyclotomicRLWEAdversaryFamily → Prop)
    (hCyclotomic :
      postCutCyclotomicRLWESecurityGame.secureAgainst cyclotomicIsPPT) :
    postCutBinarySecretRLWESecurityGame.secureAgainst
      (fun adversary ↦ cyclotomicIsPPT
        (postCutBinaryToCyclotomicReduction adversary)) := by
  exact SecurityGame.secureAgainst_of_reduction
    (fun _ hEfficient ↦ hEfficient)
    (fun adversary securityParameter ↦ le_of_eq
      (postCutBinarySecretRLWE_advantage_eq_cyclotomic
        adversary securityParameter))
    hCyclotomic

/-- KSK and fresh-input error samplers coincide definitionally. -/
theorem scalarSamplers_eq :
    ∀ securityParameter,
      family.parameters.inputErrorSampler securityParameter =
        family.parameters.keySwitchErrorSampler securityParameter :=
  family.scalarSamplers_eq_of_eta_eq fun _ ↦ rfl

/-- Every evaluation-key dimension has an explicit polynomial bound. -/
def polynomialEvaluationKeyGrowth : family.PolynomialEvaluationKeyGrowth where
  ringRankPolynomial := 1
  degreePolynomial := 16 * (Polynomial.X + 1)
  keySwitchLevelsPolynomial := 6
  tgswLevelsPolynomial := 6
  lweDimensionPolynomial := 16 * (Polynomial.X + 1)
  ringRank_le := by
    intro securityParameter
    simp [family]
  degree_le := by
    intro securityParameter
    simpa [family, errorWidth] using
      ringDegree_le_sixteen_mul_errorWidth securityParameter
  keySwitchLevels_le := by
    intro securityParameter
    simp [family, decomposition]
  tgswLevels_le := by
    intro securityParameter
    simp [family, decomposition]
  lweDimension_le := by
    intro securityParameter
    simpa [family, errorWidth] using
      ringDegree_le_sixteen_mul_errorWidth securityParameter

/-! ## Exact concrete scalar-LWE premise -/

/-- Exact scalar-row count inherited from the rank-one, six-level KSK plus the adaptive query
tape. -/
def concreteBatchSampleCount (securityParameter queryCount : ℕ) : ℕ :=
  (1 * ringDegree securityParameter) * 6 + queryCount

theorem concreteBatchSampleCount_eq (securityParameter queryCount : ℕ) :
    concreteBatchSampleCount securityParameter queryCount =
      6 * ringDegree securityParameter + queryCount := by
  simp [concreteBatchSampleCount, Nat.mul_comm]

/-- Explicit polynomial row bound for the concrete scalar-LWE problem attached to one adaptive
adversary. -/
noncomputable def concreteBatchSamplePolynomial
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters) : Polynomial ℕ :=
  96 * (Polynomial.X + 1) + adversary.queryPolynomial

theorem concreteBatchSampleCount_le_polynomial
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters)
    (securityParameter : ℕ) :
    concreteBatchSampleCount securityParameter
        (adversary.queryCount securityParameter) ≤
      (concreteBatchSamplePolynomial adversary).eval securityParameter := by
  rw [concreteBatchSampleCount_eq]
  have hdegree := ringDegree_le_sixteen_mul_errorWidth securityParameter
  have hrows : 6 * ringDegree securityParameter ≤
      96 * (securityParameter + 1) := by
    calc
      6 * ringDegree securityParameter ≤
          6 * (16 * errorWidth securityParameter) :=
        Nat.mul_le_mul_left 6 hdegree
      _ = 96 * (securityParameter + 1) := by
        simp [errorWidth]
        ring
  have hquery := adversary.queryCount_le securityParameter
  simpa [concreteBatchSamplePolynomial] using Nat.add_le_add hrows hquery

/-- The exact ordinary scalar problem used by the direct security theorem.  At parameter `λ`
and query count `Q`, this is binary-secret LWE modulo `64N^6`, in dimension `N`, with `6N + Q`
samples and centered-binomial error width `λ+1`. -/
noncomputable def concreteBatchLWEProblem
    (securityParameter queryCount : ℕ) :=
  Native.KeySwitchSecurity.binaryLweProblem
    (coefficientModulus securityParameter)
    (ringDegree securityParameter)
    (concreteBatchSampleCount securityParameter queryCount)
    (CenteredBinomial.scalarSampler
      (coefficientModulus securityParameter) (errorWidth securityParameter))

/-- Interpret an adversary from the generic family-level batch game against the explicitly
parameterized concrete problem above. -/
noncomputable def concreteBatchLWEAdversary
    (adversary : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters)
    (securityParameter : ℕ) :
    LearningWithErrors.Adversary
      (concreteBatchLWEProblem securityParameter
        (adversary.queryCount securityParameter)) := by
  simpa [concreteBatchLWEProblem, concreteBatchSampleCount, family,
    CenteredBinomial.Family.parameters,
    Encryption.Adaptive.Asymptotic.BatchLWEAdversaryAt,
    Encryption.Security.keySwitchSamples, decomposition] using
      adversary.run securityParameter

/-- The direct theorem's non-circular assumption, stated on the fully explicit concrete
binary-secret centered-binomial LWE problem. -/
noncomputable def concreteBatchLWESecurityGame :
    SecurityGame
      (Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily family.parameters) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (concreteBatchLWEProblem securityParameter
        (adversary.queryCount securityParameter))
      (concreteBatchLWEAdversary adversary securityParameter))

/-- The generic batch-LWE premise used by the reduction is exactly the explicit concrete game,
with no parameter, sampler, or advantage loss. -/
theorem concreteBatchLWESecurityGame_eq_batchLWE :
    concreteBatchLWESecurityGame =
      Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters := by
  apply congrArg SecurityGame.mk
  funext adversary securityParameter
  rfl

/-! ## Exact native degree-two circular-KDM endpoint -/

/-- **Direct computational security bound for the concrete growing family.**

The intact TFHE key cycle is represented by the exact native degree-two monomial-KDM game, while
the KSK and adaptive encryption-query rows are one fully explicit binary-secret
centered-binomial LWE instance.  Unlike the discarded wide-Gaussian route, this theorem makes no
statistical replacement of the off-diagonal residual and has no correctness premise. -/
theorem securityGame_advantage_le_nativeMonomialKDM_add_concreteBatchLWE
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
          family.parameters).advantage adversary securityParameter +
        concreteBatchLWESecurityGame.advantage
          (Encryption.Adaptive.Asymptotic.batchLWEReduction
            family.parameters adversary) securityParameter := by
  simpa only [concreteBatchLWESecurityGame_eq_batchLWE] using
    (family.securityGame_advantage_le_monomialKDM_add_batchLWE
      (fun _securityParameter ↦ rfl) adversary securityParameter)

/-- **Security-only TFHE theorem under the exact native circular-KDM assumption.**

This is the shortest construction-faithful theorem for the concrete growing family.  Its first
hypothesis is precisely security of the native degree-two cross-monomial evaluation-key
distribution; its second is the conventional binary-secret LWE problem with explicit growing
parameters.  Neither hypothesis is a correctness or decryption-noise statement. -/
theorem secureAgainst_of_nativeMonomialKDM_and_concreteBatchLWE
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          family.parameters adversary))
    (hNativeMonomialKDM :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
        family.parameters).secureAgainst isPPT)
    (hConcreteBatchLWE :
      concreteBatchLWESecurityGame.secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
      family.parameters).secureAgainst isPPT := by
  apply family.secureAgainst_of_monomialKDM_and_batchLWE
    (fun _securityParameter ↦ rfl) isPPT batchLWEIsPPT hBatchLWEClosed
    hNativeMonomialKDM
  rw [← concreteBatchLWESecurityGame_eq_batchLWE]
  exact hConcreteBatchLWE

/-- Public TFHE evaluation preserves the exact native monomial-KDM security theorem with zero
additional advantage loss. -/
theorem evaluationSecureAgainst_of_nativeMonomialKDM_and_concreteBatchLWE
    {Output : Type}
    (evaluate : Encryption.Adaptive.Asymptotic.PublicEvaluatorFamily
      (Output := Output) family.parameters)
    (baseIsPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (evaluationIsPPT :
      Encryption.Adaptive.Asymptotic.PolynomialQueryEvaluationAdversary
        (Output := Output) family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (Encryption.Adaptive.Asymptotic.compileEvaluationAdversary
          family.parameters evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          family.parameters adversary))
    (hNativeMonomialKDM :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
        family.parameters).secureAgainst baseIsPPT)
    (hConcreteBatchLWE :
      concreteBatchLWESecurityGame.secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.evaluationSecurityGame
      family.parameters evaluate).secureAgainst evaluationIsPPT := by
  apply Encryption.Adaptive.Asymptotic.evaluationSecureAgainst_of_security
    family.parameters evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact secureAgainst_of_nativeMonomialKDM_and_concreteBatchLWE
    baseIsPPT batchLWEIsPPT hBatchLWEClosed hNativeMonomialKDM hConcreteBatchLWE

/-! ## Direct native circular-security endpoint -/

/-- **Direct pointwise security bound for the concrete growing family.**

The exact adaptive TFHE advantage is bounded by one native auxiliary-input CircLWE term and three
ordinary query-counted batch-LWE terms.  Two batch terms discharge the zero-message auxiliary
branch (in the real and uniform-BRK contexts), and the final term is the honest KSK-plus-query
reduction.  Centered-binomial sampling is used in every game, so there is no sampler-replacement,
finite-view, collision, or correctness term. -/
theorem securityGame_advantage_le_nativeCircularLWE_add_three_batchLWE
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      ((Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
            family.parameters).advantage adversary securityParameter +
        ((Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
            (Encryption.Adaptive.Asymptotic.batchLWEReduction
              family.parameters adversary) securityParameter +
          (Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
            (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
              family.parameters adversary) securityParameter)) +
        (Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
          (Encryption.Adaptive.Asymptotic.batchLWEReduction
            family.parameters adversary) securityParameter := by
  exact family.securityGame_advantage_le_circularLWE_add_three_batchLWE
    (fun _ ↦ rfl) adversary securityParameter

/-- The same direct pointwise theorem with every ordinary term stated on the explicit
`(q, n, m, χ) = (64N^6, N, 6N+Q, CB_{λ+1})` binary-secret LWE problem above. -/
theorem securityGame_advantage_le_nativeCircularLWE_add_three_concreteBatchLWE
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      ((Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
            family.parameters).advantage adversary securityParameter +
        (concreteBatchLWESecurityGame.advantage
            (Encryption.Adaptive.Asymptotic.batchLWEReduction
              family.parameters adversary) securityParameter +
          concreteBatchLWESecurityGame.advantage
            (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
              family.parameters adversary) securityParameter)) +
        concreteBatchLWESecurityGame.advantage
          (Encryption.Adaptive.Asymptotic.batchLWEReduction
            family.parameters adversary) securityParameter := by
  simpa only [concreteBatchLWESecurityGame_eq_batchLWE] using
    securityGame_advantage_le_nativeCircularLWE_add_three_batchLWE
      adversary securityParameter

/-- **Primary security-only theorem for the concrete growing TFHE family.**

Negligible native auxiliary-input CircLWE advantage and ordinary query-counted batch-LWE
advantage imply negligible adaptive TFHE advantage.  The two displayed closure obligations state
that the honest and uniform-BRK reductions preserve the selected efficient-adversary classes.
No refresh-correctness hypothesis or conclusion occurs in this theorem. -/
theorem secureAgainst_of_nativeCircularLWE_and_batchLWE
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          family.parameters adversary))
    (hUniformBootstrapBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
          family.parameters adversary))
    (hCircularLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
        family.parameters).secureAgainst isPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        family.parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT := by
  exact family.secureAgainst_of_circularLWE_and_batchLWE
    (fun _ ↦ rfl) isPPT batchLWEIsPPT hBatchLWEClosed
      hUniformBootstrapBatchLWEClosed hCircularLWE hBatchLWE

/-- **Fully explicit primary TFHE security theorem.**

This version replaces the generic ordinary-LWE game by the definitionally equal concrete
binary-secret problem with modulus `64N^6`, dimension `N`, `6N+Q` samples, and centered-binomial
width `λ+1`.  Thus its only computational hypotheses are the exact native auxiliary-input CircLWE
game and this explicitly parameterized conventional LWE family. -/
theorem secureAgainst_of_nativeCircularLWE_and_concreteBatchLWE
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          family.parameters adversary))
    (hUniformBootstrapBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
          family.parameters adversary))
    (hCircularLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
        family.parameters).secureAgainst isPPT)
    (hConcreteBatchLWE :
      concreteBatchLWESecurityGame.secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT := by
  apply secureAgainst_of_nativeCircularLWE_and_batchLWE
    isPPT batchLWEIsPPT hBatchLWEClosed hUniformBootstrapBatchLWEClosed hCircularLWE
  rw [← concreteBatchLWESecurityGame_eq_batchLWE]
  exact hConcreteBatchLWE

/-- **Concrete TFHE security after arbitrary public evaluation.**

The public evaluator may use the complete native circular cloud key and may return any fixed
output type.  Its security loss is exactly zero: an evaluated-output adversary is compiled into
the base adaptive game, then the concrete native auxiliary-input CircLWE and binary-secret
centered-binomial LWE theorem above is applied.  The evaluation-efficiency closure is the only new
premise; correctness is neither assumed nor concluded. -/
theorem evaluationSecureAgainst_of_nativeCircularLWE_and_concreteBatchLWE
    {Output : Type}
    (evaluate : Encryption.Adaptive.Asymptotic.PublicEvaluatorFamily
      (Output := Output) family.parameters)
    (baseIsPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (evaluationIsPPT :
      Encryption.Adaptive.Asymptotic.PolynomialQueryEvaluationAdversary
        (Output := Output) family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (Encryption.Adaptive.Asymptotic.compileEvaluationAdversary
          family.parameters evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          family.parameters adversary))
    (hUniformBootstrapBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
          family.parameters adversary))
    (hCircularLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
        family.parameters).secureAgainst baseIsPPT)
    (hConcreteBatchLWE :
      concreteBatchLWESecurityGame.secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.evaluationSecurityGame
      family.parameters evaluate).secureAgainst evaluationIsPPT := by
  apply Encryption.Adaptive.Asymptotic.evaluationSecureAgainst_of_security
    family.parameters evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact secureAgainst_of_nativeCircularLWE_and_concreteBatchLWE
    baseIsPPT batchLWEIsPPT hBatchLWEClosed hUniformBootstrapBatchLWEClosed
    hCircularLWE hConcreteBatchLWE

/-! ## Packaged security-only foundation -/

/-- The complete computational foundation consumed by the primary growing-noise TFHE
confidentiality theorem.

This structure deliberately contains no decoding, refresh, noise-margin, or correctness field.
Its scheme-specific premise is the exact native auxiliary-input CircLWE game; its conventional
premise is the fully explicit centered-binomial binary-secret LWE family.  The remaining fields
only state that the two concrete reductions preserve the caller's chosen efficient-adversary
classes. -/
structure CircularConfidentialityFoundation
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop) : Prop where
  batchLWEClosed : ∀ adversary, isPPT adversary →
    batchLWEIsPPT
      (Encryption.Adaptive.Asymptotic.batchLWEReduction
        family.parameters adversary)
  uniformBootstrapBatchLWEClosed : ∀ adversary, isPPT adversary →
    batchLWEIsPPT
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
        family.parameters adversary)
  nativeCircularLWE :
    (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
      family.parameters).secureAgainst isPPT
  concreteBatchLWE :
    concreteBatchLWESecurityGame.secureAgainst batchLWEIsPPT

/-- A packaged circular-confidentiality foundation implies adaptive TFHE confidentiality.  This
is the primary security-only theorem with the bookkeeping hypotheses collected into one explicit
object. -/
theorem secureAgainst_of_circularConfidentialityFoundation
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (foundation : CircularConfidentialityFoundation isPPT batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
      family.parameters).secureAgainst isPPT :=
  secureAgainst_of_nativeCircularLWE_and_concreteBatchLWE
    isPPT batchLWEIsPPT foundation.batchLWEClosed
    foundation.uniformBootstrapBatchLWEClosed foundation.nativeCircularLWE
    foundation.concreteBatchLWE

/-- Arbitrary public TFHE evaluation preserves confidentiality from the same packaged
security-only foundation.  The evaluator contributes only the standard efficiency-closure
obligation and no correctness premise. -/
theorem evaluationSecureAgainst_of_circularConfidentialityFoundation
    {Output : Type}
    (evaluate : Encryption.Adaptive.Asymptotic.PublicEvaluatorFamily
      (Output := Output) family.parameters)
    (baseIsPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (evaluationIsPPT :
      Encryption.Adaptive.Asymptotic.PolynomialQueryEvaluationAdversary
        (Output := Output) family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (Encryption.Adaptive.Asymptotic.compileEvaluationAdversary
          family.parameters evaluate adversary))
    (foundation : CircularConfidentialityFoundation baseIsPPT batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.evaluationSecurityGame
      family.parameters evaluate).secureAgainst evaluationIsPPT := by
  apply Encryption.Adaptive.Asymptotic.evaluationSecureAgainst_of_security
    family.parameters evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact secureAgainst_of_circularConfidentialityFoundation
    baseIsPPT batchLWEIsPPT foundation

/-- **Concrete pointwise TFHE confidentiality bound.**

For the growing centered-binomial family, every adaptive TFHE adversary and every finite-view
schedule is bounded by one exact native auxiliary-input CircLWE term, one conventional scalar
search-LWE term, the explicit amplification loss, two exact power-of-two cyclotomic-RLWE terms,
and the adaptive input-LWE term.  The two post-cut transports have zero representation loss, and
the centered-binomial sampler-totality and equal-scalar-noise premises are discharged here.
-/
theorem
    securityGame_advantage_le_nativeCircular_add_ordinarySearchLwe_add_finiteLoss_add_two_cyclotomicRLWE_add_inputLWE
    (schedule : PolynomialViewSchedule family.parameters)
    (threshold : ThresholdFamily family.parameters)
    (hthreshold_pos : ∀ adversary securityParameter,
      0 < threshold adversary securityParameter)
    (hthreshold_one : ∀ adversary securityParameter,
      threshold adversary securityParameter ≤ 1)
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      (Encryption.Adaptive.KeySwitchFirstFiniteView.viewCount
          (family.parameters.lweDimension securityParameter)
          (schedule.rounds securityParameter) : ENNReal) *
        (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
          family.parameters).advantage
          (nativeCircularBatchReductionFamily family.parameters schedule
            (bootstrapBatchCircularReduction family.parameters schedule
              (searchReduction family.parameters schedule adversary))) securityParameter +
      (ordinarySideSearchLWESecurityGame family.parameters schedule).advantage
        (ordinarySideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)) securityParameter +
      (lossSecurityGame family.parameters schedule threshold).advantage
        adversary securityParameter +
      postCutCyclotomicRLWESecurityGame.advantage
        (postCutBinaryToCyclotomicReduction
          (realRingBatchReduction family.parameters adversary)) securityParameter +
      postCutCyclotomicRLWESecurityGame.advantage
        (postCutBinaryToCyclotomicReduction
          (zeroRingBatchReduction family.parameters adversary)) securityParameter +
      (inputBatchLWESecurityGame family.parameters).advantage
        (inputBatchLWEReduction family.parameters adversary) securityParameter := by
  have h :=
    securityGame_advantage_le_nativeCircular_add_ordinarySearchLwe_add_finiteLoss_add_postCut
      family.parameters family.keySwitchError_probFailure scalarSamplers_eq schedule
        threshold hthreshold_pos hthreshold_one adversary securityParameter
  simpa only [← postCutBinarySecretRLWESecurityGame_eq_ringBatchLWE,
    postCutBinarySecretRLWE_advantage_eq_cyclotomic] using h

/-! ## Exact input and output margins -/

/-- The growing input-error support stays strictly inside one half of the first rotation region. -/
theorem inputMargin (securityParameter : ℕ) :
    2 * errorWidth securityParameter < rotationDegree securityParameter + 1 := by
  rw [rotationDegree_add_one]
  have hwidthPos : 0 < errorWidth securityParameter := by
    simp [errorWidth]
  calc
    2 * errorWidth securityParameter < 8 * errorWidth securityParameter := by omega
    _ = targetDegree securityParameter := by rfl
    _ ≤ ringDegree securityParameter := targetDegree_le_ringDegree securityParameter

/-- Positive quarter-modulus output code. -/
def zeroCode (securityParameter : ℕ) : ZMod (coefficientModulus securityParameter) :=
  (16 * ringDegree securityParameter ^ 6 : ℕ)

/-- Opposite quarter-modulus output code. -/
def oneCode (securityParameter : ℕ) : ZMod (coefficientModulus securityParameter) :=
  -zeroCode securityParameter

@[simp]
theorem oneCode_eq_neg_zeroCode (securityParameter : ℕ) :
    oneCode securityParameter = -zeroCode securityParameter := rfl

/-- The output codewords have maximal centered distance `q/2 = 32N^6`. -/
theorem centeredDistance_zeroCode_oneCode (securityParameter : ℕ) :
    BootstrappingCorrectness.centeredDistance
        (zeroCode securityParameter) (oneCode securityParameter) =
      32 * ringDegree securityParameter ^ 6 := by
  have hdiff :
      zeroCode securityParameter - oneCode securityParameter =
        ((32 * ringDegree securityParameter ^ 6 : ℕ) :
          ZMod (coefficientModulus securityParameter)) := by
    simp only [oneCode, sub_neg_eq_add, zeroCode]
    push_cast
    ring
  rw [BootstrappingCorrectness.centeredDistance, hdiff]
  have hmodulus : coefficientModulus securityParameter =
      2 * (32 * ringDegree securityParameter ^ 6) := by
    unfold coefficientModulus
    ring_nf
  have hzlo :
      -(coefficientModulus securityParameter : ℤ) <
        ((32 * ringDegree securityParameter ^ 6 : ℕ) : ℤ) * 2 := by
    have hmodulusPosNat : 0 < coefficientModulus securityParameter := by
      exact Nat.mul_pos (by norm_num) (Nat.pow_pos (ringDegree_pos securityParameter))
    have hmodulusPosInt : (0 : ℤ) < coefficientModulus securityParameter := by
      exact_mod_cast hmodulusPosNat
    have hright :
        (0 : ℤ) ≤ ((32 * ringDegree securityParameter ^ 6 : ℕ) : ℤ) * 2 := by
      exact mul_nonneg (Int.natCast_nonneg _) (by norm_num)
    omega
  have hzhi :
      ((32 * ringDegree securityParameter ^ 6 : ℕ) : ℤ) * 2 ≤
        coefficientModulus securityParameter := by
    rw [hmodulus]
    push_cast
    ring_nf
    rfl
  have hcentered := LatticeCrypto.centeredRepr_intCast_eq
    (q := coefficientModulus securityParameter)
    ((32 * ringDegree securityParameter ^ 6 : ℕ) : ℤ) hzlo hzhi
  have hcast :
      ((32 * ringDegree securityParameter ^ 6 : ℕ) :
          ZMod (coefficientModulus securityParameter)) =
        ((((32 * ringDegree securityParameter ^ 6 : ℕ) : ℤ)) :
          ZMod (coefficientModulus securityParameter)) := by
    norm_num
  rw [hcast]
  rw [hcentered]
  exact Int.natAbs_natCast _

/-- Closed form of the sharp deterministic BRK budget with growing row-error width. -/
theorem nativeLinearNoiseBudget_eq (securityParameter : ℕ) :
    BootstrappingCorrectness.nativeLinearNoiseBudget
        (rotationDegree securityParameter) 1
        (decomposition securityParameter).levels
        (decomposition securityParameter).base
        (ringDegree securityParameter) (errorWidth securityParameter) =
      24 * ringDegree securityParameter ^ 2 *
        (2 * ringDegree securityParameter - 1) * errorWidth securityParameter := by
  simp only [BootstrappingCorrectness.nativeLinearNoiseBudget,
    BootstrappingCorrectness.linearExternalProductNoiseBudget, decomposition]
  rw [rotationDegree_add_one]
  ring

/-- The complete worst-case BRK error fits strictly inside the quarter-modulus decoding radius
for every security parameter. -/
theorem outputMargin (securityParameter : ℕ) :
    2 * BootstrappingCorrectness.nativeLinearNoiseBudget
          (rotationDegree securityParameter) 1
          (decomposition securityParameter).levels
          (decomposition securityParameter).base
          (ringDegree securityParameter) (errorWidth securityParameter) <
      BootstrappingCorrectness.centeredDistance
        (zeroCode securityParameter) (oneCode securityParameter) := by
  rw [nativeLinearNoiseBudget_eq, centeredDistance_zeroCode_oneCode]
  have hdegree : 4 ≤ ringDegree securityParameter := by
    have htarget : 4 ≤ targetDegree securityParameter := by
      simp [targetDegree, errorWidth]
      omega
    exact htarget.trans (targetDegree_le_ringDegree securityParameter)
  have hdegreePos : 0 < ringDegree securityParameter := by omega
  have hwidthPos : 0 < errorWidth securityParameter := by
    simp [errorWidth]
  have hwidthLe : errorWidth securityParameter ≤ ringDegree securityParameter := by
    have htarget : errorWidth securityParameter ≤ targetDegree securityParameter := by
      unfold targetDegree
      have := hwidthPos
      omega
    exact htarget.trans (targetDegree_le_ringDegree securityParameter)
  have hsub : 2 * ringDegree securityParameter - 1 <
      2 * ringDegree securityParameter := by omega
  have hsquare : 16 ≤ ringDegree securityParameter ^ 2 := by
    calc
      16 = 4 * 4 := by norm_num
      _ ≤ ringDegree securityParameter * ringDegree securityParameter :=
        Nat.mul_le_mul hdegree hdegree
      _ = ringDegree securityParameter ^ 2 := by ring
  have hthree : 3 < ringDegree securityParameter ^ 2 := by omega
  calc
    2 * (24 * ringDegree securityParameter ^ 2 *
        (2 * ringDegree securityParameter - 1) * errorWidth securityParameter) =
        (48 * ringDegree securityParameter ^ 2) *
          (2 * ringDegree securityParameter - 1) * errorWidth securityParameter := by ring
    _ < (48 * ringDegree securityParameter ^ 2) *
          (2 * ringDegree securityParameter) * errorWidth securityParameter := by
      exact Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left hsub (by positivity)) hwidthPos
    _ = 96 * ringDegree securityParameter ^ 3 * errorWidth securityParameter := by ring
    _ ≤ 96 * ringDegree securityParameter ^ 3 * ringDegree securityParameter :=
      Nat.mul_le_mul_left _ hwidthLe
    _ = (32 * ringDegree securityParameter ^ 4) * 3 := by ring
    _ < (32 * ringDegree securityParameter ^ 4) *
          ringDegree securityParameter ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hthree (by positivity)
    _ = 32 * ringDegree securityParameter ^ 6 := by ring

/-! ## Probability-one refresh and conditional confidentiality -/

/-- Complete fresh Boolean refresh property for the growing-noise family. -/
def RefreshCorrect : Prop :=
  ∀ (securityParameter : ℕ),
    ∀ (lweSecret : BinarySecret (rotationDegree securityParameter + 1))
      (ringSecret : RingBinarySecret 1 (rotationDegree securityParameter + 1))
      (bit : Bool),
    Pr[(fun sample ↦
      CenteredBinomialDivisibleRefresh.bitTableBootstrappingResult
          (decomposition securityParameter)
          (rotationOrder_dvd_coefficientModulus securityParameter)
          sample.1 sample.2 ringSecret
          (zeroCode securityParameter) (oneCode securityParameter)
          (CenteredBinomialRefresh.firstHalfThreshold
            (rotationDegree securityParameter)) = bit) |
      CenteredBinomialDivisibleRefresh.freshInputAndBootstrappingKey
        (decomposition securityParameter)
        (errorWidth securityParameter) (errorWidth securityParameter)
        lweSecret ringSecret bit] = 1

/-- Growing centered-binomial noise still gives probability-one fresh Boolean refresh. -/
theorem refreshCorrect : RefreshCorrect := by
  intro securityParameter lweSecret ringSecret bit
  apply CenteredBinomialDivisibleRefresh.probEvent_fresh_bitTableBootstrappingResult_eq_one
    (decomposition securityParameter)
    (rotationOrder_dvd_coefficientModulus securityParameter)
    lweSecret ringSecret (zeroCode securityParameter) (oneCode securityParameter) bit
  · rfl
  · exact inputMargin securityParameter
  · simpa only [rotationDegree_add_one] using outputMargin securityParameter

/-- **Growing-noise TFHE security and concrete probability-one refresh.**

The confidentiality conclusion is the strongest checked native route: polynomially many BRKs
reduce to one auxiliary-input CircLWE challenge, equal KSK/input errors form one ordinary scalar
search-LWE batch, and all three post-cut terms are ordinary LWE games.  The second conclusion is
unconditional functional correctness for this growing-noise construction at every `λ`. -/
theorem secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT family.parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily family.parameters schedule
          (bootstrapBatchCircularReduction family.parameters schedule
            (searchReduction family.parameters schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        family.parameters).secureAgainst nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame family.parameters schedule).secureAgainst
        (ordinarySearchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT ∧
      RefreshCorrect :=
  ⟨family.secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
      polynomialEvaluationKeyGrowth
      (fun securityParameter ↦
        ⟨0, by simpa [family] using ringDegree_pos securityParameter⟩)
      scalarSamplers_eq isPPT nativeCircularIsPPT ordinarySearchIsPPT
      realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT
      hNativeCircularClosed hOrdinarySearchClosed hRealRingBatchClosed
      hZeroRingBatchClosed hInputBatchClosed hNativeCircular hOrdinarySearch
      hRealRingBatch hZeroRingBatch hInputBatch,
    refreshCorrect⟩

/-- **Growing-noise TFHE security stated with an exact binary-secret RLWE premise.**

Because this family has native ring rank one, both post-cut BRK reductions target the same
finite negacyclic RLWE problem: its secret polynomial has independently uniform Boolean
coefficients, it has
`lweDimension * TGSW.rowCount 1 tgswLevels` samples, and its errors are the family's growing
centered-binomial ring errors.  The checked game equality above transfers this single RLWE
hardness premise with no advantage loss.  This is deliberately distinct from uniform-secret
RLWE and leaves the native auxiliary-input CircLWE first hop explicit. -/
theorem secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_binarySecretRLWE
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT family.parameters)
    (postCutRLWEIsPPT : PostCutBinarySecretRLWEAdversaryFamily → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily family.parameters schedule
          (bootstrapBatchCircularReduction family.parameters schedule
            (searchReduction family.parameters schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealPostCutRLWEClosed : ∀ adversary, isPPT adversary →
      postCutRLWEIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroPostCutRLWEClosed : ∀ adversary, isPPT adversary →
      postCutRLWEIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        family.parameters).secureAgainst nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame family.parameters schedule).secureAgainst
        (ordinarySearchIsPPT schedule))
    (hPostCutRLWE :
      postCutBinarySecretRLWESecurityGame.secureAgainst postCutRLWEIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT ∧
      RefreshCorrect := by
  have hRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst postCutRLWEIsPPT := by
    rw [← postCutBinarySecretRLWESecurityGame_eq_ringBatchLWE]
    exact hPostCutRLWE
  exact secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe
    isPPT nativeCircularIsPPT ordinarySearchIsPPT postCutRLWEIsPPT
    postCutRLWEIsPPT inputBatchIsPPT hNativeCircularClosed hOrdinarySearchClosed
    hRealPostCutRLWEClosed hZeroPostCutRLWEClosed hInputBatchClosed hNativeCircular
    hOrdinarySearch hRingBatch hRingBatch hInputBatch

/-- **Growing-noise TFHE security from the exact order-`2N` cyclotomic RLWE game.**

The post-cut premise here is the standard quotient-ring presentation
`(Z/qZ)[X] / (Φ_(2N))`, where `N` is the family's power-of-two ring degree.  Its Boolean secret
and growing centered-binomial error laws are the exact pushforwards of the executable
coefficient laws.  The complete real and uniform transcript distributions, and hence every
adversary's distinguishing advantage, are preserved by the carrier equivalence.  The only
remaining computational premises are the displayed cyclotomic RLWE game, ordinary scalar LWE,
and the native auxiliary-input circular-LWE first hop. -/
theorem secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_cyclotomicRLWE
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT family.parameters)
    (postCutCyclotomicIsPPT : PostCutCyclotomicRLWEAdversaryFamily → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily family.parameters schedule
          (bootstrapBatchCircularReduction family.parameters schedule
            (searchReduction family.parameters schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealPostCutCyclotomicClosed : ∀ adversary, isPPT adversary →
      postCutCyclotomicIsPPT
        (postCutBinaryToCyclotomicReduction
          (realRingBatchReduction family.parameters adversary)))
    (hZeroPostCutCyclotomicClosed : ∀ adversary, isPPT adversary →
      postCutCyclotomicIsPPT
        (postCutBinaryToCyclotomicReduction
          (zeroRingBatchReduction family.parameters adversary)))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        family.parameters).secureAgainst nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame family.parameters schedule).secureAgainst
        (ordinarySearchIsPPT schedule))
    (hPostCutCyclotomic :
      postCutCyclotomicRLWESecurityGame.secureAgainst postCutCyclotomicIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT ∧
      RefreshCorrect := by
  let postCutBinaryIsPPT : PostCutBinarySecretRLWEAdversaryFamily → Prop :=
    fun adversary ↦ postCutCyclotomicIsPPT
      (postCutBinaryToCyclotomicReduction adversary)
  have hPostCutBinary :
      postCutBinarySecretRLWESecurityGame.secureAgainst postCutBinaryIsPPT := by
    exact postCutBinarySecretRLWESecurityGame_secureAgainst_of_cyclotomic
      postCutCyclotomicIsPPT hPostCutCyclotomic
  exact
    secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_binarySecretRLWE
      isPPT nativeCircularIsPPT ordinarySearchIsPPT postCutBinaryIsPPT inputBatchIsPPT
      hNativeCircularClosed hOrdinarySearchClosed hRealPostCutCyclotomicClosed
      hZeroPostCutCyclotomicClosed hInputBatchClosed hNativeCircular hOrdinarySearch
      hPostCutBinary hInputBatch

/-- **Security-only growing-noise TFHE endpoint.**

This derives confidentiality directly from the generic security reduction, without using the
refresh-correctness theorem.  Native auxiliary-input CircLWE remains the explicit assumption for
the intact heterogeneous BRK/KSK cycle; the other hypotheses are ordinary scalar search/LWE and
the exact binary-secret centered-binomial cyclotomic-RLWE game. -/
theorem secureAgainst_of_nativeCircular_ordinarySearchLwe_cyclotomicRLWE
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT family.parameters)
    (postCutCyclotomicIsPPT : PostCutCyclotomicRLWEAdversaryFamily → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily family.parameters schedule
          (bootstrapBatchCircularReduction family.parameters schedule
            (searchReduction family.parameters schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealPostCutCyclotomicClosed : ∀ adversary, isPPT adversary →
      postCutCyclotomicIsPPT
        (postCutBinaryToCyclotomicReduction
          (realRingBatchReduction family.parameters adversary)))
    (hZeroPostCutCyclotomicClosed : ∀ adversary, isPPT adversary →
      postCutCyclotomicIsPPT
        (postCutBinaryToCyclotomicReduction
          (zeroRingBatchReduction family.parameters adversary)))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        family.parameters).secureAgainst nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame family.parameters schedule).secureAgainst
        (ordinarySearchIsPPT schedule))
    (hPostCutCyclotomic :
      postCutCyclotomicRLWESecurityGame.secureAgainst postCutCyclotomicIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT := by
  let postCutBinaryIsPPT : PostCutBinarySecretRLWEAdversaryFamily → Prop :=
    fun adversary ↦ postCutCyclotomicIsPPT
      (postCutBinaryToCyclotomicReduction adversary)
  have hPostCutBinary :
      postCutBinarySecretRLWESecurityGame.secureAgainst postCutBinaryIsPPT :=
    postCutBinarySecretRLWESecurityGame_secureAgainst_of_cyclotomic
      postCutCyclotomicIsPPT hPostCutCyclotomic
  have hRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst postCutBinaryIsPPT := by
    rw [← postCutBinarySecretRLWESecurityGame_eq_ringBatchLWE]
    exact hPostCutBinary
  exact family.secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
    polynomialEvaluationKeyGrowth
    (fun securityParameter ↦
      ⟨0, by simpa [family] using ringDegree_pos securityParameter⟩)
    scalarSamplers_eq isPPT nativeCircularIsPPT ordinarySearchIsPPT
    postCutBinaryIsPPT postCutBinaryIsPPT inputBatchIsPPT
    hNativeCircularClosed hOrdinarySearchClosed hRealPostCutCyclotomicClosed
    hZeroPostCutCyclotomicClosed hInputBatchClosed hNativeCircular hOrdinarySearch
    hRingBatch hRingBatch hInputBatch

/-- **Growing-noise TFHE security from a coefficient structured-LWE premise.**

This is the coefficient-explicit form of the end-to-end theorem.  Its post-cut assumption is the
finite negacyclic problem with modulus `(2N)^6`, degree and sample dimensions fixed above,
independently uniform Boolean secret coefficients, explicit schoolbook negacyclic convolution,
and independent centered-binomial coefficient errors of width `λ+1`.  Exact transcript
equivalences transfer that premise to both native ring reductions with zero loss.  The intact
evaluation-key cycle remains the separately stated auxiliary-input CircLWE premise. -/
theorem secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_coefficientStructuredLWE
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT family.parameters)
    (postCutCoefficientIsPPT :
      PostCutCoefficientStructuredLWEAdversaryFamily → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily family.parameters schedule
          (bootstrapBatchCircularReduction family.parameters schedule
            (searchReduction family.parameters schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealPostCutCoefficientClosed : ∀ adversary, isPPT adversary →
      postCutCoefficientIsPPT
        (postCutRingToCoefficientReduction
          (realRingBatchReduction family.parameters adversary)))
    (hZeroPostCutCoefficientClosed : ∀ adversary, isPPT adversary →
      postCutCoefficientIsPPT
        (postCutRingToCoefficientReduction
          (zeroRingBatchReduction family.parameters adversary)))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        family.parameters).secureAgainst nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame family.parameters schedule).secureAgainst
        (ordinarySearchIsPPT schedule))
    (hPostCutCoefficient :
      postCutCoefficientStructuredLWESecurityGame.secureAgainst
        postCutCoefficientIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT ∧
      RefreshCorrect := by
  let postCutRingIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop :=
    fun adversary ↦ postCutCoefficientIsPPT
      (postCutRingToCoefficientReduction adversary)
  have hPostCutRing :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst postCutRingIsPPT := by
    exact ringBatchLWESecurityGame_secureAgainst_of_coefficientStructuredLWE
      postCutCoefficientIsPPT hPostCutCoefficient
  have hRealPostCutRingClosed : ∀ adversary, isPPT adversary →
      postCutRingIsPPT (realRingBatchReduction family.parameters adversary) := by
    intro adversary hEfficient
    exact hRealPostCutCoefficientClosed adversary hEfficient
  have hZeroPostCutRingClosed : ∀ adversary, isPPT adversary →
      postCutRingIsPPT (zeroRingBatchReduction family.parameters adversary) := by
    intro adversary hEfficient
    exact hZeroPostCutCoefficientClosed adversary hEfficient
  exact secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe
    isPPT nativeCircularIsPPT ordinarySearchIsPPT postCutRingIsPPT
    postCutRingIsPPT inputBatchIsPPT hNativeCircularClosed hOrdinarySearchClosed
    hRealPostCutRingClosed hZeroPostCutRingClosed hInputBatchClosed hNativeCircular
    hOrdinarySearch hPostCutRing hPostCutRing hInputBatch

end

end FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd
