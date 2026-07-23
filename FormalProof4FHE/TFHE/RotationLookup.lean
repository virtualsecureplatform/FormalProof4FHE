/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BootstrappingCorrectness

/-!
# Concrete TFHE Rotation Lookup

This file discharges the algebraic part of the ideal test-vector lookup used by native TFHE
bootstrapping.  In particular, executable signed monomials compose by addition of their
exponents modulo `2N`.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE

namespace RotationLookup

noncomputable section

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- The coefficient polynomial underlying an executable signed rotation monomial is sparse. -/
theorem toPolynomial_rotationMonomial {q degree : ℕ}
    (exponent : Fin (2 * (degree + 1))) :
    (LatticeCrypto.vectorBackend (ZMod q) (degree + 1)).toPolynomial
        (BlindRotation.rotationMonomial q degree exponent) =
      if exponent.val < degree + 1 then
        Polynomial.monomial exponent.val 1
      else
        Polynomial.monomial (exponent.val - (degree + 1)) (-1) := by
  classical
  simp only [LatticeCrypto.PolyBackend.toPolynomial]
  split_ifs with hexponent
  · let selected : Fin (degree + 1) := ⟨exponent.val, hexponent⟩
    change (∑ coefficient : Fin (degree + 1),
        Polynomial.monomial coefficient.val
          (LatticeCrypto.Poly.toPi
            (BlindRotation.rotationMonomial q degree exponent) coefficient)) = _
    rw [Finset.sum_eq_single selected]
    · rw [BlindRotation.rotationMonomial_coefficient]
      simp [hexponent, selected]
    · intro coefficient _ hne
      rw [BlindRotation.rotationMonomial_coefficient]
      have hval : coefficient.val ≠ exponent.val := by
        intro heq
        apply hne
        exact Fin.ext heq
      simp [hexponent, hval]
    · simp
  · have hlower : degree + 1 ≤ exponent.val := Nat.le_of_not_gt hexponent
    have hupper : exponent.val - (degree + 1) < degree + 1 := by omega
    let selected : Fin (degree + 1) :=
      ⟨exponent.val - (degree + 1), hupper⟩
    change (∑ coefficient : Fin (degree + 1),
        Polynomial.monomial coefficient.val
          (LatticeCrypto.Poly.toPi
            (BlindRotation.rotationMonomial q degree exponent) coefficient)) = _
    rw [Finset.sum_eq_single selected]
    · rw [BlindRotation.rotationMonomial_coefficient]
      simp [hexponent, selected]
    · intro coefficient _ hne
      rw [BlindRotation.rotationMonomial_coefficient]
      have hval : coefficient.val ≠ exponent.val - (degree + 1) := by
        intro heq
        apply hne
        exact Fin.ext heq
      simp [hexponent, hval]
    · simp

/-- In the semantic negacyclic quotient, the executable representative denotes `X^exponent`. -/
theorem quotientOf_rotationMonomial {q degree : ℕ}
    (exponent : Fin (2 * (degree + 1))) :
    RLWE.quotientOf (q := q) (Nat.succ_pos degree)
        (BlindRotation.rotationMonomial q degree exponent) =
      LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
        (Polynomial.X ^ exponent.val) := by
  change LatticeCrypto.NegacyclicQuotient.ofBackend
      (LatticeCrypto.vectorBackend (ZMod q) (degree + 1))
        (BlindRotation.rotationMonomial q degree exponent) = _
  simp only [LatticeCrypto.NegacyclicQuotient.ofBackend]
  change LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
      ((LatticeCrypto.vectorBackend (ZMod q) (degree + 1)).toPolynomial
        (BlindRotation.rotationMonomial q degree exponent)) = _
  rw [toPolynomial_rotationMonomial]
  by_cases hexponent : exponent.val < degree + 1
  · rw [if_pos hexponent]
    have hmonomial : Polynomial.monomial exponent.val (1 : ZMod q) =
        Polynomial.X ^ exponent.val := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp
    rw [hmonomial]
  · rw [if_neg hexponent]
    have hlower : degree + 1 ≤ exponent.val := Nat.le_of_not_gt hexponent
    let reduced := exponent.val - (degree + 1)
    have hsplit : reduced + (degree + 1) = exponent.val :=
      Nat.sub_add_cancel hlower
    have hmonomial : Polynomial.monomial reduced (-1 : ZMod q) =
        -(Polynomial.X ^ reduced) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp
    change LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
        (Polynomial.monomial reduced (-1 : ZMod q)) = _
    rw [hmonomial]
    simp only [LatticeCrypto.NegacyclicQuotient.ofPolynomial, map_neg]
    rw [← hsplit]
    exact (LatticeCrypto.mk_X_pow_add_n
      (R := ZMod q) (n := degree + 1) reduced).symm

/-- Two negacyclic sign changes make `X^(k + 2N)` equal to `X^k`. -/
theorem ofPolynomial_X_pow_add_two_mul {q degree : ℕ} (exponent : ℕ) :
    LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
        ((Polynomial.X : Polynomial (ZMod q)) ^
          (exponent + 2 * (degree + 1))) =
      LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
        ((Polynomial.X : Polynomial (ZMod q)) ^ exponent) := by
  change (Ideal.Quotient.mk _
      (Polynomial.X ^ (exponent + 2 * (degree + 1))) :
        RLWE.QuotientRq q (degree + 1)) = _
  calc
    Ideal.Quotient.mk _ (Polynomial.X ^ (exponent + 2 * (degree + 1))) =
        Ideal.Quotient.mk _
          (Polynomial.X ^ ((exponent + (degree + 1)) + (degree + 1))) := by
      congr 2
      omega
    _ = -(Ideal.Quotient.mk _
          (Polynomial.X ^ (exponent + (degree + 1)))) :=
      LatticeCrypto.mk_X_pow_add_n (R := ZMod q) (n := degree + 1)
        (exponent + (degree + 1))
    _ = -(-(Ideal.Quotient.mk _ (Polynomial.X ^ exponent))) := by
      rw [LatticeCrypto.mk_X_pow_add_n
        (R := ZMod q) (n := degree + 1) exponent]
    _ = Ideal.Quotient.mk _ (Polynomial.X ^ exponent) := neg_neg _

/-- Executable signed rotations form the cyclic group of exponents modulo `2N`. -/
theorem rotationMonomial_mul {q degree : ℕ} [NeZero q]
    (left right : Fin (2 * (degree + 1))) :
    BlindRotation.rotationMonomial q degree left *
        BlindRotation.rotationMonomial q degree right =
      BlindRotation.rotationMonomial q degree (left + right) := by
  apply RLWE.quotientOf_injective (q := q) (Nat.succ_pos degree)
  rw [show RLWE.quotientOf (q := q) (Nat.succ_pos degree)
        (BlindRotation.rotationMonomial q degree left *
          BlindRotation.rotationMonomial q degree right) =
      RLWE.quotientOf (q := q) (Nat.succ_pos degree)
          (BlindRotation.rotationMonomial q degree left) *
        RLWE.quotientOf (q := q) (Nat.succ_pos degree)
          (BlindRotation.rotationMonomial q degree right) by
    change RLWE.quotientOf (q := q) (Nat.succ_pos degree)
        ((RLWE.negacyclicRing q (degree + 1)).mul
          (BlindRotation.rotationMonomial q degree left)
          (BlindRotation.rotationMonomial q degree right)) = _
    exact RLWE.quotientOf_mul (q := q) (Nat.succ_pos degree) _ _]
  rw [quotientOf_rotationMonomial, quotientOf_rotationMonomial,
    quotientOf_rotationMonomial]
  change (Ideal.Quotient.mk _ (Polynomial.X ^ left.val) :
      RLWE.QuotientRq q (degree + 1)) *
      Ideal.Quotient.mk _ (Polynomial.X ^ right.val) =
        Ideal.Quotient.mk _ (Polynomial.X ^ (left + right).val)
  rw [← map_mul, ← pow_add]
  rw [Fin.val_add_eq_ite]
  split_ifs with hwrap
  · let reduced := left.val + right.val - 2 * (degree + 1)
    have hsplit : reduced + 2 * (degree + 1) = left.val + right.val :=
      Nat.sub_add_cancel hwrap
    change LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
        ((Polynomial.X : Polynomial (ZMod q)) ^ (left.val + right.val)) =
      LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
        (Polynomial.X ^ reduced)
    calc
      LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
          (Polynomial.X ^ (left.val + right.val)) =
          LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
            (Polynomial.X ^ (reduced + 2 * (degree + 1))) := by rw [hsplit]
      _ = LatticeCrypto.NegacyclicQuotient.ofPolynomial (degree + 1)
          (Polynomial.X ^ reduced) :=
        ofPolynomial_X_pow_add_two_mul (q := q) (degree := degree) reduced
  · rfl

/-! ## Products of native rotation controls -/

/-- A rotation control together with its public exponent and ghost selector bit. -/
structure RotationSpec (q degree rank levels : ℕ) where
  exponent : Fin (2 * (degree + 1))
  bit : Bool
  bootstrapKeyEntry : RingGSWCiphertext q (degree + 1) rank levels

/-- Forget the explicit exponent after materializing its executable signed monomial. -/
def RotationSpec.toControl {q degree rank levels : ℕ}
    (spec : RotationSpec q degree rank levels) :
    BlindRotation.BitControl q degree rank levels where
  factor := BlindRotation.rotationMonomial q degree spec.exponent
  bit := spec.bit
  bootstrapKeyEntry := spec.bootstrapKeyEntry

/-- Sum the bit-selected exponents of a rotation trace modulo `2N`. -/
def selectedExponent {q degree rank levels : ℕ}
    (specs : List (RotationSpec q degree rank levels)) : Fin (2 * (degree + 1)) :=
  (specs.map fun spec ↦ if spec.bit then spec.exponent else 0).sum

/-- The ideal multiplier of explicit rotation controls is the monomial at their selected sum. -/
theorem idealMultiplier_map_toControl {q degree rank levels : ℕ} [NeZero q]
    (specs : List (RotationSpec q degree rank levels)) :
    BlindRotation.idealMultiplier (specs.map RotationSpec.toControl) =
      BlindRotation.rotationMonomial q degree (selectedExponent specs) := by
  induction specs with
  | nil =>
      simp [BlindRotation.idealMultiplier, selectedExponent,
        BlindRotation.rotationMonomial_zero]
  | cons spec specs ih =>
      simp only [List.map_cons, BlindRotation.idealMultiplier, selectedExponent,
        List.sum_cons, RotationSpec.toControl]
      rw [ih]
      cases hbit : spec.bit
      · simp only [Bool.false_eq_true, if_false, mul_one, zero_add]
        change BlindRotation.rotationMonomial q degree (selectedExponent specs) =
            BlindRotation.rotationMonomial q degree (selectedExponent specs)
        rfl
      · simp only [if_true]
        change BlindRotation.rotationMonomial q degree (selectedExponent specs) *
            BlindRotation.rotationMonomial q degree spec.exponent =
          BlindRotation.rotationMonomial q degree
            (spec.exponent + selectedExponent specs)
        rw [rotationMonomial_mul]
        congr 1
        exact add_comm _ _

/-- The explicit exponent/control data generated by every native scalar mask coordinate. -/
def nativeRotationSpecs {q degree rank lweDimension levels : ℕ}
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank levels lweDimension)
    (lweSecret : BinarySecret lweDimension) :
    List (RotationSpec q degree rank levels) :=
  List.ofFn fun coordinate ↦
    { exponent := -roundExponent (input.mask coordinate)
      bit := lweSecret coordinate
      bootstrapKeyEntry := bootstrappingKey coordinate }

/-- The native controls are exactly the exponent-annotated controls with annotations erased. -/
theorem map_toControl_nativeRotationSpecs
    {q degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension) :
    (nativeRotationSpecs roundExponent input bootstrappingKey lweSecret).map
        RotationSpec.toControl =
      BlindRotation.nativeControls params roundExponent input bootstrappingKey lweSecret := by
  unfold nativeRotationSpecs BlindRotation.nativeControls
  rw [← List.ofFn_comp']
  rfl

/-- Public rounded mask exponent selected by the ghost scalar secret bits. -/
def nativeMaskExponent {q degree lweDimension : ℕ}
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (lweSecret : BinarySecret lweDimension) : Fin (2 * (degree + 1)) :=
  ∑ coordinate, if lweSecret coordinate then
    -roundExponent (input.mask coordinate) else 0

/-- The list-level selected exponent is the corresponding finite-coordinate sum. -/
theorem selectedExponent_nativeRotationSpecs
    {q degree rank lweDimension levels : ℕ}
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank levels lweDimension)
    (lweSecret : BinarySecret lweDimension) :
    selectedExponent
        (nativeRotationSpecs roundExponent input bootstrappingKey lweSecret) =
      nativeMaskExponent roundExponent input lweSecret := by
  simp [selectedExponent, nativeRotationSpecs, nativeMaskExponent,
    List.sum_ofFn]

/-- The native ideal multiplier is one signed monomial at the selected rounded-mask exponent. -/
theorem idealMultiplier_nativeControls
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension) :
    BlindRotation.idealMultiplier
        (BlindRotation.nativeControls params roundExponent input
          bootstrappingKey lweSecret) =
      BlindRotation.rotationMonomial q degree
        (nativeMaskExponent roundExponent input lweSecret) := by
  rw [← map_toControl_nativeRotationSpecs params roundExponent input
    bootstrappingKey lweSecret]
  rw [idealMultiplier_map_toControl]
  rw [selectedExponent_nativeRotationSpecs]

/-! ## A concrete rotated test-vector accumulator -/

/-- The rounded scalar phase exponent represented by native body and selected-mask rotations. -/
def nativePhaseExponent {q degree lweDimension : ℕ}
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (lweSecret : BinarySecret lweDimension) : Fin (2 * (degree + 1)) :=
  nativeMaskExponent roundExponent input lweSecret + roundExponent input.body

/-- A public noiseless accumulator whose body is the rounded body rotation of a test vector. -/
def testVectorAccumulator {q degree rank : ℕ} [NeZero q]
    (bodyExponent : Fin (2 * (degree + 1)))
    (testVector : RLWE.Rq q (degree + 1)) :
    RingCiphertext q (degree + 1) rank :=
  TLWE.trivial
    (BlindRotation.rotationMonomial q degree bodyExponent * testVector)

/-- The scalar table represented by constant-coefficient extraction from a negacyclic test
vector.  Its unavoidable anti-periodicity is made explicit by using exponents modulo `2N`. -/
def coefficientLookup {q degree : ℕ} [NeZero q]
    (testVector : RLWE.Rq q (degree + 1))
    (exponent : Fin (2 * (degree + 1))) : ZMod q :=
  SampleExtraction.constantCoefficient
    (BlindRotation.rotationMonomial q degree exponent * testVector)

/-- Reduce a signed exponent modulo `N`, forgetting which of the two negacyclic signs it carries. -/
def halfIndex {degree : ℕ}
    (exponent : Fin (2 * (degree + 1))) : Fin (degree + 1) :=
  ⟨exponent.val % (degree + 1), Nat.mod_lt _ (Nat.succ_pos degree)⟩

theorem halfIndex_val_of_lt {degree : ℕ}
    (exponent : Fin (2 * (degree + 1)))
    (hexponent : exponent.val < degree + 1) :
    (halfIndex exponent).val = exponent.val := by
  exact Nat.mod_eq_of_lt hexponent

theorem halfIndex_val_of_not_lt {degree : ℕ}
    (exponent : Fin (2 * (degree + 1)))
    (hexponent : ¬exponent.val < degree + 1) :
    (halfIndex exponent).val = exponent.val - (degree + 1) := by
  unfold halfIndex
  have hlower : degree + 1 ≤ exponent.val := Nat.le_of_not_gt hexponent
  change exponent.val % (degree + 1) = exponent.val - (degree + 1)
  rw [Nat.mod_eq_sub_mod hlower]
  apply Nat.mod_eq_of_lt
  omega

/-- Constant-coefficient lookup reads the reciprocal coefficient indexed by the first half of an
exponent, negating it exactly in the second half. -/
theorem coefficientLookup_eq_reciprocal {q degree : ℕ} [NeZero q]
    (testVector : RLWE.Rq q (degree + 1))
    (exponent : Fin (2 * (degree + 1))) :
    coefficientLookup testVector exponent =
      if exponent.val < degree + 1 then
        SampleExtraction.reciprocalCoefficients
          (LatticeCrypto.Poly.toPi testVector) (halfIndex exponent)
      else
        -(SampleExtraction.reciprocalCoefficients
          (LatticeCrypto.Poly.toPi testVector) (halfIndex exponent)) := by
  classical
  unfold coefficientLookup
  rw [SampleExtraction.constantCoefficient_mul]
  by_cases hexponent : exponent.val < degree + 1
  · rw [if_pos hexponent]
    let selected := halfIndex exponent
    have hselected : selected.val = exponent.val :=
      halfIndex_val_of_lt exponent hexponent
    rw [Finset.sum_eq_single selected]
    · rw [BlindRotation.rotationMonomial_coefficient]
      simp [hexponent, hselected, selected]
    · intro coefficient _ hne
      rw [BlindRotation.rotationMonomial_coefficient]
      have hval : coefficient.val ≠ exponent.val := by
        intro heq
        apply hne
        apply Fin.ext
        rw [hselected]
        exact heq
      simp [hexponent, hval]
    · simp
  · rw [if_neg hexponent]
    let selected := halfIndex exponent
    have hselected : selected.val = exponent.val - (degree + 1) :=
      halfIndex_val_of_not_lt exponent hexponent
    rw [Finset.sum_eq_single selected]
    · rw [BlindRotation.rotationMonomial_coefficient]
      simp [hexponent, hselected, selected]
    · intro coefficient _ hne
      rw [BlindRotation.rotationMonomial_coefficient]
      have hval : coefficient.val ≠ exponent.val - (degree + 1) := by
        intro heq
        apply hne
        apply Fin.ext
        rw [hselected]
        exact heq
      simp [hexponent, hval]
    · simp

/-- Negacyclic coefficient reversal is an involution. -/
theorem reciprocalCoefficients_involutive {R : Type} [AddGroup R] {degree : ℕ}
    (values : Fin (degree + 1) → R) :
    SampleExtraction.reciprocalCoefficients
        (SampleExtraction.reciprocalCoefficients values) = values := by
  funext coefficient
  refine Fin.cases ?_ (fun positive ↦ ?_) coefficient
  · rfl
  · simp only [SampleExtraction.reciprocalCoefficients_succ, Fin.rev_rev, neg_neg]

/-- Materialize any first-half lookup table as a concrete negacyclic test vector. -/
def testVectorFromHalfTable {q degree : ℕ}
    (table : Fin (degree + 1) → ZMod q) : RLWE.Rq q (degree + 1) :=
  LatticeCrypto.Poly.ofPi (SampleExtraction.reciprocalCoefficients table)

/-- The materialized vector's reciprocal coefficients recover the source table exactly. -/
theorem reciprocalCoefficients_testVectorFromHalfTable {q degree : ℕ}
    (table : Fin (degree + 1) → ZMod q) :
    SampleExtraction.reciprocalCoefficients
        (LatticeCrypto.Poly.toPi (testVectorFromHalfTable table)) = table := by
  rw [testVectorFromHalfTable, LatticeCrypto.Poly.toPi_ofPi]
  exact reciprocalCoefficients_involutive table

/-- A materialized first-half table evaluates directly in the first exponent half and with the
required negacyclic sign in the second half. -/
theorem coefficientLookup_testVectorFromHalfTable {q degree : ℕ} [NeZero q]
    (table : Fin (degree + 1) → ZMod q)
    (exponent : Fin (2 * (degree + 1))) :
    coefficientLookup (testVectorFromHalfTable table) exponent =
      if exponent.val < degree + 1 then table (halfIndex exponent)
      else -table (halfIndex exponent) := by
  rw [coefficientLookup_eq_reciprocal,
    reciprocalCoefficients_testVectorFromHalfTable]

/-- Extend a Boolean first-half table to all signed exponents by flipping the bit after the
negacyclic sign boundary. -/
def antiPeriodicBit {degree : ℕ}
    (firstHalfBit : Fin (degree + 1) → Bool)
    (exponent : Fin (2 * (degree + 1))) : Bool :=
  if exponent.val < degree + 1 then firstHalfBit (halfIndex exponent)
  else !(firstHalfBit (halfIndex exponent))

/-- Concrete TFHE test vector for a Boolean first-half table. -/
def bitTableTestVector {q degree : ℕ}
    (zeroCode oneCode : ZMod q)
    (firstHalfBit : Fin (degree + 1) → Bool) : RLWE.Rq q (degree + 1) :=
  testVectorFromHalfTable fun index ↦
    BootstrappingCorrectness.encodeBit zeroCode oneCode (firstHalfBit index)

/-- With opposite codewords, the concrete bit-table vector evaluates to its anti-periodic Boolean
extension at every signed exponent. -/
theorem coefficientLookup_bitTableTestVector {q degree : ℕ} [NeZero q]
    (zeroCode oneCode : ZMod q)
    (firstHalfBit : Fin (degree + 1) → Bool)
    (exponent : Fin (2 * (degree + 1)))
    (hopposite : oneCode = -zeroCode) :
    coefficientLookup (bitTableTestVector zeroCode oneCode firstHalfBit) exponent =
      BootstrappingCorrectness.encodeBit zeroCode oneCode
        (antiPeriodicBit firstHalfBit exponent) := by
  rw [bitTableTestVector, coefficientLookup_testVectorFromHalfTable]
  by_cases hexponent : exponent.val < degree + 1
  · simp [antiPeriodicBit, hexponent]
  · rw [if_neg hexponent]
    cases hbit : firstHalfBit (halfIndex exponent) <;>
      simp [antiPeriodicBit, BootstrappingCorrectness.encodeBit, hexponent, hbit, hopposite]

/-- The ideal native trace on a rotated trivial accumulator is exactly one scalar test-vector
lookup at the combined rounded phase exponent. -/
theorem idealExtractedPhase_testVectorAccumulator_nativeControls
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (testVector : RLWE.Rq q (degree + 1)) :
    BootstrappingCorrectness.idealExtractedPhase ringSecret
        (testVectorAccumulator (roundExponent input.body) testVector)
        (BlindRotation.nativeControls params roundExponent input
          bootstrappingKey lweSecret) =
      coefficientLookup testVector
        (nativePhaseExponent roundExponent input lweSecret) := by
  unfold BootstrappingCorrectness.idealExtractedPhase testVectorAccumulator
    coefficientLookup nativePhaseExponent
  rw [TLWE.phase_trivial]
  rw [idealMultiplier_nativeControls params roundExponent input
    bootstrappingKey lweSecret]
  rw [← mul_assoc, rotationMonomial_mul]

/-- End-to-end native TFHE correctness with the former polynomial trace equation replaced by a
single explicit scalar table entry of the public test vector. -/
theorem decode_nativeBlindRotate_apply_testVector
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (testVector : RLWE.Rq q (degree + 1))
    (zeroCode oneCode : ZMod q) (outputBit : Bool) (rowErrorBound : ℕ)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound)
    (hlookup : coefficientLookup testVector
        (nativePhaseExponent roundExponent input lweSecret) =
      BootstrappingCorrectness.encodeBit zeroCode oneCode outputBit)
    (hmargin :
      2 * BootstrappingCorrectness.nativeNoiseBudget degree rank params.levels params.base
          lweDimension rowErrorBound <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    BootstrappingCorrectness.decodeNearest zeroCode oneCode
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params roundExponent input
              bootstrappingKey
                (testVectorAccumulator (roundExponent input.body) testVector)))) =
      outputBit := by
  apply BootstrappingCorrectness.decode_nativeBlindRotate_apply params roundExponent input
    bootstrappingKey lweSecret ringSecret
      (testVectorAccumulator (roundExponent input.body) testVector)
    zeroCode oneCode outputBit rowErrorBound hrows
  · rw [idealExtractedPhase_testVectorAccumulator_nativeControls]
    exact hlookup
  · exact hmargin

/-! ## Exact finite phase rounding at modulus `2N` -/

/-- At the special finite modulus `q = 2N`, the canonical `ZMod`/`Fin` equivalence is an exact
exponent map.  This is a useful executable correctness instance and a baseline for later
approximate modulus switching. -/
def exactRoundExponent (degree : ℕ) :
    ZMod (2 * (degree + 1)) → Fin (2 * (degree + 1)) :=
  (ZMod.finEquiv (2 * (degree + 1))).symm

@[simp]
theorem finEquiv_exactRoundExponent (degree : ℕ)
    (value : ZMod (2 * (degree + 1))) :
    ZMod.finEquiv (2 * (degree + 1)) (exactRoundExponent degree value) = value :=
  (ZMod.finEquiv (2 * (degree + 1))).apply_symm_apply value

/-- Exact exponent arithmetic recovers the scalar TLWE phase: the body rotation plus all
bit-selected negative mask rotations is `b - <s,a>` modulo `2N`. -/
theorem nativePhaseExponent_exactRoundExponent
    {degree lweDimension : ℕ}
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (lweSecret : BinarySecret lweDimension) :
    nativePhaseExponent (exactRoundExponent degree) input lweSecret =
      exactRoundExponent degree
        (TLWE.phase (embedBinarySecret lweSecret) input) := by
  let exponentEquiv := ZMod.finEquiv (2 * (degree + 1))
  apply exponentEquiv.injective
  rw [finEquiv_exactRoundExponent]
  unfold nativePhaseExponent nativeMaskExponent
  simp only [map_add, map_sum, apply_ite, map_neg, map_zero]
  have hround (value : ZMod (2 * (degree + 1))) :
      exponentEquiv (exactRoundExponent degree value) = value :=
    finEquiv_exactRoundExponent degree value
  simp_rw [hround]
  have hterm (coordinate : Fin lweDimension) :
      (if lweSecret coordinate then -input.mask coordinate else 0) =
        -(embedBit (lweSecret coordinate) * input.mask coordinate) := by
    cases lweSecret coordinate <;> simp [embedBit]
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  unfold TLWE.phase dotProduct embedBinarySecret
  abel

/-- At modulus `2N`, the complete noiseless native trace is the test-vector table evaluated at
the exact scalar TLWE phase. -/
theorem idealExtractedPhase_exactRoundExponent
    {degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq (2 * (degree + 1)) (degree + 1))
    (testVector : RLWE.Rq (2 * (degree + 1)) (degree + 1)) :
    BootstrappingCorrectness.idealExtractedPhase ringSecret
        (testVectorAccumulator (exactRoundExponent degree input.body) testVector)
        (BlindRotation.nativeControls params (exactRoundExponent degree) input
          bootstrappingKey lweSecret) =
      coefficientLookup testVector
        (exactRoundExponent degree
          (TLWE.phase (embedBinarySecret lweSecret) input)) := by
  rw [idealExtractedPhase_testVectorAccumulator_nativeControls]
  rw [nativePhaseExponent_exactRoundExponent]

/-- **Concrete finite native TFHE correctness at `q = 2N`.** The lookup obligation now mentions
only the public test-vector table at the exact scalar TLWE phase; all control-product, accumulator,
blind-rotation noise, extraction, and nearest-codeword steps are discharged. -/
theorem decode_nativeBlindRotate_apply_exactRoundExponent
    {degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq (2 * (degree + 1)) (degree + 1))
    (testVector : RLWE.Rq (2 * (degree + 1)) (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1)))
    (outputBit : Bool) (rowErrorBound : ℕ)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError
          (R := RLWE.Rq (2 * (degree + 1)) (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit (2 * (degree + 1)) (degree + 1)
            (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound)
    (hlookup : coefficientLookup testVector
        (exactRoundExponent degree
          (TLWE.phase (embedBinarySecret lweSecret) input)) =
      BootstrappingCorrectness.encodeBit zeroCode oneCode outputBit)
    (hmargin :
      2 * BootstrappingCorrectness.nativeNoiseBudget degree rank params.levels params.base
          lweDimension rowErrorBound <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    BootstrappingCorrectness.decodeNearest zeroCode oneCode
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params (exactRoundExponent degree) input
              bootstrappingKey
                (testVectorAccumulator
                  (exactRoundExponent degree input.body) testVector)))) = outputBit := by
  apply decode_nativeBlindRotate_apply_testVector params (exactRoundExponent degree) input
    bootstrappingKey lweSecret ringSecret testVector zeroCode oneCode outputBit rowErrorBound hrows
  · rw [nativePhaseExponent_exactRoundExponent]
    exact hlookup
  · exact hmargin

/-- **Closed concrete Boolean-table correctness theorem.** At `q = 2N`, a materialized Boolean
first-half table with opposite codewords is bootstrapped to its anti-periodic extension.  The only
remaining assumptions are the already explicit bootstrapping-key row bound and code-distance
margin; there is no ideal-lookup or rounding premise. -/
theorem decode_nativeBlindRotate_apply_bitTable
    {degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq (2 * (degree + 1)) (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1)))
    (firstHalfBit : Fin (degree + 1) → Bool)
    (rowErrorBound : ℕ)
    (hopposite : oneCode = -zeroCode)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError
          (R := RLWE.Rq (2 * (degree + 1)) (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit (2 * (degree + 1)) (degree + 1)
            (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound)
    (hmargin :
      2 * BootstrappingCorrectness.nativeNoiseBudget degree rank params.levels params.base
          lweDimension rowErrorBound <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    BootstrappingCorrectness.decodeNearest zeroCode oneCode
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params (exactRoundExponent degree) input
              bootstrappingKey
                (testVectorAccumulator (exactRoundExponent degree input.body)
                  (bitTableTestVector zeroCode oneCode firstHalfBit))))) =
      antiPeriodicBit firstHalfBit
        (exactRoundExponent degree
          (TLWE.phase (embedBinarySecret lweSecret) input)) := by
  apply decode_nativeBlindRotate_apply_exactRoundExponent params input bootstrappingKey
    lweSecret ringSecret (bitTableTestVector zeroCode oneCode firstHalfBit)
      zeroCode oneCode
        (antiPeriodicBit firstHalfBit
          (exactRoundExponent degree
            (TLWE.phase (embedBinarySecret lweSecret) input)))
      rowErrorBound hrows
  · exact coefficientLookup_bitTableTestVector zeroCode oneCode firstHalfBit _ hopposite
  · exact hmargin

/-- Boolean-table correctness with the sharp linear signed-rotation noise budget. -/
theorem decode_nativeBlindRotate_apply_bitTable_linear
    {degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq (2 * (degree + 1)) (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1)))
    (firstHalfBit : Fin (degree + 1) → Bool)
    (rowErrorBound : ℕ)
    (hopposite : oneCode = -zeroCode)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError
          (R := RLWE.Rq (2 * (degree + 1)) (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit (2 * (degree + 1)) (degree + 1)
            (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound)
    (hmargin :
      2 * BootstrappingCorrectness.nativeLinearNoiseBudget degree rank
          params.levels params.base lweDimension rowErrorBound <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    BootstrappingCorrectness.decodeNearest zeroCode oneCode
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params (exactRoundExponent degree) input
              bootstrappingKey
                (testVectorAccumulator (exactRoundExponent degree input.body)
                  (bitTableTestVector zeroCode oneCode firstHalfBit))))) =
      antiPeriodicBit firstHalfBit
        (exactRoundExponent degree
          (TLWE.phase (embedBinarySecret lweSecret) input)) := by
  apply BootstrappingCorrectness.decode_nativeBlindRotate_apply_linear params
    (exactRoundExponent degree) input bootstrappingKey lweSecret ringSecret
    (testVectorAccumulator (exactRoundExponent degree input.body)
      (bitTableTestVector zeroCode oneCode firstHalfBit))
    zeroCode oneCode
    (antiPeriodicBit firstHalfBit
      (exactRoundExponent degree
        (TLWE.phase (embedBinarySecret lweSecret) input)))
    rowErrorBound hrows
  · rw [idealExtractedPhase_testVectorAccumulator_nativeControls]
    rw [nativePhaseExponent_exactRoundExponent]
    exact coefficientLookup_bitTableTestVector zeroCode oneCode firstHalfBit _ hopposite
  · exact hmargin

end

end RotationLookup

end FormalProof4FHE.TFHE
