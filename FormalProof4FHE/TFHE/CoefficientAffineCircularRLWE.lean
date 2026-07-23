/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInput
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleSquareFreeSecurity
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAuxiliaryInput

set_option autoImplicit false

/-!
# The Coefficient-Affine Diagonal Left by Shared-Randomness TFHE

After removing the square-free part of the shared-randomness self bootstrapping key, the
remaining mask-row message is linear in one Boolean coefficient of the master ring key.  This
linearity is coefficient linearity: the map selects one coefficient and places it at one output
coefficient.  It is not, in general, multiplication by a fixed public element of the
negacyclic ring.

This distinction is the precise boundary between the proved full-matrix linear circular-LWE
translation and the native rank-one RLWE challenge.  The core results below are deterministic
algebraic statements; the final section packages their exact real, zero, and auxiliary-input
games.  Neither part assumes or claims security of the remaining circular endpoint.
-/

open Matrix

namespace FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE

noncomputable section

open CoefficientStructuredLWE
open FullBRKQuadraticSpan
open SharedRandomnessOneCycle
open SharedRandomnessOneCycle.SquareFreeSecurity

/-- Move one selected input coefficient to one selected output coefficient and zero every other
output.  This is the elementary matrix `E_(output,input)` on coefficient vectors. -/
def coefficientTransfer {q degree : ℕ}
    (input output : Fin degree) :
    Coefficients q degree →ₗ[ZMod q] Coefficients q degree where
  toFun := fun value coefficient ↦
    if coefficient = output then value input else 0
  map_add' := by
    intro left right
    funext coefficient
    by_cases h : coefficient = output <;> simp [h]
  map_smul' := by
    intro scalar value
    funext coefficient
    by_cases h : coefficient = output <;> simp [h]

@[simp]
theorem coefficientTransfer_apply {q degree : ℕ}
    (input output : Fin degree) (value : Coefficients q degree)
    (coefficient : Fin degree) :
    coefficientTransfer input output value coefficient =
      if coefficient = output then value input else 0 :=
  rfl

/-- Negacyclic multiplication by a fixed public right factor is additive in its coefficient
vector input. -/
theorem negacyclicProduct_add_left {q degree : ℕ}
    (left right multiplier : Coefficients q degree) :
    negacyclicProduct (left + right) multiplier =
      negacyclicProduct left multiplier + negacyclicProduct right multiplier := by
  funext coefficient
  unfold negacyclicProduct LatticeCrypto.negacyclicConvCoeff
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro indices _
  by_cases houtput :
      (indices.1.val + indices.2.val) % degree = coefficient.val
  · by_cases hwrap : indices.1.val + indices.2.val < degree
    · simp [houtput, hwrap, add_mul]
    · simp [houtput, hwrap, add_mul]
      abel
  · simp [houtput]

/-- Negacyclic multiplication by a fixed public right factor commutes with coefficient scalars. -/
theorem negacyclicProduct_smul_left {q degree : ℕ}
    (scalar : ZMod q) (value multiplier : Coefficients q degree) :
    negacyclicProduct (scalar • value) multiplier =
      scalar • negacyclicProduct value multiplier := by
  funext coefficient
  simp [negacyclicProduct, LatticeCrypto.negacyclicConvCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro indices _
  by_cases houtput :
      (indices.1.val + indices.2.val) % degree = coefficient.val
  · by_cases hwrap : indices.1.val + indices.2.val < degree
    · simp [houtput, hwrap, mul_assoc]
    · simp [houtput, hwrap, mul_assoc]
  · simp [houtput]

/-- Coefficient-linear endomorphism induced by multiplication with one fixed public negacyclic
polynomial. -/
def rightNegacyclicMulLinear {q degree : ℕ}
    (multiplier : Coefficients q degree) :
    Coefficients q degree →ₗ[ZMod q] Coefficients q degree where
  toFun := fun value ↦ negacyclicProduct value multiplier
  map_add' := fun left right ↦ negacyclicProduct_add_left left right multiplier
  map_smul' := fun scalar value ↦ negacyclicProduct_smul_left scalar value multiplier

@[simp]
theorem rightNegacyclicMulLinear_apply {q degree : ℕ}
    (multiplier value : Coefficients q degree) :
    rightNegacyclicMulLinear multiplier value = negacyclicProduct value multiplier :=
  rfl

/-- Selecting one coefficient and then multiplying by a public gadget element remains one fixed
coefficient-linear operator. -/
def transferredRightMul {q degree : ℕ}
    (input output : Fin degree) (multiplier : Coefficients q degree) :
    Coefficients q degree →ₗ[ZMod q] Coefficients q degree :=
  (rightNegacyclicMulLinear multiplier).comp (coefficientTransfer input output)

@[simp]
theorem transferredRightMul_apply {q degree : ℕ}
    (input output : Fin degree) (multiplier value : Coefficients q degree) :
    transferredRightMul input output multiplier value =
      negacyclicProduct (coefficientTransfer input output value) multiplier :=
  rfl

/-- Ring polynomial containing one selected Boolean secret coefficient at one selected output
coordinate. -/
def selectedCoefficientPolynomial
    (q degree : ℕ) (input output : Fin degree)
    (secret : Fin degree → Bool) : RLWE.Rq q degree :=
  LatticeCrypto.Poly.ofPi
    (coefficientTransfer input output (binaryCoefficients q secret))

/-- Taking coefficients of the sparse polynomial gives exactly the coefficient-transfer linear
map. -/
@[simp]
theorem coefficientEquiv_selectedCoefficientPolynomial
    (q degree : ℕ) (input output : Fin degree)
    (secret : Fin degree → Bool) :
    coefficientEquiv q degree
        (selectedCoefficientPolynomial q degree input output secret) =
      coefficientTransfer input output (binaryCoefficients q secret) := by
  funext coefficient
  simp [coefficientEquiv, selectedCoefficientPolynomial]

/-- The rank-one native Boolean diagonal is exactly the coefficient projector `E_(i,i)`. -/
theorem diagonalCrossAtDegree_rankOne_eq_selectedCoefficientPolynomial
    (q degree : ℕ) (ringSecret : RingBinarySecret 1 degree)
    (coordinate : Fin degree) :
    diagonalCrossAtDegree q degree 1 ringSecret 0 coordinate 0 =
      selectedCoefficientPolynomial q degree coordinate coordinate
        (ringSecret 0) := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  simp [diagonalCrossAtDegree, selectedCoefficientPolynomial,
    coefficientTransfer, binaryCoefficients]

/-- Coefficient form of the preceding native-ring identity. -/
theorem coefficientEquiv_diagonalCrossAtDegree_rankOne
    (q degree : ℕ) (ringSecret : RingBinarySecret 1 degree)
    (coordinate : Fin degree) :
    coefficientEquiv q degree
        (diagonalCrossAtDegree q degree 1 ringSecret 0 coordinate 0) =
      coefficientTransfer coordinate coordinate
        (binaryCoefficients q (ringSecret 0)) := by
  rw [diagonalCrossAtDegree_rankOne_eq_selectedCoefficientPolynomial]
  exact coefficientEquiv_selectedCoefficientPolynomial q degree coordinate coordinate
    (ringSecret 0)

/-- The shared-randomness prefix diagonal is the same selected coefficient polynomial. -/
theorem prefixDiagonalCross_apply_eq_selectedCoefficientPolynomial
    (q prefixDimension suffixDimension : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    prefixDiagonalCross q prefixDimension suffixDimension ringSecret coordinate 0 =
      selectedCoefficientPolynomial q (prefixDimension + suffixDimension)
        (prefixCoefficient coordinate) (prefixCoefficient coordinate) (ringSecret 0) := by
  exact diagonalCrossAtDegree_rankOne_eq_selectedCoefficientPolynomial
    q (prefixDimension + suffixDimension) ringSecret (prefixCoefficient coordinate)

/-- After multiplication by a public gadget polynomial, the native mask-diagonal coordinate is
exactly the composed coefficient-linear operator `rightMul ∘ E_(i,i)`. -/
theorem coefficientEquiv_prefixDiagonalCross_mul
    (q prefixDimension suffixDimension : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension)
    (multiplier : RLWE.Rq q (prefixDimension + suffixDimension)) :
    coefficientEquiv q (prefixDimension + suffixDimension)
        (prefixDiagonalCross q prefixDimension suffixDimension ringSecret coordinate 0 *
          multiplier) =
      transferredRightMul (prefixCoefficient coordinate) (prefixCoefficient coordinate)
        (coefficientEquiv q (prefixDimension + suffixDimension) multiplier)
        (binaryCoefficients q (ringSecret 0)) := by
  rw [coefficientEquiv_mul,
    show coefficientEquiv q (prefixDimension + suffixDimension)
        (prefixDiagonalCross q prefixDimension suffixDimension ringSecret coordinate 0) =
      coefficientTransfer (prefixCoefficient coordinate) (prefixCoefficient coordinate)
        (binaryCoefficients q (ringSecret 0)) by
      rw [prefixDiagonalCross_apply_eq_selectedCoefficientPolynomial]
      exact coefficientEquiv_selectedCoefficientPolynomial q
        (prefixDimension + suffixDimension) (prefixCoefficient coordinate)
        (prefixCoefficient coordinate) (ringSecret 0)]
  rfl

/-- Coefficient zero in the nonempty master ring forced by a prefix coordinate. -/
def prefixConstantCoefficient {prefixDimension suffixDimension : ℕ}
    (coordinate : Fin prefixDimension) : Fin (prefixDimension + suffixDimension) :=
  ⟨0, by
    have := coordinate.isLt
    omega⟩

/-- The native constant-polynomial copy of a selected prefix bit is the elementary transfer from
that input coefficient to coefficient zero. -/
theorem selectedCoefficientPolynomial_prefix_constant_eq
    (q prefixDimension suffixDimension : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    selectedCoefficientPolynomial q (prefixDimension + suffixDimension)
        (prefixCoefficient coordinate) (prefixConstantCoefficient coordinate) (ringSecret 0) =
      embedConstantBit q (prefixDimension + suffixDimension)
        (prefixSecret ringSecret coordinate) := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change LatticeCrypto.Poly.toPi
      (selectedCoefficientPolynomial q (prefixDimension + suffixDimension)
        (prefixCoefficient coordinate) (prefixConstantCoefficient coordinate)
        (ringSecret 0)) coefficient =
    LatticeCrypto.Poly.toPi
      (embedConstantBit q (prefixDimension + suffixDimension)
        (prefixSecret ringSecret coordinate)) coefficient
  simp only [selectedCoefficientPolynomial, LatticeCrypto.Poly.toPi_ofPi,
    coefficientTransfer_apply, binaryCoefficients, embedConstantBit,
    embedBinaryPolynomial]
  by_cases hcoefficient : coefficient = prefixConstantCoefficient coordinate
  · subst coefficient
    simp [prefixConstantCoefficient, prefixSecret, prefixCoefficient]
  · have hvalue : coefficient.val ≠ 0 := by
      intro hzero
      apply hcoefficient
      apply Fin.ext
      simp [prefixConstantCoefficient, hzero]
    simp [hcoefficient, hvalue, embedBit]

/-- After gadget multiplication, the native body-diagonal term is the composed coefficient
operator `rightMul ∘ E_(0,i)`. -/
theorem coefficientEquiv_prefixConstantBit_mul
    (q prefixDimension suffixDimension : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension)
    (multiplier : RLWE.Rq q (prefixDimension + suffixDimension)) :
    coefficientEquiv q (prefixDimension + suffixDimension)
        (embedConstantBit q (prefixDimension + suffixDimension)
            (prefixSecret ringSecret coordinate) * multiplier) =
      transferredRightMul (prefixCoefficient coordinate) (prefixConstantCoefficient coordinate)
        (coefficientEquiv q (prefixDimension + suffixDimension) multiplier)
        (binaryCoefficients q (ringSecret 0)) := by
  rw [← selectedCoefficientPolynomial_prefix_constant_eq]
  rw [coefficientEquiv_mul, coefficientEquiv_selectedCoefficientPolynomial]
  rfl

/-! ## The exact coefficient-affine structured-LWE class -/

/-- A fixed public linear operator on negacyclic coefficient vectors. -/
abbrev CoefficientOperator (q degree : ℕ) :=
  Coefficients q degree →ₗ[ZMod q] Coefficients q degree

/-- Rank-one structured-LWE noiseless output augmented by an arbitrary fixed coefficient-linear
message.  This is the precise full-matrix-linear class containing the diagonal projector. -/
def coefficientAffineNoiseless {q degree sampleCount : ℕ}
    (operator : Fin sampleCount → CoefficientOperator q degree)
    (secret : Fin degree → Bool)
    (challenge : Challenge q degree 1 sampleCount) : Output q degree sampleCount :=
  fun sample ↦
    negacyclicProduct (binaryCoefficients q secret) (challenge 0 sample) +
      operator sample (binaryCoefficients q secret)

/-- The fixed diagonal table is a member of the coefficient-affine class. -/
def diagonalOperators {q degree sampleCount : ℕ}
    (coordinate : Fin sampleCount → Fin degree) :
    Fin sampleCount → CoefficientOperator q degree :=
  fun sample ↦ coefficientTransfer (coordinate sample) (coordinate sample)

@[simp]
theorem coefficientAffineNoiseless_diagonalOperators
    {q degree sampleCount : ℕ}
    (coordinate : Fin sampleCount → Fin degree)
    (secret : Fin degree → Bool)
    (challenge : Challenge q degree 1 sampleCount)
    (sample : Fin sampleCount) :
    coefficientAffineNoiseless (diagonalOperators coordinate) secret challenge sample =
      negacyclicProduct (binaryCoefficients q secret) (challenge 0 sample) +
        coefficientTransfer (coordinate sample) (coordinate sample)
          (binaryCoefficients q secret) :=
  rfl

/-- Ring-linear messages are absorbable into a rank-one challenge by a public translation. -/
theorem ringMultiplication_absorbs_into_challenge
    {R : Type} [CommRing R] (secret challenge multiplier : R) :
    secret * challenge + secret * multiplier = secret * (challenge + multiplier) := by
  rw [mul_add]

/-- A Boolean message map is absorbable by the usual rank-one RLWE challenge translation when
it is multiplication by one fixed public ring element. -/
def RingMultiplicationOnBinary
    (q degree : ℕ)
    (message : (Fin degree → Bool) → RLWE.Rq q degree) : Prop :=
  ∃ multiplier : RLWE.Rq q degree,
    ∀ secret, message secret = embedBinaryPolynomial q degree secret * multiplier

/-- Coefficient zero in every syntactic degree `extra + 2`. -/
def firstCoordinate (extra : ℕ) : Fin (extra + 2) :=
  ⟨0, by omega⟩

/-- Coefficient one in every syntactic degree `extra + 2`. -/
def secondCoordinate (extra : ℕ) : Fin (extra + 2) :=
  ⟨1, by omega⟩

/-- The Boolean basis polynomial at coefficient zero is the ring unit. -/
theorem embedBinaryPolynomial_single_first_eq_one
    (q extra : ℕ) [NeZero q] :
    embedBinaryPolynomial q (extra + 2)
        (TGSW.MonomialKDM.singleBit (firstCoordinate extra) true) = 1 := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change LatticeCrypto.Poly.toPi
      (embedBinaryPolynomial q (extra + 2)
        (TGSW.MonomialKDM.singleBit (firstCoordinate extra) true)) coefficient =
    LatticeCrypto.Poly.toPi (1 : RLWE.Rq q (extra + 2)) coefficient
  simp only [embedBinaryPolynomial, LatticeCrypto.Poly.toPi_ofPi]
  rw [BlindRotation.rq_one_coefficient]
  simp [TGSW.MonomialKDM.singleBit, firstCoordinate, embedBit]

/-- The zero-coordinate projector maps the Boolean basis at coefficient zero to the ring unit. -/
theorem selectedCoefficientPolynomial_single_first_eq_one
    (q extra : ℕ) [NeZero q] :
    selectedCoefficientPolynomial q (extra + 2)
        (firstCoordinate extra) (firstCoordinate extra)
        (TGSW.MonomialKDM.singleBit (firstCoordinate extra) true) = 1 := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change LatticeCrypto.Poly.toPi
      (selectedCoefficientPolynomial q (extra + 2)
        (firstCoordinate extra) (firstCoordinate extra)
        (TGSW.MonomialKDM.singleBit (firstCoordinate extra) true)) coefficient =
    LatticeCrypto.Poly.toPi (1 : RLWE.Rq q (extra + 2)) coefficient
  simp only [selectedCoefficientPolynomial, LatticeCrypto.Poly.toPi_ofPi,
    coefficientTransfer_apply, binaryCoefficients]
  rw [BlindRotation.rq_one_coefficient]
  simp [TGSW.MonomialKDM.singleBit, firstCoordinate, embedBit]

/-- The same projector kills the Boolean basis at coefficient one. -/
theorem selectedCoefficientPolynomial_single_second_eq_zero
    (q extra : ℕ) [NeZero q] :
    selectedCoefficientPolynomial q (extra + 2)
        (firstCoordinate extra) (firstCoordinate extra)
        (TGSW.MonomialKDM.singleBit (secondCoordinate extra) true) = 0 := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change LatticeCrypto.Poly.toPi
      (selectedCoefficientPolynomial q (extra + 2)
        (firstCoordinate extra) (firstCoordinate extra)
        (TGSW.MonomialKDM.singleBit (secondCoordinate extra) true)) coefficient =
    LatticeCrypto.Poly.toPi (0 : RLWE.Rq q (extra + 2)) coefficient
  simp only [selectedCoefficientPolynomial, LatticeCrypto.Poly.toPi_ofPi,
    coefficientTransfer_apply, binaryCoefficients]
  rw [BlindRotation.rq_zero_coefficient]
  simp [TGSW.MonomialKDM.singleBit, firstCoordinate, secondCoordinate, embedBit]

/-- The Boolean basis polynomial at coefficient one is nonzero whenever the coefficient ring is
nontrivial. -/
theorem embedBinaryPolynomial_single_second_ne_zero
    (q extra : ℕ) [NeZero q] (hq : (1 : ZMod q) ≠ 0) :
    embedBinaryPolynomial q (extra + 2)
        (TGSW.MonomialKDM.singleBit (secondCoordinate extra) true) ≠ 0 := by
  intro hzero
  have hcoefficient := congrArg
    (fun value : RLWE.Rq q (extra + 2) ↦
      LatticeCrypto.Poly.toPi value (secondCoordinate extra)) hzero
  apply hq
  simpa [embedBinaryPolynomial, TGSW.MonomialKDM.singleBit,
    secondCoordinate, embedBit] using hcoefficient

/-- **Native diagonal obstruction.**  In degree at least two, even the first diagonal
coefficient projector cannot be written, on Boolean secrets, as multiplication by a fixed
public negacyclic-ring element.  Thus its coefficient linearity is strictly more general than
the ring-linearity consumed by the ordinary rank-one RLWE challenge shift. -/
theorem firstDiagonal_not_ringMultiplicationOnBinary
    (q extra : ℕ) [NeZero q] (hq : (1 : ZMod q) ≠ 0) :
    ¬ RingMultiplicationOnBinary q (extra + 2)
      (selectedCoefficientPolynomial q (extra + 2)
        (firstCoordinate extra) (firstCoordinate extra)) := by
  rintro ⟨multiplier, hrepresentation⟩
  have hfirst := hrepresentation
    (TGSW.MonomialKDM.singleBit (firstCoordinate extra) true)
  rw [selectedCoefficientPolynomial_single_first_eq_one,
    embedBinaryPolynomial_single_first_eq_one, one_mul] at hfirst
  have hmultiplier : multiplier = 1 := hfirst.symm
  have hsecond := hrepresentation
    (TGSW.MonomialKDM.singleBit (secondCoordinate extra) true)
  rw [selectedCoefficientPolynomial_single_second_eq_zero, hmultiplier, mul_one] at hsecond
  exact embedBinaryPolynomial_single_second_ne_zero q extra hq hsecond.symm

/-- The obstruction applies directly to the rank-one native diagonal cross coordinate, rather
than only to its sparse-polynomial normal form. -/
theorem nativeFirstDiagonalCross_not_ringMultiplicationOnBinary
    (q extra : ℕ) [NeZero q] (hq : (1 : ZMod q) ≠ 0) :
    ¬ RingMultiplicationOnBinary q (extra + 2)
      (fun secret ↦
        diagonalCrossAtDegree q (extra + 2) 1 (fun _ ↦ secret) 0
          (firstCoordinate extra) 0) := by
  intro hnative
  apply firstDiagonal_not_ringMultiplicationOnBinary q extra hq
  rcases hnative with ⟨multiplier, hrepresentation⟩
  refine ⟨multiplier, fun secret ↦ ?_⟩
  rw [← diagonalCrossAtDegree_rankOne_eq_selectedCoefficientPolynomial
    q (extra + 2) (fun _ ↦ secret) (firstCoordinate extra)]
  exact hrepresentation secret

/-! ## Exact auxiliary-input circular problem for the diagonal-only BRK -/

namespace AuxiliaryInput

/-- The master binary ring key is the sole hidden key; the source scalar key is its prefix. -/
abbrev Secret (prefixDimension suffixDimension : ℕ) :=
  RingBinarySecret 1 (prefixDimension + suffixDimension)

/-- The complete diagonal-only BRK carrier. -/
abbrev Challenge
    (q prefixDimension suffixDimension tgswLevels : ℕ) :=
  SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels

/-- The retained real suffix-to-prefix KSK correlated with the same master key. -/
abbrev Auxiliary
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) :=
  SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels

/-- Fixed-side-information circular-RLWE problem whose real branch is exactly the diagonal-only
shared-randomness BRK, whose zero branch is the native zero BRK, and whose auxiliary input is the
unchanged real KSK. -/
noncomputable def problem
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    LWE.AuxiliaryInput.Problem
      (Secret prefixDimension suffixDimension)
      (Challenge q prefixDimension suffixDimension tgswLevels)
      (Auxiliary q prefixDimension suffixDimension keySwitchLevels) where
  sampleSecret := Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  sampleReal := fun ringSecret ↦
    generateDiagonalOnlyBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget ringSecret
  sampleZero := fun ringSecret ↦
    SharedRandomnessOneCycle.generateZeroBootstrappingKey q prefixDimension suffixDimension
      tgswLevels ringErrorSampler tgswGadget ringSecret
  sampleUniform :=
    $ᵗ (Challenge q prefixDimension suffixDimension tgswLevels)
  sampleAuxiliary := fun ringSecret ↦
    SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension suffixDimension
      keySwitchLevels keySwitchErrorSampler keySwitchGadget ringSecret

/-- Package a cloud-key adversary as a continuation that does not reveal the experiment's hidden
master key. -/
def packAdversary
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.Continuation
      (Secret prefixDimension suffixDimension)
      (Challenge q prefixDimension suffixDimension tgswLevels)
      (Auxiliary q prefixDimension suffixDimension keySwitchLevels) :=
  fun _ bootstrappingKey keySwitchKey ↦
    adversary ⟨bootstrappingKey, keySwitchKey⟩

/-- The generic real branch is definitionally the diagonal-only cloud-key game. -/
theorem realGame_eq_diagonalOnlyGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.realGame
        (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packAdversary adversary) =
      diagonalOnlyGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary := by
  simp [LWE.AuxiliaryInput.realGame, problem, packAdversary, diagonalOnlyGame,
    diagonalOnlyCloudKeyView, bind_assoc, monad_norm]

/-- The generic zero branch is definitionally the existing BRK-zero game with the same KSK. -/
theorem zeroGame_eq_bootstrapZeroGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.zeroGame
        (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packAdversary adversary) =
      bootstrapZeroGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary := by
  simp [LWE.AuxiliaryInput.zeroGame, problem, packAdversary, bootstrapZeroGame,
    bootstrapZeroCloudKeyView, generateBootstrapZeroCloudKey, bind_assoc, monad_norm]

/-- Real diagonal-only BRK versus uniform BRK, retaining the real KSK. -/
noncomputable def circularLweAdvantage
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  LWE.AuxiliaryInput.circularLweAdvantage
    (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (packAdversary adversary)

/-- Zero BRK versus uniform BRK, retaining the same real KSK. -/
noncomputable def zeroLweAdvantage
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  LWE.AuxiliaryInput.zeroLweAdvantage
    (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (packAdversary adversary)

/-- The generic fixed-hint KDM advantage is exactly the diagonal term in the checked one-cycle
factorization. -/
theorem kdmAdvantage_eq_diagonalAdvantage
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.kdmAdvantage
        (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packAdversary adversary) =
      diagonalAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary := by
  unfold LWE.AuxiliaryInput.kdmAdvantage diagonalAdvantage
  rw [realGame_eq_diagonalOnlyGame, zeroGame_eq_bootstrapZeroGame]

/-- The remaining diagonal term is bounded by its exact coefficient-affine circular-RLWE
endpoint plus the explicit zero-BRK side-information LWE endpoint. -/
theorem diagonalAdvantage_le_circularLwe_add_zeroLwe
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    diagonalAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤
      circularLweAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary +
        zeroLweAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary := by
  rw [← kdmAdvantage_eq_diagonalAdvantage]
  exact LWE.AuxiliaryInput.kdmAdvantage_le_circularLwe_add_zeroLwe _ _

/-- Refined one-cycle boundary after naming the diagonal endpoint: the intact native advantage
costs the fixed square-free table, coefficient-affine circular RLWE, and the explicit zero-BRK
side-information LWE term. -/
theorem oneCircularAdvantage_le_squareFree_add_circularLwe_add_zeroLwe
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    oneCircularAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤
      squareFreeAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary +
        (circularLweAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary +
          zeroLweAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary) := by
  exact (oneCircularAdvantage_le_squareFree_add_diagonal q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
    keySwitchGadget adversary).trans
      (add_le_add
        (le_refl (squareFreeAdvantage q prefixDimension suffixDimension tgswLevels
          keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget adversary))
        (diagonalAdvantage_le_circularLwe_add_zeroLwe q prefixDimension suffixDimension
          tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget adversary))

/-! ## Secret-continuation form used by adaptive FHE security

The public-cloud-key split above is enough to state one-circular key indistinguishability.  An
adaptive encryption proof, however, subsequently uses the hidden master key to create challenge
ciphertexts.  The following games therefore keep the same master key available to an arbitrary
continuation.  This is the form consumed by the asymptotic FHE theorem.
-/

/-- Diagonal-only BRK followed by an arbitrary continuation that may also use the master key. -/
noncomputable def diagonalOnlySecretContinuationGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ←
    generateDiagonalOnlyBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ←
    SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension suffixDimension
      keySwitchLevels keySwitchErrorSampler keySwitchGadget ringSecret
  continuation ringSecret bootstrappingKey keySwitchKey

/-- Split diagonal-plus-square-free BRK followed by a secret-dependent continuation. -/
noncomputable def splitSecretContinuationGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ←
    generateSplitBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ←
    SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension suffixDimension
      keySwitchLevels keySwitchErrorSampler keySwitchGadget ringSecret
  continuation ringSecret bootstrappingKey keySwitchKey

/-- The honest secret-continuation game is distributionally identical to the explicit
diagonal-plus-square-free presentation. -/
theorem realSecretContinuationGame_evalDist_eq_split
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    evalDist
        (SharedRandomnessOneCycle.realSecretContinuationGame q prefixDimension
          suffixDimension tgswLevels keySwitchLevels ringErrorSampler
          keySwitchErrorSampler tgswGadget keySwitchGadget continuation) =
      evalDist
        (splitSecretContinuationGame q prefixDimension suffixDimension tgswLevels
          keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget continuation) := by
  unfold SharedRandomnessOneCycle.realSecretContinuationGame splitSecretContinuationGame
  refine evalDist_bind_congr'
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) fun ringSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (generateBootstrappingKey_evalDist_eq_split q prefixDimension suffixDimension
      tgswLevels ringErrorSampler tgswGadget ringSecret)
    (fun bootstrappingKey ↦
      SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension suffixDimension
          keySwitchLevels keySwitchErrorSampler keySwitchGadget ringSecret >>=
        fun keySwitchKey ↦ continuation ringSecret bootstrappingKey keySwitchKey)

/-- Exact fixed square-free-table advantage in the secret-continuation experiment. -/
noncomputable def secretContinuationSquareFreeAdvantage
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  (SharedRandomnessOneCycle.realSecretContinuationGame q prefixDimension suffixDimension
      tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget continuation).boolDistAdvantage
    (diagonalOnlySecretContinuationGame q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      continuation)

/-- Package a native secret continuation into the diagonal-only auxiliary-input problem. -/
def packContinuation
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.Continuation
      (Secret prefixDimension suffixDimension)
      (Challenge q prefixDimension suffixDimension tgswLevels)
      (Auxiliary q prefixDimension suffixDimension keySwitchLevels) :=
  continuation

/-- The diagonal problem's real branch is exactly the diagonal-only secret-continuation game. -/
theorem realGame_eq_diagonalOnlySecretContinuationGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.realGame
        (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packContinuation continuation) =
      diagonalOnlySecretContinuationGame q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        continuation := by
  rfl

/-- The diagonal problem's uniform branch is the original one-cycle uniform-BRK experiment. -/
theorem uniformGame_eq_nativeSecretContinuationGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.uniformGame
        (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packContinuation continuation) =
      SharedRandomnessOneCycle.AuxiliaryInput.uniformSecretContinuationGame
        q prefixDimension suffixDimension tgswLevels keySwitchLevels
        keySwitchErrorSampler keySwitchGadget continuation := by
  rfl

/-- Diagonal-only coefficient-affine circular-RLWE advantage for a secret continuation. -/
noncomputable def secretContinuationCircularLweAdvantage
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  LWE.AuxiliaryInput.circularLweAdvantage
    (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (packContinuation continuation)

/-- **Finite FHE-context split.**  Native one-cycle circular RLWE in an arbitrary
secret-dependent continuation costs only the fixed square-free table and the exact
coefficient-affine diagonal circular-RLWE endpoint. -/
theorem nativeCircularLweAdvantage_le_squareFree_add_coefficientAffine
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    SharedRandomnessOneCycle.AuxiliaryInput.circularLweAdvantage
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget continuation ≤
      secretContinuationSquareFreeAdvantage q prefixDimension suffixDimension tgswLevels
          keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          continuation +
        secretContinuationCircularLweAdvantage q prefixDimension suffixDimension tgswLevels
          keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          continuation := by
  unfold SharedRandomnessOneCycle.AuxiliaryInput.circularLweAdvantage
    LWE.AuxiliaryInput.circularLweAdvantage
  rw [SharedRandomnessOneCycle.AuxiliaryInput.realGame_eq_native,
    SharedRandomnessOneCycle.AuxiliaryInput.uniformGame_eq_native]
  unfold secretContinuationSquareFreeAdvantage secretContinuationCircularLweAdvantage
    LWE.AuxiliaryInput.circularLweAdvantage
  rw [realGame_eq_diagonalOnlySecretContinuationGame,
    uniformGame_eq_nativeSecretContinuationGame]
  exact ProbComp.boolDistAdvantage_triangle
    (SharedRandomnessOneCycle.realSecretContinuationGame q prefixDimension suffixDimension
      tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget continuation)
    (diagonalOnlySecretContinuationGame q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      continuation)
    (SharedRandomnessOneCycle.AuxiliaryInput.uniformSecretContinuationGame q
      prefixDimension suffixDimension tgswLevels keySwitchLevels keySwitchErrorSampler
      keySwitchGadget continuation)

end AuxiliaryInput

end

end FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE
