/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareTopWeightLeakage

/-!
# Pair Structure of the Highest Two-Adic Square Leakage

For an even negacyclic ring dimension `N = 2M`, the highest two-adic leakage
`2^k S^2 mod 2^(k+1)` does not expose `N` independent Boolean coefficients.  The basis
coordinates `i` and `i + M` have opposite squares because `X^N = -1`; multiplication by
`2^k` identifies those signs.  Their two contributions consequently depend only on
`s_i xor s_(i+M)`.

This file proves the executable-ring identity and factors the complete leakage through the
`M` pair-XOR bits.  It sharpens the remaining joint security endpoint from arbitrary leakage
of the whole secret to an explicit half-dimensional quotient.  It does not assert that RLWE
remains hard under this leakage.
-/

open scoped BigOperators

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightPairLeakage

open FormalProof4FHE.TFHE
open FormalProof4FHE.TFHE.Native
open FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightCoefficientAffine
open FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightLeakage

noncomputable section

/-- If each half has dimension `half + 1`, this is the polynomial degree parameter for the
full even-dimensional ring.  Its ring dimension is definitionally the sum of the two halves. -/
abbrev evenDegree (half : ℕ) : ℕ := (half + 1) + half

/-- Embed a coordinate into the first half of an even-dimensional ring. -/
def firstOfPair (half : ℕ) (coordinate : Fin (half + 1)) :
    Fin (evenDegree half + 1) :=
  Fin.castAdd (half + 1) coordinate

/-- Embed the same coordinate into the second half of an even-dimensional ring. -/
def secondOfPair (half : ℕ) (coordinate : Fin (half + 1)) :
    Fin (evenDegree half + 1) :=
  Fin.natAdd (half + 1) coordinate

@[simp]
theorem firstOfPair_val (half : ℕ) (coordinate : Fin (half + 1)) :
    (firstOfPair half coordinate).val = coordinate.val := rfl

@[simp]
theorem secondOfPair_val (half : ℕ) (coordinate : Fin (half + 1)) :
    (secondOfPair half coordinate).val = half + 1 + coordinate.val := rfl

/-- One bit records whether the two antipodal secret coefficients differ. -/
def pairXor (half : ℕ) (secret : Fin (evenDegree half + 1) → Bool) :
    Fin (half + 1) → Bool :=
  fun coordinate ↦ Bool.xor
    (secret (firstOfPair half coordinate))
    (secret (secondOfPair half coordinate))

/-- The first coefficient in every antipodal pair. -/
def firstHalf (half : ℕ) (secret : Fin (evenDegree half + 1) → Bool) :
    Fin (half + 1) → Bool :=
  fun coordinate ↦ secret (firstOfPair half coordinate)

/-- Reconstruct all `2M` secret bits from the `M` pair-XOR bits and the `M` first-half bits. -/
def fromPairXorFirst (half : ℕ)
    (data : (Fin (half + 1) → Bool) × (Fin (half + 1) → Bool)) :
    Fin (evenDegree half + 1) → Bool :=
  Fin.append (m := half + 1) (n := half + 1) data.2
    (fun coordinate ↦ Bool.xor (data.2 coordinate) (data.1 coordinate))

/-- Splitting a binary polynomial into its pair-XOR quotient and first-half fiber coordinate is
an exact equivalence. -/
def pairXorEquiv (half : ℕ) :
    (Fin (evenDegree half + 1) → Bool) ≃
      ((Fin (half + 1) → Bool) × (Fin (half + 1) → Bool)) where
  toFun := fun secret ↦ (pairXor half secret, firstHalf half secret)
  invFun := fromPairXorFirst half
  left_inv := by
    intro secret
    funext coordinate
    refine Fin.addCases (m := half + 1) (n := half + 1) ?_ ?_ coordinate
    · intro first
      simp [fromPairXorFirst, firstHalf, firstOfPair]
    · intro second
      simp [fromPairXorFirst, firstHalf, pairXor, firstOfPair, secondOfPair]
      rw [← Fin.natAdd_eq_addNat (half + 1) second, Fin.append_right,
        Fin.natAdd_eq_addNat]
  right_inv := by
    rintro ⟨bits, first⟩
    apply Prod.ext
    · funext coordinate
      simp [fromPairXorFirst, pairXor, firstOfPair, secondOfPair]
      rw [← Fin.natAdd_eq_addNat (half + 1) coordinate, Fin.append_right]
      cases first coordinate <;> cases bits coordinate <;> rfl
    · funext coordinate
      simp [fromPairXorFirst, firstHalf, firstOfPair]

/-- Every pair-XOR vector occurs. -/
theorem pairXor_surjective (half : ℕ) :
    Function.Surjective (pairXor half) := by
  intro bits
  let first : Fin (half + 1) → Bool := fun _ ↦ false
  let secret := (pairXorEquiv half).symm (bits, first)
  refine ⟨secret, ?_⟩
  have hequal := (pairXorEquiv half).apply_symm_apply (bits, first)
  exact congrArg Prod.fst hequal

/-- Each fixed quotient fiber is exactly the freely chosen first half of the secret. -/
def pairXorFiberEquiv (half : ℕ) (bits : Fin (half + 1) → Bool) :
    {secret : Fin (evenDegree half + 1) → Bool // pairXor half secret = bits} ≃
      (Fin (half + 1) → Bool) where
  toFun := fun secret ↦ firstHalf half secret.1
  invFun := fun first ↦
    ⟨fromPairXorFirst half (bits, first), by
      have hequal := (pairXorEquiv half).apply_symm_apply (bits, first)
      exact congrArg Prod.fst hequal⟩
  left_inv := by
    intro secret
    apply Subtype.ext
    change fromPairXorFirst half (bits, firstHalf half secret.1) = secret.1
    calc
      _ = fromPairXorFirst half
          (pairXor half secret.1, firstHalf half secret.1) := by
        rw [secret.2]
      _ = secret.1 := (pairXorEquiv half).symm_apply_apply secret.1
  right_inv := by
    intro first
    have hequal := (pairXorEquiv half).apply_symm_apply (bits, first)
    exact congrArg Prod.snd hequal

/-- Every fixed pair-XOR value has exactly `2^(half+1)` compatible binary secrets. -/
theorem card_pairXor_fiber (half : ℕ) (bits : Fin (half + 1) → Bool) :
    Fintype.card
        {secret : Fin (evenDegree half + 1) → Bool // pairXor half secret = bits} =
      2 ^ (half + 1) := by
  rw [Fintype.card_congr (pairXorFiberEquiv half bits)]
  simp

/-- A uniformly sampled `2M`-bit secret has a uniformly sampled `M`-bit pair-XOR quotient.
The other `M` bits are the independent fiber coordinate supplied by `pairXorEquiv`. -/
theorem pairXor_uniform_evalDist (half : ℕ) :
    evalDist (pairXor half <$>
        ($ᵗ (Fin (evenDegree half + 1) → Bool))) =
      evalDist ($ᵗ (Fin (half + 1) → Bool)) := by
  have hequiv :
      evalDist (pairXorEquiv half <$>
          ($ᵗ (Fin (evenDegree half + 1) → Bool))) =
        evalDist ($ᵗ ((Fin (half + 1) → Bool) ×
          (Fin (half + 1) → Bool))) :=
    evalDist_map_bijective_uniform_cross
      (α := Fin (evenDegree half + 1) → Bool)
      (β := (Fin (half + 1) → Bool) × (Fin (half + 1) → Bool))
      (pairXorEquiv half) (pairXorEquiv half).bijective
  calc
    _ = evalDist (Prod.fst <$> (pairXorEquiv half <$>
        ($ᵗ (Fin (evenDegree half + 1) → Bool)))) := by
      simp [pairXorEquiv, Functor.map_map]
    _ = evalDist (Prod.fst <$> ($ᵗ ((Fin (half + 1) → Bool) ×
        (Fin (half + 1) → Bool)))) := by
      exact evalDist_map_eq_of_evalDist_eq hequiv Prod.fst
    _ = _ := evalDist_map_fst_uniformSample_prod

/-- Regard a ring coordinate as a positive signed-rotation exponent. -/
def coordinateExponent (degree : ℕ) (coordinate : Fin (degree + 1)) :
    Fin (2 * (degree + 1)) :=
  ⟨coordinate.val, by omega⟩

/-- A Boolean coefficient basis polynomial is the corresponding executable positive
negacyclic monomial. -/
theorem binaryBasis_eq_rotationMonomial
    (q degree : ℕ) [NeZero q] (coordinate : Fin (degree + 1)) :
    binaryBasis q (degree + 1) coordinate =
      BlindRotation.rotationMonomial q degree (coordinateExponent degree coordinate) := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro output
  change LatticeCrypto.Poly.toPi
      (binaryBasis q (degree + 1) coordinate) output =
    LatticeCrypto.Poly.toPi
      (BlindRotation.rotationMonomial q degree
        (coordinateExponent degree coordinate)) output
  unfold binaryBasis
  simp only [FormalProof4FHE.TFHE.embedBinaryPolynomial,
    LatticeCrypto.Poly.toPi_ofPi, FormalProof4FHE.TFHE.embedBit,
    FormalProof4FHE.TFHE.TGSW.MonomialKDM.singleBit]
  rw [BlindRotation.rotationMonomial_coefficient]
  have hcoordinate : coordinate.val < degree + 1 := coordinate.isLt
  by_cases houtput : output = coordinate
  · subst output
    simp [coordinateExponent, hcoordinate]
  · have hvalue : output.val ≠ coordinate.val := by
      intro heq
      apply houtput
      exact Fin.ext heq
    simp [coordinateExponent, hcoordinate, houtput, hvalue]

/-- The square of a first-half basis monomial has exponent `2 * coordinate`. -/
def firstSquareExponent (half : ℕ) (coordinate : Fin (half + 1)) :
    Fin (2 * (evenDegree half + 1)) :=
  ⟨2 * coordinate.val, by
    have hcoordinate := coordinate.isLt
    simp only [evenDegree]
    omega⟩

/-- The square of the antipodal second-half basis monomial is shifted by one full ring
dimension, hence represents the negative of the first square. -/
def secondSquareExponent (half : ℕ) (coordinate : Fin (half + 1)) :
    Fin (2 * (evenDegree half + 1)) :=
  ⟨2 * coordinate.val + (evenDegree half + 1), by
    have hcoordinate := coordinate.isLt
    simp only [evenDegree]
    omega⟩

theorem coordinateExponent_first_add_self
    (half : ℕ) (coordinate : Fin (half + 1)) :
    coordinateExponent (evenDegree half) (firstOfPair half coordinate) +
        coordinateExponent (evenDegree half) (firstOfPair half coordinate) =
      firstSquareExponent half coordinate := by
  apply Fin.ext
  rw [Fin.val_add_eq_of_add_lt]
  · simp [coordinateExponent, firstSquareExponent]
    omega
  · simp only [coordinateExponent, firstOfPair_val]
    simp only [evenDegree]
    omega

theorem coordinateExponent_second_add_self
    (half : ℕ) (coordinate : Fin (half + 1)) :
    coordinateExponent (evenDegree half) (secondOfPair half coordinate) +
        coordinateExponent (evenDegree half) (secondOfPair half coordinate) =
      secondSquareExponent half coordinate := by
  apply Fin.ext
  rw [Fin.val_add_eq_of_add_lt]
  · simp [coordinateExponent, secondSquareExponent]
    simp only [evenDegree]
    omega
  · simp only [coordinateExponent, secondOfPair_val]
    simp only [evenDegree]
    omega

/-- Before applying the top two-adic weight, antipodal basis squares differ by the
negacyclic sign. -/
theorem rotationMonomial_secondSquare_eq_neg_firstSquare
    (q half : ℕ) [NeZero q] (coordinate : Fin (half + 1)) :
    BlindRotation.rotationMonomial q (evenDegree half)
        (secondSquareExponent half coordinate) =
      -BlindRotation.rotationMonomial q (evenDegree half)
        (firstSquareExponent half coordinate) := by
  apply RLWE.quotientOf_injective (q := q) (Nat.succ_pos (evenDegree half))
  rw [RotationLookup.quotientOf_rotationMonomial]
  rw [show RLWE.quotientOf (q := q) (Nat.succ_pos (evenDegree half))
        (-BlindRotation.rotationMonomial q (evenDegree half)
          (firstSquareExponent half coordinate)) =
      -RLWE.quotientOf (q := q) (Nat.succ_pos (evenDegree half))
        (BlindRotation.rotationMonomial q (evenDegree half)
          (firstSquareExponent half coordinate)) by
    exact (RLWE.rqSemantics q (Nat.succ_pos (evenDegree half))).neg_sound _]
  rw [RotationLookup.quotientOf_rotationMonomial]
  change LatticeCrypto.NegacyclicQuotient.ofPolynomial (evenDegree half + 1)
      ((Polynomial.X : Polynomial (ZMod q)) ^
        (2 * coordinate.val + (evenDegree half + 1))) =
    -LatticeCrypto.NegacyclicQuotient.ofPolynomial (evenDegree half + 1)
      ((Polynomial.X : Polynomial (ZMod q)) ^ (2 * coordinate.val))
  exact LatticeCrypto.mk_X_pow_add_n
    (R := ZMod q) (n := evenDegree half + 1) (2 * coordinate.val)

/-- Squaring the two antipodal Boolean basis polynomials gives negatives of one another. -/
theorem binaryBasis_second_sq_eq_neg_first_sq
    (q half : ℕ) [NeZero q] (coordinate : Fin (half + 1)) :
    binaryBasis q (evenDegree half + 1) (secondOfPair half coordinate) ^ 2 =
      -(binaryBasis q (evenDegree half + 1) (firstOfPair half coordinate) ^ 2) := by
  rw [binaryBasis_eq_rotationMonomial, binaryBasis_eq_rotationMonomial,
    pow_two, pow_two, RotationLookup.rotationMonomial_mul,
    RotationLookup.rotationMonomial_mul,
    coordinateExponent_second_add_self,
    coordinateExponent_first_add_self]
  exact rotationMonomial_secondSquare_eq_neg_firstSquare q half coordinate

/-- The highest two-adic ring weight is fixed by negation modulo `2^(exponent+1)`. -/
theorem neg_topWeight_eq_topWeight (exponent degree : ℕ) :
    -topWeight exponent degree = topWeight exponent degree := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul]
  exact topWeight_annihilated exponent degree

/-- After multiplying by the highest two-adic weight, antipodal basis squares coincide. -/
theorem topWeight_mul_antipodalBasis_sq
    (exponent half : ℕ) (coordinate : Fin (half + 1)) :
    topWeight exponent (evenDegree half) *
        binaryBasis (2 ^ (exponent + 1)) (evenDegree half + 1)
          (secondOfPair half coordinate) ^ 2 =
      topWeight exponent (evenDegree half) *
        binaryBasis (2 ^ (exponent + 1)) (evenDegree half + 1)
          (firstOfPair half coordinate) ^ 2 := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [binaryBasis_second_sq_eq_neg_first_sq, mul_neg]
  calc
    -(topWeight exponent (evenDegree half) *
        binaryBasis (2 ^ (exponent + 1)) (evenDegree half + 1)
          (firstOfPair half coordinate) ^ 2) =
        (-topWeight exponent (evenDegree half)) *
          binaryBasis (2 ^ (exponent + 1)) (evenDegree half + 1)
            (firstOfPair half coordinate) ^ 2 := by rw [neg_mul]
    _ = _ := by rw [neg_topWeight_eq_topWeight]

/-- The weighted square attached to one first-half coordinate. -/
noncomputable def pairedBasisValue (exponent half : ℕ)
    (coordinate : Fin (half + 1)) :
    RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1) :=
  topWeight exponent (evenDegree half) *
    binaryBasis (2 ^ (exponent + 1)) (evenDegree half + 1)
      (firstOfPair half coordinate) ^ 2

/-- Two copies of a top-weighted basis square cancel. -/
theorem pairedBasisValue_add_self_eq_zero
    (exponent half : ℕ) (coordinate : Fin (half + 1)) :
    pairedBasisValue exponent half coordinate +
        pairedBasisValue exponent half coordinate = 0 := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [← two_mul]
  unfold pairedBasisValue
  rw [← mul_assoc, topWeight_annihilated, zero_mul]

/-- Output coordinate occupied by the square of a first-half basis monomial. -/
def pairOutput (half : ℕ) (coordinate : Fin (half + 1)) :
    Fin (evenDegree half + 1) :=
  ⟨2 * coordinate.val, by
    have hcoordinate := coordinate.isLt
    simp only [evenDegree]
    omega⟩

/-- A paired basis value is the top scalar times one positive rotation monomial. -/
theorem pairedBasisValue_eq_nsmul_rotation
    (exponent half : ℕ) (coordinate : Fin (half + 1)) :
    pairedBasisValue exponent half coordinate =
      (2 ^ exponent) •
        BlindRotation.rotationMonomial (2 ^ (exponent + 1)) (evenDegree half)
          (firstSquareExponent half coordinate) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  unfold pairedBasisValue topWeight
  rw [binaryBasis_eq_rotationMonomial, pow_two,
    RotationLookup.rotationMonomial_mul,
    coordinateExponent_first_add_self]
  simp only [nsmul_eq_mul]
  ring

/-- The selected square coordinate reads the top scalar for its own pair and zero for every
other pair. -/
theorem pairedBasisValue_coefficient
    (exponent half : ℕ) (source output : Fin (half + 1)) :
    CoefficientStructuredLWE.coefficientEquiv
        (2 ^ (exponent + 1)) (evenDegree half + 1)
        (pairedBasisValue exponent half source) (pairOutput half output) =
      if output = source then
        ((2 ^ exponent : ℕ) : ZMod (2 ^ (exponent + 1))) else 0 := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [pairedBasisValue_eq_nsmul_rotation]
  change Gadget.Base.coefficientAddHom (evenDegree half + 1) (pairOutput half output)
      ((2 ^ exponent) • BlindRotation.rotationMonomial
        (2 ^ (exponent + 1)) (evenDegree half)
          (firstSquareExponent half source)) = _
  rw [map_nsmul]
  simp only [Gadget.Base.coefficientAddHom_apply]
  rw [BlindRotation.rotationMonomial_coefficient]
  have hsource : 2 * source.val < evenDegree half + 1 := by
    simp only [evenDegree]
    omega
  by_cases hequal : output = source
  · subst output
    simp [firstSquareExponent, pairOutput, hsource]
  · have hvalue : 2 * output.val ≠ 2 * source.val := by
      intro hdouble
      apply hequal
      apply Fin.ext
      omega
    simp [firstSquareExponent, pairOutput, hsource, hequal, hvalue]

/-- Reconstruct the complete top-square leakage from one XOR bit per antipodal pair. -/
noncomputable def pairedTopSquare (exponent half : ℕ)
    (bits : Fin (half + 1) → Bool) :
    RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1) :=
  ∑ coordinate, if bits coordinate then pairedBasisValue exponent half coordinate else 0

/-- Each designated even coefficient recovers its corresponding pair-XOR bit times the nonzero
top scalar. -/
theorem pairedTopSquare_coefficient
    (exponent half : ℕ) (bits : Fin (half + 1) → Bool)
    (output : Fin (half + 1)) :
    CoefficientStructuredLWE.coefficientEquiv
        (2 ^ (exponent + 1)) (evenDegree half + 1)
        (pairedTopSquare exponent half bits) (pairOutput half output) =
      if bits output then
        ((2 ^ exponent : ℕ) : ZMod (2 ^ (exponent + 1))) else 0 := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  unfold pairedTopSquare
  rw [CoefficientStructuredLWE.coefficientEquiv_sum]
  rw [Finset.sum_apply]
  have hterm (source : Fin (half + 1)) :
      CoefficientStructuredLWE.coefficientEquiv
          (2 ^ (exponent + 1)) (evenDegree half + 1)
          (if bits source then pairedBasisValue exponent half source else 0)
          (pairOutput half output) =
        if bits source then
          if output = source then
            ((2 ^ exponent : ℕ) : ZMod (2 ^ (exponent + 1))) else 0
        else 0 := by
    cases hbit : bits source
    · simp [CoefficientStructuredLWE.coefficientEquiv_zero]
    · simp [pairedBasisValue_coefficient]
  simp_rw [hterm]
  rw [Finset.sum_eq_single output]
  · simp
  · intro source _ hsource
    simp [Ne.symm hsource]
  · simp

/-- The nonzero top scalar modulo the doubled power of two. -/
theorem topScalar_ne_zero (exponent : ℕ) :
    ((2 ^ exponent : ℕ) : ZMod (2 ^ (exponent + 1))) ≠ 0 := by
  have hpositive : 0 < 2 ^ exponent := pow_pos (by omega) _
  have hlt : 2 ^ exponent < 2 ^ (exponent + 1) := by
    rw [pow_succ]
    omega
  intro hzero
  exact (Nat.not_dvd_of_pos_of_lt hpositive hlt)
    ((ZMod.natCast_eq_zero_iff (2 ^ exponent) (2 ^ (exponent + 1))).mp hzero)

/-- The paired reconstruction is injective: the actual ring element contains exactly the
pair-XOR vector, not a further quotient of it. -/
theorem pairedTopSquare_injective (exponent half : ℕ) :
    Function.Injective (pairedTopSquare exponent half) := by
  intro left right hequal
  funext output
  have hcoefficient := congrArg
    (fun value ↦ CoefficientStructuredLWE.coefficientEquiv
      (2 ^ (exponent + 1)) (evenDegree half + 1) value (pairOutput half output))
    hequal
  rw [pairedTopSquare_coefficient, pairedTopSquare_coefficient] at hcoefficient
  cases hleft : left output <;> cases hright : right output
  · rfl
  · exfalso
    apply topScalar_ne_zero exponent
    simpa [hleft, hright] using hcoefficient.symm
  · exfalso
    apply topScalar_ne_zero exponent
    simpa [hleft, hright] using hcoefficient
  · rfl

/-- **Half-dimensional factorization of the highest two-adic square.**  In ring dimension
`2 * (half + 1)`, the full value `2^exponent * S^2` depends exactly through the pair-XOR
vector. -/
theorem topSquareLinearized_eq_pairedTopSquare
    (exponent half : ℕ)
    (secret : Fin (evenDegree half + 1) → Bool) :
    topSquareLinearized exponent (evenDegree half) secret =
      pairedTopSquare exponent half (pairXor half secret) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  classical
  unfold topSquareLinearized pairedTopSquare
  change (∑ coordinate : Fin ((half + 1) + (half + 1)),
      if secret coordinate then
        topWeight exponent (evenDegree half) *
          binaryBasis (2 ^ (exponent + 1)) (evenDegree half + 1) coordinate ^ 2
      else 0) = _
  rw [Fin.sum_univ_add (a := half + 1) (b := half + 1)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  change
    (if secret (firstOfPair half coordinate) then
        pairedBasisValue exponent half coordinate else 0) +
      (if secret (secondOfPair half coordinate) then
        topWeight exponent (evenDegree half) *
          binaryBasis (2 ^ (exponent + 1)) (evenDegree half + 1)
            (secondOfPair half coordinate) ^ 2 else 0) =
      if pairXor half secret coordinate then
        pairedBasisValue exponent half coordinate else 0
  rw [topWeight_mul_antipodalBasis_sq]
  change
    (if secret (firstOfPair half coordinate) then
        pairedBasisValue exponent half coordinate else 0) +
      (if secret (secondOfPair half coordinate) then
        pairedBasisValue exponent half coordinate else 0) =
      if pairXor half secret coordinate then
        pairedBasisValue exponent half coordinate else 0
  cases hfirst : secret (firstOfPair half coordinate) <;>
    cases hsecond : secret (secondOfPair half coordinate) <;>
    simp [hfirst, hsecond, pairXor,
      pairedBasisValue_add_self_eq_zero]

/-- Equal pair-XOR vectors give identical complete top-square leakage. -/
theorem topSquareLinearized_eq_of_pairXor_eq
    (exponent half : ℕ)
    (left right : Fin (evenDegree half + 1) → Bool)
    (hequal : pairXor half left = pairXor half right) :
    topSquareLinearized exponent (evenDegree half) left =
      topSquareLinearized exponent (evenDegree half) right := by
  rw [topSquareLinearized_eq_pairedTopSquare,
    topSquareLinearized_eq_pairedTopSquare, hequal]

/-! ## Factorization of the complete two-row auxiliary leakage -/

/-- Pair-XOR quotient of the single rank-one ring secret. -/
def ringPairXor (half : ℕ)
    (ringSecret : RingBinarySecret 1 (evenDegree half + 1)) :
    Fin (half + 1) → Bool :=
  pairXor half (ringSecret 0)

/-- Reconstruct the upper paired square and lower zero row solely from the pair-XOR vector. -/
noncomputable def pairedLeakage (exponent half : ℕ)
    (bits : Fin (half + 1) → Bool) : Leakage exponent (evenDegree half) :=
  fun row ↦
    if (TGSW.rowIndex row).1 = 0 then
      CoefficientStructuredLWE.coefficientEquiv
        (2 ^ (exponent + 1)) (evenDegree half + 1)
        (pairedTopSquare exponent half bits)
    else 0

/-- The complete upper/lower leakage reconstruction is injective in the pair-XOR vector. -/
theorem pairedLeakage_injective (exponent half : ℕ) :
    Function.Injective (pairedLeakage exponent half) := by
  intro left right hequal
  have hupper := congrFun hequal
    (TGSW.RingSquare.PreimageCompiler.Full.upperRow (0 : Fin 1))
  unfold pairedLeakage at hupper
  simp only [TGSW.RingSquare.PreimageCompiler.Full.rowIndex_upperRow,
    Fin.isValue, ↓reduceIte] at hupper
  apply pairedTopSquare_injective exponent half
  exact (CoefficientStructuredLWE.coefficientEquiv
    (2 ^ (exponent + 1)) (evenDegree half + 1)).injective hupper

/-- The complete structured auxiliary value in the joint security reduction factors through
only the antipodal pair-XOR vector. -/
theorem topLeakage_eq_pairedLeakage
    (exponent half : ℕ)
    (ringSecret : RingBinarySecret 1 (evenDegree half + 1)) :
    topLeakage exponent (evenDegree half) ringSecret =
      pairedLeakage exponent half (ringPairXor half ringSecret) := by
  funext row
  unfold topLeakage
  rw [← coefficientEquiv_topRGSWLinearizedMessages
    exponent (evenDegree half) (ringSecret 0) row]
  unfold pairedLeakage topRGSWLinearizedMessages ringPairXor
  split
  · rw [topSquareLinearized_eq_pairedTopSquare]
  · exact CoefficientStructuredLWE.coefficientEquiv_zero
      (2 ^ (exponent + 1)) (evenDegree half + 1)

/-- Secrets with the same pair-XOR quotient expose exactly the same complete top-square
auxiliary value. -/
theorem topLeakage_eq_of_ringPairXor_eq
    (exponent half : ℕ)
    (left right : RingBinarySecret 1 (evenDegree half + 1))
    (hequal : ringPairXor half left = ringPairXor half right) :
    topLeakage exponent (evenDegree half) left =
    topLeakage exponent (evenDegree half) right := by
  rw [topLeakage_eq_pairedLeakage, topLeakage_eq_pairedLeakage, hequal]

/-- The actual complete auxiliary leakage is equal exactly when the pair-XOR vectors are equal.
Thus it exposes precisely `N/2` Boolean quotient bits in even dimension `N`. -/
theorem topLeakage_eq_iff_ringPairXor_eq
    (exponent half : ℕ)
    (left right : RingBinarySecret 1 (evenDegree half + 1)) :
    topLeakage exponent (evenDegree half) left =
        topLeakage exponent (evenDegree half) right ↔
      ringPairXor half left = ringPairXor half right := by
  constructor
  · intro hequal
    rw [topLeakage_eq_pairedLeakage, topLeakage_eq_pairedLeakage] at hequal
    exact pairedLeakage_injective exponent half hequal
  · exact topLeakage_eq_of_ringPairXor_eq exponent half left right

/-! ## Exact joint security endpoint with `N/2` explicit quotient bits -/

/-- The auxiliary carrier containing exactly one XOR bit per antipodal secret pair. -/
abbrev PairAuxiliary (half : ℕ) := Fin (half + 1) → Bool

/-- Ordinary two-row binary-secret coefficient RLWE with only the exact pair-XOR quotient
exposed.  Its real and zero samplers coincide; no circular ciphertext is included in this
problem definition. -/
noncomputable def pairLeakageProblem
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1))) :
    LWE.AuxiliaryInput.Problem
      (RingBinarySecret 1 (evenDegree half + 1))
      (Transcript exponent (evenDegree half))
      (PairAuxiliary half) where
  sampleSecret := sampleRingSecret 1 (evenDegree half + 1)
  sampleReal := fixedSecretOrdinarySampler exponent (evenDegree half) errorSampler
  sampleZero := fixedSecretOrdinarySampler exponent (evenDegree half) errorSampler
  sampleUniform := $ᵗ (Transcript exponent (evenDegree half))
  sampleAuxiliary := fun ringSecret ↦ pure (ringPairXor half ringSecret)

/-- The endpoint contains no circular ciphertext: its real and zero conditional RLWE samplers
are definitionally identical. -/
theorem pairLeakageProblem_sampleReal_eq_sampleZero
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1))) :
    (pairLeakageProblem exponent half errorSampler).sampleReal =
      (pairLeakageProblem exponent half errorSampler).sampleZero := rfl

/-- Consequently, its real-versus-zero KDM advantage is exactly zero for every continuation;
the nontrivial premise below is ordinary RLWE pseudorandomness conditioned on the quotient. -/
theorem pairLeakageProblem_kdmAdvantage_eq_zero
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1)))
    (continuation : LWE.AuxiliaryInput.Continuation
      (RingBinarySecret 1 (evenDegree half + 1))
      (Transcript exponent (evenDegree half)) (PairAuxiliary half)) :
    LWE.AuxiliaryInput.kdmAdvantage
        (pairLeakageProblem exponent half errorSampler) continuation = 0 := by
  unfold LWE.AuxiliaryInput.kdmAdvantage
  have hequal : LWE.AuxiliaryInput.realGame
      (pairLeakageProblem exponent half errorSampler) continuation =
      LWE.AuxiliaryInput.zeroGame
        (pairLeakageProblem exponent half errorSampler) continuation := rfl
  rw [hequal]
  simp [ProbComp.boolDistAdvantage]

/-- Restore the native top-square body from the exact `N/2`-bit quotient. -/
def pairLeakageContinuation
    {exponent half : ℕ}
    {errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1))}
    (adversary : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent (evenDegree half) errorSampler)) :
    LWE.AuxiliaryInput.Continuation
      (RingBinarySecret 1 (evenDegree half + 1))
      (Transcript exponent (evenDegree half))
      (PairAuxiliary half) :=
  fun _ transcript bits ↦
    adversary (addLeakage (pairedLeakage exponent half bits) transcript)

/-- The pair-XOR leakage real game is literally the previous structured-ring-leakage real game
after reconstructing the ring value. -/
theorem pairLeakageRealGame_eq_leakageRealGame
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1)))
    (adversary : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent (evenDegree half) errorSampler)) :
    LWE.AuxiliaryInput.realGame
        (pairLeakageProblem exponent half errorSampler)
        (pairLeakageContinuation adversary) =
      LWE.AuxiliaryInput.realGame
        (leakageProblem exponent (evenDegree half) errorSampler)
        (leakageContinuation adversary) := by
  simp [LWE.AuxiliaryInput.realGame, pairLeakageProblem,
    pairLeakageContinuation, leakageProblem, leakageContinuation,
    topLeakage_eq_pairedLeakage]

/-- The same exact identification holds in the uniform branch. -/
theorem pairLeakageUniformGame_eq_leakageUniformGame
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1)))
    (adversary : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent (evenDegree half) errorSampler)) :
    LWE.AuxiliaryInput.uniformGame
        (pairLeakageProblem exponent half errorSampler)
        (pairLeakageContinuation adversary) =
      LWE.AuxiliaryInput.uniformGame
        (leakageProblem exponent (evenDegree half) errorSampler)
        (leakageContinuation adversary) := by
  simp [LWE.AuxiliaryInput.uniformGame, pairLeakageProblem,
    pairLeakageContinuation, leakageProblem, leakageContinuation,
    topLeakage_eq_pairedLeakage]

/-- Revealing the ring element `2^k S^2` is exactly equivalent, for the restoring continuation,
to revealing the `N/2` pair-XOR bits. -/
theorem pairLeakageAdvantage_eq_leakageRLWE
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1)))
    (adversary : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent (evenDegree half) errorSampler)) :
    LWE.AuxiliaryInput.circularLweAdvantage
        (pairLeakageProblem exponent half errorSampler)
        (pairLeakageContinuation adversary) =
      LWE.AuxiliaryInput.circularLweAdvantage
        (leakageProblem exponent (evenDegree half) errorSampler)
        (leakageContinuation adversary) := by
  unfold LWE.AuxiliaryInput.circularLweAdvantage
  rw [pairLeakageRealGame_eq_leakageRealGame,
    pairLeakageUniformGame_eq_leakageUniformGame]

/-- The complete coefficient-affine top-row advantage is exactly ordinary binary-secret RLWE
with the uniform `N/2`-bit pair-XOR quotient exposed. -/
theorem topCoefficientAdvantage_eq_pairLeakageRLWE
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1)))
    (adversary : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent (evenDegree half) errorSampler)) :
    LearningWithErrors.advantage
        (topRGSWCoefficientProblem exponent (evenDegree half) errorSampler) adversary =
      LWE.AuxiliaryInput.circularLweAdvantage
        (pairLeakageProblem exponent half errorSampler)
        (pairLeakageContinuation adversary) := by
  rw [topCoefficientAdvantage_eq_leakageRLWE,
    pairLeakageAdvantage_eq_leakageRLWE]

/-- The genuine unstripped highest-weight native circular term is exactly the named
pair-XOR-leakage RLWE advantage. -/
theorem nativeCircularLweAdvantage_eq_pairLeakageRLWE
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (evenDegree half + 1) 1) :
    Native.RingSquareRGSW.circularLweAdvantage
        (2 ^ (exponent + 1)) (evenDegree half + 1) 1 errorSampler
        (topGadget exponent (evenDegree half)) distinguisher =
      LWE.AuxiliaryInput.circularLweAdvantage
        (pairLeakageProblem exponent half errorSampler)
        (pairLeakageContinuation (errorSampler := errorSampler)
          (TopWeightSecurity.coefficientAdversary (errorSampler := errorSampler)
            (Native.RingSquareRGSW.restoreDistinguisher
              (topGadget exponent (evenDegree half)) distinguisher))) := by
  rw [nativeCircularLweAdvantage_eq_leakageRLWE,
    pairLeakageAdvantage_eq_leakageRLWE]

/-- **Native `RGSW_S(-S)` reduction in even dimension.**  The genuine top-weight KDM advantage
is bounded by ordinary two-row binary-secret RLWE with the exact uniform `N/2`-bit pair-XOR
quotient exposed, plus ordinary two-row zero-message binary-secret RLWE.  Both terms retain the
original narrow error sampler. -/
theorem kdmAdvantage_le_pairLeakageRLWE_add_ordinaryRLWE
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (evenDegree half + 1) 1) :
    Native.RingSquareRGSW.kdmAdvantage
        (2 ^ (exponent + 1)) (evenDegree half + 1) 1 errorSampler
        (topGadget exponent (evenDegree half)) distinguisher ≤
      LWE.AuxiliaryInput.circularLweAdvantage
          (pairLeakageProblem exponent half errorSampler)
          (pairLeakageContinuation (errorSampler := errorSampler)
            (TopWeightSecurity.coefficientAdversary (errorSampler := errorSampler)
              (Native.RingSquareRGSW.restoreDistinguisher
                (topGadget exponent (evenDegree half)) distinguisher))) +
        LearningWithErrors.advantage
          (CoefficientStructuredLWE.ringProblem
            (2 ^ (exponent + 1)) (evenDegree half + 1) 1
            (TGSW.rowCount 1 1) errorSampler)
          (TopWeightSecurity.zeroRLWEAdversary distinguisher) := by
  simpa only [← pairLeakageAdvantage_eq_leakageRLWE] using
    kdmAdvantage_le_leakageRLWE_add_ordinaryRLWE
      exponent (evenDegree half) errorSampler distinguisher

/-- Concrete hardness of ordinary RLWE with the exact pair-XOR quotient exposed. -/
def PairLeakageRLWEHardAgainst
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1)))
    (allowed : LWE.AuxiliaryInput.Continuation
      (RingBinarySecret 1 (evenDegree half + 1))
      (Transcript exponent (evenDegree half)) (PairAuxiliary half) → Prop)
    (bound : ℝ) : Prop :=
  LWE.AuxiliaryInput.CircularLWEHardAgainst
    (pairLeakageProblem exponent half errorSampler) allowed bound

/-- Pair-XOR-leakage RLWE and ordinary binary-secret RLWE imply genuine native top-weight
`RGSW_S(-S)` KDM security. -/
theorem kdmHardAgainst_of_pairLeakageRLWE_and_binarySecretRLWE
    (exponent half : ℕ)
    (errorSampler : ProbComp
      (RLWE.Rq (2 ^ (exponent + 1)) (evenDegree half + 1)))
    (nativeAllowed : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (evenDegree half + 1) 1 → Prop)
    (pairAllowed : LWE.AuxiliaryInput.Continuation
      (RingBinarySecret 1 (evenDegree half + 1))
      (Transcript exponent (evenDegree half)) (PairAuxiliary half) → Prop)
    (ordinaryAllowed : LearningWithErrors.Adversary
      (CoefficientStructuredLWE.ringProblem
        (2 ^ (exponent + 1)) (evenDegree half + 1) 1
        (TGSW.rowCount 1 1) errorSampler) → Prop)
    (pairBound ordinaryBound : ℝ)
    (hPairClosed : ∀ distinguisher, nativeAllowed distinguisher →
      pairAllowed
        (pairLeakageContinuation (errorSampler := errorSampler)
          (TopWeightSecurity.coefficientAdversary (errorSampler := errorSampler)
            (Native.RingSquareRGSW.restoreDistinguisher
              (topGadget exponent (evenDegree half)) distinguisher))))
    (hOrdinaryClosed : ∀ distinguisher, nativeAllowed distinguisher →
      ordinaryAllowed (TopWeightSecurity.zeroRLWEAdversary distinguisher))
    (hPair : PairLeakageRLWEHardAgainst exponent half errorSampler
      pairAllowed pairBound)
    (hOrdinary : TopWeightSecurity.BinarySecretRLWEHardAgainst
      exponent (evenDegree half) errorSampler ordinaryAllowed ordinaryBound) :
    Native.RingSquareRGSW.KDMHardAgainst
      (2 ^ (exponent + 1)) (evenDegree half + 1) 1 errorSampler
      (topGadget exponent (evenDegree half)) nativeAllowed
      (pairBound + ordinaryBound) := by
  intro distinguisher hallowed
  exact (kdmAdvantage_le_pairLeakageRLWE_add_ordinaryRLWE
    exponent half errorSampler distinguisher).trans
      (add_le_add
        (hPair _ (hPairClosed distinguisher hallowed))
        (hOrdinary _ (hOrdinaryClosed distinguisher hallowed)))

/-- Centered-binomial specialization.  The native, pair-leakage, and ordinary RLWE games all
use the same width `eta`; no smoothing or error widening is introduced. -/
theorem centeredBinomial_kdmHardAgainst_of_pairLeakageRLWE_and_binarySecretRLWE
    (exponent half eta : ℕ)
    (nativeAllowed : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (evenDegree half + 1) 1 → Prop)
    (pairAllowed : LWE.AuxiliaryInput.Continuation
      (RingBinarySecret 1 (evenDegree half + 1))
      (Transcript exponent (evenDegree half)) (PairAuxiliary half) → Prop)
    (ordinaryAllowed : LearningWithErrors.Adversary
      (CoefficientStructuredLWE.ringProblem
        (2 ^ (exponent + 1)) (evenDegree half + 1) 1 (TGSW.rowCount 1 1)
        (RLWE.CenteredBinomial.sampler
          (2 ^ (exponent + 1)) (evenDegree half + 1) eta)) → Prop)
    (pairBound ordinaryBound : ℝ)
    (hPairClosed : ∀ distinguisher, nativeAllowed distinguisher →
      pairAllowed
        (pairLeakageContinuation
          (errorSampler := RLWE.CenteredBinomial.sampler
            (2 ^ (exponent + 1)) (evenDegree half + 1) eta)
          (TopWeightSecurity.coefficientAdversary
            (errorSampler := RLWE.CenteredBinomial.sampler
              (2 ^ (exponent + 1)) (evenDegree half + 1) eta)
            (Native.RingSquareRGSW.restoreDistinguisher
              (topGadget exponent (evenDegree half)) distinguisher))))
    (hOrdinaryClosed : ∀ distinguisher, nativeAllowed distinguisher →
      ordinaryAllowed (TopWeightSecurity.zeroRLWEAdversary distinguisher))
    (hPair : PairLeakageRLWEHardAgainst exponent half
      (RLWE.CenteredBinomial.sampler
        (2 ^ (exponent + 1)) (evenDegree half + 1) eta)
      pairAllowed pairBound)
    (hOrdinary : TopWeightSecurity.BinarySecretRLWEHardAgainst
      exponent (evenDegree half)
      (RLWE.CenteredBinomial.sampler
        (2 ^ (exponent + 1)) (evenDegree half + 1) eta)
      ordinaryAllowed ordinaryBound) :
    Native.RingSquareRGSW.KDMHardAgainst
      (2 ^ (exponent + 1)) (evenDegree half + 1) 1
      (RLWE.CenteredBinomial.sampler
        (2 ^ (exponent + 1)) (evenDegree half + 1) eta)
      (topGadget exponent (evenDegree half)) nativeAllowed
      (pairBound + ordinaryBound) := by
  exact kdmHardAgainst_of_pairLeakageRLWE_and_binarySecretRLWE
    exponent half
    (RLWE.CenteredBinomial.sampler
      (2 ^ (exponent + 1)) (evenDegree half + 1) eta)
    nativeAllowed pairAllowed ordinaryAllowed pairBound ordinaryBound
    hPairClosed hOrdinaryClosed hPair hOrdinary

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightPairLeakage
