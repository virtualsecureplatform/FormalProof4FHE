/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CircularBoundary

/-!
# Degree-Two Monomial Presentation of Native TFHE Circular KDM

The positive KDM theorems in the supplied references use construction-specific formats.  In
particular, Brakerski--Goldwasser--Kalai handle degree-`d` KDM by changing the secret-key geometry
to include its low-degree monomials.  That theorem cannot be applied directly to native TFHE, but
its algebraic boundary can be stated exactly.

After native TGSW normalization, a mask-block row carries

`-(ringSecret_j * (scalarSecret_i * gadget_l))`.

This is the fixed gadget-scaled outer-product family exposed by native TRGSW, not an arbitrary
quadratic KDM family. A general degree-two KDM theorem would be sufficient, but is stronger than
the exact TFHE obligation formalized here.  One entry is rank one; when a complete self-BRK
contains one entry for every secret coordinate, the joint table contains every pairwise monomial.
`FullBRKQuadraticSpan` proves that public linear combinations of its mask rows realize arbitrary
weighted quadratic forms, with their combined error tracked exactly.

For a nonzero gadget value this function is not affine in the two native key coordinates.  If the
degree-two coordinate `ringSecret_j * scalarSecret_i` is added to an expanded key, however, the
same phase is a linear coordinate projection followed by public gadget scaling.  This file proves
both statements and re-expresses the complete native direct-bilinear game using that monomial
presentation.

The final game equality is exact.  It is a format-identification theorem, not a reduction from
ordinary LWE/RLWE and not an application of a KDM theorem for a transformed encryption scheme.
-/

open Matrix

namespace FormalProof4FHE.TFHE.TGSW.MonomialKDM

/-- The degree-two coordinates obtained by multiplying one message coordinate into every target
secret coordinate. -/
def crossMonomial {R : Type} [CommRing R] {dimension : ℕ}
    (secret : Fin dimension → R) (message : R) : Fin dimension → R :=
  fun coordinate ↦ secret coordinate * message

@[simp]
theorem crossMonomial_apply {R : Type} [CommRing R] {dimension : ℕ}
    (secret : Fin dimension → R) (message : R) (coordinate : Fin dimension) :
    crossMonomial secret message coordinate = secret coordinate * message :=
  rfl

/-- Once the degree-two coordinates are supplied explicitly, the mask-block phase is a public
linear gadget scaling of those coordinates. -/
def monomialPhasePart {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (cross : Fin dimension → R) :
    Fin (rowCount dimension levels) → R :=
  CircularBoundary.crossKeyPhasePart cross gadget 1

/-- A mask-block row is a public gadget scaling of exactly one degree-two coordinate. -/
theorem monomialPhasePart_castSucc {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (cross : Fin dimension → R)
    (coordinate : Fin dimension) (level : Fin levels) :
    monomialPhasePart gadget cross
        (finProdFinEquiv (Fin.castSucc coordinate, level)) =
      -(cross coordinate * gadget level) := by
  unfold monomialPhasePart
  rw [CircularBoundary.crossKeyPhasePart_castSucc]
  simp

/-- The final block contains no degree-two coordinate. -/
@[simp]
theorem monomialPhasePart_last {R : Type} [Ring R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (cross : Fin dimension → R)
    (level : Fin levels) :
    monomialPhasePart gadget cross
        (finProdFinEquiv (Fin.last dimension, level)) = 0 := by
  simp [monomialPhasePart, CircularBoundary.crossKeyPhasePart_last]

/-- The monomial phase presentation is additive in the expanded degree-two coordinates. -/
theorem monomialPhasePart_add {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (left right : Fin dimension → R) :
    monomialPhasePart gadget (left + right) =
      monomialPhasePart gadget left + monomialPhasePart gadget right := by
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  refine Fin.lastCases ?_ (fun coordinate ↦ ?_) block
  · simp
  · simp only [monomialPhasePart_castSucc, Pi.add_apply]
    ring

/-- Public scalar multiplication commutes with the monomial phase presentation. -/
theorem monomialPhasePart_scale {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (scalar : R) (cross : Fin dimension → R) :
    monomialPhasePart gadget (fun coordinate ↦ scalar * cross coordinate) =
      fun row ↦ scalar * monomialPhasePart gadget cross row := by
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  refine Fin.lastCases ?_ (fun coordinate ↦ ?_) block
  · simp
  · simp only [monomialPhasePart_castSucc]
    ring

/-- The native bilinear cross-key phase is exactly the linear monomial-coordinate phase after the
degree-two lift. -/
theorem crossKeyPhasePart_eq_monomialPhasePart {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    CircularBoundary.crossKeyPhasePart secret gadget message =
      monomialPhasePart gadget (crossMonomial secret message) := by
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  refine Fin.lastCases ?_ (fun coordinate ↦ ?_) block
  · simp [monomialPhasePart, CircularBoundary.crossKeyPhasePart_last]
  · rw [CircularBoundary.crossKeyPhasePart_castSucc]
    unfold monomialPhasePart
    rw [CircularBoundary.crossKeyPhasePart_castSucc]
    simp only [crossMonomial_apply, one_mul]
    ring

/-- Gadget phase written as an affine body coordinate plus public linear projections of an
explicit degree-two monomial vector. -/
def expandedGadgetPhase {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R) (cross : Fin dimension → R) :
    Fin (rowCount dimension levels) → R :=
  CircularBoundary.affinePhasePart gadget message + monomialPhasePart gadget cross

/-- Exact factorization of the complete normalized TGSW phase through the degree-two monomial
lift. -/
theorem gadgetPhase_eq_expandedGadgetPhase {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    gadgetPhase secret gadget message =
      expandedGadgetPhase gadget message (crossMonomial secret message) := by
  rw [CircularBoundary.gadgetPhase_eq_affine_add_cross,
    crossKeyPhasePart_eq_monomialPhasePart]
  rfl

/-- A direct fresh module-LWE presentation whose messages are supplied through the affine-plus-
monomial expanded coordinates. -/
def expandedDirectEncrypt {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (message : R) (cross : Fin dimension → R) :
    ProbComp (Ciphertext R dimension levels) :=
  TLWE.batchEncrypt dimension (rowCount dimension levels) errorSampler secret
    (expandedGadgetPhase gadget message cross)

/-- Supplying the honest degree-two monomials makes the expanded direct sampler exactly the
existing normalized native TGSW sampler. -/
theorem directEncrypt_eq_expandedDirectEncrypt {R : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    directEncrypt dimension levels errorSampler secret gadget message =
      expandedDirectEncrypt dimension levels errorSampler secret gadget message
        (crossMonomial secret message) := by
  unfold directEncrypt expandedDirectEncrypt
  rw [gadgetPhase_eq_expandedGadgetPhase]

/-- A nonzero scaled product cannot be represented by an affine expression in its two native
coordinates.  This is the algebraic reason an affine-KDM theorem cannot simply be applied to a
native TFHE mask-block phase. -/
theorem scaledProduct_not_affine {R : Type} [CommRing R]
    {gadgetValue : R} (hgadget : gadgetValue ≠ 0) :
    ¬ ∃ firstCoefficient secondCoefficient constant : R,
      ∀ first second : R,
        -(first * (second * gadgetValue)) =
          firstCoefficient * first + secondCoefficient * second + constant := by
  rintro ⟨firstCoefficient, secondCoefficient, constant, haffine⟩
  have hconstant : constant = 0 := by
    simpa using (haffine 0 0).symm
  have hfirst : firstCoefficient = 0 := by
    simpa [hconstant] using (haffine 1 0).symm
  have hsecond : secondCoefficient = 0 := by
    simpa [hconstant] using (haffine 0 1).symm
  have hnonzero := haffine 1 1
  simp only [one_mul, hfirst, hsecond, hconstant, zero_mul, add_zero] at hnonzero
  exact hgadget (neg_eq_zero.mp hnonzero)

/-- The proposition that a scaled degree-two product admits an affine representation in its two
native coordinates.  Packaging the property behind the abstract `CommRing` interface also avoids
selecting representation-specific operation instances when it is specialized to an executable
ring carrier. -/
def ScaledProductAffine {R : Type} [CommRing R] (gadgetValue : R) : Prop :=
  ∃ firstCoefficient secondCoefficient constant : R,
    ∀ first second : R,
      -(first * (second * gadgetValue)) =
        firstCoefficient * first + secondCoefficient * second + constant

/-- Predicate-packaged form of `scaledProduct_not_affine`. -/
theorem not_scaledProductAffine {R : Type} [CommRing R]
    {gadgetValue : R} (hgadget : gadgetValue ≠ 0) :
    ¬ ScaledProductAffine gadgetValue := by
  exact scaledProduct_not_affine hgadget

/-- The ordinary Boolean embedding with its operation dictionaries fixed by an abstract
`CommRing`.  The wrapper is useful when the executable ring carrier also exposes lower-priority
bundled operation instances. -/
def commRingEmbedBit {R : Type} [CommRing R] (bit : Bool) : R :=
  embedBit bit

/-- Affineness restricted to the actual two-bit input support.  This is strictly the relevant
KDM question for one binary ring-key coordinate and one binary scalar-key coordinate; failure of
affineness on the whole carrier alone would not rule out agreement on this smaller support. -/
def BinaryScaledProductAffine {R : Type} [CommRing R] (gadgetValue : R) : Prop :=
  ∃ firstCoefficient secondCoefficient constant : R,
    ∀ first second : Bool,
      -(embedBit first * (embedBit second * gadgetValue)) =
        firstCoefficient * embedBit first +
          secondCoefficient * embedBit second + constant

/-- A nonzero scaled Boolean product is not affine even on the four possible bit pairs. -/
theorem not_binaryScaledProductAffine {R : Type} [CommRing R]
    {gadgetValue : R} (hgadget : gadgetValue ≠ 0) :
    ¬ BinaryScaledProductAffine gadgetValue := by
  rintro ⟨firstCoefficient, secondCoefficient, constant, haffine⟩
  have hconstant : constant = 0 := by
    simpa [embedBit] using (haffine false false).symm
  have hfirst : firstCoefficient = 0 := by
    simpa [embedBit, hconstant] using (haffine true false).symm
  have hsecond : secondCoefficient = 0 := by
    simpa [embedBit, hconstant] using (haffine false true).symm
  have hnonzero := haffine true true
  simp only [embedBit, if_true, one_mul, hfirst, hsecond, hconstant, zero_mul,
    add_zero] at hnonzero
  exact hgadget (neg_eq_zero.mp hnonzero)

/-- A Boolean vector supported at one selected coordinate. -/
def singleBit {dimension : ℕ} (coordinate : Fin dimension) (bit : Bool) :
    Fin dimension → Bool :=
  fun index ↦ if index = coordinate then bit else false

@[simp]
theorem singleBit_self {dimension : ℕ} (coordinate : Fin dimension) (bit : Bool) :
    singleBit coordinate bit coordinate = bit := by
  simp [singleBit]

@[simp]
theorem sum_mul_embedBit_singleBit {R : Type} [CommRing R] {dimension : ℕ}
    (coefficients : Fin dimension → R) (coordinate : Fin dimension) (bit : Bool) :
    (∑ index, coefficients index * embedBit (singleBit coordinate bit index)) =
      coefficients coordinate * embedBit bit := by
  classical
  cases bit <;> simp [singleBit, embedBit]

/-- Affineness of one cross-coordinate product as a function of two complete binary key vectors.
This matches the coordinate representation used by vector-LWE affine-KDM results. -/
def BinaryVectorScaledProductAffine {R : Type} [CommRing R]
    {firstDimension secondDimension : ℕ}
    (firstCoordinate : Fin firstDimension) (secondCoordinate : Fin secondDimension)
    (gadgetValue : R) : Prop :=
  ∃ firstCoefficients : Fin firstDimension → R,
    ∃ secondCoefficients : Fin secondDimension → R,
    ∃ constant : R,
      ∀ first : Fin firstDimension → Bool,
        ∀ second : Fin secondDimension → Bool,
        -(embedBit (first firstCoordinate) *
            (embedBit (second secondCoordinate) * gadgetValue)) =
          (∑ coordinate, firstCoefficients coordinate * embedBit (first coordinate)) +
            (∑ coordinate, secondCoefficients coordinate * embedBit (second coordinate)) +
              constant

/-- A nonzero Boolean cross-coordinate product is not affine even when arbitrary coefficients on
every coordinate of both complete binary key vectors are allowed. -/
theorem not_binaryVectorScaledProductAffine {R : Type} [CommRing R]
    {firstDimension secondDimension : ℕ}
    {firstCoordinate : Fin firstDimension} {secondCoordinate : Fin secondDimension}
    {gadgetValue : R} (hgadget : gadgetValue ≠ 0) :
    ¬ BinaryVectorScaledProductAffine firstCoordinate secondCoordinate gadgetValue := by
  rintro ⟨firstCoefficients, secondCoefficients, constant, haffine⟩
  apply not_binaryScaledProductAffine hgadget
  refine ⟨firstCoefficients firstCoordinate, secondCoefficients secondCoordinate, constant, ?_⟩
  intro first second
  simpa only [singleBit_self, sum_mul_embedBit_singleBit] using
    (haffine (singleBit firstCoordinate first) (singleBit secondCoordinate second))

/-- Affineness of a native polynomial-coordinate product on two complete binary keys.  The first
binary vector is embedded as one ring element; the second contributes one selected scalar bit. -/
def BinaryPolynomialScaledProductAffine {R : Type} [CommRing R]
    {firstDimension secondDimension : ℕ}
    (embedPolynomial : (Fin firstDimension → Bool) → R)
    (secondCoordinate : Fin secondDimension) (gadgetValue : R) : Prop :=
  ∃ firstCoefficients : Fin firstDimension → R,
    ∃ secondCoefficients : Fin secondDimension → R,
    ∃ constant : R,
      ∀ first : Fin firstDimension → Bool,
        ∀ second : Fin secondDimension → Bool,
          -(embedPolynomial first *
              (embedBit (second secondCoordinate) * gadgetValue)) =
            (∑ coordinate, firstCoefficients coordinate * embedBit (first coordinate)) +
              (∑ coordinate, secondCoefficients coordinate * embedBit (second coordinate)) +
                constant

/-- If a polynomial embedding contains the ordinary constant-bit embedding on one coordinate,
then its nonzero scalar cross product cannot be affine on the complete binary-key support. -/
theorem not_binaryPolynomialScaledProductAffine {R : Type} [CommRing R]
    {firstDimension secondDimension : ℕ}
    {embedPolynomial : (Fin firstDimension → Bool) → R}
    {firstCoordinate : Fin firstDimension} {secondCoordinate : Fin secondDimension}
    {gadgetValue : R}
    (hembed : ∀ bit, embedPolynomial (singleBit firstCoordinate bit) = embedBit bit)
    (hgadget : gadgetValue ≠ 0) :
    ¬ BinaryPolynomialScaledProductAffine
      embedPolynomial secondCoordinate gadgetValue := by
  rintro ⟨firstCoefficients, secondCoefficients, constant, haffine⟩
  apply not_binaryScaledProductAffine hgadget
  refine ⟨firstCoefficients firstCoordinate, secondCoefficients secondCoordinate, constant, ?_⟩
  intro first second
  simpa only [hembed, singleBit_self, sum_mul_embedBit_singleBit] using
    (haffine (singleBit firstCoordinate first) (singleBit secondCoordinate second))

/-- Every nonzero native mask-block gadget coordinate has a genuinely non-affine dependence on
the corresponding ring-secret and scalar-secret coordinates. -/
theorem maskBlockPhase_not_affine {R : Type} [CommRing R]
    {levels : ℕ} (gadget : Fin levels → R) (level : Fin levels)
    (hgadget : gadget level ≠ 0) :
    ¬ ∃ firstCoefficient secondCoefficient constant : R,
      ∀ ringCoordinate scalarCoordinate : R,
        -(ringCoordinate * (scalarCoordinate * gadget level)) =
          firstCoefficient * ringCoordinate +
            secondCoefficient * scalarCoordinate + constant :=
  scaledProduct_not_affine hgadget

end FormalProof4FHE.TFHE.TGSW.MonomialKDM

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM

open TGSW

/-- Native bootstrapping-key generation with every direct TGSW phase routed explicitly through
the degree-two monomial lift. -/
noncomputable def generateBootstrappingKey
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
  Fin.mOfFn lweDimension fun coordinate ↦
    TGSW.MonomialKDM.expandedDirectEncrypt ringRank tgswLevels errorSampler
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate))
      (TGSW.MonomialKDM.crossMonomial
        (embedRingSecret q ringSecret)
        (embedConstantBit q degree (lweSecret coordinate)))

/-- The degree-two monomial presentation is exactly the existing direct-bilinear native BRK
sampler, not merely statistically close to it. -/
theorem generateBootstrappingKey_eq_direct
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    generateBootstrappingKey q degree ringRank tgswLevels lweDimension
        errorSampler gadget lweSecret ringSecret =
      Native.BootstrapSecurity.generateDirectBootstrappingKey
        q degree ringRank tgswLevels lweDimension
        errorSampler gadget lweSecret ringSecret := by
  unfold generateBootstrappingKey
    Native.BootstrapSecurity.generateDirectBootstrappingKey
  congr 1
  funext coordinate
  exact (TGSW.MonomialKDM.directEncrypt_eq_expandedDirectEncrypt
    ringRank tgswLevels errorSampler (embedRingSecret q ringSecret) gadget
    (embedConstantBit q degree (lweSecret coordinate))).symm

/-- Native cycle specification whose real BRK is written through degree-two monomial
coordinates. -/
noncomputable def cycleSpec
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    Circular.CycleSpec
      (BinarySecret lweDimension)
      (RingBinarySecret ringRank degree)
      (BinarySecret (ringRank * degree))
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) where
  sampleLweSecret := Native.sampleLweSecret lweDimension
  sampleRingSecret := Native.sampleRingSecret ringRank degree
  extractRingSecret := keyExtract
  bootstrapReal := generateBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget
  bootstrapZero := Native.generateZeroBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  keySwitchReal := Native.generateKeySwitchKey
    q lweDimension (ringRank * degree) keySwitchLevels
      keySwitchErrorSampler keySwitchGadget
  keySwitchZero := Native.generateZeroKeySwitchKey
    q lweDimension (ringRank * degree) keySwitchLevels keySwitchErrorSampler

/-- The monomial cycle specification and the direct-bilinear cycle specification are exactly the
same native distribution. -/
theorem cycleSpec_eq_directCycleSpec
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    cycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget =
      Native.BootstrapSecurity.directCycleSpec
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget := by
  unfold cycleSpec Native.BootstrapSecurity.directCycleSpec
  congr 1
  funext lweSecret ringSecret
  exact generateBootstrappingKey_eq_direct
    q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget lweSecret ringSecret

/-- Degree-two monomial-KDM presentation of the exact native BRK-first intact-cycle advantage. -/
noncomputable def advantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) : ℝ :=
  (Circular.realContinuationGame
    (cycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    continuation).boolDistAdvantage
  (Circular.bootstrapZeroContinuationGame
    (cycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    continuation)

/-- The monomial-KDM and direct-bilinear presentations have exactly equal advantage for every
downstream continuation. -/
theorem advantage_eq_directBilinear
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    advantage ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget continuation =
      Native.BootstrapSecurity.directBilinearAdvantage
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget continuation := by
  unfold advantage Native.BootstrapSecurity.directBilinearAdvantage
  rw [cycleSpec_eq_directCycleSpec]

/-- Hardness interface for the exact degree-two monomial presentation. -/
def HardAgainst
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation →
    advantage ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget continuation ≤ bound

/-- The degree-two monomial hardness interface is equivalent—not merely sufficient—to the exact
native direct-bilinear circular/KDM interface. -/
theorem hardAgainst_iff_directBilinear
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (bound : ℝ) :
    HardAgainst ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget allowed bound ↔
      Native.BootstrapSecurity.DirectBilinearHardAgainst
        ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget allowed bound := by
  constructor
  · intro h continuation hallowed
    rw [← advantage_eq_directBilinear]
    exact h continuation hallowed
  · intro h continuation hallowed
    rw [advantage_eq_directBilinear]
    exact h continuation hallowed

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM
