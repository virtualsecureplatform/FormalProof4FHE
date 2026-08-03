/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWCVZRParityPrefix
import FormalProof4FHE.TFHE.NativeTRGSWCompleteViewAuxiliarySource
import FormalProof4FHE.TFHE.NativeTRGSWSpectralInfeasibility

/-!
# Native TRGSW quadratic KDM security and the TFHE control length

This module formalizes the mathematical claims in
`sketch/native_trgsw_quadratic_kdm_and_tfhe_t.tex`.

The native nonce row is normalized exactly as an RLWE encryption of the key-dependent message
`-h * m * S`.  For a subset key `S = E(P) + Z`, the resulting phase is genuinely quadratic in
the encrypted prefix.  Public gadget translation nevertheless constructs the complete native
known-message rows from homogeneous rows, and it is a permutation on a uniform source.

The security theorem uses the already checked complete-view match-and-square inequality.  This
file adds the direct source compiler needed by the note: its real branch is the two-copy
match-and-square game and its uniform branch is the fair endpoint.  Consequently its source
advantage is *exactly* one ordinary-RLWE advantage; there is no extra CVZR branch-selection
factor.

For the parity split `S = P(X^2) + X Z(X^2)`, the file proves the full multiplication identity,
the two-half-sample construction of a full homogeneous row, its uniform-source bijection, and
the public aggregation identity exposing `h * S^2`.  Exact KSK-mask and CBD-error statements are
provided by `NativeTRGSWCVZRParityPrefix` and are composed here by reference.

The final section gives implementation-independent definitions of the control length and source
sample count.  It deliberately does not identify the theorem's control length with a key-switch
digit-count field.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWQuadraticKDMAndTFHET

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open NativeTRGSWAggregateProjectedLeakage
open NativeTRGSWCompleteViewAuxiliarySource
open NativeTRGSWCVZRReduction
open NativeTRGSWCVZRParityPrefix
open RGSWCoefficientCircularSecurity
open TGSW.RingSquare.PreimageCompiler.MultiSourceCounting
open DirectSubsetKeyBRK
open Native.CoefficientStructuredLWE

/-! ## Exact native nonce and body rows -/

/-- One native mask/body row over an arbitrary commutative ring. -/
abbrev NativeRow (R : Type) := R × R

/-- A homogeneous zero-message row. -/
def homogeneousRow {R : Type} [CommRing R]
    (secret mask error : R) : NativeRow R :=
  (mask, mask * secret + error)

/-- Native nonce placement: the gadget message is added to the displayed mask. -/
def nativeNonceRow {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (rawMask error : R) : NativeRow R :=
  (rawMask + gadget * bitScalar message, rawMask * secret + error)

/-- The same nonce row after renaming its displayed mask. -/
def normalizedNonceRow {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (displayedMask error : R) : NativeRow R :=
  (displayedMask,
    displayedMask * secret - gadget * bitScalar message * secret + error)

/-- A native nonce row is exactly an RLWE row encrypting `-h * m * S`. -/
theorem nativeNonceRow_eq_normalized {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (rawMask error : R) :
    nativeNonceRow secret gadget message rawMask error =
      normalizedNonceRow secret gadget message
        (rawMask + gadget * bitScalar message) error := by
  apply Prod.ext
  · rfl
  · simp only [nativeNonceRow, normalizedNonceRow]
    ring

/-- Native body placement: the known gadget message is added to the body. -/
def nativeBodyRow {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (mask error : R) : NativeRow R :=
  (mask, mask * secret + error + gadget * bitScalar message)

/-- The body row is an ordinary RLWE encryption of the linear message `h * m`. -/
theorem nativeBodyRow_phase {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (mask error : R) :
    (nativeBodyRow secret gadget message mask error).2 -
        (nativeBodyRow secret gadget message mask error).1 * secret =
      gadget * bitScalar message + error := by
  simp [nativeBodyRow]
  ring

/-- The normalized nonce phase is the restricted KDM message plus the original error. -/
theorem normalizedNonceRow_phase {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (displayedMask error : R) :
    (normalizedNonceRow secret gadget message displayedMask error).2 -
        (normalizedNonceRow secret gadget message displayedMask error).1 * secret =
      -(gadget * bitScalar message * secret) + error := by
  simp [normalizedNonceRow]
  ring

/-- One nonce row together with its matching body row. -/
abbrev NativeRowPair (R : Type) := NativeRow R × NativeRow R

/-- Publicly translate a pair of homogeneous rows to the native known-message layout. -/
def translateKnownMessageRows {R : Type} [CommRing R]
    (gadget : R) (message : Bool) (rows : NativeRowPair R) : NativeRowPair R :=
  ((rows.1.1 + gadget * bitScalar message, rows.1.2),
    (rows.2.1, rows.2.2 + gadget * bitScalar message))

/-- Inverse public translation. -/
def untranslateKnownMessageRows {R : Type} [CommRing R]
    (gadget : R) (message : Bool) (rows : NativeRowPair R) : NativeRowPair R :=
  ((rows.1.1 - gadget * bitScalar message, rows.1.2),
    (rows.2.1, rows.2.2 - gadget * bitScalar message))

@[simp]
theorem untranslateKnownMessageRows_translate {R : Type} [CommRing R]
    (gadget : R) (message : Bool) (rows : NativeRowPair R) :
    untranslateKnownMessageRows gadget message
        (translateKnownMessageRows gadget message rows) = rows := by
  rcases rows with ⟨⟨nonceMask, nonceBody⟩, ⟨bodyMask, bodyBody⟩⟩
  simp [translateKnownMessageRows, untranslateKnownMessageRows]

@[simp]
theorem translateKnownMessageRows_untranslate {R : Type} [CommRing R]
    (gadget : R) (message : Bool) (rows : NativeRowPair R) :
    translateKnownMessageRows gadget message
        (untranslateKnownMessageRows gadget message rows) = rows := by
  rcases rows with ⟨⟨nonceMask, nonceBody⟩, ⟨bodyMask, bodyBody⟩⟩
  simp [translateKnownMessageRows, untranslateKnownMessageRows]

/-- Known-message translation is a permutation of the complete nonce/body carrier. -/
theorem translateKnownMessageRows_bijective {R : Type} [CommRing R]
    (gadget : R) (message : Bool) :
    Function.Bijective (translateKnownMessageRows gadget message :
      NativeRowPair R → NativeRowPair R) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untranslateKnownMessageRows gadget message,
      untranslateKnownMessageRows_translate gadget message,
      translateKnownMessageRows_untranslate gadget message⟩

/-- Therefore every fixed known-message translation preserves the uniform complete row-pair
law exactly. -/
theorem translateKnownMessageRows_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    (gadget : R) (message : Bool) :
    evalDist (translateKnownMessageRows gadget message <$>
        ($ᵗ (NativeRowPair R))) =
      evalDist ($ᵗ (NativeRowPair R)) :=
  evalDist_map_bijective_uniform_cross
    (α := NativeRowPair R) (β := NativeRowPair R)
    (translateKnownMessageRows gadget message)
    (translateKnownMessageRows_bijective gadget message)

/-- Translating two honest homogeneous rows constructs the exact native nonce/body pair. -/
theorem translateKnownMessageRows_real {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool)
    (nonceMask nonceError bodyMask bodyError : R) :
    translateKnownMessageRows gadget message
        (homogeneousRow secret nonceMask nonceError,
          homogeneousRow secret bodyMask bodyError) =
      (nativeNonceRow secret gadget message nonceMask nonceError,
        nativeBodyRow secret gadget message bodyMask bodyError) := by
  rfl

/-! ## Complete BRK translation -/

/-- Complete native nonce/body carrier indexed by the control coordinate and gadget level. -/
abbrev NativeControlRows (R Control Level : Type) :=
  Control → Level → NativeRowPair R

/-- Translate every nonce/body pair using the known control prefix. -/
def translateBRK {R Control Level : Type} [CommRing R]
    (gadget : Level → R) (message : Control → Bool)
    (rows : NativeControlRows R Control Level) :
    NativeControlRows R Control Level :=
  fun control level ↦
    translateKnownMessageRows (gadget level) (message control) (rows control level)

/-- Inverse complete-BRK translation. -/
def untranslateBRK {R Control Level : Type} [CommRing R]
    (gadget : Level → R) (message : Control → Bool)
    (rows : NativeControlRows R Control Level) :
    NativeControlRows R Control Level :=
  fun control level ↦
    untranslateKnownMessageRows (gadget level) (message control) (rows control level)

@[simp]
theorem untranslateBRK_translate {R Control Level : Type} [CommRing R]
    (gadget : Level → R) (message : Control → Bool)
    (rows : NativeControlRows R Control Level) :
    untranslateBRK gadget message (translateBRK gadget message rows) = rows := by
  funext control level
  exact untranslateKnownMessageRows_translate _ _ _

@[simp]
theorem translateBRK_untranslate {R Control Level : Type} [CommRing R]
    (gadget : Level → R) (message : Control → Bool)
    (rows : NativeControlRows R Control Level) :
    translateBRK gadget message (untranslateBRK gadget message rows) = rows := by
  funext control level
  exact translateKnownMessageRows_untranslate _ _ _

theorem translateBRK_bijective {R Control Level : Type} [CommRing R]
    (gadget : Level → R) (message : Control → Bool) :
    Function.Bijective (translateBRK gadget message :
      NativeControlRows R Control Level → NativeControlRows R Control Level) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untranslateBRK gadget message,
      untranslateBRK_translate gadget message,
      translateBRK_untranslate gadget message⟩

/-- The whole translated BRK, not merely each row marginal, remains exactly uniform. -/
theorem translateBRK_uniform_evalDist
    {R Control Level : Type} [CommRing R] [Fintype R]
    [Fintype Control] [Fintype Level] [SampleableType R]
    [SampleableType (NativeControlRows R Control Level)]
    (gadget : Level → R) (message : Control → Bool) :
    evalDist (translateBRK gadget message <$>
        ($ᵗ (NativeControlRows R Control Level))) =
      evalDist ($ᵗ (NativeControlRows R Control Level)) :=
  evalDist_map_bijective_uniform_cross
    (α := NativeControlRows R Control Level)
    (β := NativeControlRows R Control Level)
    (translateBRK gadget message) (translateBRK_bijective gadget message)

/-- Complete indexed homogeneous BRK source rows. -/
def homogeneousBRKRows {R Control Level : Type} [CommRing R]
    (secret : R)
    (nonceMask bodyMask nonceError bodyError : Control → Level → R) :
    NativeControlRows R Control Level :=
  fun control level ↦
    (homogeneousRow secret (nonceMask control level) (nonceError control level),
      homogeneousRow secret (bodyMask control level) (bodyError control level))

/-- Complete indexed native known-message BRK rows. -/
def nativeKnownMessageBRKRows {R Control Level : Type} [CommRing R]
    (secret : R) (gadget : Level → R) (message : Control → Bool)
    (nonceMask bodyMask nonceError bodyError : Control → Level → R) :
    NativeControlRows R Control Level :=
  fun control level ↦
    (nativeNonceRow secret (gadget level) (message control)
        (nonceMask control level) (nonceError control level),
      nativeBodyRow secret (gadget level) (message control)
        (bodyMask control level) (bodyError control level))

/-- Whole-family real law: public translation constructs every native nonce and body row
simultaneously while preserving the complete indexed error vector. -/
theorem translateBRK_real
    {R Control Level : Type} [CommRing R]
    (secret : R) (gadget : Level → R) (message : Control → Bool)
    (nonceMask bodyMask nonceError bodyError : Control → Level → R) :
    translateBRK gadget message
        (homogeneousBRKRows secret nonceMask bodyMask nonceError bodyError) =
      nativeKnownMessageBRKRows secret gadget message
        nonceMask bodyMask nonceError bodyError := by
  funext control level
  exact translateKnownMessageRows_real secret (gadget level) (message control)
    (nonceMask control level) (nonceError control level)
    (bodyMask control level) (bodyError control level)

/-- Complete restricted-KDM public view, including the forwarded KSK and auxiliary state. -/
abbrev RestrictedQuadraticKDMView
    (R Control Level KeySwitchKey Auxiliary : Type) :=
  CompleteView (NativeControlRows R Control Level) KeySwitchKey Auxiliary

/-- Translating the complete view changes only its BRK row carrier. -/
def translateRestrictedQuadraticKDMView
    {R Control Level KeySwitchKey Auxiliary : Type} [CommRing R]
    (gadget : Level → R) (message : Control → Bool)
    (view : RestrictedQuadraticKDMView R Control Level KeySwitchKey Auxiliary) :
    RestrictedQuadraticKDMView R Control Level KeySwitchKey Auxiliary :=
  view.mapRows (translateBRK gadget message)

@[simp]
theorem translateRestrictedQuadraticKDMView_keySwitchKey
    {R Control Level KeySwitchKey Auxiliary : Type} [CommRing R]
    (gadget : Level → R) (message : Control → Bool)
    (view : RestrictedQuadraticKDMView R Control Level KeySwitchKey Auxiliary) :
    (translateRestrictedQuadraticKDMView gadget message view).keySwitchKey =
      view.keySwitchKey := rfl

@[simp]
theorem translateRestrictedQuadraticKDMView_auxiliary
    {R Control Level KeySwitchKey Auxiliary : Type} [CommRing R]
    (gadget : Level → R) (message : Control → Bool)
    (view : RestrictedQuadraticKDMView R Control Level KeySwitchKey Auxiliary) :
    (translateRestrictedQuadraticKDMView gadget message view).auxiliary =
      view.auxiliary := rfl

/-! ## The subset-key quadratic term -/

/-- Split ring key used by the subset-key model. -/
def subsetSecret {R Index : Type} [CommRing R] [Fintype Index]
    (basis : Index → R) (prefixBits : Index → Bool) (suffix : R) : R :=
  prefixEmbedding basis prefixBits + suffix

/-- KDM plaintext appearing in one normalized nonce row. -/
def nonceKDMMessage {R Index : Type} [CommRing R] [Fintype Index]
    (basis : Index → R) (prefixBits : Index → Bool) (suffix gadget : R)
    (control : Index) : R :=
  -(gadget * bitScalar (prefixBits control) *
    subsetSecret basis prefixBits suffix)

/-- Exact split into mixed prefix/suffix and quadratic prefix/prefix terms. -/
theorem nonceKDMMessage_expansion
    {R Index : Type} [CommRing R] [Fintype Index]
    (basis : Index → R) (prefixBits : Index → Bool) (suffix gadget : R)
    (control : Index) :
    nonceKDMMessage basis prefixBits suffix gadget control =
      -(gadget * bitScalar (prefixBits control) * suffix) -
        gadget * bitScalar (prefixBits control) *
          prefixEmbedding basis prefixBits := by
  simp only [nonceKDMMessage, subsetSecret]
  ring

/-- Fully expanded square-free Boolean-polynomial form.  Binaryity simplifies diagonal squares
but leaves every off-diagonal and mixed term. -/
theorem nonceKDMMessage_eq_sum
    {R Index : Type} [CommRing R] [Fintype Index]
    (basis : Index → R) (prefixBits : Index → Bool) (suffix gadget : R)
    (control : Index) :
    nonceKDMMessage basis prefixBits suffix gadget control =
      -(gadget * bitScalar (prefixBits control) * suffix) -
        ∑ coordinate,
          gadget * basis coordinate * bitScalar (prefixBits control) *
            bitScalar (prefixBits coordinate) := by
  rw [nonceKDMMessage_expansion]
  unfold prefixEmbedding
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- The native two-bit nonce restriction has the nonzero mixed derivative from the sketch. -/
theorem nonce_mixedBooleanDerivative
    {R : Type} [CommRing R]
    (displayedMask gadget controlBasis otherBasis suffix : R) :
    mixedBooleanDerivative
        (nonceTwo displayedMask gadget controlBasis otherBasis suffix) =
      -gadget * otherBasis :=
  mixedBooleanDerivative_nonceTwo
    displayedMask gadget controlBasis otherBasis suffix

/-! ## Parity-split half-ring construction -/

/- Select one coherent proof-facing algebra dictionary for `Rq`.  The executable carrier also
exports bundled addition and multiplication operations directly; fixing these projections avoids
the degree-zero instance mismatch between the two presentations. -/
local instance parityRqCommRing (q degree : ℕ) : CommRing (RLWE.Rq q degree) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree

local instance parityRqAddCommGroup (q degree : ℕ) : AddCommGroup (RLWE.Rq q degree) :=
  (parityRqCommRing q degree).toAddCommGroup

local instance parityRqAdd (q degree : ℕ) : Add (RLWE.Rq q degree) :=
  (parityRqAddCommGroup q degree).toAdd

local instance parityRqSub (q degree : ℕ) : Sub (RLWE.Rq q degree) :=
  (parityRqCommRing q degree).toAddGroupWithOne.toAddGroup.toSub

local instance parityRqNeg (q degree : ℕ) : Neg (RLWE.Rq q degree) :=
  (parityRqAddCommGroup q degree).toNeg

local instance parityRqZero (q degree : ℕ) : Zero (RLWE.Rq q degree) :=
  (parityRqAddCommGroup q degree).toZero

local instance parityRqMul (q degree : ℕ) : Mul (RLWE.Rq q degree) :=
  (parityRqCommRing q degree).toMul

local instance parityRqOne (q degree : ℕ) : One (RLWE.Rq q degree) :=
  (parityRqCommRing q degree).toAddGroupWithOne.toOne

/-- Public even/odd embedding `Phi(u,v) = u(X^2) + X v(X^2)`. -/
def parityJoin (q half : ℕ)
    (even odd : RLWE.Rq q half) : RLWE.Rq q (2 * half) :=
  RLWE.EvenOddDecomposition.joinRq q half even odd

/-- Proof-facing negacyclic multiplication used by the matrix-RLWE interface. -/
def parityMul (q degree : ℕ)
    (left right : RLWE.Rq q degree) : RLWE.Rq q degree :=
  RLWE.EvenOddDecomposition.proofMul q degree left right

/-- Interleaving preserves addition in the selected proof-facing ring dictionary. -/
theorem parityJoin_add (q half : ℕ)
    (even₁ odd₁ even₂ odd₂ : RLWE.Rq q half) :
    parityJoin q half (even₁ + even₂) (odd₁ + odd₂) =
      parityJoin q half even₁ odd₁ + parityJoin q half even₂ odd₂ := by
  cases half with
  | zero =>
      apply (coefficientEquiv q 0).injective
      funext coefficient
      exact coefficient.elim0
  | succ half =>
      simpa [parityJoin] using
        (RLWE.EvenOddDecomposition.joinRq_add q (half + 1)
          even₁ odd₁ even₂ odd₂)

/-- Right distributivity for the explicitly selected proof-facing multiplication. -/
theorem parityMul_add_right (q degree : ℕ)
    (left right₁ right₂ : RLWE.Rq q degree) :
    parityMul q degree left (right₁ + right₂) =
      parityMul q degree left right₁ + parityMul q degree left right₂ := by
  change left * (right₁ + right₂) = left * right₁ + left * right₂
  exact mul_add left right₁ right₂

/-- Parity-split full ring secret. -/
def paritySecret (q half : ℕ) (prefixSecret suffix : RLWE.Rq q half) :
    RLWE.Rq q (2 * half) :=
  parityJoin q half prefixSecret suffix

/-- The parity split is the sum of its disjoint even and odd components. -/
theorem paritySecret_eq_prefix_add_suffix
    (q half : ℕ) (prefixSecret suffix : RLWE.Rq q half) :
    paritySecret q half prefixSecret suffix =
      parityJoin q half prefixSecret 0 + parityJoin q half 0 suffix := by
  simpa [paritySecret] using
    (parityJoin_add q half prefixSecret 0 0 suffix)

/-- Full multiplication law for the parity decomposition. -/
theorem parityJoin_mul
    (q half : ℕ) [Nontrivial (ZMod q)] (hhalf : 0 < half)
    (maskEven maskOdd prefixSecret suffix : RLWE.Rq q half) :
    parityMul q (2 * half) (parityJoin q half maskEven maskOdd)
        (paritySecret q half prefixSecret suffix) =
      parityJoin q half
        (parityMul q half maskEven prefixSecret +
          parityMul q half
            (parityMul q half
              (RLWE.EvenOddDecomposition.smallRootRq q half hhalf) maskOdd)
            suffix)
        (parityMul q half maskOdd prefixSecret +
          parityMul q half maskEven suffix) := by
  cases half with
  | zero => omega
  | succ half =>
      rw [paritySecret_eq_prefix_add_suffix]
      rw [parityMul_add_right]
      have heven :
          parityMul q (2 * (half + 1))
              (parityJoin q (half + 1) maskEven maskOdd)
              (parityJoin q (half + 1) prefixSecret 0) =
            parityJoin q (half + 1)
              (parityMul q (half + 1) maskEven prefixSecret)
              (parityMul q (half + 1) maskOdd prefixSecret) := by
        simpa [parityMul, parityJoin, RLWE.EvenOddDecomposition.proofMul] using
          (RLWE.EvenOddDecomposition.joinRq_commRing_mul_even
            q (half + 1) hhalf maskEven maskOdd prefixSecret)
      have hodd :
          parityMul q (2 * (half + 1))
              (parityJoin q (half + 1) maskEven maskOdd)
              (parityJoin q (half + 1) 0 suffix) =
            parityJoin q (half + 1)
              (parityMul q (half + 1)
                (parityMul q (half + 1)
                  (RLWE.EvenOddDecomposition.smallRootRq q (half + 1) hhalf) maskOdd)
                suffix)
              (parityMul q (half + 1) maskEven suffix) := by
        simpa [parityMul, parityJoin, RLWE.EvenOddDecomposition.proofMul] using
          (RLWE.EvenOddDecomposition.joinRq_commRing_mul_odd
            q (half + 1) hhalf maskEven maskOdd suffix)
      rw [heven, hodd]
      rw [← parityJoin_add]

/-- Multiplication by an even-supported prefix is two ordinary half-ring products. -/
theorem parityJoin_mul_prefix
    (q half : ℕ) [Nontrivial (ZMod q)] (hhalf : 0 < half)
    (maskEven maskOdd prefixSecret : RLWE.Rq q half) :
    parityMul q (2 * half) (parityJoin q half maskEven maskOdd)
        (parityJoin q half prefixSecret 0) =
      parityJoin q half (parityMul q half maskEven prefixSecret)
        (parityMul q half maskOdd prefixSecret) := by
  cases half with
  | zero => omega
  | succ half =>
      simpa [parityMul, parityJoin, RLWE.EvenOddDecomposition.proofMul] using
        (RLWE.EvenOddDecomposition.joinRq_commRing_mul_even
          q (half + 1) hhalf maskEven maskOdd prefixSecret)

/-- Multiplication by an odd-supported suffix has the public `Y` twist in its even half. -/
theorem parityJoin_mul_suffix
    (q half : ℕ) [Nontrivial (ZMod q)] (hhalf : 0 < half)
    (maskEven maskOdd suffix : RLWE.Rq q half) :
    parityMul q (2 * half) (parityJoin q half maskEven maskOdd)
        (parityJoin q half 0 suffix) =
      parityJoin q half
        (parityMul q half
          (parityMul q half
            (RLWE.EvenOddDecomposition.smallRootRq q half hhalf) maskOdd) suffix)
        (parityMul q half maskEven suffix) := by
  cases half with
  | zero => omega
  | succ half =>
      simpa [parityMul, parityJoin, RLWE.EvenOddDecomposition.proofMul] using
        (RLWE.EvenOddDecomposition.joinRq_commRing_mul_odd
          q (half + 1) hhalf maskEven maskOdd suffix)

/-- Two small-ring rows consumed to construct one full-ring row. -/
abbrev HalfRowPair (q half : ℕ) :=
  (RLWE.Rq q half × RLWE.Rq q half) ×
    (RLWE.Rq q half × RLWE.Rq q half)

/-- Add the publicly known odd-secret contribution after joining two half-ring samples. -/
def assembleParityZeroRow (q half : ℕ) (suffix : RLWE.Rq q half)
    (source : HalfRowPair q half) : NativeRow (RLWE.Rq q (2 * half)) :=
  let mask := parityJoin q half source.1.1 source.2.1
  let prefixBody := parityJoin q half source.1.2 source.2.2
  (mask, prefixBody + parityMul q (2 * half) mask (parityJoin q half 0 suffix))

/-- Real-source identity: two half-ring RLWE samples under `P` produce one full-ring
homogeneous row under `Phi(P,Z)`, preserving the joined error exactly. -/
theorem assembleParityZeroRow_real
    (q half : ℕ) [Nontrivial (ZMod q)] (hhalf : 0 < half)
    (prefixSecret suffix maskEven maskOdd errorEven errorOdd : RLWE.Rq q half) :
    assembleParityZeroRow q half suffix
        ((maskEven, parityMul q half maskEven prefixSecret + errorEven),
          (maskOdd, parityMul q half maskOdd prefixSecret + errorOdd)) =
      (parityJoin q half maskEven maskOdd,
        parityMul q (2 * half) (parityJoin q half maskEven maskOdd)
            (paritySecret q half prefixSecret suffix) +
          parityJoin q half errorEven errorOdd) := by
  apply Prod.ext
  · rfl
  · simp only [assembleParityZeroRow]
    rw [parityJoin_add q half
      (parityMul q half maskEven prefixSecret)
      (parityMul q half maskOdd prefixSecret) errorEven errorOdd]
    rw [parityJoin_mul q half hhalf maskEven maskOdd prefixSecret suffix]
    rw [parityJoin_add q half
      (parityMul q half maskEven prefixSecret)
      (parityMul q half maskOdd prefixSecret)
      (parityMul q half
        (parityMul q half
          (RLWE.EvenOddDecomposition.smallRootRq q half hhalf) maskOdd) suffix)
      (parityMul q half maskEven suffix)]
    rw [parityJoin_mul_suffix q half hhalf maskEven maskOdd suffix]
    abel

/-- Recover the two half rows from a full row after removing the known suffix contribution. -/
def splitParityZeroRow (q half : ℕ) (suffix : RLWE.Rq q half)
    (row : NativeRow (RLWE.Rq q (2 * half))) : HalfRowPair q half :=
  let mask := RLWE.EvenOddDecomposition.ringParityEquiv q half row.1
  let prefixBody := RLWE.EvenOddDecomposition.ringParityEquiv q half
    (row.2 - parityMul q (2 * half) row.1 (parityJoin q half 0 suffix))
  ((mask.1, prefixBody.1), (mask.2, prefixBody.2))

@[simp]
theorem splitParityZeroRow_assemble
    (q half : ℕ) (suffix : RLWE.Rq q half) (source : HalfRowPair q half) :
    splitParityZeroRow q half suffix
        (assembleParityZeroRow q half suffix source) = source := by
  rcases source with ⟨⟨maskEven, bodyEven⟩, ⟨maskOdd, bodyOdd⟩⟩
  unfold splitParityZeroRow assembleParityZeroRow
  dsimp only
  let shift := parityMul q (2 * half) (parityJoin q half maskEven maskOdd)
    (parityJoin q half 0 suffix)
  have hcancel : parityJoin q half bodyEven bodyOdd + shift - shift =
      parityJoin q half bodyEven bodyOdd := add_sub_cancel_right _ _
  change
    ((((RLWE.EvenOddDecomposition.ringParityEquiv q half)
          (parityJoin q half maskEven maskOdd)).1,
        ((RLWE.EvenOddDecomposition.ringParityEquiv q half)
          (parityJoin q half bodyEven bodyOdd + shift - shift)).1),
      (((RLWE.EvenOddDecomposition.ringParityEquiv q half)
          (parityJoin q half maskEven maskOdd)).2,
        ((RLWE.EvenOddDecomposition.ringParityEquiv q half)
          (parityJoin q half bodyEven bodyOdd + shift - shift)).2)) =
      ((maskEven, bodyEven), (maskOdd, bodyOdd))
  rw [hcancel]
  simp [parityJoin]

@[simp]
theorem assembleParityZeroRow_split
    (q half : ℕ) (suffix : RLWE.Rq q half)
    (row : NativeRow (RLWE.Rq q (2 * half))) :
    assembleParityZeroRow q half suffix
        (splitParityZeroRow q half suffix row) = row := by
  rcases row with ⟨mask, body⟩
  unfold splitParityZeroRow assembleParityZeroRow
  dsimp only
  unfold parityJoin
  rw [RLWE.EvenOddDecomposition.joinRq_ringParityEquiv]
  rw [RLWE.EvenOddDecomposition.joinRq_ringParityEquiv]
  rw [sub_add_cancel]

/-- The two-half-row construction is a bijection for every fixed suffix. -/
theorem assembleParityZeroRow_bijective
    (q half : ℕ) (suffix : RLWE.Rq q half) :
    Function.Bijective (assembleParityZeroRow q half suffix) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨splitParityZeroRow q half suffix,
      splitParityZeroRow_assemble q half suffix,
      assembleParityZeroRow_split q half suffix⟩

/-- Uniform half-ring masks and bodies produce an exactly uniform full-ring row. -/
theorem assembleParityZeroRow_uniform_evalDist
    (q half : ℕ) [NeZero q] (suffix : RLWE.Rq q half) :
    evalDist (assembleParityZeroRow q half suffix <$>
        ($ᵗ (HalfRowPair q half))) =
      evalDist ($ᵗ (NativeRow (RLWE.Rq q (2 * half)))) :=
  evalDist_map_bijective_uniform_cross
    (α := HalfRowPair q half)
    (β := NativeRow (RLWE.Rq q (2 * half)))
    (assembleParityZeroRow q half suffix)
    (assembleParityZeroRow_bijective q half suffix)

/-! ## Public aggregation exposes the quadratic ciphertext -/

/-- Public weighted aggregate of a ring-row family. -/
def aggregateMask {R Index : Type} [CommRing R] [Fintype Index]
    (basis masks : Index → R) : R :=
  ∑ coordinate, basis coordinate * masks coordinate

/-- Corresponding weighted aggregate error. -/
def aggregateError {R Index : Type} [CommRing R] [Fintype Index]
    (basis errors : Index → R) : R :=
  ∑ coordinate, basis coordinate * errors coordinate

/-- Aggregating one normalized nonce row per prefix coordinate yields one RLWE row encrypting
`-h * E(P) * S`. -/
theorem aggregateNonceBody_eq
    {R Index : Type} [CommRing R] [Fintype Index]
    (basis masks errors : Index → R) (prefixBits : Index → Bool)
    (secret gadget : R) :
    (∑ coordinate,
      basis coordinate *
        (masks coordinate * secret -
          gadget * bitScalar (prefixBits coordinate) * secret + errors coordinate)) =
      aggregateMask basis masks * secret -
        gadget * prefixEmbedding basis prefixBits * secret +
          aggregateError basis errors := by
  unfold aggregateMask aggregateError prefixEmbedding
  calc
    (∑ coordinate,
        basis coordinate *
          (masks coordinate * secret -
            gadget * bitScalar (prefixBits coordinate) * secret + errors coordinate)) =
        ∑ coordinate,
          ((basis coordinate * (masks coordinate * secret) -
            basis coordinate *
              (gadget * bitScalar (prefixBits coordinate) * secret)) +
            basis coordinate * errors coordinate) := by
          apply Finset.sum_congr rfl
          intro coordinate _
          ring
    _ =
        (∑ coordinate, basis coordinate * (masks coordinate * secret)) -
          (∑ coordinate,
            basis coordinate *
              (gadget * bitScalar (prefixBits coordinate) * secret)) +
          ∑ coordinate, basis coordinate * errors coordinate := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      rw [show
          (∑ coordinate, basis coordinate * (masks coordinate * secret)) =
            (∑ coordinate, basis coordinate * masks coordinate) * secret by
        calc
          _ = ∑ coordinate, (basis coordinate * masks coordinate) * secret := by
            apply Finset.sum_congr rfl
            intro coordinate _
            ring
          _ = _ := (Finset.sum_mul ..).symm]
      rw [show
          (∑ coordinate,
            basis coordinate *
              (gadget * bitScalar (prefixBits coordinate) * secret)) =
            (gadget * ∑ coordinate,
              bitScalar (prefixBits coordinate) * basis coordinate) * secret by
        calc
          _ = ∑ coordinate,
              (gadget * (bitScalar (prefixBits coordinate) * basis coordinate)) *
                secret := by
            apply Finset.sum_congr rfl
            intro coordinate _
            ring
          _ = (∑ coordinate,
              gadget * (bitScalar (prefixBits coordinate) * basis coordinate)) *
                secret := (Finset.sum_mul ..).symm
          _ = _ := by rw [Finset.mul_sum]]

/-- If the encrypted prefix embedding is the complete secret, public aggregation produces the
square-KDM message `-h * S^2`. -/
theorem aggregateNonceBody_eq_square
    {R Index : Type} [CommRing R] [Fintype Index]
    (basis masks errors : Index → R) (prefixBits : Index → Bool)
    (secret gadget : R)
    (hsecret : prefixEmbedding basis prefixBits = secret) :
    (∑ coordinate,
      basis coordinate *
        (masks coordinate * secret -
          gadget * bitScalar (prefixBits coordinate) * secret + errors coordinate)) =
      aggregateMask basis masks * secret - gadget * secret ^ 2 +
        aggregateError basis errors := by
  rw [aggregateNonceBody_eq, hsecret]
  ring

/-- If one public aggregation weight is a unit, the aggregate of independent uniform masks is
exactly uniform. -/
theorem aggregateMask_uniform_evalDist_of_isUnit
    {R : Type} {count : ℕ} [CommRing R] [Fintype R] [DecidableEq R]
    [SampleableType (Fin count → R)] [SampleableType R]
    (basis : Fin count → R) (selected : Fin count)
    (hunit : IsUnit (basis selected)) :
    evalDist (aggregateMask basis <$> ($ᵗ (Fin count → R))) =
      evalDist ($ᵗ R) := by
  change evalDist (maskCombination basis <$> ($ᵗ (Fin count → R))) =
    evalDist ($ᵗ R)
  simpa [add_zero] using
    (NativeTRGSWSpectralInfeasibility.evalDist_maskCombination_add_uniform_of_isUnit
      basis selected hunit 0)

/-! ## Direct match-and-square source compiler -/

/-- A direct public compiler from one decisional source transcript.  Unlike a two-branch CVZR
compiler, it maps the real source directly to `targetView true` and the uniform source directly to
`targetView false`; consequently no branch-selection factor is incurred. -/
structure ExactDirectSourceCompiler
    {Sample Secret Output View : Type} [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (targetView : Bool → ProbComp View) where
  build : (Sample × Output) → ProbComp View
  realLaw :
    evalDist (LearningWithErrors.distr problem >>= build) =
      evalDist (targetView true)
  uniformLaw :
    evalDist (LearningWithErrors.uniformDistr problem >>= build) =
      evalDist (targetView false)

namespace ExactDirectSourceCompiler

variable {Sample Secret Output View : Type} [Add Output]
  {problem : LearningWithErrors.Problem Sample Secret Output}
  {targetView : Bool → ProbComp View}

/-- The direct source adversary. -/
def reduction (compiler : ExactDirectSourceCompiler problem targetView)
    (distinguisher : Distinguisher View) :
    LearningWithErrors.Adversary problem :=
  fun transcript ↦ compiler.build transcript >>= distinguisher

/-- Exact equality between the direct source advantage and the target distinguishing advantage. -/
theorem reduction_advantage_eq_targetAdvantage
    (compiler : ExactDirectSourceCompiler problem targetView)
    (distinguisher : Distinguisher View) :
    LearningWithErrors.advantage problem (compiler.reduction distinguisher) =
      DirectSubsetKeyBRK.targetAdvantage targetView distinguisher := by
  have hreal :
      evalDist (LearningWithErrors.distr problem >>= fun transcript ↦
        compiler.build transcript >>= distinguisher) =
        evalDist (targetView true >>= distinguisher) := by
    rw [show (LearningWithErrors.distr problem >>= fun transcript ↦
          compiler.build transcript >>= distinguisher) =
        (LearningWithErrors.distr problem >>= compiler.build) >>= distinguisher by
      simp [bind_assoc]]
    rw [evalDist_bind, compiler.realLaw, ← evalDist_bind]
  have huniform :
      evalDist (LearningWithErrors.uniformDistr problem >>= fun transcript ↦
        compiler.build transcript >>= distinguisher) =
        evalDist (targetView false >>= distinguisher) := by
    rw [show (LearningWithErrors.uniformDistr problem >>= fun transcript ↦
          compiler.build transcript >>= distinguisher) =
        (LearningWithErrors.uniformDistr problem >>= compiler.build) >>= distinguisher by
      simp [bind_assoc]]
    rw [evalDist_bind, compiler.uniformLaw, ← evalDist_bind]
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold LearningWithErrors.game0 LearningWithErrors.game1 reduction
    DirectSubsetKeyBRK.targetAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl hreal, probOutput_congr rfl huniform]

end ExactDirectSourceCompiler

/-! ## Ordinary half-ring RLWE endpoint -/

/-- Ordinary degree-`half` binary-secret RLWE with the requested total number of half-ring
samples. -/
noncomputable def halfRingBinaryRLWEProblem
    (q half samples : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q half)) :=
  RLWE.problem q half samples
    (binarySmallSecretSampler q half) errorSampler

/-- The exact compiler target is the real match-and-square game versus its fair ideal endpoint. -/
abbrev ExactHalfRingMatchSquareCompiler
    {q half samples : ℕ} [NeZero q]
    {Suffix : Type}
    (errorSampler : ProbComp (RLWE.Rq q half))
    (keySampler : ProbComp (BinarySecret half × Suffix))
    (fakePrefixSampler : ProbComp (BinarySecret half))
    (plus minus : BinarySecret half →
      (BinarySecret half × Suffix) → ProbComp Bool) :=
  ExactDirectSourceCompiler
    (halfRingBinaryRLWEProblem q half samples errorSampler)
    (completeViewZeroRowTargetView keySampler fakePrefixSampler plus minus)

/-- Ordinary-RLWE adversary implementing the complete two-copy squared-bias test. -/
def halfRingMatchSquareReduction
    {q half samples : ℕ} [NeZero q]
    {Suffix : Type}
    {errorSampler : ProbComp (RLWE.Rq q half)}
    {keySampler : ProbComp (BinarySecret half × Suffix)}
    {fakePrefixSampler : ProbComp (BinarySecret half)}
    {plus minus : BinarySecret half →
      (BinarySecret half × Suffix) → ProbComp Bool}
    (compiler : ExactHalfRingMatchSquareCompiler (samples := samples) errorSampler
      keySampler fakePrefixSampler plus minus) :
    LearningWithErrors.Adversary
      (halfRingBinaryRLWEProblem q half samples errorSampler) :=
  compiler.reduction identityDistinguisher

/-- Crucial direct-source identity: the complete-view match-and-square source term is exactly one
ordinary half-ring RLWE advantage, with no extra factor two. -/
theorem halfRingMatchSquareReduction_advantage_eq
    {q half samples : ℕ} [NeZero q]
    {Suffix : Type}
    {errorSampler : ProbComp (RLWE.Rq q half)}
    {keySampler : ProbComp (BinarySecret half × Suffix)}
    {fakePrefixSampler : ProbComp (BinarySecret half)}
    {plus minus : BinarySecret half →
      (BinarySecret half × Suffix) → ProbComp Bool}
    (compiler : ExactHalfRingMatchSquareCompiler (samples := samples) errorSampler
      keySampler fakePrefixSampler plus minus) :
    LearningWithErrors.advantage
        (halfRingBinaryRLWEProblem q half samples errorSampler)
        (halfRingMatchSquareReduction compiler) =
      completeViewZeroRowReductionAdvantage
        keySampler fakePrefixSampler plus minus := by
  unfold halfRingMatchSquareReduction
  rw [ExactDirectSourceCompiler.reduction_advantage_eq_targetAdvantage]
  exact completeViewZeroRowTargetAdvantage_eq
    keySampler fakePrefixSampler plus minus

/-! ## Sample accounting -/

/-- Number of full-ring homogeneous rows in one complete rank-`ringRank` BRK. -/
def fullRingRowsPerBRK (ringRank gadgetLevels controlLength : ℕ) : ℕ :=
  (ringRank + 1) * gadgetLevels * controlLength

/-- Half-ring samples used by one local parity-split complete view. -/
def halfRingSamplesPerView
    (ringRank gadgetLevels controlLength kskSamples auxiliarySamples : ℕ) : ℕ :=
  2 * fullRingRowsPerBRK ringRank gadgetLevels controlLength +
    kskSamples + auxiliarySamples

/-- Match-and-square consumes two conditionally independent local views. -/
def halfRingSamplesForMatchSquare
    (ringRank gadgetLevels controlLength kskSamples auxiliarySamples : ℕ) : ℕ :=
  2 * halfRingSamplesPerView ringRank gadgetLevels controlLength
    kskSamples auxiliarySamples

/-- Rank one specializes the BRK contribution to `4 * levels * controlLength`. -/
theorem halfRingSamplesPerView_rankOne
    (gadgetLevels controlLength kskSamples auxiliarySamples : ℕ) :
    halfRingSamplesPerView 1 gadgetLevels controlLength kskSamples auxiliarySamples =
      4 * gadgetLevels * controlLength + kskSamples + auxiliarySamples := by
  simp [halfRingSamplesPerView, fullRingRowsPerBRK]
  ring

/-! ## Final restricted quadratic-KDM theorem -/

/-- Complete-view native quadratic-KDM security from the direct ordinary half-ring RLWE source.

`hdiagonal` charges the two whole-view construction defects.  The exact direct compiler packages
the disjoint BRK/KSK/auxiliary construction and its prescribed joint error law.  Because its
source advantage is definitionally the match-and-square source term, the final radical contains
one ordinary RLWE advantage rather than twice that advantage. -/
theorem nativeRestrictedQuadraticKDMGap_le_halfRingRLWE
    {q half : ℕ} [NeZero q]
    {Suffix : Type} [Fintype Suffix]
    (ringRank gadgetLevels kskSamples auxiliarySamples : ℕ)
    (errorSampler : ProbComp (RLWE.Rq q half))
    (keySampler : ProbComp (BinarySecret half × Suffix))
    (prefixSampler fakePrefixSampler : ProbComp (BinarySecret half))
    (plus minus : BinarySecret half →
      (BinarySecret half × Suffix) → ProbComp Bool)
    (nativeKDMGap sigmaReal sigmaZero : ℝ)
    (compiler : ExactHalfRingMatchSquareCompiler
      (samples := halfRingSamplesForMatchSquare ringRank gadgetLevels half
        kskSamples auxiliarySamples)
      errorSampler keySampler fakePrefixSampler plus minus)
    (hmarginal : evalDist (Prod.fst <$> keySampler) = evalDist prefixSampler)
    (hdiagonal : nativeKDMGap ≤ sigmaReal + sigmaZero +
      completeViewAggregateAdvantage keySampler plus minus)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakePrefixSampler key.1 ≠ 0)
    (hoptimized : ∀ prefixValue,
      probabilityMass fakePrefixSampler prefixValue =
        Real.sqrt (probabilityMass
          (leakageLaw keySampler Prod.fst) prefixValue) /
          halfRenyiNormalizer keySampler Prod.fst) :
    nativeKDMGap ≤ sigmaReal + sigmaZero +
      Real.sqrt (2 * halfRenyiConcentration prefixSampler *
        LearningWithErrors.advantage
          (halfRingBinaryRLWEProblem q half
            (halfRingSamplesForMatchSquare ringRank gadgetLevels half
              kskSamples auxiliarySamples) errorSampler)
          (halfRingMatchSquareReduction compiler)) := by
  apply nativeCompleteViewAggregateGap_le_prefixMarginal
    keySampler prefixSampler fakePrefixSampler plus minus
    nativeKDMGap sigmaReal sigmaZero
    (LearningWithErrors.advantage
      (halfRingBinaryRLWEProblem q half
        (halfRingSamplesForMatchSquare ringRank gadgetLevels half
          kskSamples auxiliarySamples) errorSampler)
      (halfRingMatchSquareReduction compiler))
    hmarginal hdiagonal
  · rw [← halfRingMatchSquareReduction_advantage_eq compiler]
  · exact hcover
  · exact hoptimized

/-! ## The meaning of the TFHE control length -/

/-- In ordinary TFHE gate bootstrapping, every input-LWE key coordinate is a BRK control bit. -/
def standardTFHEControlLength (inputLWEDimension : ℕ) : ℕ :=
  inputLWEDimension

/-- In a genuine subset-key construction, the control length is the selected subset cardinality. -/
def subsetTFHEControlLength {ambientDimension : ℕ}
    (subset : Finset (Fin ambientDimension)) : ℕ :=
  subset.card

/-- In the parity split of a degree-`2 * half` ring, the encrypted even half has `half`
coordinates. -/
def parityTFHEControlLength (half : ℕ) : ℕ :=
  half

@[simp]
theorem parityTFHEControlLength_eq_half_degree (half : ℕ) :
    parityTFHEControlLength half = (2 * half) / 2 := by
  simp [parityTFHEControlLength]

/-- The theorem's `t` controls the number of native TRGSW ciphertexts in the BRK. -/
def bootstrappingKeyCiphertextCount (controlLength : ℕ) : ℕ :=
  controlLength

/-- It contributes linearly to the native row count. -/
theorem bootstrappingKeyRowCount_eq
    (ringRank gadgetLevels controlLength : ℕ) :
    fullRingRowsPerBRK ringRank gadgetLevels controlLength =
      TGSW.rowCount ringRank gadgetLevels * controlLength := by
  rfl

/-- The independently named key-switch digit count is not used in the control-length
definition. -/
structure TFHELengthParameters where
  controlLength : ℕ
  ringDegree : ℕ
  gadgetLevels : ℕ
  keySwitchDigitCount : ℕ

/-- Exact Rényi-half concentration of a uniform binary control prefix. -/
theorem uniformBinaryControlConcentration (controlLength : ℕ) :
    halfRenyiConcentration ($ᵗ (BinarySecret controlLength)) =
      (2 : ℝ) ^ controlLength := by
  exact halfRenyiConcentration_uniform_binaryTuple controlLength

/-- One isolated binary control coordinate has concentration at most two for every prior. -/
theorem oneCoordinateControlConcentration_le_two (sampler : ProbComp Bool) :
    halfRenyiConcentration sampler ≤ 2 := by
  simpa using halfRenyiConcentration_le_card sampler

/-- Substituting the uniform-prefix concentration into the final radical gives the exact
`2^t` complexity-leveraging loss from the note. -/
theorem uniformBinaryControl_sourceTerm
    (controlLength : ℕ) (sourceAdvantage : ℝ) :
    2 * halfRenyiConcentration ($ᵗ (BinarySecret controlLength)) * sourceAdvantage =
      2 * (2 : ℝ) ^ controlLength * sourceAdvantage := by
  rw [uniformBinaryControlConcentration]

/-- Generic sufficient source condition obtained by solving the square-root bound.  This is the
parameter-independent form of the exponent calculation in the note. -/
theorem sqrt_sourceTerm_le_target
    (concentration sourceAdvantage target : ℝ)
    (htarget : 0 ≤ target)
    (hbound : 2 * concentration * sourceAdvantage ≤ target ^ 2) :
    Real.sqrt (2 * concentration * sourceAdvantage) ≤ target := by
  rw [Real.sqrt_le_iff]
  exact ⟨htarget, hbound⟩

end

end FormalProof4FHE.TFHE.NativeTRGSWQuadraticKDMAndTFHET
