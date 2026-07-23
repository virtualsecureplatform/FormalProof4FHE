/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.Basic
import FormalProof4FHE.Probability.FiniteProduct
import Batteries.Data.Fin.OfBits

set_option autoImplicit false

/-!
# Packed Linear Circular RLWE at a Power-of-Two Modulus

This module formalizes the ring analogue of the proved *linear* circular-LWE step in
Micciancio--Vaikuntanathan (PKC 2024).  A binary polynomial `s₀` is the secret of an ordinary
binary-secret RLWE challenge.  Independently sampled higher bit planes are packed with `s₀`
coefficientwise into a uniformly random element of `R_(2^ℓ)`.  A triangular public transcript
permutation then changes the RLWE key and inserts any fixed ring-linear functions of all bit
planes.  Real and uniform games are preserved exactly, so the circular-hint advantage equals one
ordinary binary-secret RLWE advantage with no hybrid or statistical loss.

The theorem concerns direct fresh RLWE rows whose messages are linear in the bit planes.  Native
TFHE TRGSW mask rows contain products of a target scalar-key bit and a ring-key coefficient; those
degree-two messages are not covered here.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.PackedLinearCircularRLWE

noncomputable section

/- `Rq` exposes executable coefficient operations as well as the projections of its certified
`CommRing`.  Select one coherent proof-facing dictionary locally so generic ring normalization
and the matrix-LWE operations use definitionally identical algebra structures. -/
local instance packedRqCommRing (q degree : ℕ) : CommRing (RLWE.Rq q degree) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree

local instance packedRqAddCommGroup (q degree : ℕ) : AddCommGroup (RLWE.Rq q degree) :=
  (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAddCommGroup

local instance packedRqAdd (q degree : ℕ) : Add (RLWE.Rq q degree) :=
  (packedRqAddCommGroup q degree).toAdd

local instance packedRqSub (q degree : ℕ) : Sub (RLWE.Rq q degree) :=
  (packedRqAddCommGroup q degree).toSub

local instance packedRqNeg (q degree : ℕ) : Neg (RLWE.Rq q degree) :=
  (packedRqAddCommGroup q degree).toNeg

local instance packedRqZero (q degree : ℕ) : Zero (RLWE.Rq q degree) :=
  (packedRqAddCommGroup q degree).toZero

local instance packedRqMul (q degree : ℕ) : Mul (RLWE.Rq q degree) :=
  (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toMul

local instance packedRqOne (q degree : ℕ) : One (RLWE.Rq q degree) :=
  (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAddGroupWithOne.toOne

/-! ## Exact coefficientwise bit packing -/

/-- One binary polynomial, in the coefficient layout used by native TFHE. -/
abbrev BinaryPolynomial (degree : ℕ) := Fin degree → Bool

/-- Higher bit planes, stored coefficient-first. -/
abbrev HigherPlanes (extraLevels degree : ℕ) :=
  Fin degree → Fin extraLevels → Bool

/-- The low binary polynomial together with all independently sampled higher planes. -/
abbrev SplitSecret (extraLevels degree : ℕ) :=
  BinaryPolynomial degree × HigherPlanes extraLevels degree

/-- All `extraLevels + 1` coefficient bit planes of one packed ring secret. -/
abbrev PackedBits (extraLevels degree : ℕ) :=
  Fin degree → Fin (extraLevels + 1) → Bool

/-- Put the low polynomial in bit plane zero and the remaining planes above it. -/
def join {extraLevels degree : ℕ}
    (secret : SplitSecret extraLevels degree) : PackedBits extraLevels degree :=
  fun coefficient ↦ Fin.cases (secret.1 coefficient) (secret.2 coefficient)

/-- Split bit plane zero from all higher planes. -/
def split {extraLevels degree : ℕ}
    (bits : PackedBits extraLevels degree) : SplitSecret extraLevels degree :=
  (fun coefficient ↦ bits coefficient 0,
    fun coefficient level ↦ bits coefficient level.succ)

@[simp]
theorem split_join {extraLevels degree : ℕ}
    (secret : SplitSecret extraLevels degree) :
    split (join secret) = secret := by
  apply Prod.ext
  · funext coefficient
    rfl
  · funext coefficient level
    rfl

@[simp]
theorem join_split {extraLevels degree : ℕ}
    (bits : PackedBits extraLevels degree) :
    join (split bits) = bits := by
  funext coefficient level
  refine Fin.cases ?_ (fun higher ↦ ?_) level
  · rfl
  · rfl

/-- Splitting off bit plane zero is an equivalence. -/
def splitEquiv (extraLevels degree : ℕ) :
    SplitSecret extraLevels degree ≃ PackedBits extraLevels degree where
  toFun := join
  invFun := split
  left_inv := split_join
  right_inv := join_split

/-- Little-endian bits are in bijection with one residue modulo the matching power of two. -/
def coefficientBitsEquiv (levels : ℕ) :
    (Fin levels → Bool) ≃ ZMod (2 ^ levels) where
  toFun := fun bits ↦ (Nat.ofBits bits : ZMod (2 ^ levels))
  invFun := fun value index ↦ value.val.testBit index.val
  left_inv := by
    intro bits
    funext index
    change ((Nat.ofBits bits : ZMod (2 ^ levels)).val.testBit index.val) = bits index
    rw [ZMod.val_natCast,
      Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow bits),
      Nat.testBit_ofBits_lt bits index.val index.isLt]
  right_inv := by
    intro value
    apply ZMod.val_injective
    simp [Nat.ofBits_testBit,
      Nat.mod_eq_of_lt (ZMod.val_lt value)]

/-- Coefficientwise little-endian packing is an equivalence from all bit planes to `R_q`. -/
def packedBitsEquiv (extraLevels degree : ℕ) :
    PackedBits extraLevels degree ≃ RLWE.Rq (2 ^ (extraLevels + 1)) degree where
  toFun := fun bits ↦ LatticeCrypto.Poly.ofPi fun coefficient ↦
    coefficientBitsEquiv (extraLevels + 1) (bits coefficient)
  invFun := fun value coefficient ↦
    (coefficientBitsEquiv (extraLevels + 1)).symm
      (LatticeCrypto.Poly.toPi value coefficient)
  left_inv := by
    intro bits
    funext coefficient
    simp only [LatticeCrypto.Poly.toPi_ofPi]
    exact (coefficientBitsEquiv (extraLevels + 1)).symm_apply_apply (bits coefficient)
  right_inv := by
    intro value
    change LatticeCrypto.Poly.ofPi (fun coefficient ↦
        (coefficientBitsEquiv (extraLevels + 1))
          ((coefficientBitsEquiv (extraLevels + 1)).symm
            (LatticeCrypto.Poly.toPi value coefficient))) = value
    rw [show (fun coefficient ↦
          (coefficientBitsEquiv (extraLevels + 1))
            ((coefficientBitsEquiv (extraLevels + 1)).symm
              (LatticeCrypto.Poly.toPi value coefficient))) =
        LatticeCrypto.Poly.toPi value by
      funext coefficient
      exact (coefficientBitsEquiv (extraLevels + 1)).apply_symm_apply
        (LatticeCrypto.Poly.toPi value coefficient)]
    exact LatticeCrypto.Poly.ofPi_toPi value

/-- Assemble every coefficient from its little-endian bit planes. -/
def assemble {extraLevels degree : ℕ} (bits : PackedBits extraLevels degree) :
    RLWE.Rq (2 ^ (extraLevels + 1)) degree :=
  LatticeCrypto.Poly.ofPi fun coefficient ↦
    (Nat.ofBits (bits coefficient) : ZMod (2 ^ (extraLevels + 1)))

@[simp]
theorem assemble_coefficient {extraLevels degree : ℕ}
    (bits : PackedBits extraLevels degree) (coefficient : Fin degree) :
    LatticeCrypto.Poly.toPi (assemble bits) coefficient =
      (Nat.ofBits (bits coefficient) : ZMod (2 ^ (extraLevels + 1))) := by
  simp [assemble]

/-- The public additive key offset contributed by the higher bit planes. -/
def higherDelta {extraLevels degree : ℕ}
    (higher : HigherPlanes extraLevels degree) :
    RLWE.Rq (2 ^ (extraLevels + 1)) degree :=
  assemble (join (fun _ ↦ false, higher))

/-- The locally selected proof-facing addition agrees with the executable coefficient addition. -/
private theorem packedAdd_eq_executable {q degree : ℕ}
    (left right : RLWE.Rq q degree) :
    @HAdd.hAdd (RLWE.Rq q degree) (RLWE.Rq q degree) (RLWE.Rq q degree)
        (@instHAdd (RLWE.Rq q degree) (packedRqAdd q degree)) left right =
      @HAdd.hAdd (RLWE.Rq q degree) (RLWE.Rq q degree) (RLWE.Rq q degree)
        (@instHAdd (RLWE.Rq q degree)
          (RLWE.negacyclicRing q degree).instAddPoly) left right := by
  cases degree with
  | zero =>
      apply LatticeCrypto.NegacyclicRing.poly_ext
      intro coefficient
      exact coefficient.elim0
  | succ degree => rfl

/-- Packing splits exactly into the embedded low binary polynomial plus a public-to-the-reduction
offset determined only by the independently sampled higher planes. -/
theorem assemble_join_eq_low_add_higherDelta {extraLevels degree : ℕ}
    (low : BinaryPolynomial degree) (higher : HigherPlanes extraLevels degree) :
    assemble (join (low, higher)) =
      embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree low + higherDelta higher := by
  rw [packedAdd_eq_executable]
  apply LatticeCrypto.NegacyclicRing.poly_ext
  intro coefficient
  rw [LatticeCrypto.NegacyclicRing.coeff_add]
  simp only [LatticeCrypto.vectorNegacyclicRing_backend,
    LatticeCrypto.vectorBackend_coeff]
  change LatticeCrypto.Poly.toPi (assemble (join (low, higher))) coefficient =
    LatticeCrypto.Poly.toPi
        (embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree low) coefficient +
      LatticeCrypto.Poly.toPi (higherDelta higher) coefficient
  rw [assemble_coefficient]
  simp only [embedBinaryPolynomial, LatticeCrypto.Poly.toPi_ofPi,
    higherDelta, assemble_coefficient]
  change (Nat.ofBits (Fin.cases (low coefficient) (higher coefficient)) :
      ZMod (2 ^ (extraLevels + 1))) =
    embedBit (low coefficient) +
      (Nat.ofBits (Fin.cases false (higher coefficient)) :
        ZMod (2 ^ (extraLevels + 1)))
  rw [Nat.ofBits_succ, Nat.ofBits_succ]
  cases low coefficient <;> simp [embedBit, Function.comp_def, add_comm]

/-- The low/higher representation packs bijectively into the complete power-of-two ring. -/
theorem assemble_join_bijective (extraLevels degree : ℕ) :
    Function.Bijective
      (fun secret : SplitSecret extraLevels degree ↦ assemble (join secret)) :=
  by
    have hassemble :
        (fun bits : PackedBits extraLevels degree ↦ assemble bits) =
          packedBitsEquiv extraLevels degree := by
      funext bits
      rfl
    rw [show (fun secret : SplitSecret extraLevels degree ↦ assemble (join secret)) =
        (fun bits : PackedBits extraLevels degree ↦ assemble bits) ∘ join by rfl,
      hassemble]
    exact ((packedBitsEquiv extraLevels degree).bijective).comp
      (splitEquiv extraLevels degree).bijective

/-- Independent low and higher bit planes. -/
def sampleSplitSecret (extraLevels degree : ℕ) :
    ProbComp (SplitSecret extraLevels degree) := do
  let low ← $ᵗ (BinaryPolynomial degree)
  let higher ← $ᵗ (HigherPlanes extraLevels degree)
  return (low, higher)

/-- The explicit independent sampler is the canonical uniform product law. -/
theorem sampleSplitSecret_evalDist_eq_uniform (extraLevels degree : ℕ) :
    evalDist (sampleSplitSecret extraLevels degree) =
      evalDist ($ᵗ (SplitSecret extraLevels degree)) := by
  have uniformProduct :
      ($ᵗ (SplitSecret extraLevels degree) :
        ProbComp (SplitSecret extraLevels degree)) =
      Prod.mk <$> ($ᵗ (BinaryPolynomial degree)) <*>
        ($ᵗ (HigherPlanes extraLevels degree)) := rfl
  rw [uniformProduct]
  simp [sampleSplitSecret, monad_norm]

/-- **Exact secret-law step.** Packing independent uniform bit planes gives a uniform element of
the full negacyclic ring at modulus `2^(extraLevels+1)`. -/
theorem assemble_sampleSplitSecret_evalDist (extraLevels degree : ℕ) :
    evalDist
        ((fun secret : SplitSecret extraLevels degree ↦ assemble (join secret)) <$>
          sampleSplitSecret extraLevels degree) =
      evalDist ($ᵗ RLWE.Rq (2 ^ (extraLevels + 1)) degree) := by
  let pack := fun secret : SplitSecret extraLevels degree ↦ assemble (join secret)
  calc
    _ = evalDist (pack <$> ($ᵗ (SplitSecret extraLevels degree))) := by
      simpa only [pack, evalDist_map] using congrArg
        (fun distribution ↦ pack <$> distribution)
        (sampleSplitSecret_evalDist_eq_uniform extraLevels degree)
    _ = _ := evalDist_map_bijective_uniform_cross
      (α := SplitSecret extraLevels degree)
      (β := RLWE.Rq (2 ^ (extraLevels + 1)) degree)
      pack (assemble_join_bijective extraLevels degree)

/-! ## Direct ring-linear circular messages -/

/-- Public coefficients of a fixed batch of ring-linear functions of all bit planes. -/
abbrev Coefficients (extraLevels degree samples : ℕ) :=
  Fin (extraLevels + 1) → Fin samples →
    RLWE.Rq (2 ^ (extraLevels + 1)) degree

/-- Public constant terms of the message batch. -/
abbrev Offset (extraLevels degree samples : ℕ) :=
  Fin samples → RLWE.Rq (2 ^ (extraLevels + 1)) degree

/-- Embed one selected bit plane as a binary polynomial in the packed ring. -/
def embeddedPlane {extraLevels degree : ℕ}
    (bits : PackedBits extraLevels degree) (level : Fin (extraLevels + 1)) :
    RLWE.Rq (2 ^ (extraLevels + 1)) degree :=
  embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree
    (fun coefficient ↦ bits coefficient level)

/-- Evaluate an arbitrary fixed ring-linear message batch on all packed bit planes. -/
def linearMessage {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (secret : SplitSecret extraLevels degree) :
    Fin samples → RLWE.Rq (2 ^ (extraLevels + 1)) degree :=
  fun sample ↦ offset sample +
    ∑ level, embeddedPlane (join secret) level * coefficients level sample

/-- The part of the message known after the reduction samples all higher planes. -/
def higherMessage {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (higher : HigherPlanes extraLevels degree) :
    Fin samples → RLWE.Rq (2 ^ (extraLevels + 1)) degree :=
  fun sample ↦ offset sample +
    ∑ level : Fin extraLevels,
      embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree
          (fun coefficient ↦ higher coefficient level) *
        coefficients level.succ sample

/-- Plane zero is the only secret-dependent part not known to the reduction. -/
theorem linearMessage_eq_low_add_higherMessage
    {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (low : BinaryPolynomial degree) (higher : HigherPlanes extraLevels degree) :
    linearMessage coefficients offset (low, higher) =
      fun sample ↦
        embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree low *
            coefficients 0 sample +
          higherMessage coefficients offset higher sample := by
  funext sample
  simp only [linearMessage, higherMessage]
  rw [Fin.sum_univ_succ]
  simp only [embeddedPlane, join, Fin.cases_zero, Fin.cases_succ]
  calc
    _ = (offset sample +
          embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree low *
            coefficients 0 sample) +
        ∑ level,
          embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree
              (fun coefficient ↦ higher coefficient level) *
            coefficients level.succ sample := (add_assoc _ _ _).symm
    _ = (embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree low *
          coefficients 0 sample + offset sample) +
        ∑ level,
          embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree
              (fun coefficient ↦ higher coefficient level) *
            coefficients level.succ sample := by
      rw [add_comm (offset sample)]
    _ = _ := add_assoc _ _ _

/-- Rank-one ring challenge type for the direct circular batch. -/
abbrev Challenge (extraLevels degree samples : ℕ) :=
  Matrix (Fin 1) (Fin samples) (RLWE.Rq (2 ^ (extraLevels + 1)) degree)

/-- Ring output vector for the direct circular batch. -/
abbrev Output (extraLevels degree samples : ℕ) :=
  Fin samples → RLWE.Rq (2 ^ (extraLevels + 1)) degree

/-- Public rank-one RLWE transcript. -/
abbrev Transcript (extraLevels degree samples : ℕ) :=
  FormalProof4FHE.LWE.BatchTranscript
    (RLWE.Rq (2 ^ (extraLevels + 1)) degree) 1 samples

/-- The ordinary source secret is just the low binary polynomial. -/
def sourceEmbed {extraLevels degree : ℕ} (low : BinaryPolynomial degree) :
    Fin 1 → RLWE.Rq (2 ^ (extraLevels + 1)) degree :=
  fun _ ↦ embedBinaryPolynomial (2 ^ (extraLevels + 1)) degree low

/-- The target encryption key is the coefficientwise packed secret. -/
def targetEmbed {extraLevels degree : ℕ}
    (secret : SplitSecret extraLevels degree) :
    Fin 1 → RLWE.Rq (2 ^ (extraLevels + 1)) degree :=
  fun _ ↦ assemble (join secret)

/-- Translate the public challenge to absorb the plane-zero linear message. -/
def shiftChallenge {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (challenge : Challenge extraLevels degree samples) :
    Challenge extraLevels degree samples :=
  fun _ sample ↦ challenge 0 sample - coefficients 0 sample

/-- Undo the plane-zero challenge translation. -/
def unshiftChallenge {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (challenge : Challenge extraLevels degree samples) :
    Challenge extraLevels degree samples :=
  fun _ sample ↦ challenge 0 sample + coefficients 0 sample

@[simp]
theorem unshiftChallenge_shiftChallenge {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (challenge : Challenge extraLevels degree samples) :
    unshiftChallenge coefficients (shiftChallenge coefficients challenge) = challenge := by
  funext coordinate sample
  rw [Subsingleton.elim coordinate 0]
  simp only [unshiftChallenge, shiftChallenge]
  exact sub_add_cancel _ _

@[simp]
theorem shiftChallenge_unshiftChallenge {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (challenge : Challenge extraLevels degree samples) :
    shiftChallenge coefficients (unshiftChallenge coefficients challenge) = challenge := by
  funext coordinate sample
  rw [Subsingleton.elim coordinate 0]
  simp only [unshiftChallenge, shiftChallenge]
  exact add_sub_cancel_right _ _

/-- The public challenge translation is a permutation. -/
theorem shiftChallenge_bijective {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples) :
    Function.Bijective (shiftChallenge coefficients) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unshiftChallenge coefficients,
      unshiftChallenge_shiftChallenge coefficients,
      shiftChallenge_unshiftChallenge coefficients⟩

/-- Triangular transcript transform implementing both message insertion and the additive key
change from the low plane to the packed secret. -/
def transformTranscript {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (higher : HigherPlanes extraLevels degree)
    (transcript : Transcript extraLevels degree samples) :
    Transcript extraLevels degree samples :=
  let challenge := shiftChallenge coefficients transcript.1
  (challenge, transcript.2 +
    vecMul (fun _ : Fin 1 ↦ higherDelta higher) challenge +
      higherMessage coefficients offset higher)

/-- Inverse triangular transcript transform. -/
def untransformTranscript {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (higher : HigherPlanes extraLevels degree)
    (transcript : Transcript extraLevels degree samples) :
    Transcript extraLevels degree samples :=
  (unshiftChallenge coefficients transcript.1,
    transcript.2 -
      vecMul (fun _ : Fin 1 ↦ higherDelta higher) transcript.1 -
        higherMessage coefficients offset higher)

private theorem add_add_sub_sub_cancel {A : Type} [AddCommGroup A]
    (left middle right : A) :
    left + middle + right - middle - right = left := by
  abel

private theorem sub_sub_add_add_cancel {A : Type} [AddCommGroup A]
    (left middle right : A) :
    left - middle - right + middle + right = left := by
  abel

@[simp]
theorem untransformTranscript_transformTranscript
    {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (higher : HigherPlanes extraLevels degree)
    (transcript : Transcript extraLevels degree samples) :
    untransformTranscript coefficients offset higher
      (transformTranscript coefficients offset higher transcript) = transcript := by
  apply Prod.ext
  · exact unshiftChallenge_shiftChallenge coefficients transcript.1
  · funext sample
    simp [untransformTranscript, transformTranscript]
    exact add_add_sub_sub_cancel
      (A := RLWE.Rq (2 ^ (extraLevels + 1)) degree)
      (transcript.2 sample)
      (vecMul (fun _ : Fin 1 ↦ higherDelta higher)
        (shiftChallenge coefficients transcript.1) sample)
      (higherMessage coefficients offset higher sample)

@[simp]
theorem transformTranscript_untransformTranscript
    {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (higher : HigherPlanes extraLevels degree)
    (transcript : Transcript extraLevels degree samples) :
    transformTranscript coefficients offset higher
      (untransformTranscript coefficients offset higher transcript) = transcript := by
  apply Prod.ext
  · exact shiftChallenge_unshiftChallenge coefficients transcript.1
  · funext sample
    simp [untransformTranscript, transformTranscript]
    exact sub_sub_add_add_cancel
      (A := RLWE.Rq (2 ^ (extraLevels + 1)) degree)
      (transcript.2 sample)
      (vecMul (fun _ : Fin 1 ↦ higherDelta higher) transcript.1 sample)
      (higherMessage coefficients offset higher sample)

/-- For every fixed higher-plane choice, the complete transcript transform is a permutation. -/
theorem transformTranscript_bijective {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (higher : HigherPlanes extraLevels degree) :
    Function.Bijective (transformTranscript coefficients offset higher) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untransformTranscript coefficients offset higher,
      untransformTranscript_transformTranscript coefficients offset higher,
      transformTranscript_untransformTranscript coefficients offset higher⟩

/-- The transform sends one ordinary binary-secret RLWE transcript to the intended packed-key
ring-linear circular transcript, preserving every error exactly. -/
theorem transformTranscript_real {extraLevels degree samples : ℕ}
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (low : BinaryPolynomial degree) (higher : HigherPlanes extraLevels degree)
    (challenge : Challenge extraLevels degree samples)
    (error : Output extraLevels degree samples) :
    transformTranscript coefficients offset higher
        (TLWE.batchAssemble (sourceEmbed low) challenge 0 error) =
      TLWE.batchAssemble (targetEmbed (low, higher))
        (shiftChallenge coefficients challenge)
        (linearMessage coefficients offset (low, higher)) error := by
  apply Prod.ext
  · rfl
  · funext sample
    rw [linearMessage_eq_low_add_higherMessage]
    have hkey := assemble_join_eq_low_add_higherDelta low higher
    simp only [transformTranscript, TLWE.batchAssemble, sourceEmbed, targetEmbed,
      Pi.add_apply, Matrix.vecMul, dotProduct, shiftChallenge]
    simp only [Fin.sum_univ_one]
    rw [hkey]
    ring_nf
    simp only [Pi.zero_apply, add_zero]

/-! ## Exact real/uniform game reduction -/

/-- Ordinary binary-secret rank-one RLWE underlying the packed circular-hint theorem. -/
noncomputable def ordinaryProblem (extraLevels degree samples : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree)) :
    LearningWithErrors.Problem
      (Challenge extraLevels degree samples)
      (BinaryPolynomial degree)
      (Output extraLevels degree samples) :=
  FormalProof4FHE.LWE.embeddedBatchProblem 1 samples
    ($ᵗ (BinaryPolynomial degree))
    (fun low ↦ sourceEmbed (extraLevels := extraLevels) low) errorSampler

/-- Direct fresh RLWE rows under the packed key, carrying a fixed ring-linear function of every
coefficient bit plane. -/
noncomputable def problem (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree)) :
    LearningWithErrors.Problem
      (Challenge extraLevels degree samples)
      (SplitSecret extraLevels degree)
      (Output extraLevels degree samples) where
  sampleChallenge := $ᵗ (Challenge extraLevels degree samples)
  sampleSecret := sampleSplitSecret extraLevels degree
  sampleError := ProbComp.sampleIID samples errorSampler
  noiseless := fun secret challenge ↦
    vecMul (targetEmbed secret) challenge + linearMessage coefficients offset secret
  sampleUniform := $ᵗ (Output extraLevels degree samples)

/-- The fixed plane-zero challenge translation preserves the uniform challenge law. -/
theorem shiftChallenge_uniform_evalDist
    (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples) :
    evalDist (shiftChallenge coefficients <$>
        ($ᵗ (Challenge extraLevels degree samples))) =
      evalDist ($ᵗ (Challenge extraLevels degree samples)) :=
  evalDist_map_bijective_uniform_cross
    (α := Challenge extraLevels degree samples)
    (β := Challenge extraLevels degree samples)
    (shiftChallenge coefficients) (shiftChallenge_bijective coefficients)

/-- The ordinary uniform branch is the canonical uniform transcript sampler. -/
theorem ordinary_uniformDistr_eq_uniformSample
    (extraLevels degree samples : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree)) :
    LearningWithErrors.uniformDistr
        (ordinaryProblem extraLevels degree samples errorSampler) =
      ($ᵗ (Transcript extraLevels degree samples)) := by
  unfold LearningWithErrors.uniformDistr ordinaryProblem
    FormalProof4FHE.LWE.embeddedBatchProblem
  have uniformProduct :
      ($ᵗ (Transcript extraLevels degree samples) :
        ProbComp (Transcript extraLevels degree samples)) =
      Prod.mk <$> ($ᵗ (Challenge extraLevels degree samples)) <*>
        ($ᵗ (Output extraLevels degree samples)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- The packed linear-circular uniform branch is the same canonical sampler. -/
theorem uniformDistr_eq_uniformSample
    (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree)) :
    LearningWithErrors.uniformDistr
        (problem extraLevels degree samples coefficients offset errorSampler) =
      ($ᵗ (Transcript extraLevels degree samples)) := by
  unfold LearningWithErrors.uniformDistr problem
  have uniformProduct :
      ($ᵗ (Transcript extraLevels degree samples) :
        ProbComp (Transcript extraLevels degree samples)) =
      Prod.mk <$> ($ᵗ (Challenge extraLevels degree samples)) <*>
        ($ᵗ (Output extraLevels degree samples)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- Every fixed higher-plane transform preserves the complete public uniform transcript. -/
theorem transformTranscript_uniform_evalDist
    (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (higher : HigherPlanes extraLevels degree) :
    evalDist (transformTranscript coefficients offset higher <$>
        ($ᵗ (Transcript extraLevels degree samples))) =
      evalDist ($ᵗ (Transcript extraLevels degree samples)) :=
  evalDist_map_bijective_uniform_cross
    (α := Transcript extraLevels degree samples)
    (β := Transcript extraLevels degree samples)
    (transformTranscript coefficients offset higher)
    (transformTranscript_bijective coefficients offset higher)

/-- Reduction from packed linear-circular RLWE to ordinary binary-secret RLWE. -/
noncomputable def reduction
    {extraLevels degree samples : ℕ}
    {coefficients : Coefficients extraLevels degree samples}
    {offset : Offset extraLevels degree samples}
    {errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree)}
    (adversary : LearningWithErrors.Adversary
      (problem extraLevels degree samples coefficients offset errorSampler)) :
    LearningWithErrors.Adversary
      (ordinaryProblem extraLevels degree samples errorSampler) :=
  fun transcript ↦ do
    let higher ← $ᵗ (HigherPlanes extraLevels degree)
    adversary (transformTranscript coefficients offset higher transcript)

/-- The transformed ordinary real distribution is exactly the packed linear-circular real
distribution. -/
theorem real_evalDist
    (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree)) :
    evalDist (LearningWithErrors.distr
          (ordinaryProblem extraLevels degree samples errorSampler) >>= fun transcript ↦
        ($ᵗ (HigherPlanes extraLevels degree)) >>= fun higher ↦
        pure (transformTranscript coefficients offset higher transcript)) =
      evalDist (LearningWithErrors.distr
        (problem extraLevels degree samples coefficients offset errorSampler)) := by
  let challenges : ProbComp (Challenge extraLevels degree samples) :=
    $ᵗ (Challenge extraLevels degree samples)
  let lows : ProbComp (BinaryPolynomial degree) := $ᵗ (BinaryPolynomial degree)
  let highs : ProbComp (HigherPlanes extraLevels degree) :=
    $ᵗ (HigherPlanes extraLevels degree)
  let errors : ProbComp (Output extraLevels degree samples) :=
    ProbComp.sampleIID samples errorSampler
  let sourceFinish := fun
      (challenge : Challenge extraLevels degree samples)
      (low : BinaryPolynomial degree)
      (error : Output extraLevels degree samples) ↦
        (pure (TLWE.batchAssemble (sourceEmbed (extraLevels := extraLevels) low)
          challenge 0 error) : ProbComp (Transcript extraLevels degree samples))
  let targetFinish := fun
      (challenge : Challenge extraLevels degree samples)
      (secret : SplitSecret extraLevels degree)
      (error : Output extraLevels degree samples) ↦
        (pure (TLWE.batchAssemble (targetEmbed secret) challenge
          (linearMessage coefficients offset secret) error) :
            ProbComp (Transcript extraLevels degree samples))
  have ordinaryDistr :
      LearningWithErrors.distr
          (ordinaryProblem extraLevels degree samples errorSampler) =
        (challenges >>= fun challenge ↦
          lows >>= fun low ↦
          errors >>= fun error ↦ sourceFinish challenge low error) := by
    simp [LearningWithErrors.distr, ordinaryProblem,
      FormalProof4FHE.LWE.embeddedBatchProblem, challenges, lows, errors,
      sourceFinish, TLWE.batchAssemble, monad_norm]
  rw [ordinaryDistr]
  simp only [bind_assoc]
  calc
    _ = evalDist (challenges >>= fun challenge ↦
        lows >>= fun low ↦
        highs >>= fun higher ↦
        errors >>= fun error ↦
        pure (transformTranscript coefficients offset higher
          (TLWE.batchAssemble (sourceEmbed (extraLevels := extraLevels) low)
            challenge 0 error))) := by
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      refine evalDist_bind_congr' lows fun low ↦ ?_
      exact evalDist_bind_bind_swap errors highs
        (fun error higher ↦ pure (transformTranscript coefficients offset higher
          (TLWE.batchAssemble (sourceEmbed (extraLevels := extraLevels) low)
            challenge 0 error)))
    _ = evalDist (challenges >>= fun challenge ↦
        lows >>= fun low ↦
        highs >>= fun higher ↦
        errors >>= fun error ↦
        targetFinish (shiftChallenge coefficients challenge) (low, higher) error) := by
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      refine evalDist_bind_congr' lows fun low ↦ ?_
      refine evalDist_bind_congr' highs fun higher ↦ ?_
      refine evalDist_bind_congr' errors fun error ↦ ?_
      exact congrArg evalDist (congrArg pure
        (transformTranscript_real coefficients offset low higher challenge error))
    _ = evalDist (challenges >>= fun challenge ↦
        sampleSplitSecret extraLevels degree >>= fun secret ↦
        errors >>= fun error ↦
        targetFinish (shiftChallenge coefficients challenge) secret error) := by
      simp [sampleSplitSecret, lows, highs, bind_assoc, monad_norm]
    _ = evalDist (challenges >>= fun challenge ↦
        sampleSplitSecret extraLevels degree >>= fun secret ↦
        errors >>= fun error ↦ targetFinish challenge secret error) := by
      let finish := fun (challenge : Challenge extraLevels degree samples) ↦
        sampleSplitSecret extraLevels degree >>= fun secret ↦
        errors >>= fun error ↦ targetFinish challenge secret error
      rw [show (challenges >>= fun challenge ↦ finish
            (shiftChallenge coefficients challenge)) =
          ((shiftChallenge coefficients <$> challenges) >>= finish) by
            simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind],
        evalDist_bind, show evalDist (shiftChallenge coefficients <$> challenges) =
            evalDist challenges by
          exact shiftChallenge_uniform_evalDist
            extraLevels degree samples coefficients,
        ← evalDist_bind]
    _ = evalDist (LearningWithErrors.distr
        (problem extraLevels degree samples coefficients offset errorSampler)) := by
      simp [LearningWithErrors.distr, problem, challenges, errors, targetFinish,
        TLWE.batchAssemble, monad_norm]

/-- Sampling higher planes and transforming the ordinary uniform branch still gives the target
uniform branch exactly. -/
theorem uniform_evalDist
    (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree)) :
    evalDist (LearningWithErrors.uniformDistr
          (ordinaryProblem extraLevels degree samples errorSampler) >>= fun transcript ↦
        ($ᵗ (HigherPlanes extraLevels degree)) >>= fun higher ↦
        pure (transformTranscript coefficients offset higher transcript)) =
      evalDist (LearningWithErrors.uniformDistr
        (problem extraLevels degree samples coefficients offset errorSampler)) := by
  rw [ordinary_uniformDistr_eq_uniformSample,
    uniformDistr_eq_uniformSample]
  let source : ProbComp (Transcript extraLevels degree samples) :=
    $ᵗ (Transcript extraLevels degree samples)
  let highs : ProbComp (HigherPlanes extraLevels degree) :=
    $ᵗ (HigherPlanes extraLevels degree)
  calc
    _ = evalDist (highs >>= fun higher ↦
        source >>= fun transcript ↦
        pure (transformTranscript coefficients offset higher transcript)) :=
      evalDist_bind_bind_swap source highs
        (fun transcript higher ↦
          pure (transformTranscript coefficients offset higher transcript))
    _ = evalDist (highs >>= fun _ ↦ source) := by
      refine evalDist_bind_congr' highs fun higher ↦ ?_
      simpa only [source, map_eq_bind_pure_comp, Function.comp_def] using
        (transformTranscript_uniform_evalDist
          extraLevels degree samples coefficients offset higher)
    _ = evalDist source :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        highs (by simp [highs]) source
    _ = _ := rfl

/-- Exact real-game identity for the packed linear-circular reduction. -/
theorem game0_evalDist_eq
    (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree))
    (adversary : LearningWithErrors.Adversary
      (problem extraLevels degree samples coefficients offset errorSampler)) :
    evalDist (LearningWithErrors.game0
        (problem extraLevels degree samples coefficients offset errorSampler) adversary) =
      evalDist (LearningWithErrors.game0
        (ordinaryProblem extraLevels degree samples errorSampler)
        (reduction adversary)) := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [reduction]
  rw [show (LearningWithErrors.distr
          (ordinaryProblem extraLevels degree samples errorSampler) >>= fun transcript ↦
        ($ᵗ (HigherPlanes extraLevels degree)) >>= fun higher ↦
        adversary (transformTranscript coefficients offset higher transcript)) =
      ((LearningWithErrors.distr
            (ordinaryProblem extraLevels degree samples errorSampler) >>= fun transcript ↦
          ($ᵗ (HigherPlanes extraLevels degree)) >>= fun higher ↦
          pure (transformTranscript coefficients offset higher transcript)) >>= adversary) by
        simp only [bind_assoc, pure_bind],
    evalDist_bind, evalDist_bind,
    real_evalDist extraLevels degree samples coefficients offset errorSampler]

/-- Exact uniform-game identity for the packed linear-circular reduction. -/
theorem game1_evalDist_eq
    (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree))
    (adversary : LearningWithErrors.Adversary
      (problem extraLevels degree samples coefficients offset errorSampler)) :
    evalDist (LearningWithErrors.game1
        (problem extraLevels degree samples coefficients offset errorSampler) adversary) =
      evalDist (LearningWithErrors.game1
        (ordinaryProblem extraLevels degree samples errorSampler)
        (reduction adversary)) := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [reduction]
  rw [show (LearningWithErrors.uniformDistr
          (ordinaryProblem extraLevels degree samples errorSampler) >>= fun transcript ↦
        ($ᵗ (HigherPlanes extraLevels degree)) >>= fun higher ↦
        adversary (transformTranscript coefficients offset higher transcript)) =
      ((LearningWithErrors.uniformDistr
            (ordinaryProblem extraLevels degree samples errorSampler) >>= fun transcript ↦
          ($ᵗ (HigherPlanes extraLevels degree)) >>= fun higher ↦
          pure (transformTranscript coefficients offset higher transcript)) >>= adversary) by
        simp only [bind_assoc, pure_bind],
    evalDist_bind, evalDist_bind,
    uniform_evalDist extraLevels degree samples coefficients offset errorSampler]

/-- **Packed linear circular-RLWE theorem.** At modulus `2^(extraLevels+1)`, any fixed batch of
direct fresh RLWE rows carrying arbitrary ring-linear functions of all coefficient bit planes has
exactly the advantage of one ordinary binary-secret RLWE adversary. -/
theorem advantage_eq_binarySecretRLWE
    (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree))
    (adversary : LearningWithErrors.Adversary
      (problem extraLevels degree samples coefficients offset errorSampler)) :
    LearningWithErrors.advantage
        (problem extraLevels degree samples coefficients offset errorSampler) adversary =
      LearningWithErrors.advantage
        (ordinaryProblem extraLevels degree samples errorSampler)
        (reduction adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_evalDist_eq extraLevels degree samples coefficients offset
        errorSampler adversary) true,
    evalDist_ext_iff.mp
      (game1_evalDist_eq extraLevels degree samples coefficients offset
        errorSampler adversary) true]

/-- Any reduction-closed ordinary binary-secret RLWE bound transfers with no loss. -/
theorem hardAgainst_of_binarySecretRLWE
    (extraLevels degree samples : ℕ)
    (coefficients : Coefficients extraLevels degree samples)
    (offset : Offset extraLevels degree samples)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree))
    (circularAllowed : LearningWithErrors.Adversary
      (problem extraLevels degree samples coefficients offset errorSampler) → Prop)
    (ordinaryAllowed : LearningWithErrors.Adversary
      (ordinaryProblem extraLevels degree samples errorSampler) → Prop)
    (bound : ℝ)
    (hReductionClosed : ∀ adversary, circularAllowed adversary →
      ordinaryAllowed (reduction adversary))
    (hRLWE : FormalProof4FHE.LWE.HardAgainst
      (ordinaryProblem extraLevels degree samples errorSampler)
      ordinaryAllowed bound) :
    FormalProof4FHE.LWE.HardAgainst
      (problem extraLevels degree samples coefficients offset errorSampler)
      circularAllowed bound := by
  intro adversary hadversary
  rw [advantage_eq_binarySecretRLWE extraLevels degree samples coefficients offset
    errorSampler adversary]
  exact hRLWE _ (hReductionClosed adversary hadversary)

/-! ## Canonical gadget-encryption instance -/

/-- Number of direct gadget rows for every bit plane, followed by ordinary zero-message rows. -/
abbrev gadgetSampleCount (extraLevels zeroSamples : ℕ) :=
  (extraLevels + 1) * (extraLevels + 1) + zeroSamples

/-- Canonical powers-of-two gadget coefficients.  The first block has one row for every
`(messagePlane, encodingLevel)` pair; the final block consists of zero-message RLWE rows. -/
def gadgetCoefficients (extraLevels degree zeroSamples : ℕ) :
    Coefficients extraLevels degree (gadgetSampleCount extraLevels zeroSamples) :=
  fun source sample ↦
    (finSumFinEquiv.symm sample).elim
      (fun hint ↦
        let indexed := finProdFinEquiv.symm hint
        if source = indexed.1 then
          ((2 ^ indexed.2.val : ℕ) :
            RLWE.Rq (2 ^ (extraLevels + 1)) degree)
        else 0)
      (fun _ ↦ 0)

/-- Zero public offset for the canonical gadget batch. -/
def gadgetOffset (extraLevels degree zeroSamples : ℕ) :
    Offset extraLevels degree (gadgetSampleCount extraLevels zeroSamples) :=
  fun _ ↦ 0

@[simp]
theorem gadgetCoefficients_hint
    (extraLevels degree zeroSamples : ℕ)
    (source message encoding : Fin (extraLevels + 1)) :
    gadgetCoefficients extraLevels degree zeroSamples source
        (finSumFinEquiv (Sum.inl (finProdFinEquiv (message, encoding)))) =
      if source = message then
        ((2 ^ encoding.val : ℕ) : RLWE.Rq (2 ^ (extraLevels + 1)) degree)
      else 0 := by
  simp only [gadgetCoefficients, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp]
theorem gadgetCoefficients_zero
    (extraLevels degree zeroSamples : ℕ)
    (source : Fin (extraLevels + 1)) (row : Fin zeroSamples) :
    gadgetCoefficients extraLevels degree zeroSamples source
        (finSumFinEquiv (Sum.inr row)) = 0 := by
  simp only [gadgetCoefficients, Equiv.symm_apply_apply, Sum.elim_inr]

/-- On a gadget row, the generic linear message is exactly the selected bit-plane polynomial
times the powers-of-two encoding gadget. -/
theorem linearMessage_gadget_hint
    (extraLevels degree zeroSamples : ℕ)
    (secret : SplitSecret extraLevels degree)
    (message encoding : Fin (extraLevels + 1)) :
    linearMessage
        (gadgetCoefficients extraLevels degree zeroSamples)
        (gadgetOffset extraLevels degree zeroSamples) secret
        (finSumFinEquiv (Sum.inl (finProdFinEquiv (message, encoding)))) =
      embeddedPlane (join secret) message *
        ((2 ^ encoding.val : ℕ) : RLWE.Rq (2 ^ (extraLevels + 1)) degree) := by
  simp only [linearMessage, gadgetOffset, zero_add,
    gadgetCoefficients_hint]
  rw [Finset.sum_eq_single message]
  · simp
  · intro source _ hsource
    simp [hsource]
  · simp

/-- The trailing canonical rows really carry message zero. -/
theorem linearMessage_gadget_zero
    (extraLevels degree zeroSamples : ℕ)
    (secret : SplitSecret extraLevels degree) (row : Fin zeroSamples) :
    linearMessage
        (gadgetCoefficients extraLevels degree zeroSamples)
        (gadgetOffset extraLevels degree zeroSamples) secret
        (finSumFinEquiv (Sum.inr row)) = 0 := by
  simp only [linearMessage, gadgetOffset, zero_add, gadgetCoefficients_zero,
    mul_zero, Finset.sum_const_zero]

/-- Canonical powers-of-two gadget encryptions of every secret bit plane, jointly with any fixed
number of zero rows, reduce exactly to ordinary binary-secret RLWE.  This is the direct ring
counterpart of the proved linear circular-LWE theorem from PKC 2024. -/
theorem gadgetAdvantage_eq_binarySecretRLWE
    (extraLevels degree zeroSamples : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (extraLevels + 1)) degree))
    (adversary : LearningWithErrors.Adversary
      (problem extraLevels degree (gadgetSampleCount extraLevels zeroSamples)
        (gadgetCoefficients extraLevels degree zeroSamples)
        (gadgetOffset extraLevels degree zeroSamples) errorSampler)) :
    LearningWithErrors.advantage
        (problem extraLevels degree (gadgetSampleCount extraLevels zeroSamples)
          (gadgetCoefficients extraLevels degree zeroSamples)
          (gadgetOffset extraLevels degree zeroSamples) errorSampler) adversary =
      LearningWithErrors.advantage
        (ordinaryProblem extraLevels degree
          (gadgetSampleCount extraLevels zeroSamples) errorSampler)
        (reduction adversary) :=
  advantage_eq_binarySecretRLWE extraLevels degree
    (gadgetSampleCount extraLevels zeroSamples)
    (gadgetCoefficients extraLevels degree zeroSamples)
    (gadgetOffset extraLevels degree zeroSamples) errorSampler adversary

end

end FormalProof4FHE.TFHE.PackedLinearCircularRLWE
