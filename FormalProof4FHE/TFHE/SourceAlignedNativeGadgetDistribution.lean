/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SourceAlignedGadgetConstruction
import FormalProof4FHE.TFHE.BootstrappingSecurity

/-!
# Uniform Distribution of the Native Source-Aligned Gadget

This file proves the marginal distributional fact behind the concrete column construction.  For
fixed native TFHE secrets and messages, direct TGSW generation exposes a uniform mask matrix.
The finite product over all BRK controls is therefore a jointly uniform mask tensor, and the
existing exact direct/native reparameterization transports that law to native BRK generation.
Flattening the control and TGSW-row axes is an explicit equivalence, so the common ring gadget
constructed from an honest native BRK is jointly uniform.

This does not prove that a KSK derived from those columns has the native independent KSK law.  The
full correlated `(BRK, widened KSK)` comparison remains a separate construction-level premise.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.SourceAlignedFactorPropagation.NativeAlignment

noncomputable section


/-- Native BRK mask tensor before flattening the control and row axes. -/
abbrev BootstrappingMask
    (q degree ringRank levels lweDimension : ℕ) :=
  Fin lweDimension →
    Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank levels)) (RLWE.Rq q degree)

/-- Read the complete public mask tensor of a native BRK. -/
def bootstrappingMask
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q degree ringRank levels lweDimension) :
    BootstrappingMask q degree ringRank levels lweDimension :=
  fun control ↦ (bootstrappingKey control).1

theorem directEncrypt_mask_evalDist_eq_uniform
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    evalDist ((fun ciphertext ↦ ciphertext.1) <$>
        TGSW.directEncrypt dimension levels errorSampler secret gadget message) =
      evalDist
        ($ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) := by
  let Challenge : ProbComp
      (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :=
    $ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R
  let Errors := ProbComp.sampleIID (TGSW.rowCount dimension levels) errorSampler
  have h : evalDist (Challenge >>= fun challenge ↦
      Errors >>= fun _error ↦ pure challenge) = evalDist Challenge := by
    calc
      _ = evalDist (Challenge >>= fun challenge ↦ pure challenge) := by
        refine evalDist_bind_congr' Challenge fun challenge ↦ ?_
        exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          Errors (by simp [Errors]) (pure challenge)
      _ = evalDist Challenge := by simp
  simpa only [TGSW.directEncrypt, TLWE.batchEncrypt, TLWE.batchAssemble, Challenge, Errors,
    map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] using h

/-- Direct native BRK generation exposes a jointly uniform complete mask tensor. -/
theorem generateDirectBootstrappingKey_mask_evalDist_eq_uniform
    (q degree ringRank levels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (bootstrappingMask <$>
        Native.BootstrapSecurity.generateDirectBootstrappingKey
          q degree ringRank levels lweDimension errorSampler gadget lweSecret ringSecret) =
      evalDist ($ᵗ (BootstrappingMask q degree ringRank levels lweDimension)) := by
  let Challenge :=
    Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank levels)) (RLWE.Rq q degree)
  let Entry : Fin lweDimension → ProbComp
      (TGSW.Ciphertext (RLWE.Rq q degree) ringRank levels) :=
    fun coordinate ↦ TGSW.directEncrypt ringRank levels errorSampler
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate))
  let MaskEntry : Fin lweDimension → ProbComp Challenge :=
    fun coordinate ↦ (fun ciphertext ↦ ciphertext.1) <$> Entry coordinate
  have hentry : ∀ coordinate,
      evalDist (MaskEntry coordinate) = evalDist ($ᵗ Challenge) := by
    intro coordinate
    exact directEncrypt_mask_evalDist_eq_uniform ringRank levels errorSampler
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate))
  calc
    evalDist (bootstrappingMask <$>
        Native.BootstrapSecurity.generateDirectBootstrappingKey
          q degree ringRank levels lweDimension errorSampler gadget lweSecret ringSecret) =
        evalDist (Fin.mOfFn lweDimension MaskEntry) := by
      rw [← FormalProof4FHE.FiniteProduct.map_fin_mOfFn
        lweDimension Entry (fun _ ciphertext ↦ ciphertext.1)]
      rfl
    _ = evalDist (Fin.mOfFn lweDimension (fun _ ↦ $ᵗ Challenge)) :=
      FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
        lweDimension MaskEntry (fun _ ↦ $ᵗ Challenge) hentry
    _ = evalDist ($ᵗ (BootstrappingMask q degree ringRank levels lweDimension)) := by
      simpa only [ProbComp.sampleIID, Challenge] using
        (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
          (alpha := Challenge) lweDimension)

/-- The original structured native BRK has the same jointly uniform mask tensor. -/
theorem generateBootstrappingKey_mask_evalDist_eq_uniform
    (q degree ringRank levels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (bootstrappingMask <$> Native.generateBootstrappingKey
        q degree ringRank levels lweDimension errorSampler gadget lweSecret ringSecret) =
      evalDist ($ᵗ (BootstrappingMask q degree ringRank levels lweDimension)) := by
  have hdirect := evalDist_map_eq_of_evalDist_eq
    (Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
      q degree ringRank levels lweDimension errorSampler gadget lweSecret ringSecret)
    bootstrappingMask
  exact hdirect.trans
    (generateDirectBootstrappingKey_mask_evalDist_eq_uniform
      q degree ringRank levels lweDimension errorSampler gadget lweSecret ringSecret)

/-- Flatten the control and TGSW-row axes of a complete native mask tensor. -/
def flattenMask
    {q degree ringRank levels lweDimension : ℕ}
    (mask : BootstrappingMask q degree ringRank levels lweDimension) :
    Matrix (Fin ringRank) (Fin (controlRowCount ringRank levels lweDimension))
      (RLWE.Rq q degree) :=
  fun coordinate row ↦
    mask (controlRowIndex row).1 coordinate (controlRowIndex row).2

/-- Flattening the mask tensor is an equivalence of finite matrix carriers. -/
def flattenMaskEquiv (q degree ringRank levels lweDimension : ℕ) :
    BootstrappingMask q degree ringRank levels lweDimension ≃
      Matrix (Fin ringRank) (Fin (controlRowCount ringRank levels lweDimension))
        (RLWE.Rq q degree) where
  toFun := flattenMask
  invFun gadget := fun control coordinate row ↦
    gadget coordinate (finProdFinEquiv (control, row))
  left_inv mask := by
    funext control coordinate row
    simp [flattenMask, controlRowIndex]
  right_inv gadget := by
    funext coordinate row
    obtain ⟨⟨control, nativeRow⟩, rfl⟩ := finProdFinEquiv.surjective row
    simp [flattenMask, controlRowIndex]

/-- Flattening a uniform native mask tensor gives a uniform common ring gadget. -/
theorem flattenMask_uniform_evalDist
    (q degree ringRank levels lweDimension : ℕ) [NeZero q] :
    evalDist (flattenMask <$>
        ($ᵗ (BootstrappingMask q degree ringRank levels lweDimension))) =
      evalDist
        ($ᵗ Matrix (Fin ringRank)
          (Fin (controlRowCount ringRank levels lweDimension)) (RLWE.Rq q degree)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := BootstrappingMask q degree ringRank levels lweDimension)
    (β := Matrix (Fin ringRank)
      (Fin (controlRowCount ringRank levels lweDimension)) (RLWE.Rq q degree))
    (flattenMaskEquiv q degree ringRank levels lweDimension)
    (flattenMaskEquiv q degree ringRank levels lweDimension).bijective

theorem commonRingGadget_eq_flattenMask
    {q degree ringRank levels lweDimension : ℕ}
    (bootstrappingKey : Native.BootstrappingKey
      q degree ringRank levels lweDimension) :
    commonRingGadget bootstrappingKey =
      flattenMask (bootstrappingMask bootstrappingKey) := by
  rfl

/-- Therefore the common gadget extracted from an honestly generated native BRK is jointly
uniform as a ring matrix. -/
theorem generateBootstrappingKey_commonRingGadget_evalDist_eq_uniform
    (q degree ringRank levels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin levels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (commonRingGadget <$> Native.generateBootstrappingKey
        q degree ringRank levels lweDimension errorSampler gadget lweSecret ringSecret) =
      evalDist
        ($ᵗ Matrix (Fin ringRank)
          (Fin (controlRowCount ringRank levels lweDimension)) (RLWE.Rq q degree)) := by
  have hmasks := evalDist_map_eq_of_evalDist_eq
    (generateBootstrappingKey_mask_evalDist_eq_uniform
      q degree ringRank levels lweDimension errorSampler gadget lweSecret ringSecret)
    flattenMask
  calc
    evalDist (commonRingGadget <$> Native.generateBootstrappingKey
        q degree ringRank levels lweDimension errorSampler gadget lweSecret ringSecret) =
      evalDist (flattenMask <$> (bootstrappingMask <$>
        Native.generateBootstrappingKey q degree ringRank levels lweDimension
          errorSampler gadget lweSecret ringSecret)) := by
        congr 1
        simp only [Functor.map_map]
        rfl
    _ = evalDist (flattenMask <$>
        ($ᵗ (BootstrappingMask q degree ringRank levels lweDimension))) := hmasks
    _ = evalDist
        ($ᵗ Matrix (Fin ringRank)
          (Fin (controlRowCount ringRank levels lweDimension)) (RLWE.Rq q degree)) :=
      flattenMask_uniform_evalDist q degree ringRank levels lweDimension

end

end FormalProof4FHE.TFHE.SourceAlignedFactorPropagation.NativeAlignment
