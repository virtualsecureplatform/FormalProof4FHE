/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomial
import FormalProof4FHE.LWE.MultiKeyAffine
import FormalProof4FHE.TFHE.BlindRotation
import FormalProof4FHE.TFHE.Native
import FormalProof4FHE.SharedRandomness.Ordinary

/-!
# Exact Scalar-Secret Randomization of Native TFHE Evaluation Keys

This module proves the fixed-mask randomization identities used at the start of a CircLWE
search-to-decision argument for native finite-modulus TFHE.

For the scalar binary key `s` and a fixed binary mask `r`, `maskedSecret s r` is the bitwise XOR
`s ⊕ r`.  The corresponding public evaluation-key transport is exact:

* key-switch rows are changed by signed public masks plus the required affine body correction;
* a TGSW encryption of bit `sᵢ` is toggled into one of `sᵢ ⊕ rᵢ`;
* symmetric homogeneous-row noise makes that TGSW toggle distribution preserving;
* centered-binomial ring noise supplies the required symmetry with no statistical loss; and
* the transports lift to the joint real BRK+KSK view and to the uniform-BRK+real-KSK endpoint.

These are information-theoretic distribution identities.  They do not prove the remaining
CircLWE search-to-decision step, which additionally requires homomorphic evaluation of the shifted
secret function and noise smudging.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.ScalarSecretRandomization

def maskedSecret {dimension : ℕ} (secret mask : BinarySecret dimension) :
    BinarySecret dimension :=
  fun coordinate => LWE.MultiKeyAffine.maskedBit (secret coordinate) (mask coordinate)

def maskSign {R : Type} [Ring R] (mask : Bool) : R :=
  if mask then -1 else 1

@[simp]
theorem embed_maskedBit {R : Type} [Ring R] (secret mask : Bool) :
    embedBit (R := R) (LWE.MultiKeyAffine.maskedBit secret mask) =
      maskSign (R := R) mask * embedBit secret + embedBit mask := by
  cases secret <;> cases mask <;> simp [LWE.MultiKeyAffine.maskedBit, maskSign, embedBit]

def transformChallenge {R : Type} [Ring R] {dimension samples : ℕ}
    (mask : BinarySecret dimension) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    Matrix (Fin dimension) (Fin samples) R :=
  fun coordinate sample => maskSign (R := R) (mask coordinate) * challenge coordinate sample

@[simp]
theorem transformChallenge_involutive {R : Type} [Ring R] {dimension samples : ℕ}
    (mask : BinarySecret dimension) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    transformChallenge mask (transformChallenge mask challenge) = challenge := by
  funext coordinate sample
  cases h : mask coordinate <;> simp [transformChallenge, maskSign, h]

theorem transformChallenge_bijective {R : Type} [Ring R] {dimension samples : ℕ}
    (mask : BinarySecret dimension) :
    Function.Bijective (transformChallenge (R := R) (samples := samples) mask) :=
  Function.Involutive.bijective (transformChallenge_involutive mask)

def transformBatch {R : Type} [Ring R] {dimension samples : ℕ}
    (mask : BinarySecret dimension) (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    TLWE.BatchCiphertext R dimension samples :=
  let challenge := transformChallenge mask ciphertext.1
  (challenge, ciphertext.2 + vecMul (embedBinarySecret mask) challenge)

def untransformBatch {R : Type} [Ring R] {dimension samples : ℕ}
    (mask : BinarySecret dimension) (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    TLWE.BatchCiphertext R dimension samples :=
  (transformChallenge mask ciphertext.1,
    ciphertext.2 - vecMul (embedBinarySecret mask) ciphertext.1)

@[simp]
theorem untransformBatch_transformBatch {R : Type} [CommRing R] {dimension samples : ℕ}
    (mask : BinarySecret dimension) (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    untransformBatch mask (transformBatch mask ciphertext) = ciphertext := by
  apply Prod.ext
  · exact transformChallenge_involutive mask ciphertext.1
  · funext sample
    simp [untransformBatch, transformBatch]

@[simp]
theorem transformBatch_untransformBatch {R : Type} [CommRing R] {dimension samples : ℕ}
    (mask : BinarySecret dimension) (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    transformBatch mask (untransformBatch mask ciphertext) = ciphertext := by
  apply Prod.ext
  · exact transformChallenge_involutive mask ciphertext.1
  · funext sample
    simp [untransformBatch, transformBatch]

theorem transformBatch_bijective {R : Type} [CommRing R] {dimension samples : ℕ}
    (mask : BinarySecret dimension) :
    Function.Bijective (transformBatch (R := R) (samples := samples) mask) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untransformBatch mask, untransformBatch_transformBatch mask,
      transformBatch_untransformBatch mask⟩

theorem transformBatch_batchAssemble {R : Type} [CommRing R] {dimension samples : ℕ}
    (secret mask : BinarySecret dimension)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error : Fin samples → R) :
    transformBatch mask
        (TLWE.batchAssemble (embedBinarySecret secret) challenge message error) =
      TLWE.batchAssemble (embedBinarySecret (maskedSecret secret mask))
        (transformChallenge mask challenge) message error := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [transformBatch, TLWE.batchAssemble, Pi.add_apply, Matrix.vecMul,
      dotProduct]
    simp_rw [show ∀ coordinate,
        embedBinarySecret (maskedSecret secret mask) coordinate =
          maskSign (R := R) (mask coordinate) * embedBinarySecret secret coordinate +
            embedBinarySecret mask coordinate by
      intro coordinate
      exact embed_maskedBit (secret coordinate) (mask coordinate)]
    simp only [transformChallenge]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    have hdot :
        (∑ coordinate,
            embedBinarySecret secret coordinate * challenge coordinate sample) =
          ∑ coordinate,
            maskSign (R := R) (mask coordinate) * embedBinarySecret secret coordinate *
              (maskSign (mask coordinate) * challenge coordinate sample) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      cases mask coordinate <;> simp [maskSign]
    rw [hdot]
    abel

theorem transformChallenge_uniform_evalDist {R : Type}
    [CommRing R] [Fintype R] [SampleableType R] {dimension samples : ℕ}
    (mask : BinarySecret dimension) :
    evalDist (transformChallenge (R := R) (samples := samples) mask <$>
        ($ᵗ Matrix (Fin dimension) (Fin samples) R)) =
      evalDist ($ᵗ Matrix (Fin dimension) (Fin samples) R) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin dimension) (Fin samples) R)
    (β := Matrix (Fin dimension) (Fin samples) R)
    (transformChallenge mask) (transformChallenge_bijective mask)

theorem transformBatch_batchEncrypt_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R] {dimension samples : ℕ}
    (errorSampler : ProbComp R) (secret mask : BinarySecret dimension)
    (message : Fin samples → R) :
    evalDist (transformBatch mask <$>
        TLWE.batchEncrypt dimension samples errorSampler
          (embedBinarySecret secret) message) =
      evalDist (TLWE.batchEncrypt dimension samples errorSampler
        (embedBinarySecret (maskedSecret secret mask)) message) := by
  let errors := ProbComp.sampleIID samples errorSampler
  let finish := fun (challenge : Matrix (Fin dimension) (Fin samples) R)
      (error : Fin samples → R) =>
        (pure (TLWE.batchAssemble (embedBinarySecret (maskedSecret secret mask))
          challenge message error) : ProbComp (TLWE.BatchCiphertext R dimension samples))
  rw [show TLWE.batchEncrypt dimension samples errorSampler
      (embedBinarySecret secret) message =
      (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error =>
          pure (TLWE.batchAssemble (embedBinarySecret secret) challenge message error)) by
    simp [TLWE.batchEncrypt, errors, monad_norm]]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error => finish (transformChallenge mask challenge) error) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R) fun challenge => ?_
      refine evalDist_bind_congr' errors fun error => ?_
      simpa only [finish] using congrArg evalDist
        (congrArg pure (transformBatch_batchAssemble secret mask challenge message error))
    _ = evalDist ((transformChallenge mask <$>
          ($ᵗ Matrix (Fin dimension) (Fin samples) R)) >>= fun challenge =>
        errors >>= fun error => finish challenge error) := by
      rw [map_eq_bind_pure_comp, bind_assoc]
      simp only [Function.comp_apply, pure_bind]
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error => finish challenge error) := by
      rw [evalDist_bind, transformChallenge_uniform_evalDist mask, ← evalDist_bind]
    _ = _ := by
      simp [TLWE.batchEncrypt, errors, finish, monad_norm]

/-! ## TGSW message-bit toggling -/

def negateCiphertext {R : Type} [Neg R] {dimension levels : ℕ}
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    TGSW.Ciphertext R dimension levels :=
  (-ciphertext.1, -ciphertext.2)

@[simp]
theorem negateCiphertext_involutive {R : Type} [AddGroup R] {dimension levels : ℕ}
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    negateCiphertext (negateCiphertext ciphertext) = ciphertext := by
  apply Prod.ext
  · funext coordinate row
    simp [negateCiphertext]
  · funext row
    simp [negateCiphertext]

theorem TGSW.addGadget_sub_neg {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (left right : R)
    (homogeneous : TGSW.Ciphertext R dimension levels) :
    TGSW.addGadget gadget left
        (negateCiphertext (TGSW.addGadget gadget right homogeneous)) =
      TGSW.addGadget gadget (left - right) (negateCiphertext homogeneous) := by
  apply Prod.ext
  · funext coordinate row
    simp only [TGSW.addGadget, TGSW.gadgetMaskShift, Matrix.add_apply,
      negateCiphertext, Matrix.neg_apply]
    split_ifs <;> ring
  · funext row
    simp only [TGSW.addGadget, TGSW.gadgetBodyShift, Pi.add_apply,
      negateCiphertext, Pi.neg_apply]
    split_ifs <;> ring

@[simp]
theorem embedBit_true_sub {R : Type} [Ring R] (bit : Bool) :
    embedBit (R := R) true - embedBit bit = embedBit (!bit) := by
  cases bit <;> simp [embedBit]

def toggleTGSW {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (mask : Bool)
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    TGSW.Ciphertext R dimension levels :=
  if mask then
    TGSW.addGadget gadget (embedBit true) (negateCiphertext ciphertext)
  else ciphertext

theorem toggleTGSW_addGadget {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (bit mask : Bool)
    (homogeneous : TGSW.Ciphertext R dimension levels) :
    toggleTGSW gadget mask
        (TGSW.addGadget gadget (embedBit bit) homogeneous) =
      TGSW.addGadget gadget
        (embedBit (LWE.MultiKeyAffine.maskedBit bit mask))
        (if mask then negateCiphertext homogeneous else homogeneous) := by
  cases mask with
  | false => simp [toggleTGSW, LWE.MultiKeyAffine.maskedBit]
  | true =>
      simpa only [toggleTGSW, if_true, LWE.MultiKeyAffine.maskedBit,
          embedBit_true_sub] using
        TGSW.addGadget_sub_neg gadget (embedBit (R := R) true)
          (embedBit bit) homogeneous

@[simp]
theorem toggleTGSW_involutive {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (mask : Bool)
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    toggleTGSW gadget mask (toggleTGSW gadget mask ciphertext) = ciphertext := by
  cases mask with
  | false => simp [toggleTGSW]
  | true =>
      simp only [toggleTGSW, if_true]
      simpa using
        TGSW.addGadget_sub_neg gadget (embedBit (R := R) true)
          (embedBit true) (negateCiphertext ciphertext)

/-- Composing a public message-bit toggle with the corresponding XOR-transport toggle cancels
the transport mask. -/
theorem toggleTGSW_maskedBit_comp {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (bit mask : Bool)
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    toggleTGSW gadget (LWE.MultiKeyAffine.maskedBit bit mask)
        (toggleTGSW gadget mask ciphertext) =
      toggleTGSW gadget bit ciphertext := by
  cases bit with
  | false =>
      cases mask with
      | false => rfl
      | true => exact toggleTGSW_involutive gadget true ciphertext
  | true =>
      cases mask <;> rfl

theorem toggleTGSW_bijective {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (mask : Bool) :
    Function.Bijective (toggleTGSW (dimension := dimension) gadget mask) :=
  Function.Involutive.bijective (toggleTGSW_involutive gadget mask)

/-! ## Symmetric homogeneous-row sampling -/

def NegationSymmetric {R : Type} [Neg R] (sampler : ProbComp R) : Prop :=
  ∀ error, Pr[= -error | sampler] = Pr[= error | sampler]

theorem negate_sampleIID_evalDist {R : Type} [AddCommGroup R] [Finite R]
    (length : ℕ) (sampler : ProbComp R) (hsymmetric : NegationSymmetric sampler) :
    evalDist ((fun error : Fin length → R => -error) <$>
        ProbComp.sampleIID length sampler) =
      evalDist (ProbComp.sampleIID length sampler) := by
  apply evalDist_ext
  intro output
  calc
    Pr[= output | (fun error : Fin length → R => -error) <$>
        ProbComp.sampleIID length sampler] =
        Pr[= -output | ProbComp.sampleIID length sampler] := by
      simpa using
        (probOutput_map_injective (ProbComp.sampleIID length sampler)
          (f := fun error : Fin length → R => -error) neg_injective (-output))
    _ = ∏ coordinate, Pr[= (-output) coordinate | sampler] :=
      FormalProof4FHE.SharedRandomness.probOutput_sampleIID length sampler (-output)
    _ = ∏ coordinate, Pr[= output coordinate | sampler] := by
      apply Finset.prod_congr rfl
      intro coordinate _
      simpa using hsymmetric (output coordinate)
    _ = Pr[= output | ProbComp.sampleIID length sampler] :=
      (FormalProof4FHE.SharedRandomness.probOutput_sampleIID length sampler output).symm

def negateChallenge {R : Type} [Neg R] {dimension samples : ℕ}
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    Matrix (Fin dimension) (Fin samples) R :=
  fun coordinate sample => -challenge coordinate sample

@[simp]
theorem negateChallenge_involutive {R : Type} [AddGroup R] {dimension samples : ℕ}
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    negateChallenge (negateChallenge challenge) = challenge := by
  funext coordinate sample
  simp [negateChallenge]

theorem negateChallenge_bijective {R : Type} [AddGroup R] {dimension samples : ℕ} :
    Function.Bijective (negateChallenge (R := R) (dimension := dimension) (samples := samples)) :=
  Function.Involutive.bijective negateChallenge_involutive

theorem negateChallenge_uniform_evalDist {R : Type}
    [AddCommGroup R] [Fintype R] [SampleableType R] {dimension samples : ℕ} :
    evalDist (negateChallenge (R := R) <$>
        ($ᵗ Matrix (Fin dimension) (Fin samples) R)) =
      evalDist ($ᵗ Matrix (Fin dimension) (Fin samples) R) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin dimension) (Fin samples) R)
    (β := Matrix (Fin dimension) (Fin samples) R)
    (negateChallenge (R := R) (dimension := dimension) (samples := samples))
    negateChallenge_bijective

theorem negateCiphertext_batchAssemble_zero {R : Type} [CommRing R]
    {dimension levels : ℕ} (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (error : Fin (TGSW.rowCount dimension levels) → R) :
    negateCiphertext (TLWE.batchAssemble secret challenge 0 error) =
      TLWE.batchAssemble secret (negateChallenge challenge) 0 (-error) := by
  apply Prod.ext
  · funext coordinate row
    rfl
  · funext row
    simp only [negateCiphertext, TLWE.batchAssemble, Pi.neg_apply, Pi.add_apply,
      Matrix.vecMul, dotProduct, negateChallenge]
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
    simp
    exact add_comm _ _

theorem negate_homogeneous_batchEncrypt_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension levels : ℕ} (errorSampler : ProbComp R)
    (hsymmetric : NegationSymmetric errorSampler) (secret : Fin dimension → R) :
    evalDist (negateCiphertext <$>
        TLWE.batchEncrypt dimension (TGSW.rowCount dimension levels)
          errorSampler secret 0) =
      evalDist (TLWE.batchEncrypt dimension (TGSW.rowCount dimension levels)
        errorSampler secret 0) := by
  let samples := TGSW.rowCount dimension levels
  let errors := ProbComp.sampleIID samples errorSampler
  let finish := fun (challenge : Matrix (Fin dimension) (Fin samples) R)
      (error : Fin samples → R) =>
        (pure (TLWE.batchAssemble secret challenge 0 error) :
          ProbComp (TGSW.Ciphertext R dimension levels))
  rw [show TLWE.batchEncrypt dimension (TGSW.rowCount dimension levels)
      errorSampler secret 0 =
      (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error =>
          pure (TLWE.batchAssemble secret challenge 0 error)) by
    simp [TLWE.batchEncrypt, samples, errors, monad_norm]]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error =>
          finish (negateChallenge challenge) (-error)) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R)
        fun challenge => ?_
      refine evalDist_bind_congr' errors fun error => ?_
      simpa only [samples, finish] using congrArg evalDist
        (congrArg pure (negateCiphertext_batchAssemble_zero
          (levels := levels) secret challenge error))
    _ = evalDist ((negateChallenge <$>
          ($ᵗ Matrix (Fin dimension) (Fin samples) R)) >>= fun challenge =>
        ((fun error : Fin samples → R => -error) <$> errors) >>= fun error =>
          finish challenge error) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        ((fun error : Fin samples → R => -error) <$> errors) >>= fun error =>
          finish challenge error) := by
      rw [evalDist_bind, negateChallenge_uniform_evalDist, ← evalDist_bind]
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error => finish challenge error) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R)
        fun _ => ?_
      rw [evalDist_bind, negate_sampleIID_evalDist samples errorSampler hsymmetric,
        ← evalDist_bind]
    _ = _ := by
      simp [samples, errors, finish, monad_norm]

theorem toggleTGSW_encrypt_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension levels : ℕ} (errorSampler : ProbComp R)
    (hsymmetric : NegationSymmetric errorSampler) (secret : Fin dimension → R)
    (gadget : Fin levels → R) (bit mask : Bool) :
    evalDist (toggleTGSW gadget mask <$>
        TGSW.encrypt dimension levels errorSampler secret gadget (embedBit bit)) =
      evalDist (TGSW.encrypt dimension levels errorSampler secret gadget
        (embedBit (LWE.MultiKeyAffine.maskedBit bit mask))) := by
  cases mask with
  | false =>
      rw [show toggleTGSW gadget false = id by
        funext ciphertext
        simp [toggleTGSW]]
      simp [LWE.MultiKeyAffine.maskedBit]
  | true =>
      let homogeneous := TLWE.batchEncrypt dimension (TGSW.rowCount dimension levels)
        errorSampler secret 0
      let finish := fun ciphertext : TGSW.Ciphertext R dimension levels =>
        (pure (TGSW.addGadget gadget
          (embedBit (LWE.MultiKeyAffine.maskedBit bit true)) ciphertext) :
          ProbComp (TGSW.Ciphertext R dimension levels))
      rw [show TGSW.encrypt dimension levels errorSampler secret gadget (embedBit bit) =
          homogeneous >>= fun ciphertext =>
            pure (TGSW.addGadget gadget (embedBit bit) ciphertext) by
        rfl]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      calc
        _ = evalDist (homogeneous >>= fun ciphertext =>
            finish (negateCiphertext ciphertext)) := by
          refine evalDist_bind_congr' homogeneous fun ciphertext => ?_
          simpa [finish] using congrArg evalDist (congrArg
            (fun value => (pure value : ProbComp (TGSW.Ciphertext R dimension levels)))
            (toggleTGSW_addGadget gadget bit true ciphertext))
        _ = evalDist ((negateCiphertext <$> homogeneous) >>= finish) := by
          simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
        _ = evalDist (homogeneous >>= finish) := by
          rw [evalDist_bind,
            negate_homogeneous_batchEncrypt_evalDist errorSampler hsymmetric secret,
            ← evalDist_bind]
        _ = _ := by
          simp [TGSW.encrypt, homogeneous, finish, monad_norm]

theorem toggleTGSW_centeredBinomial_encrypt_evalDist
    {q degree dimension levels eta : ℕ} [NeZero q]
    (secret : Fin dimension → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1)) (bit mask : Bool) :
    evalDist (toggleTGSW gadget mask <$>
        TGSW.encrypt dimension levels (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          secret gadget (embedConstantBit q (degree + 1) bit)) =
      evalDist (TGSW.encrypt dimension levels
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) secret gadget
        (embedConstantBit q (degree + 1)
          (LWE.MultiKeyAffine.maskedBit bit mask))) := by
  rw [BlindRotation.embedConstantBit_eq_embedBit,
    BlindRotation.embedConstantBit_eq_embedBit]
  apply toggleTGSW_encrypt_evalDist
  intro error
  change Pr[= RLWE.CenteredBinomial.negError q (degree + 1) error |
      RLWE.CenteredBinomial.sampler q (degree + 1) eta] = _
  exact RLWE.CenteredBinomial.probOutput_negError q (degree + 1) eta error

/-! ## Independent pointwise transport -/

theorem mOfFn_map_evalDist_congr {α β : Type} (length : ℕ)
    (first : Fin length → ProbComp α) (second : Fin length → ProbComp β)
    (transform : Fin length → α → β)
    (hcoordinate : ∀ coordinate,
      evalDist (transform coordinate <$> first coordinate) =
        evalDist (second coordinate)) :
    evalDist ((fun values coordinate => transform coordinate (values coordinate)) <$>
        Fin.mOfFn length first) =
      evalDist (Fin.mOfFn length second) := by
  induction length with
  | zero =>
      simp only [Fin.mOfFn, map_pure, evalDist_pure]
      congr 1
      funext coordinate
      exact coordinate.elim0
  | succ length ih =>
      let firstTail := Fin.mOfFn length fun coordinate => first coordinate.succ
      let secondTail := Fin.mOfFn length fun coordinate => second coordinate.succ
      let transformTail := fun (values : Fin length → α) coordinate =>
        transform coordinate.succ (values coordinate)
      have htail :
          evalDist (transformTail <$> firstTail) = evalDist secondTail := by
        exact ih (fun coordinate => first coordinate.succ)
          (fun coordinate => second coordinate.succ)
          (fun coordinate => transform coordinate.succ)
          (fun coordinate => hcoordinate coordinate.succ)
      have map_cons (head : α) (tail : Fin length → α) :
          (fun coordinate => transform coordinate
            (Fin.cons (α := fun _ => α) head tail coordinate)) =
            Fin.cons (α := fun _ => β) (transform 0 head) (transformTail tail) := by
        funext coordinate
        refine Fin.cases ?_ (fun index => ?_) coordinate
        · rfl
        · rfl
      change evalDist ((fun values coordinate => transform coordinate (values coordinate)) <$>
          (first 0 >>= fun head => firstTail >>= fun tail => pure (Fin.cons head tail))) =
        evalDist (second 0 >>= fun head =>
          secondTail >>= fun tail => pure (Fin.cons head tail))
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      calc
        _ = evalDist (first 0 >>= fun head => firstTail >>= fun tail =>
            pure (Fin.cons (transform 0 head) (transformTail tail))) := by
          refine evalDist_bind_congr' (first 0) fun head => ?_
          refine evalDist_bind_congr' firstTail fun tail => ?_
          simpa only using congrArg evalDist (congrArg
            (fun value => (pure value : ProbComp (Fin (length + 1) → β)))
            (map_cons head tail))
        _ = evalDist ((transform 0 <$> first 0) >>= fun head =>
            (transformTail <$> firstTail) >>= fun tail =>
              pure (Fin.cons head tail)) := by
          simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
        _ = evalDist (second 0 >>= fun head =>
            (transformTail <$> firstTail) >>= fun tail =>
              pure (Fin.cons head tail)) := by
          rw [evalDist_bind, hcoordinate 0, ← evalDist_bind]
        _ = evalDist (second 0 >>= fun head => secondTail >>= fun tail =>
            pure (Fin.cons head tail)) := by
          refine evalDist_bind_congr' (second 0) fun _ => ?_
          rw [evalDist_bind, htail, ← evalDist_bind]
        _ = _ := by simp

/-! ## Bootstrapping-key transport -/

def transformBootstrappingKey {R : Type} [CommRing R]
    {dimension levels lweDimension : ℕ} (gadget : Fin levels → R)
    (mask : BinarySecret lweDimension)
    (bootstrappingKey : Fin lweDimension → TGSW.Ciphertext R dimension levels) :
    Fin lweDimension → TGSW.Ciphertext R dimension levels :=
  fun coordinate => toggleTGSW gadget (mask coordinate) (bootstrappingKey coordinate)

@[simp]
theorem transformBootstrappingKey_involutive {R : Type} [CommRing R]
    {dimension levels lweDimension : ℕ} (gadget : Fin levels → R)
    (mask : BinarySecret lweDimension)
    (bootstrappingKey : Fin lweDimension → TGSW.Ciphertext R dimension levels) :
    transformBootstrappingKey gadget mask
        (transformBootstrappingKey gadget mask bootstrappingKey) = bootstrappingKey := by
  funext coordinate
  simp [transformBootstrappingKey]

theorem transformBootstrappingKey_bijective {R : Type} [CommRing R]
    {dimension levels lweDimension : ℕ} (gadget : Fin levels → R)
    (mask : BinarySecret lweDimension) :
    Function.Bijective (transformBootstrappingKey
      (dimension := dimension) gadget mask) :=
  Function.Involutive.bijective (transformBootstrappingKey_involutive gadget mask)

theorem transformBootstrappingKey_uniform_evalDist
    {q degree ringRank levels lweDimension : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q degree) (mask : BinarySecret lweDimension) :
    evalDist (transformBootstrappingKey gadget mask <$>
        ($ᵗ Native.BootstrappingKey q degree ringRank levels lweDimension)) =
      evalDist ($ᵗ Native.BootstrappingKey q degree ringRank levels lweDimension) :=
  evalDist_map_bijective_uniform_cross
    (α := Native.BootstrappingKey q degree ringRank levels lweDimension)
    (β := Native.BootstrappingKey q degree ringRank levels lweDimension)
    (transformBootstrappingKey gadget mask)
    (transformBootstrappingKey_bijective gadget mask)

theorem transformBootstrappingKey_generate_centeredBinomial_evalDist
    {q degree ringRank levels lweDimension eta : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist (transformBootstrappingKey gadget mask <$>
        Native.generateBootstrappingKey q (degree + 1) ringRank levels lweDimension
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          gadget lweSecret ringSecret) =
      evalDist (Native.generateBootstrappingKey q (degree + 1) ringRank levels lweDimension
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        gadget (maskedSecret lweSecret mask) ringSecret) := by
  rw [show transformBootstrappingKey gadget mask =
      (fun bootstrappingKey coordinate =>
        toggleTGSW gadget (mask coordinate) (bootstrappingKey coordinate)) by rfl]
  simpa only [Native.generateBootstrappingKey, maskedSecret] using
    mOfFn_map_evalDist_congr lweDimension
      (fun coordinate =>
        TGSW.encrypt ringRank levels
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q (degree + 1) (lweSecret coordinate)))
      (fun coordinate =>
        TGSW.encrypt ringRank levels
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q (degree + 1)
            (LWE.MultiKeyAffine.maskedBit (lweSecret coordinate) (mask coordinate))))
      (fun coordinate => toggleTGSW gadget (mask coordinate))
      (fun coordinate => toggleTGSW_centeredBinomial_encrypt_evalDist
        (embedRingSecret q ringSecret) gadget (lweSecret coordinate) (mask coordinate))

/-! ## Key-switch-key transport -/

def transformKeySwitchKey {q targetDimension sourceDimension levels : ℕ}
    (mask : BinarySecret targetDimension)
    (keySwitchKey : Native.KeySwitchKey q targetDimension sourceDimension levels) :
    Native.KeySwitchKey q targetDimension sourceDimension levels :=
  transformBatch mask keySwitchKey

theorem transformKeySwitchKey_bijective {q targetDimension sourceDimension levels : ℕ}
    (mask : BinarySecret targetDimension) :
    Function.Bijective (transformKeySwitchKey
      (q := q) (sourceDimension := sourceDimension) (levels := levels) mask) :=
  transformBatch_bijective mask

theorem transformKeySwitchKey_generate_evalDist
    {q targetDimension sourceDimension levels : ℕ} [NeZero q]
    (errorSampler : ProbComp (ZMod q)) (gadget : Fin levels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret mask : BinarySecret targetDimension) :
    evalDist (transformKeySwitchKey mask <$>
        Native.generateKeySwitchKey q targetDimension sourceDimension levels
          errorSampler gadget sourceSecret targetSecret) =
      evalDist (Native.generateKeySwitchKey q targetDimension sourceDimension levels
        errorSampler gadget sourceSecret (maskedSecret targetSecret mask)) := by
  change evalDist (transformBatch mask <$>
      TLWE.batchEncrypt targetDimension (sourceDimension * levels) errorSampler
        (embedBinarySecret targetSecret)
        (Native.keySwitchMessages sourceDimension levels gadget sourceSecret)) = _
  exact transformBatch_batchEncrypt_evalDist errorSampler targetSecret mask
    (Native.keySwitchMessages sourceDimension levels gadget sourceSecret)

/-! ## Joint auxiliary-input views -/

theorem independentPair_map_evalDist_congr {α β γ δ : Type}
    (first : ProbComp α) (second : ProbComp β)
    (first' : ProbComp γ) (second' : ProbComp δ)
    (transformFirst : α → γ) (transformSecond : β → δ)
    (hfirst : evalDist (transformFirst <$> first) = evalDist first')
    (hsecond : evalDist (transformSecond <$> second) = evalDist second') :
    evalDist ((fun pair => (transformFirst pair.1, transformSecond pair.2)) <$>
        (first >>= fun left => second >>= fun right => pure (left, right))) =
      evalDist (first' >>= fun left => second' >>= fun right => pure (left, right)) := by
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  calc
    _ = evalDist ((transformFirst <$> first) >>= fun left =>
        (transformSecond <$> second) >>= fun right => pure (left, right)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (first' >>= fun left =>
        (transformSecond <$> second) >>= fun right => pure (left, right)) := by
      rw [evalDist_bind, hfirst, ← evalDist_bind]
    _ = evalDist (first' >>= fun left => second' >>= fun right =>
        pure (left, right)) := by
      refine evalDist_bind_congr' first' fun _ => ?_
      rw [evalDist_bind, hsecond, ← evalDist_bind]
    _ = _ := by simp

noncomputable def transformEvaluationKeyPair
    {q degree ringRank tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (mask : BinarySecret lweDimension)
    (view : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ×
      Native.KeySwitchKey q lweDimension sourceDimension keySwitchLevels) :
    Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ×
      Native.KeySwitchKey q lweDimension sourceDimension keySwitchLevels :=
  (transformBootstrappingKey tgswGadget mask view.1,
    transformKeySwitchKey mask view.2)

theorem transformEvaluationKeyPair_bijective
    {q degree ringRank tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (mask : BinarySecret lweDimension) :
    Function.Bijective (transformEvaluationKeyPair
      (ringRank := ringRank) (sourceDimension := sourceDimension)
      (keySwitchLevels := keySwitchLevels) tgswGadget mask) := by
  change Function.Bijective (Prod.map
    (transformBootstrappingKey tgswGadget mask)
    (transformKeySwitchKey mask))
  exact (transformBootstrappingKey_bijective tgswGadget mask).prodMap
    (transformKeySwitchKey_bijective mask)

noncomputable def sampleRealEvaluationKeyPair
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ×
      Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) := do
  let bootstrappingKey ← Native.generateBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
    lweSecret ringSecret
  let keySwitchKey ← Native.generateKeySwitchKey
    q lweDimension (ringRank * degree) keySwitchLevels
    keySwitchErrorSampler keySwitchGadget (keyExtract ringSecret) lweSecret
  return (bootstrappingKey, keySwitchKey)

noncomputable def sampleUniformBootstrapEvaluationKeyPair
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ×
      Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) := do
  let bootstrappingKey ←
    $ᵗ Native.BootstrappingKey q degree ringRank tgswLevels lweDimension
  let keySwitchKey ← Native.generateKeySwitchKey
    q lweDimension (ringRank * degree) keySwitchLevels
    keySwitchErrorSampler keySwitchGadget (keyExtract ringSecret) lweSecret
  return (bootstrappingKey, keySwitchKey)

theorem transform_realEvaluationKeyPair_centeredBinomial_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ}
    [NeZero q] (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist (transformEvaluationKeyPair tgswGadget mask <$>
        sampleRealEvaluationKeyPair q (degree + 1) ringRank tgswLevels
          lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret ringSecret) =
      evalDist (sampleRealEvaluationKeyPair q (degree + 1) ringRank tgswLevels
        lweDimension keySwitchLevels
        (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
        keySwitchErrorSampler tgswGadget keySwitchGadget
        (maskedSecret lweSecret mask) ringSecret) := by
  rw [show transformEvaluationKeyPair tgswGadget mask =
      (fun view =>
        (transformBootstrappingKey tgswGadget mask view.1,
          transformKeySwitchKey mask view.2)) by rfl]
  unfold sampleRealEvaluationKeyPair
  exact independentPair_map_evalDist_congr _ _ _ _ _ _
    (transformBootstrappingKey_generate_centeredBinomial_evalDist
      tgswGadget lweSecret mask ringSecret)
    (transformKeySwitchKey_generate_evalDist keySwitchErrorSampler keySwitchGadget
      (keyExtract ringSecret) lweSecret mask)

theorem transform_uniformBootstrapEvaluationKeyPair_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    [NeZero q] (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (transformEvaluationKeyPair tgswGadget mask <$>
        sampleUniformBootstrapEvaluationKeyPair q degree ringRank tgswLevels
          lweDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget
          lweSecret ringSecret) =
      evalDist (sampleUniformBootstrapEvaluationKeyPair q degree ringRank tgswLevels
        lweDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (maskedSecret lweSecret mask) ringSecret) := by
  rw [show transformEvaluationKeyPair tgswGadget mask =
      (fun view =>
        (transformBootstrappingKey tgswGadget mask view.1,
          transformKeySwitchKey mask view.2)) by rfl]
  unfold sampleUniformBootstrapEvaluationKeyPair
  exact independentPair_map_evalDist_congr _ _ _ _ _ _
    (transformBootstrappingKey_uniform_evalDist tgswGadget mask)
    (transformKeySwitchKey_generate_evalDist keySwitchErrorSampler keySwitchGadget
      (keyExtract ringSecret) lweSecret mask)

/-! ## Uniformly sampled scalar masks -/

/-- XOR-masking twice by one fixed scalar key recovers the original mask. -/
@[simp]
theorem maskedSecret_involutive {dimension : ℕ}
    (secret mask : BinarySecret dimension) :
    maskedSecret secret (maskedSecret secret mask) = mask := by
  funext coordinate
  exact LWE.MultiKeyAffine.maskedBit_involutive
    (secret coordinate) (mask coordinate)

/-- XOR with a fixed scalar key, packaged as a permutation of binary secrets. -/
def maskedSecretEquiv {dimension : ℕ} (secret : BinarySecret dimension) :
    BinarySecret dimension ≃ BinarySecret dimension where
  toFun := maskedSecret secret
  invFun := maskedSecret secret
  left_inv := maskedSecret_involutive secret
  right_inv := maskedSecret_involutive secret

/-- A uniform binary mask XORed with any fixed scalar key is exactly uniform. -/
theorem maskedSecret_uniform_evalDist {dimension : ℕ}
    (secret : BinarySecret dimension) :
    evalDist (maskedSecret secret <$> ($ᵗ BinarySecret dimension)) =
      evalDist ($ᵗ BinarySecret dimension) :=
  evalDist_map_bijective_uniform_cross
    (α := BinarySecret dimension) (β := BinarySecret dimension)
    (maskedSecret secret) (maskedSecretEquiv secret).bijective

/-- Binary XOR masking is symmetric in the source key and mask. -/
theorem maskedSecret_comm {dimension : ℕ}
    (left right : BinarySecret dimension) :
    maskedSecret left right = maskedSecret right left := by
  funext coordinate
  cases hleft : left coordinate <;> cases hright : right coordinate <;>
    simp [maskedSecret, LWE.MultiKeyAffine.maskedBit, hleft, hright]

/-- A uniformly sampled source key remains uniform after XOR with one fixed mask. -/
theorem maskedSecret_uniform_left_evalDist {dimension : ℕ}
    (mask : BinarySecret dimension) :
    evalDist ((fun secret ↦ maskedSecret secret mask) <$>
        ($ᵗ BinarySecret dimension)) =
      evalDist ($ᵗ BinarySecret dimension) := by
  have hfun : (fun secret ↦ maskedSecret secret mask) = maskedSecret mask := by
    funext secret
    exact maskedSecret_comm secret mask
  rw [hfun, maskedSecret_uniform_evalDist mask]

/-- Fixed-mask transport preserves a view whose binary source key is sampled uniformly.

This is the distributional core of the CircLWE secret-randomization step: if every fixed-key
view transports exactly from `secret` to `secret ⊕ mask`, then averaging over the uniform
source key makes the public transformed view invariant. -/
theorem transform_uniformSecretView_evalDist
    {View : Type} {dimension : ℕ}
    (mask : BinarySecret dimension)
    (sampleView : BinarySecret dimension → ProbComp View)
    (transformView : BinarySecret dimension → View → View)
    (htransport : ∀ secret,
      evalDist (transformView mask <$> sampleView secret) =
        evalDist (sampleView (maskedSecret secret mask))) :
    evalDist (do
        let secret ← $ᵗ BinarySecret dimension
        let view ← sampleView secret
        return transformView mask view) =
      evalDist (do
        let secret ← $ᵗ BinarySecret dimension
        sampleView secret) := by
  calc
    _ = evalDist (($ᵗ BinarySecret dimension) >>= fun secret ↦
        transformView mask <$> sampleView secret) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def]
    _ = evalDist (($ᵗ BinarySecret dimension) >>= fun secret ↦
        sampleView (maskedSecret secret mask)) := by
      exact evalDist_bind_congr' ($ᵗ BinarySecret dimension) htransport
    _ = evalDist (((fun secret ↦ maskedSecret secret mask) <$>
          ($ᵗ BinarySecret dimension)) >>= sampleView) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (($ᵗ BinarySecret dimension) >>= sampleView) := by
      rw [evalDist_bind, maskedSecret_uniform_left_evalDist mask, ← evalDist_bind]
    _ = _ := by rfl

/-- Generic lift from fixed-mask view transport to a fresh uniformly sampled scalar key.

If every fixed mask transports `sampleView secret` to `sampleView (secret ⊕ mask)`, then
sampling that mask uniformly and returning the transported key and view is exactly the experiment
that samples a fresh uniform key and its native view. -/
theorem sampleMaskedView_evalDist
    {View : Type} {dimension : ℕ}
    (secret : BinarySecret dimension)
    (sampleView : BinarySecret dimension → ProbComp View)
    (transformView : BinarySecret dimension → View → View)
    (htransport : ∀ mask,
      evalDist (transformView mask <$> sampleView secret) =
        evalDist (sampleView (maskedSecret secret mask))) :
    evalDist (do
      let mask ← $ᵗ BinarySecret dimension
      let view ← sampleView secret
      return (maskedSecret secret mask, transformView mask view)) =
      evalDist (do
        let freshSecret ← $ᵗ BinarySecret dimension
        let view ← sampleView freshSecret
        return (freshSecret, view)) := by
  let finish := fun (freshSecret : BinarySecret dimension) (view : View) =>
    (pure (freshSecret, view) : ProbComp (BinarySecret dimension × View))
  calc
    _ = evalDist (($ᵗ BinarySecret dimension) >>= fun mask =>
        (transformView mask <$> sampleView secret) >>= fun view =>
          finish (maskedSecret secret mask) view) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind,
        finish]
    _ = evalDist (($ᵗ BinarySecret dimension) >>= fun mask =>
        sampleView (maskedSecret secret mask) >>= fun view =>
          finish (maskedSecret secret mask) view) := by
      refine evalDist_bind_congr' ($ᵗ BinarySecret dimension) fun mask => ?_
      rw [evalDist_bind, htransport mask, ← evalDist_bind]
    _ = evalDist ((maskedSecret secret <$> ($ᵗ BinarySecret dimension)) >>=
        fun freshSecret => sampleView freshSecret >>= fun view =>
          finish freshSecret view) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (($ᵗ BinarySecret dimension) >>= fun freshSecret =>
        sampleView freshSecret >>= fun view => finish freshSecret view) := by
      rw [evalDist_bind, maskedSecret_uniform_evalDist secret, ← evalDist_bind]
    _ = _ := by simp [finish, monad_norm]

/-- Mask a fixed scalar key and publicly transport its centered-binomial real evaluation-key
view, returning the randomized key alongside that transformed view. -/
noncomputable def sampleMaskedRealScalarView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ)
    [NeZero q] (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) := do
  let mask ← $ᵗ BinarySecret lweDimension
  let view ← sampleRealEvaluationKeyPair q (degree + 1) ringRank tgswLevels
    lweDimension keySwitchLevels
    (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
    keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret ringSecret
  return (maskedSecret lweSecret mask,
    transformEvaluationKeyPair tgswGadget mask view)

/-- Sample a fresh uniform scalar key and its centered-binomial real evaluation-key view while
keeping the ring key fixed. -/
noncomputable def sampleFreshRealScalarView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ)
    [NeZero q] (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) := do
  let freshSecret ← $ᵗ BinarySecret lweDimension
  let view ← sampleRealEvaluationKeyPair q (degree + 1) ringRank tgswLevels
    lweDimension keySwitchLevels
    (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
    keySwitchErrorSampler tgswGadget keySwitchGadget freshSecret ringSecret
  return (freshSecret, view)

/-- Uniform scalar masking plus the public native evaluation-key transform produces exactly a
fresh scalar key and its real centered-binomial BRK+KSK view. -/
theorem sampleMaskedRealScalarView_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ}
    [NeZero q] (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist (sampleMaskedRealScalarView q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchErrorSampler
      tgswGadget keySwitchGadget lweSecret ringSecret) =
      evalDist (sampleFreshRealScalarView q degree ringRank tgswLevels
        lweDimension keySwitchLevels ringEta keySwitchErrorSampler
        tgswGadget keySwitchGadget ringSecret) := by
  unfold sampleMaskedRealScalarView sampleFreshRealScalarView
  exact sampleMaskedView_evalDist lweSecret
    (fun freshSecret =>
      sampleRealEvaluationKeyPair q (degree + 1) ringRank tgswLevels
        lweDimension keySwitchLevels
        (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
        keySwitchErrorSampler tgswGadget keySwitchGadget freshSecret ringSecret)
    (transformEvaluationKeyPair tgswGadget)
    (fun mask => transform_realEvaluationKeyPair_centeredBinomial_evalDist
      keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret mask ringSecret)

/-- Mask a fixed scalar key and publicly transport the uniform-BRK evaluation-key endpoint. -/
noncomputable def sampleMaskedUniformScalarView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ)
    [NeZero q] (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) := do
  let mask ← $ᵗ BinarySecret lweDimension
  let view ← sampleUniformBootstrapEvaluationKeyPair q degree ringRank tgswLevels
    lweDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget
    lweSecret ringSecret
  return (maskedSecret lweSecret mask,
    transformEvaluationKeyPair tgswGadget mask view)

/-- Sample a fresh uniform scalar key and the uniform-BRK+real-KSK endpoint for a fixed ring
key. -/
noncomputable def sampleFreshUniformScalarView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ)
    [NeZero q] (keySwitchErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank degree) := do
  let freshSecret ← $ᵗ BinarySecret lweDimension
  let view ← sampleUniformBootstrapEvaluationKeyPair q degree ringRank tgswLevels
    lweDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget
    freshSecret ringSecret
  return (freshSecret, view)

/-- Uniform scalar masking also produces exactly the fresh-scalar-key distribution at the
uniform-BRK endpoint. -/
theorem sampleMaskedUniformScalarView_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    [NeZero q] (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (sampleMaskedUniformScalarView q degree ringRank tgswLevels
      lweDimension keySwitchLevels keySwitchErrorSampler
      tgswGadget keySwitchGadget lweSecret ringSecret) =
      evalDist (sampleFreshUniformScalarView q degree ringRank tgswLevels
        lweDimension keySwitchLevels keySwitchErrorSampler
        keySwitchGadget ringSecret) := by
  unfold sampleMaskedUniformScalarView sampleFreshUniformScalarView
  exact sampleMaskedView_evalDist lweSecret
    (fun freshSecret =>
      sampleUniformBootstrapEvaluationKeyPair q degree ringRank tgswLevels
        lweDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget
        freshSecret ringSecret)
    (transformEvaluationKeyPair tgswGadget)
    (fun mask => transform_uniformBootstrapEvaluationKeyPair_evalDist
      keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret mask ringSecret)

end FormalProof4FHE.TFHE.Native.ScalarSecretRandomization
