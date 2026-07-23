/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.ConditionalSmudging
import FormalProof4FHE.TFHE.BootstrappingSecurity
import FormalProof4FHE.TFHE.InternalProduct

/-!
# Translation Normal Forms for Fresh Native TGSW Ciphertexts

Adding one fixed public TGSW ciphertext to an independently sampled direct TGSW encryption
translates its uniform masks and shifts its error by exactly the fixed ciphertext's phase.
Uniform-mask translation is a permutation, so the resulting distribution is exactly the
residual-encryption sampler already consumed by conditional smudging.

This is the distributional tool needed after the shifted evaluator's true branch has been
reparameterized as an independent difference.  It applies whenever the public perturbation is
independent of the retained fresh source entry; no claim of that independence is hidden here.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.Translation

noncomputable section

/-- Translate all fresh TLWE masks by the fixed public mask part of one TGSW ciphertext. -/
def translateChallenge {R : Type} [Add R] {dimension levels : ℕ}
    (delta : TGSW.Ciphertext R dimension levels)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :
    Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R :=
  challenge + delta.1

/-- Fixed mask translation is a bijection on the complete TGSW challenge matrix. -/
theorem translateChallenge_bijective {R : Type} [AddGroup R]
    {dimension levels : ℕ}
    (delta : TGSW.Ciphertext R dimension levels) :
    Function.Bijective (translateChallenge delta) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨fun challenge => challenge - delta.1, ?_, ?_⟩
  · intro challenge
    funext coordinate row
    exact add_sub_cancel_right _ _
  · intro challenge
    funext coordinate row
    exact sub_add_cancel _ _

/-- Consequently a fixed TGSW mask translation preserves the exact uniform challenge law. -/
theorem translateChallenge_uniform_evalDist {R : Type}
    [AddGroup R] [Fintype R] [SampleableType R]
    {dimension levels : ℕ}
    (delta : TGSW.Ciphertext R dimension levels) :
    evalDist (translateChallenge delta <$>
        ($ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)) =
      evalDist
        ($ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (β := Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (translateChallenge delta) (translateChallenge_bijective delta)

/-- Direct fresh TGSW encryption never fails when its one-row error sampler never fails. -/
theorem probFailure_directEncrypt_eq_zero
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (hError : Pr[⊥ | errorSampler] = 0) :
    Pr[⊥ | TGSW.directEncrypt dimension levels errorSampler secret gadget message] = 0 := by
  have hErrors :
      Pr[⊥ | ProbComp.sampleIID (TGSW.rowCount dimension levels) errorSampler] = 0 := by
    simpa only [ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.probFailure_fin_mOfFn_eq_zero
        (TGSW.rowCount dimension levels) (fun _ => errorSampler) (fun _ => hError))
  letI : NeverFail
      (ProbComp.sampleIID (TGSW.rowCount dimension levels) errorSampler) :=
    NeverFail.of_probFailure_eq_zero _ hErrors
  have hDirect : NeverFail
      (TGSW.directEncrypt dimension levels errorSampler secret gadget message) := by
    unfold TGSW.directEncrypt TLWE.batchEncrypt
    apply NeverFail.bind_of_forall
  exact hDirect.probFailure_eq_zero

/-- Deterministic translation normal form: adding a fixed ciphertext translates the mask and
adds precisely its row phase to the source error vector. -/
theorem add_batchAssemble
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (message error : Fin (TGSW.rowCount dimension levels) → R)
    (delta : TGSW.Ciphertext R dimension levels) :
    TGSW.add (TLWE.batchAssemble secret challenge message error) delta =
      TLWE.batchAssemble secret (translateChallenge delta challenge) message
        (TLWE.batchPhase secret delta + error) := by
  apply Prod.ext
  · funext coordinate row
    rfl
  · funext row
    simp only [TGSW.add, TLWE.batchOfRows, TLWE.entry, TLWE.add, TLWE.batchAssemble,
      TLWE.batchPhase, translateChallenge, Pi.add_apply, Pi.sub_apply, Matrix.add_apply,
      Matrix.vecMul, dotProduct]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    ring

/-- Adding a fixed independent ciphertext to a direct TGSW encryption is exactly direct residual
encryption with residual equal to the fixed ciphertext's phase vector. -/
theorem add_directEncrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ)
    (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (delta : TGSW.Ciphertext R dimension levels) :
    evalDist ((fun ciphertext => TGSW.add ciphertext delta) <$>
        TGSW.directEncrypt dimension levels errorSampler secret gadget message) =
      evalDist
        (TGSW.directEncryptWithResidual dimension levels errorSampler secret gadget
          message (TLWE.batchPhase secret delta)) := by
  let challenges :
      ProbComp (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :=
    $ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R
  let errors := ProbComp.sampleIID (TGSW.rowCount dimension levels) errorSampler
  let residual := TLWE.batchPhase secret delta
  let finish := fun
      (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
      (error : Fin (TGSW.rowCount dimension levels) → R) =>
    TLWE.batchAssemble secret challenge (TGSW.gadgetPhase secret gadget message)
      (residual + error)
  have hshape :
      evalDist ((fun ciphertext => TGSW.add ciphertext delta) <$>
          TGSW.directEncrypt dimension levels errorSampler secret gadget message) =
        evalDist (challenges >>= fun challenge =>
          errors >>= fun error =>
            pure (finish (translateChallenge delta challenge) error)) := by
    simp only [TGSW.directEncrypt, TLWE.batchEncrypt, challenges, errors, finish,
      residual, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    simp_rw [add_batchAssemble]
  rw [hshape]
  calc
    _ = evalDist ((translateChallenge delta <$> challenges) >>= fun challenge =>
        errors >>= fun error => pure (finish challenge error)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (challenges >>= fun challenge =>
        errors >>= fun error => pure (finish challenge error)) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (translateChallenge_uniform_evalDist delta)
        (fun challenge => errors >>= fun error => pure (finish challenge error))
    _ = _ := by
      simp [TGSW.directEncryptWithResidual, TLWE.batchEncryptWithResidual,
        challenges, errors, residual, finish, monad_norm]

/-- If the perturbation is sampled independently after the fresh source ciphertext, sampling may
be commuted and the fixed-translation law applied conditionally.  This exposes the exact residual
mixture without assuming any bound on the perturbation. -/
theorem add_independent_directEncrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ)
    (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (perturbationSampler : ProbComp (TGSW.Ciphertext R dimension levels)) :
    evalDist (TGSW.directEncrypt dimension levels errorSampler secret gadget message >>= fun source =>
        perturbationSampler >>= fun perturbation =>
          pure (TGSW.add source perturbation)) =
      evalDist (perturbationSampler >>= fun perturbation =>
        TGSW.directEncryptWithResidual dimension levels errorSampler secret gadget message
          (TLWE.batchPhase secret perturbation)) := by
  calc
    _ = evalDist (perturbationSampler >>= fun perturbation =>
        TGSW.directEncrypt dimension levels errorSampler secret gadget message >>= fun source =>
          pure (TGSW.add source perturbation)) :=
      evalDist_bind_bind_swap
        (TGSW.directEncrypt dimension levels errorSampler secret gadget message)
        perturbationSampler
        (fun source perturbation => pure (TGSW.add source perturbation))
    _ = _ := by
      refine evalDist_bind_congr' perturbationSampler fun perturbation => ?_
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (add_directEncrypt_evalDist dimension levels errorSampler secret gadget message
          perturbation)

/-- The same exact translation law starts from the native structured TGSW sampler. -/
theorem add_encrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ)
    (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (delta : TGSW.Ciphertext R dimension levels) :
    evalDist ((fun ciphertext => TGSW.add ciphertext delta) <$>
        TGSW.encrypt dimension levels errorSampler secret gadget message) =
      evalDist
        (TGSW.directEncryptWithResidual dimension levels errorSampler secret gadget
          message (TLWE.batchPhase secret delta)) := by
  rw [evalDist_map]
  rw [TGSW.encrypt_evalDist_eq_directEncrypt]
  rw [← evalDist_map]
  exact add_directEncrypt_evalDist dimension levels errorSampler secret gadget message delta

end

end FormalProof4FHE.TFHE.TGSW.Translation
