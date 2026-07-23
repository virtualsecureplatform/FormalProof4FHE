/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareRGSWSecurity

/-!
# Exact Actual-to-Native Normal Form for `RGSW_S(-S)`

This file closes the structural part of the standalone ring-square distribution gap.  Publicly
stripping the direct gadget-phase presentation of `RGSW_S(-S)` translates only its mask matrix.
That translation is a bijection, preserves every sampled row error, and changes the message
vector exactly to the native square/zero vector.  Consequently the genuine stripped RGSW
sampler and the abstract native square-batch sampler have identical distributions, and their
named compiler gaps are exactly equal.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.ActualNormalForm

open FormalProof4FHE.TFHE
open FormalProof4FHE.TFHE.TGSW.RingSquare
open FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler

noncomputable section

def strippedChallenge {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R :=
  (stripLinearBlock gadget (challenge, 0)).1

def restoredChallenge {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R :=
  (restoreLinearBlock gadget (challenge, 0)).1

theorem stripLinearBlock_fst
    {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (body : Fin (TGSW.rowCount 1 levels) → R) :
    (stripLinearBlock gadget (challenge, body)).1 =
      strippedChallenge gadget challenge := by
  funext coordinate row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      change
        (TLWE.entry (stripLinearBlock gadget (challenge, body))
            (finProdFinEquiv (Fin.last 1, level))).mask coordinate =
          (TLWE.entry (stripLinearBlock gadget (challenge, 0))
            (finProdFinEquiv (Fin.last 1, level))).mask coordinate
      rw [entry_strip_last, entry_strip_last]
      rfl
  | cast index =>
      change
        (TLWE.entry (stripLinearBlock gadget (challenge, body))
            (finProdFinEquiv (Fin.castSucc index, level))).mask coordinate =
          (TLWE.entry (stripLinearBlock gadget (challenge, 0))
            (finProdFinEquiv (Fin.castSucc index, level))).mask coordinate
      rw [entry_strip_castSucc, entry_strip_castSucc]
      rfl

theorem stripLinearBlock_snd
    {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (body : Fin (TGSW.rowCount 1 levels) → R) :
    (stripLinearBlock gadget (challenge, body)).2 = body := by
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      change
        (TLWE.entry (stripLinearBlock gadget (challenge, body))
            (finProdFinEquiv (Fin.last 1, level))).body =
          body (finProdFinEquiv (Fin.last 1, level))
      rw [entry_strip_last]
      rfl
  | cast index =>
      change
        (TLWE.entry (stripLinearBlock gadget (challenge, body))
            (finProdFinEquiv (Fin.castSucc index, level))).body =
          body (finProdFinEquiv (Fin.castSucc index, level))
      rw [entry_strip_castSucc]
      rfl

theorem restoreLinearBlock_fst
    {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (body : Fin (TGSW.rowCount 1 levels) → R) :
    (restoreLinearBlock gadget (challenge, body)).1 =
      restoredChallenge gadget challenge := by
  funext coordinate row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      change
        (TLWE.entry (restoreLinearBlock gadget (challenge, body))
            (finProdFinEquiv (Fin.last 1, level))).mask coordinate =
          (TLWE.entry (restoreLinearBlock gadget (challenge, 0))
            (finProdFinEquiv (Fin.last 1, level))).mask coordinate
      rw [entry_restore_last, entry_restore_last]
      rfl
  | cast index =>
      change
        (TLWE.entry (restoreLinearBlock gadget (challenge, body))
            (finProdFinEquiv (Fin.castSucc index, level))).mask coordinate =
          (TLWE.entry (restoreLinearBlock gadget (challenge, 0))
            (finProdFinEquiv (Fin.castSucc index, level))).mask coordinate
      rw [entry_restore_castSucc, entry_restore_castSucc]
      rfl

theorem restoreLinearBlock_snd
    {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (body : Fin (TGSW.rowCount 1 levels) → R) :
    (restoreLinearBlock gadget (challenge, body)).2 = body := by
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      change
        (TLWE.entry (restoreLinearBlock gadget (challenge, body))
            (finProdFinEquiv (Fin.last 1, level))).body =
          body (finProdFinEquiv (Fin.last 1, level))
      rw [entry_restore_last]
      rfl
  | cast index =>
      change
        (TLWE.entry (restoreLinearBlock gadget (challenge, body))
            (finProdFinEquiv (Fin.castSucc index, level))).body =
          body (finProdFinEquiv (Fin.castSucc index, level))
      rw [entry_restore_castSucc]
      rfl

@[simp]
theorem restoredChallenge_strippedChallenge
    {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    restoredChallenge gadget (strippedChallenge gadget challenge) = challenge := by
  let zeroBody : Fin (TGSW.rowCount 1 levels) → R := 0
  have hStrip :
      stripLinearBlock gadget (challenge, zeroBody) =
        (strippedChallenge gadget challenge, zeroBody) := by
    apply Prod.ext
    · exact stripLinearBlock_fst gadget challenge zeroBody
    · exact stripLinearBlock_snd gadget challenge zeroBody
  calc
    restoredChallenge gadget (strippedChallenge gadget challenge) =
        (restoreLinearBlock gadget
          (strippedChallenge gadget challenge, zeroBody)).1 := rfl
    _ = (restoreLinearBlock gadget
          (stripLinearBlock gadget (challenge, zeroBody))).1 :=
      congrArg (fun ciphertext ↦ (restoreLinearBlock gadget ciphertext).1) hStrip.symm
    _ = challenge := congrArg Prod.fst
      (restore_strip gadget (challenge, zeroBody))

@[simp]
theorem strippedChallenge_restoredChallenge
    {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    strippedChallenge gadget (restoredChallenge gadget challenge) = challenge := by
  let zeroBody : Fin (TGSW.rowCount 1 levels) → R := 0
  have hRestore :
      restoreLinearBlock gadget (challenge, zeroBody) =
        (restoredChallenge gadget challenge, zeroBody) := by
    apply Prod.ext
    · exact restoreLinearBlock_fst gadget challenge zeroBody
    · exact restoreLinearBlock_snd gadget challenge zeroBody
  calc
    strippedChallenge gadget (restoredChallenge gadget challenge) =
        (stripLinearBlock gadget
          (restoredChallenge gadget challenge, zeroBody)).1 := rfl
    _ = (stripLinearBlock gadget
          (restoreLinearBlock gadget (challenge, zeroBody))).1 :=
      congrArg (fun ciphertext ↦ (stripLinearBlock gadget ciphertext).1) hRestore.symm
    _ = challenge := congrArg Prod.fst
      (strip_restore gadget (challenge, zeroBody))

theorem strippedChallenge_bijective
    {R : Type} [AddGroup R] {levels : ℕ}
    (gadget : Fin levels → R) :
    Function.Bijective (strippedChallenge gadget) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨restoredChallenge gadget, restoredChallenge_strippedChallenge gadget,
      strippedChallenge_restoredChallenge gadget⟩

theorem stripLinearBlock_batchAssemble_gadgetPhase_negSecret
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (error : Fin (TGSW.rowCount 1 levels) → R) :
    stripLinearBlock gadget
        (TLWE.batchAssemble secret challenge
          (TGSW.gadgetPhase secret gadget (-secret 0)) error) =
      TLWE.batchAssemble secret (strippedChallenge gadget challenge)
        (Full.squareMessages secret gadget) error := by
  apply (Full.batchRowsEquiv R 1 (TGSW.rowCount 1 levels)).injective
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      let left := TLWE.entry
        (stripLinearBlock gadget
          (TLWE.batchAssemble secret challenge
            (TGSW.gadgetPhase secret gadget (-secret 0)) error))
        (finProdFinEquiv (Fin.last 1, level))
      let right := TLWE.entry
        (TLWE.batchAssemble secret (strippedChallenge gadget challenge)
          (Full.squareMessages secret gadget) error)
        (finProdFinEquiv (Fin.last 1, level))
      have hmask : left.mask = right.mask := by
        funext coordinate
        change
          (stripLinearBlock gadget
              (TLWE.batchAssemble secret challenge
                (TGSW.gadgetPhase secret gadget (-secret 0)) error)).1
              coordinate (finProdFinEquiv (Fin.last 1, level)) =
            strippedChallenge gadget challenge coordinate
              (finProdFinEquiv (Fin.last 1, level))
        exact congrArg
          (fun mask ↦ mask coordinate (finProdFinEquiv (Fin.last 1, level)))
          (stripLinearBlock_fst gadget challenge
            (vecMul secret challenge +
              TGSW.gadgetPhase secret gadget (-secret 0) + error))
      have hphase := phase_entry_strip_last_eq_error secret gadget
        (TLWE.batchAssemble secret challenge
          (TGSW.gadgetPhase secret gadget (-secret 0)) error) level
      have hrowError :
          TGSW.rowError secret gadget (-secret 0)
              (TLWE.batchAssemble secret challenge
                (TGSW.gadgetPhase secret gadget (-secret 0)) error)
              (Fin.last 1, level) =
            error (finProdFinEquiv (Fin.last 1, level)) := by
        simp [TGSW.rowError]
      rw [hrowError] at hphase
      change TLWE.phase secret left =
        error (finProdFinEquiv (Fin.last 1, level)) at hphase
      have hright : TLWE.phase secret right =
          error (finProdFinEquiv (Fin.last 1, level)) := by
        unfold right
        rw [TLWE.phase_entry, TLWE.batchPhase_batchAssemble]
        change
          Full.squareMessages secret gadget (Full.lowerRow level) +
              error (Full.lowerRow level) =
            error (Full.lowerRow level)
        rw [Full.squareMessages_lower]
        exact zero_add _
      have hphaseEq : TLWE.phase secret left = TLWE.phase secret right := by
        have hleft : TLWE.phase secret left =
            error (finProdFinEquiv (Fin.last 1, level)) := by
          simpa [left] using hphase
        have hright' :
            error (finProdFinEquiv (Fin.last 1, level)) =
              TLWE.phase secret right := by
          simpa [right] using hright.symm
        exact hleft.trans hright'
      rw [TLWE.Ciphertext.mk.injEq]
      constructor
      · exact hmask
      · unfold TLWE.phase at hphaseEq
        rw [hmask] at hphaseEq
        exact sub_left_injective hphaseEq
  | cast coordinate =>
      have hcoordinate : coordinate = 0 := Fin.eq_zero coordinate
      subst coordinate
      let left := TLWE.entry
        (stripLinearBlock gadget
          (TLWE.batchAssemble secret challenge
            (TGSW.gadgetPhase secret gadget (-secret 0)) error))
        (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level))
      let right := TLWE.entry
        (TLWE.batchAssemble secret (strippedChallenge gadget challenge)
          (Full.squareMessages secret gadget) error)
        (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level))
      have hmask : left.mask = right.mask := by
        funext coordinate
        change
          (stripLinearBlock gadget
              (TLWE.batchAssemble secret challenge
                (TGSW.gadgetPhase secret gadget (-secret 0)) error)).1
              coordinate (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)) =
            strippedChallenge gadget challenge coordinate
              (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level))
        exact congrArg
          (fun mask ↦ mask coordinate
            (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)))
          (stripLinearBlock_fst gadget challenge
            (vecMul secret challenge +
              TGSW.gadgetPhase secret gadget (-secret 0) + error))
      have hphase := phase_entry_strip_castSucc_eq_square_add_error secret gadget
        (TLWE.batchAssemble secret challenge
          (TGSW.gadgetPhase secret gadget (-secret 0)) error) (0 : Fin 1) level
      have hrowError :
          TGSW.rowError secret gadget (-secret 0)
              (TLWE.batchAssemble secret challenge
                (TGSW.gadgetPhase secret gadget (-secret 0)) error)
              (Fin.castSucc (0 : Fin 1), level) =
            error (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)) := by
        simp [TGSW.rowError]
      rw [hrowError] at hphase
      simp [squarePhase] at hphase
      change TLWE.phase secret left =
        secret 0 * secret 0 * gadget level +
          error (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)) at hphase
      have hright : TLWE.phase secret right =
          secret 0 * secret 0 * gadget level +
            error (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)) := by
        unfold right
        rw [TLWE.phase_entry, TLWE.batchPhase_batchAssemble]
        change
          Full.squareMessages secret gadget (Full.upperRow level) +
              error (Full.upperRow level) =
            secret 0 * secret 0 * gadget level + error (Full.upperRow level)
        rw [Full.squareMessages_upper]
      have hphaseEq : TLWE.phase secret left = TLWE.phase secret right := by
        have hleft : TLWE.phase secret left =
            secret 0 * secret 0 * gadget level +
              error (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)) := by
          simpa [left] using hphase
        have hright' :
            secret 0 * secret 0 * gadget level +
                error (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)) =
              TLWE.phase secret right := by
          simpa [right] using hright.symm
        exact hleft.trans hright'
      rw [TLWE.Ciphertext.mk.injEq]
      constructor
      · exact hmask
      · unfold TLWE.phase at hphaseEq
        rw [hmask] at hphaseEq
        exact sub_left_injective hphaseEq

/-- The direct stripped presentation is exactly the native square/zero batch distribution. -/
theorem directEncryptSquareView_evalDist_eq_nativeSquareBatch
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R) :
    evalDist (directEncryptSquareView levels errorSampler secret gadget) =
      evalDist (TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler secret
        (Full.squareMessages secret gadget)) := by
  let Challenges : ProbComp
      (Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R
  let Errors : ProbComp (Fin (TGSW.rowCount 1 levels) → R) :=
    ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler
  have hLeft :
      directEncryptSquareView levels errorSampler secret gadget =
        (Challenges >>= fun challenge ↦
          Errors >>= fun error ↦
            pure (TLWE.batchAssemble secret (strippedChallenge gadget challenge)
              (Full.squareMessages secret gadget) error)) := by
    simp [directEncryptSquareView, TGSW.directEncrypt, TLWE.batchEncrypt,
      Challenges, Errors, monad_norm]
    apply bind_congr
    intro challenge
    apply bind_congr
    intro error
    simpa only [Function.comp_apply] using congrArg
      (fun ciphertext ↦ (pure ciphertext : ProbComp (TGSW.Ciphertext R 1 levels)))
      (stripLinearBlock_batchAssemble_gadgetPhase_negSecret
        secret gadget challenge error)
  have hRight :
      TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler secret
          (Full.squareMessages secret gadget) =
        (Challenges >>= fun challenge ↦
          Errors >>= fun error ↦
            pure (TLWE.batchAssemble secret challenge
              (Full.squareMessages secret gadget) error)) := by
    simp [TLWE.batchEncrypt, Challenges, Errors, monad_norm]
  rw [hLeft, hRight]
  apply evalDist_ext
  intro ciphertext
  simpa only [Challenges] using
    (probOutput_bind_bijective_uniform_cross
      (α := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
      (β := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
      (strippedChallenge gadget) (strippedChallenge_bijective gadget)
      (fun challenge ↦ Errors >>= fun error ↦
        pure (TLWE.batchAssemble secret challenge
          (Full.squareMessages secret gadget) error)) ciphertext)

/-- The structured stripped presentation is exactly the native square/zero batch distribution. -/
theorem encryptSquareView_evalDist_eq_nativeSquareBatch
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R) :
    evalDist (encryptSquareView levels errorSampler secret gadget) =
      evalDist (TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler secret
        (Full.squareMessages secret gadget)) :=
  (encryptSquareView_evalDist_eq_direct levels errorSampler secret gadget).trans
    (directEncryptSquareView_evalDist_eq_nativeSquareBatch
      levels errorSampler secret gadget)

/-- Consequently the actual and abstract-native stripped batch samplers coincide exactly. -/
theorem actualSquareBatchSampler_evalDist_eq_nativeSquareBatchSampler
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) :
    evalDist
        (Full.actualSquareBatchSampler levels secretSampler embed errorSampler gadget) =
      evalDist
        (Full.nativeSquareBatchSampler levels secretSampler embed errorSampler gadget) := by
  unfold Full.actualSquareBatchSampler Full.nativeSquareBatchSampler
  exact evalDist_bind_congr' secretSampler fun secretValue ↦
    encryptSquareView_evalDist_eq_nativeSquareBatch
      levels errorSampler (embed secretValue) gadget

/-- The named genuine-RGSW compiler gap is exactly the native square-batch gap. -/
theorem actualDistributionGap_eq_nativeDistributionGap
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) (selectors : Full.Selectors R levels sourceCount) :
    Full.actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget
        selectors =
      Full.nativeDistributionGap levels sourceCount secretSampler embed errorSampler gadget
        selectors := by
  unfold Full.actualDistributionGap Full.nativeDistributionGap tvDist
  rw [actualSquareBatchSampler_evalDist_eq_nativeSquareBatchSampler]

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.ActualNormalForm
