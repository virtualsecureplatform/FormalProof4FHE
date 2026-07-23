/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareBatchResidualSmudging

/-!
# Exact Compiler Normal Form for `RGSW_S(-S)`

This file connects the hidden ordinary-RLWE short-preimage compiler to the full contextual
residual-smudging experiment.  The target challenge transformation is a bijection, successful
selectors give an exact deterministic shifted-square identity, and independent sampling can be
reordered to obtain the exact full-experiment normal form.

Consequently, the genuine stripped `RGSW_S(-S)` gap is bounded directly by the induced residual
translation cost.  The remaining research obligations are precisely successful efficient short
selectors and a negligible translation bound for correctness-compatible parameters.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.CompilerNormalForm

noncomputable section

def compiledTargetChallenge {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R :=
  (Full.compileTargets selectors sourceBatch (challenge, 0)).1

def restoredTargetChallenge {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R :=
  (Full.restoreTargets selectors sourceBatch (challenge, 0)).1

@[simp]
theorem entry_batchAssemble_eq_assemble
    {R : Type} [Semiring R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error : Fin samples → R) (row : Fin samples) :
    TLWE.entry (TLWE.batchAssemble secret challenge message error) row =
      TLWE.assemble secret (fun coordinate ↦ challenge coordinate row)
        (message row) (error row) := by
  rfl

@[simp]
theorem entry_vecMul_add_eq_assemble_zero
    {R : Type} [Semiring R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) (row : Fin samples) :
    TLWE.entry (challenge, vecMul secret challenge + error) row =
      TLWE.assemble secret (fun coordinate ↦ challenge coordinate row) 0 (error row) := by
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · rfl
  · simp [TLWE.entry, TLWE.assemble, Matrix.vecMul, dotProduct]

@[simp]
theorem entry_add_vecMul_eq_assemble_zero
    {R : Type} [CommSemiring R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) (row : Fin samples) :
    TLWE.entry (challenge, error + vecMul secret challenge) row =
      TLWE.assemble secret (fun coordinate ↦ challenge coordinate row) 0 (error row) := by
  rw [add_comm]
  exact entry_vecMul_add_eq_assemble_zero secret challenge error row

@[simp]
theorem entry_compileTargets_upper
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (targets : Full.TargetBatch R levels) (level : Fin levels) :
    TLWE.entry (Full.compileTargets selectors sourceBatch targets) (Full.upperRow level) =
      compileRows (selectors level)
        (Full.sourceRowsAt sourceBatch level, TLWE.entry targets (Full.upperRow level)) := by
  simp [Full.compileTargets]

@[simp]
theorem entry_restoreTargets_upper
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (targets : Full.TargetBatch R levels) (level : Fin levels) :
    TLWE.entry (Full.restoreTargets selectors sourceBatch targets) (Full.upperRow level) =
      Row.addMask (Full.approximationAt selectors sourceBatch level)
        (TLWE.entry targets (Full.upperRow level)) := by
  simp [Full.restoreTargets]

@[simp]
theorem entry_restoreTargets_lower
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (targets : Full.TargetBatch R levels) (level : Fin levels) :
    TLWE.entry (Full.restoreTargets selectors sourceBatch targets) (Full.lowerRow level) =
      TLWE.entry targets (Full.lowerRow level) := by
  simp [Full.restoreTargets]

theorem compileTargets_fst
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (body : Fin (TGSW.rowCount 1 levels) → R) :
    (Full.compileTargets selectors sourceBatch (challenge, body)).1 =
      compiledTargetChallenge selectors sourceBatch challenge := by
  funext coordinate row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      change
        (TLWE.entry (Full.compileTargets selectors sourceBatch (challenge, body))
            (Full.lowerRow level)).mask coordinate =
          (TLWE.entry (Full.compileTargets selectors sourceBatch (challenge, 0))
            (Full.lowerRow level)).mask coordinate
      rw [Full.entry_compileTargets_lower, Full.entry_compileTargets_lower]
      rfl
  | cast index =>
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      change
        (TLWE.entry (Full.compileTargets selectors sourceBatch (challenge, body))
            (Full.upperRow level)).mask coordinate =
          (TLWE.entry (Full.compileTargets selectors sourceBatch (challenge, 0))
            (Full.upperRow level)).mask coordinate
      rw [entry_compileTargets_upper, entry_compileTargets_upper]
      rfl

theorem compileTargets_snd
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (body : Fin (TGSW.rowCount 1 levels) → R) :
    (Full.compileTargets selectors sourceBatch (challenge, body)).2 = body := by
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      change
        (TLWE.entry (Full.compileTargets selectors sourceBatch (challenge, body))
            (Full.lowerRow level)).body = body (Full.lowerRow level)
      rw [Full.entry_compileTargets_lower]
      rfl
  | cast index =>
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      change
        (TLWE.entry (Full.compileTargets selectors sourceBatch (challenge, body))
            (Full.upperRow level)).body = body (Full.upperRow level)
      rw [entry_compileTargets_upper]
      rfl

theorem restoreTargets_fst
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (body : Fin (TGSW.rowCount 1 levels) → R) :
    (Full.restoreTargets selectors sourceBatch (challenge, body)).1 =
      restoredTargetChallenge selectors sourceBatch challenge := by
  funext coordinate row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      change
        (TLWE.entry (Full.restoreTargets selectors sourceBatch (challenge, body))
            (Full.lowerRow level)).mask coordinate =
          (TLWE.entry (Full.restoreTargets selectors sourceBatch (challenge, 0))
            (Full.lowerRow level)).mask coordinate
      rw [entry_restoreTargets_lower, entry_restoreTargets_lower]
      rfl
  | cast index =>
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      change
        (TLWE.entry (Full.restoreTargets selectors sourceBatch (challenge, body))
            (Full.upperRow level)).mask coordinate =
          (TLWE.entry (Full.restoreTargets selectors sourceBatch (challenge, 0))
            (Full.upperRow level)).mask coordinate
      rw [entry_restoreTargets_upper, entry_restoreTargets_upper]
      rfl

theorem restoreTargets_snd
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (body : Fin (TGSW.rowCount 1 levels) → R) :
    (Full.restoreTargets selectors sourceBatch (challenge, body)).2 = body := by
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      change
        (TLWE.entry (Full.restoreTargets selectors sourceBatch (challenge, body))
            (Full.lowerRow level)).body = body (Full.lowerRow level)
      rw [entry_restoreTargets_lower]
      rfl
  | cast index =>
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      change
        (TLWE.entry (Full.restoreTargets selectors sourceBatch (challenge, body))
            (Full.upperRow level)).body = body (Full.upperRow level)
      rw [entry_restoreTargets_upper]
      rfl

@[simp]
theorem restoredTargetChallenge_compiledTargetChallenge
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    restoredTargetChallenge selectors sourceBatch
        (compiledTargetChallenge selectors sourceBatch challenge) = challenge := by
  let zeroBody : Fin (TGSW.rowCount 1 levels) → R := 0
  have hCompile :
      Full.compileTargets selectors sourceBatch (challenge, zeroBody) =
        (compiledTargetChallenge selectors sourceBatch challenge, zeroBody) := by
    apply Prod.ext
    · exact compileTargets_fst selectors sourceBatch challenge zeroBody
    · exact compileTargets_snd selectors sourceBatch challenge zeroBody
  calc
    restoredTargetChallenge selectors sourceBatch
        (compiledTargetChallenge selectors sourceBatch challenge) =
      (Full.restoreTargets selectors sourceBatch
        (compiledTargetChallenge selectors sourceBatch challenge, zeroBody)).1 := rfl
    _ = (Full.restoreTargets selectors sourceBatch
          (Full.compileTargets selectors sourceBatch (challenge, zeroBody))).1 :=
      congrArg (fun target ↦ (Full.restoreTargets selectors sourceBatch target).1)
        hCompile.symm
    _ = challenge := congrArg Prod.fst
      (Full.restoreTargets_compileTargets selectors sourceBatch (challenge, zeroBody))

@[simp]
theorem compiledTargetChallenge_restoredTargetChallenge
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    compiledTargetChallenge selectors sourceBatch
        (restoredTargetChallenge selectors sourceBatch challenge) = challenge := by
  let zeroBody : Fin (TGSW.rowCount 1 levels) → R := 0
  have hRestore :
      Full.restoreTargets selectors sourceBatch (challenge, zeroBody) =
        (restoredTargetChallenge selectors sourceBatch challenge, zeroBody) := by
    apply Prod.ext
    · exact restoreTargets_fst selectors sourceBatch challenge zeroBody
    · exact restoreTargets_snd selectors sourceBatch challenge zeroBody
  calc
    compiledTargetChallenge selectors sourceBatch
        (restoredTargetChallenge selectors sourceBatch challenge) =
      (Full.compileTargets selectors sourceBatch
        (restoredTargetChallenge selectors sourceBatch challenge, zeroBody)).1 := rfl
    _ = (Full.compileTargets selectors sourceBatch
          (Full.restoreTargets selectors sourceBatch (challenge, zeroBody))).1 :=
      congrArg (fun target ↦ (Full.compileTargets selectors sourceBatch target).1)
        hRestore.symm
    _ = challenge := congrArg Prod.fst
      (Full.compileTargets_restoreTargets selectors sourceBatch (challenge, zeroBody))

theorem compiledTargetChallenge_bijective
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount) :
    Function.Bijective (compiledTargetChallenge selectors sourceBatch) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨restoredTargetChallenge selectors sourceBatch,
      restoredTargetChallenge_compiledTargetChallenge selectors sourceBatch,
      compiledTargetChallenge_restoredTargetChallenge selectors sourceBatch⟩

@[simp]
theorem compiledTargetChallenge_upper
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (coordinate : Fin 1) (level : Fin levels) :
    compiledTargetChallenge selectors sourceBatch challenge coordinate
        (Full.upperRow level) =
      challenge 0 (Full.upperRow level) -
        gadgetApproximation
          (selectors level (sourceMasks (Full.sourceRowsAt sourceBatch level)))
          (Full.sourceRowsAt sourceBatch level) := by
  change
    (TLWE.entry (Full.compileTargets selectors sourceBatch (challenge, 0))
      (Full.upperRow level)).mask coordinate = _
  rw [entry_compileTargets_upper]
  rfl

@[simp]
theorem compiledTargetChallenge_lower
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (coordinate : Fin 1) (level : Fin levels) :
    compiledTargetChallenge selectors sourceBatch challenge coordinate
        (Full.lowerRow level) = challenge coordinate (Full.lowerRow level) := by
  change
    (TLWE.entry (Full.compileTargets selectors sourceBatch (challenge, 0))
      (Full.lowerRow level)).mask coordinate = _
  rw [Full.entry_compileTargets_lower]
  rfl

def contextShift {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (secret : Fin 1 → R) (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount) : Fin levels → R :=
  fun level ↦ ResidualSmudging.inducedShift secret
    (selectors level (sourceMasks (Full.sourceRowsAt sourceBatch level)))
    (Full.sourceRowsAt sourceBatch level)

theorem compileTargets_batchAssemble_zero_eq_shifted
    {R : Type} [CommRing R] {levels sourceCount : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (sourceBatch : Full.SourceBatch R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (error : Fin (TGSW.rowCount 1 levels) → R)
    (hSuccess : ∀ level,
      Full.SelectorSucceedsAt gadget selectors sourceBatch level) :
    Full.compileTargets selectors sourceBatch
        (TLWE.batchAssemble secret challenge 0 error) =
      TLWE.batchAssemble secret
        (compiledTargetChallenge selectors sourceBatch challenge)
        (Full.squareMessages secret gadget)
        (fun row ↦
          BatchResidualSmudging.upperShiftVector
              (contextShift secret selectors sourceBatch) row + error row) := by
  apply (Full.batchRowsEquiv R 1 (TGSW.rowCount 1 levels)).injective
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases with
  | last =>
      change
        TLWE.entry
            (Full.compileTargets selectors sourceBatch
              (TLWE.batchAssemble secret challenge 0 error))
            (Full.lowerRow level) =
          TLWE.entry
            (TLWE.batchAssemble secret
              (compiledTargetChallenge selectors sourceBatch challenge)
              (Full.squareMessages secret gadget)
              (fun row ↦
                BatchResidualSmudging.upperShiftVector
                    (contextShift secret selectors sourceBatch) row + error row))
            (Full.lowerRow level)
      rw [Full.entry_compileTargets_lower]
      simp
  | cast index =>
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      have h := ResidualSmudging.squareFromPreimage_assemble_zero_eq_assembleSquareRow
        secret (fun coordinate ↦ challenge coordinate (Full.upperRow level))
        (gadget level) (error (Full.upperRow level))
        (selectors level (sourceMasks (Full.sourceRowsAt sourceBatch level)))
        (Full.sourceRowsAt sourceBatch level) (hSuccess level)
      change
        TLWE.entry
            (Full.compileTargets selectors sourceBatch
              (TLWE.batchAssemble secret challenge 0 error))
            (Full.upperRow level) =
          TLWE.entry
            (TLWE.batchAssemble secret
              (compiledTargetChallenge selectors sourceBatch challenge)
              (Full.squareMessages secret gadget)
              (fun row ↦
                BatchResidualSmudging.upperShiftVector
                    (contextShift secret selectors sourceBatch) row + error row))
            (Full.upperRow level)
      rw [entry_compileTargets_upper]
      simpa [compileRows, contextShift, assembleSquareRow, add_comm] using h

/-- Hidden source material retained by the reduction, but never published in the compiled
square batch. -/
structure Context (R Secret : Type) (levels sourceCount : ℕ) where
  secretValue : Secret
  sourceBatch : Full.SourceBatch R levels sourceCount

/-- Sample the hidden secret and its ordinary-RLWE source batch. -/
def contextSampler {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R) :
    ProbComp (Context R Secret levels sourceCount) := do
  let sourceChallenge ←
    $ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R
  let secretValue ← secretSampler
  let sourceError ← ProbComp.sampleIID (levels * sourceCount) errorSampler
  return ⟨secretValue,
    TLWE.batchAssemble (embed secretValue) sourceChallenge 0 sourceError⟩

/-- Compile a fresh zero-message target batch from one fixed hidden source context. -/
def compileFromContext {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (selectors : Full.Selectors R levels sourceCount)
    (context : Context R Secret levels sourceCount) :
    ProbComp (Full.TargetBatch R levels) := do
  let targetChallenge ←
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R
  let targetError ← ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler
  return Full.compileTargets selectors context.sourceBatch
    (TLWE.batchAssemble (embed context.secretValue) targetChallenge 0 targetError)

/-- On a successful hidden source context, its conditional compiler law is exactly the
fixed-secret shifted-square law. -/
theorem compileFromContext_evalDist_eq_shifted
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : Context R Secret levels sourceCount)
    (hSuccess : ∀ level,
      Full.SelectorSucceedsAt gadget selectors context.sourceBatch level) :
    evalDist (compileFromContext embed errorSampler selectors context) =
      evalDist
        (BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler levels
          (embed context.secretValue) errorSampler gadget
          (contextShift (embed context.secretValue) selectors context.sourceBatch)) := by
  let Challenges : ProbComp
      (Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R
  let Errors : ProbComp (Fin (TGSW.rowCount 1 levels) → R) :=
    ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler
  let shift := contextShift (embed context.secretValue) selectors context.sourceBatch
  let finish := fun
      (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
      (targetError : Fin (TGSW.rowCount 1 levels) → R) ↦
    TLWE.batchAssemble (embed context.secretValue) challenge
      (Full.squareMessages (embed context.secretValue) gadget)
      (fun row ↦ BatchResidualSmudging.upperShiftVector shift row + targetError row)
  have hLeft :
      compileFromContext embed errorSampler selectors context =
        (Challenges >>= fun challenge ↦
          Errors >>= fun error ↦
            pure (finish
              (compiledTargetChallenge selectors context.sourceBatch challenge) error)) := by
    simp [compileFromContext, Challenges, Errors, finish, shift, monad_norm]
    apply bind_congr
    intro challenge
    apply bind_congr
    intro error
    simpa [Function.comp_apply, TLWE.batchAssemble] using congrArg
      (fun target ↦ (pure target : ProbComp (Full.TargetBatch R levels)))
      (compileTargets_batchAssemble_zero_eq_shifted
        (embed context.secretValue) gadget selectors context.sourceBatch
        challenge error hSuccess)
  have hRight :
      BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler levels
          (embed context.secretValue) errorSampler gadget shift =
        (Challenges >>= fun challenge ↦
          Errors >>= fun error ↦ pure (finish challenge error)) := by
    simp [BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler,
      BatchResidualSmudging.shiftedBatchErrorSampler,
      Challenges, Errors, finish, shift, monad_norm]
  rw [hLeft, hRight]
  apply evalDist_ext
  intro target
  simpa only [Challenges] using
    (probOutput_bind_bijective_uniform_cross
      (α := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
      (β := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
      (compiledTargetChallenge selectors context.sourceBatch)
      (compiledTargetChallenge_bijective selectors context.sourceBatch)
      (fun challenge ↦ Errors >>= fun error ↦ pure (finish challenge error)) target)

/-- Sampling unused ordinary-RLWE source material around the native square batch does not
change its output distribution. -/
theorem nativeSquareBatchSampler_evalDist_eq_contextual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R) :
    evalDist
        (Full.nativeSquareBatchSampler levels secretSampler embed errorSampler gadget) =
      evalDist
        (contextSampler levels sourceCount secretSampler embed errorSampler >>=
          fun context ↦
            BatchResidualSmudging.fixedSecretSquareBatchSampler levels
              (embed context.secretValue) errorSampler gadget) := by
  let SourceChallenges : ProbComp
      (Matrix (Fin 1) (Fin (levels * sourceCount)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R
  let SourceErrors : ProbComp (Fin (levels * sourceCount) → R) :=
    ProbComp.sampleIID (levels * sourceCount) errorSampler
  let Native := fun secretValue ↦
    BatchResidualSmudging.fixedSecretSquareBatchSampler levels
      (embed secretValue) errorSampler gadget
  have hNative :
      Full.nativeSquareBatchSampler levels secretSampler embed errorSampler gadget =
        (secretSampler >>= Native) := by
    rfl
  have hContext :
      contextSampler levels sourceCount secretSampler embed errorSampler >>=
          (fun context ↦ Native context.secretValue) =
        (SourceChallenges >>= fun _sourceChallenge ↦
          secretSampler >>= fun secretValue ↦
            SourceErrors >>= fun _sourceError ↦ Native secretValue) := by
    simp [contextSampler, SourceChallenges, SourceErrors, Native, monad_norm]
  rw [hNative, hContext]
  have hDrop (secretValue : Secret) :
      evalDist
          (SourceChallenges >>= fun _sourceChallenge ↦
            SourceErrors >>= fun _sourceError ↦ Native secretValue) =
        evalDist (Native secretValue) := by
    calc
      _ = evalDist (SourceChallenges >>= fun _sourceChallenge ↦ Native secretValue) := by
        apply evalDist_bind_congr' SourceChallenges
        intro _sourceChallenge
        exact
          FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
            SourceErrors (by simp [SourceErrors]) (Native secretValue)
      _ = evalDist (Native secretValue) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          SourceChallenges (by simp [SourceChallenges]) (Native secretValue)
  calc
    evalDist (secretSampler >>= Native) =
        evalDist (secretSampler >>= fun secretValue ↦
          SourceChallenges >>= fun _sourceChallenge ↦
            SourceErrors >>= fun _sourceError ↦ Native secretValue) := by
      symm
      exact evalDist_bind_congr' secretSampler hDrop
    _ = evalDist (SourceChallenges >>= fun _sourceChallenge ↦
          secretSampler >>= fun secretValue ↦
            SourceErrors >>= fun _sourceError ↦ Native secretValue) := by
      exact (evalDist_bind_bind_swap SourceChallenges secretSampler
        (fun _sourceChallenge secretValue ↦
          SourceErrors >>= fun _sourceError ↦ Native secretValue)).symm

/-- The real unequal ordinary-RLWE experiment is exactly the hidden-context compiler sampler,
up to swapping independent draws. -/
theorem compiledBatchSampler_evalDist_eq_contextual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount) :
    evalDist
        (Full.compiledBatchSampler levels sourceCount secretSampler embed errorSampler
          selectors) =
      evalDist
        (contextSampler levels sourceCount secretSampler embed errorSampler >>=
          compileFromContext embed errorSampler selectors) := by
  let SourceChallenges : ProbComp
      (Matrix (Fin 1) (Fin (levels * sourceCount)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R
  let TargetChallenges : ProbComp
      (Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R
  let SourceErrors : ProbComp (Fin (levels * sourceCount) → R) :=
    ProbComp.sampleIID (levels * sourceCount) errorSampler
  let TargetErrors : ProbComp (Fin (TGSW.rowCount 1 levels) → R) :=
    ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler
  let finish := fun
      (sourceChallenge : Matrix (Fin 1) (Fin (levels * sourceCount)) R)
      (targetChallenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
      (secretValue : Secret)
      (sourceError : Fin (levels * sourceCount) → R)
      (targetError : Fin (TGSW.rowCount 1 levels) → R) ↦
    (pure (Full.compileTargets selectors
      (TLWE.batchAssemble (embed secretValue) sourceChallenge 0 sourceError)
      (TLWE.batchAssemble (embed secretValue) targetChallenge 0 targetError)) :
        ProbComp (Full.TargetBatch R levels))
  have uniformChallenge :
      ($ᵗ (LWE.TwoBlock.Challenge R 1 (levels * sourceCount)
          (TGSW.rowCount 1 levels)) :
        ProbComp (LWE.TwoBlock.Challenge R 1 (levels * sourceCount)
          (TGSW.rowCount 1 levels))) =
        Prod.mk <$> SourceChallenges <*> TargetChallenges := by
    rfl
  have hCompiled :
      Full.compiledBatchSampler levels sourceCount secretSampler embed errorSampler
          selectors =
        (SourceChallenges >>= fun sourceChallenge ↦
          TargetChallenges >>= fun targetChallenge ↦
            secretSampler >>= fun secretValue ↦
              SourceErrors >>= fun sourceError ↦
          TargetErrors >>= fun targetError ↦
                  finish sourceChallenge targetChallenge secretValue sourceError targetError) := by
    rw [show
      Full.compiledBatchSampler levels sourceCount secretSampler embed errorSampler
          selectors =
        (LearningWithErrors.distr
          (LWE.TwoBlock.problem 1 (levels * sourceCount) (TGSW.rowCount 1 levels)
            secretSampler embed errorSampler) >>=
          fun transcript ↦ pure (Full.compileTranscript selectors transcript)) by rfl]
    unfold LearningWithErrors.distr
    unfold LWE.TwoBlock.problem LWE.TwoBlock.heterogeneousProblem
    rw [uniformChallenge]
    simp [Full.compileTranscript, Full.transcriptPairEquiv,
      LWE.TwoBlock.toTranscriptPair, SourceChallenges, TargetChallenges,
      SourceErrors, TargetErrors, finish, TLWE.batchAssemble, monad_norm]
  have hContext :
      contextSampler levels sourceCount secretSampler embed errorSampler >>=
          compileFromContext embed errorSampler selectors =
        (SourceChallenges >>= fun sourceChallenge ↦
          secretSampler >>= fun secretValue ↦
            SourceErrors >>= fun sourceError ↦
              TargetChallenges >>= fun targetChallenge ↦
                TargetErrors >>= fun targetError ↦
                  finish sourceChallenge targetChallenge secretValue sourceError targetError) := by
    simp [contextSampler, compileFromContext, SourceChallenges, TargetChallenges,
      SourceErrors, TargetErrors, finish, TLWE.batchAssemble, monad_norm]
  rw [hCompiled, hContext]
  apply evalDist_bind_congr' SourceChallenges
  intro sourceChallenge
  calc
    evalDist (TargetChallenges >>= fun targetChallenge ↦
        secretSampler >>= fun secretValue ↦
          SourceErrors >>= fun sourceError ↦
            TargetErrors >>= fun targetError ↦
              finish sourceChallenge targetChallenge secretValue sourceError targetError) =
      evalDist (secretSampler >>= fun secretValue ↦
        TargetChallenges >>= fun targetChallenge ↦
          SourceErrors >>= fun sourceError ↦
            TargetErrors >>= fun targetError ↦
              finish sourceChallenge targetChallenge secretValue sourceError targetError) := by
        exact evalDist_bind_bind_swap TargetChallenges secretSampler _
    _ = evalDist (secretSampler >>= fun secretValue ↦
        SourceErrors >>= fun sourceError ↦
          TargetChallenges >>= fun targetChallenge ↦
            TargetErrors >>= fun targetError ↦
              finish sourceChallenge targetChallenge secretValue sourceError targetError) := by
      apply evalDist_bind_congr' secretSampler
      intro secretValue
      exact evalDist_bind_bind_swap TargetChallenges SourceErrors _

/-- If every sampled hidden source context satisfies the selector equations, the full compiler
has the exact contextual shifted-square normal form. -/
theorem compiledBatchSampler_evalDist_eq_contextualShifted
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (hSuccess : ∀ context,
      context ∈ support
        (contextSampler levels sourceCount secretSampler embed errorSampler) →
      ∀ level, Full.SelectorSucceedsAt gadget selectors context.sourceBatch level) :
    evalDist
        (Full.compiledBatchSampler levels sourceCount secretSampler embed errorSampler
          selectors) =
      evalDist
        (contextSampler levels sourceCount secretSampler embed errorSampler >>=
          fun context ↦
            BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler levels
              (embed context.secretValue) errorSampler gadget
              (contextShift (embed context.secretValue) selectors context.sourceBatch)) := by
  rw [compiledBatchSampler_evalDist_eq_contextual]
  apply evalDist_bind_congr
  intro context hcontext
  exact compileFromContext_evalDist_eq_shifted embed errorSampler gadget selectors context
    (hSuccess context hcontext)

/-- The genuine stripped `RGSW_S(-S)` gap follows directly from successful hidden selectors and
the explicit residual translation bound; no sampler-normal-form hypotheses remain. -/
theorem actualDistributionGap_le_of_selectorSuccess
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount) (bound : ℝ)
    (hSuccess : ∀ context,
      context ∈ support
        (contextSampler levels sourceCount secretSampler embed errorSampler) →
      ∀ level, Full.SelectorSucceedsAt gadget selectors context.sourceBatch level)
    (hShift : ∀ context,
      context ∈ support
        (contextSampler levels sourceCount secretSampler embed errorSampler) →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (contextShift (embed context.secretValue) selectors context.sourceBatch level)) ≤
        bound) :
    Full.actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget
      selectors ≤ bound := by
  apply BatchResidualSmudging.actualDistributionGap_le_of_contextual_normalForms
    levels sourceCount secretSampler embed errorSampler gadget selectors
      (contextSampler levels sourceCount secretSampler embed errorSampler)
      (fun context ↦ embed context.secretValue)
      (fun context ↦
        contextShift (embed context.secretValue) selectors context.sourceBatch)
      bound
  · exact nativeSquareBatchSampler_evalDist_eq_contextual
      levels sourceCount secretSampler embed errorSampler gadget
  · exact compiledBatchSampler_evalDist_eq_contextualShifted
      levels sourceCount secretSampler embed errorSampler gadget selectors hSuccess
  · exact hShift

/-- The standalone circular-security advantage is bounded by the explicit selector residual plus
the ordinary batch-RLWE advantage. -/
theorem rgswMinusSecretAdvantage_le_selectorResidual_add_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) (bound : ℝ)
    (hSuccess : ∀ context,
      context ∈ support
        (contextSampler levels sourceCount secretSampler embed errorSampler) →
      ∀ level, Full.SelectorSucceedsAt gadget selectors context.sourceBatch level)
    (hShift : ∀ context,
      context ∈ support
        (contextSampler levels sourceCount secretSampler embed errorSampler) →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (contextShift (embed context.secretValue) selectors context.sourceBatch level)) ≤
        bound) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed errorSampler gadget
        distinguisher ≤
      bound +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Full.reduction selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  apply BatchResidualSmudging.rgswMinusSecretAdvantage_le_contextualSmudging_add_batchLWE
    levels sourceCount secretSampler embed errorSampler gadget selectors distinguisher
      (contextSampler levels sourceCount secretSampler embed errorSampler)
      (fun context ↦ embed context.secretValue)
      (fun context ↦
        contextShift (embed context.secretValue) selectors context.sourceBatch)
      bound
  · exact nativeSquareBatchSampler_evalDist_eq_contextual
      levels sourceCount secretSampler embed errorSampler gadget
  · exact compiledBatchSampler_evalDist_eq_contextualShifted
      levels sourceCount secretSampler embed errorSampler gadget selectors hSuccess
  · exact hShift

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.CompilerNormalForm
