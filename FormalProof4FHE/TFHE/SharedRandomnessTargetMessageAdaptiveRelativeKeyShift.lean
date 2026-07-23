/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveRelativeView

set_option autoImplicit false

/-!
# Message-Normalized Relative Key Shift for the Direct Adaptive TFHE View

This file separates the exact BRK plaintext update from the genuinely nonlinear relative-key
shift.  For a fixed nested key `S` and normalized relative mask, write `S'` for the masked key.
Centered-binomial symmetry gives a public exact first hop

`(BRK(KeyExtract(S), S_source), Ext(S_suffix, S_source))`

to

`(BRK(KeyExtract(S'), S_source), Ext(S_suffix, S_source))`.

The remaining certificate consequently has the unambiguous endpoint

`(BRK(KeyExtract(S'), S_source), Ext(S_suffix, S_source))`

to

`(BRK(KeyExtract(S'), S'_source), Ext(S'_suffix, S'_source))`.

It is this second hop—not target-message transport, the adaptive input tape, or the global
anchor—that is the native ring-specific research obligation.  The compiler below preserves its
error exactly and then reuses the checked relative/anchor complete-view compiler.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

open FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

/-- Change only the BRK plaintext vector to the one selected by a normalized relative mask.
The source ring encryption key and the complete ring-extension table are left unchanged. -/
def transformEvaluationMaterialRelativeMessages
    {q degree suffixRank levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (relativeMask : RelativeNestedMask suffixRank degree)
    (material : Auxiliary q (degree + 1) 1 suffixRank levels) :
    Auxiliary q (degree + 1) 1 suffixRank levels :=
  (transformSourceBootstrappingKeyMessages gadget
      (liftRelativeNestedMask relativeMask) material.1,
    material.2)

/-- The material distribution after the BRK messages have been changed to `KeyExtract(S')`,
but before either nested ring-key block has been shifted. -/
def sampleRelativeMessageShiftedMaterial
    (q degree suffixRank levels eta : ℕ) [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1))
    (relativeMask : RelativeNestedMask suffixRank degree) :
    ProbComp (Auxiliary q (degree + 1) 1 suffixRank levels) := do
  let shiftedSecret := act secret (liftRelativeNestedMask relativeMask)
  let bootstrappingKey ← Native.generateBootstrappingKey q (degree + 1) 1 levels
    (targetScalarDimension 1 suffixRank (degree + 1))
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) gadget
    (targetMessages shiftedSecret.1 shiftedSecret.2) secret.1
  let extensionKey ← generateRingExtensionKey q (degree + 1) 1 suffixRank levels
    extensionErrorSampler gadget secret.1 secret.2
  return (bootstrappingKey, extensionKey)

/-- Centered-binomial BRK plaintext transport identifies the transformed real material exactly
with the message-normalized intermediate distribution. -/
theorem transformEvaluationMaterialRelativeMessages_sample_evalDist
    {q degree suffixRank levels eta : ℕ} [NeZero q]
    (extensionErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1))
    (relativeMask : RelativeNestedMask suffixRank degree) :
    evalDist
        (transformEvaluationMaterialRelativeMessages gadget relativeMask <$>
          sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            extensionErrorSampler gadget secret) =
      evalDist
        (sampleRelativeMessageShiftedMaterial q degree suffixRank levels eta
          extensionErrorSampler gadget secret relativeMask) := by
  let sourceBootstrappingKey :=
    generateSourceBootstrappingKey q (degree + 1) 1 suffixRank levels
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta) gadget secret.1 secret.2
  let transformedBootstrappingKey :=
    transformSourceBootstrappingKeyMessages gadget
        (liftRelativeNestedMask relativeMask) <$>
      sourceBootstrappingKey
  let shiftedSecret := act secret (liftRelativeNestedMask relativeMask)
  let targetBootstrappingKey :=
    Native.generateBootstrappingKey q (degree + 1) 1 levels
      (targetScalarDimension 1 suffixRank (degree + 1))
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta) gadget
      (targetMessages shiftedSecret.1 shiftedSecret.2) secret.1
  let extensionKey := generateRingExtensionKey q (degree + 1) 1 suffixRank levels
    extensionErrorSampler gadget secret.1 secret.2
  have hbootstrappingKey :
      evalDist transformedBootstrappingKey = evalDist targetBootstrappingKey := by
    simpa only [transformedBootstrappingKey, sourceBootstrappingKey,
      targetBootstrappingKey, shiftedSecret] using
      (transformSourceBootstrappingKeyMessages_generate_evalDist
        (eta := eta) gadget secret (liftRelativeNestedMask relativeMask))
  have hextension : evalDist (id <$> extensionKey) = evalDist extensionKey := by
    simp
  change
    evalDist
        ((fun pair ↦
            (transformSourceBootstrappingKeyMessages gadget
                (liftRelativeNestedMask relativeMask) pair.1,
              pair.2)) <$>
          (sourceBootstrappingKey >>= fun left ↦
            extensionKey >>= fun right ↦ pure (left, right))) =
      evalDist
        (targetBootstrappingKey >>= fun left ↦
          extensionKey >>= fun right ↦ pure (left, right))
  simpa only [id_eq] using
    (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.independentPair_map_evalDist_congr
      sourceBootstrappingKey extensionKey targetBootstrappingKey extensionKey
      (transformSourceBootstrappingKeyMessages gadget
        (liftRelativeNestedMask relativeMask)) id
      hbootstrappingKey hextension)

/-- The precise nonlinear core left after the target BRK plaintext vector is already correct.
It shifts the BRK ring encryption key and simultaneously updates both the messages and encryption
key of the ring-extension table. -/
structure RelativeKeyShiftMaterialEvaluator
    (q degree suffixRank levels eta : ℕ) [NeZero q]
    (narrowExtensionErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1)) where
  evaluateKeyShift :
    RelativeNestedMask suffixRank degree →
      Auxiliary q (degree + 1) 1 suffixRank levels →
        ProbComp (Auxiliary q (degree + 1) 1 suffixRank levels)
  error : ℝ
  error_nonneg : 0 ≤ error
  keyShiftDistance_le : ∀ secret relativeMask,
    tvDist
        (sampleRelativeMessageShiftedMaterial q degree suffixRank levels eta
            narrowExtensionErrorSampler gadget secret relativeMask >>=
          evaluateKeyShift relativeMask)
        (sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget
          (act secret (liftRelativeNestedMask relativeMask))) ≤ error

namespace RelativeKeyShiftMaterialEvaluator

/-- Execute exact target-message normalization and then the supplied nonlinear key shift. -/
def evaluateFromReal
    {q degree suffixRank levels eta : ℕ} [NeZero q]
    {narrowExtensionErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeKeyShiftMaterialEvaluator q degree suffixRank levels eta
      narrowExtensionErrorSampler wideBootstrapErrorSampler
      wideExtensionErrorSampler gadget)
    (relativeMask : RelativeNestedMask suffixRank degree)
    (material : Auxiliary q (degree + 1) 1 suffixRank levels) :
    ProbComp (Auxiliary q (degree + 1) 1 suffixRank levels) :=
  evaluator.evaluateKeyShift relativeMask
    (transformEvaluationMaterialRelativeMessages gadget relativeMask material)

/-- Exact BRK message normalization contributes zero to the nonlinear core's TV budget. -/
theorem evaluateFromReal_distance_le
    {q degree suffixRank levels eta : ℕ} [NeZero q]
    {narrowExtensionErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeKeyShiftMaterialEvaluator q degree suffixRank levels eta
      narrowExtensionErrorSampler wideBootstrapErrorSampler
      wideExtensionErrorSampler gadget)
    (secret : Secret 1 suffixRank (degree + 1))
    (relativeMask : RelativeNestedMask suffixRank degree) :
    tvDist
        (sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            narrowExtensionErrorSampler gadget secret >>=
          evaluator.evaluateFromReal relativeMask)
        (sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget
          (act secret (liftRelativeNestedMask relativeMask))) ≤ evaluator.error := by
  let sourceMaterial :=
    sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      narrowExtensionErrorSampler gadget secret
  let transformedMaterial :=
    transformEvaluationMaterialRelativeMessages gadget relativeMask <$> sourceMaterial
  let shiftedMaterial :=
    sampleRelativeMessageShiftedMaterial q degree suffixRank levels eta
      narrowExtensionErrorSampler gadget secret relativeMask
  have hmaterial : evalDist transformedMaterial = evalDist shiftedMaterial := by
    simpa only [transformedMaterial, sourceMaterial, shiftedMaterial] using
      transformEvaluationMaterialRelativeMessages_sample_evalDist
        (eta := eta) narrowExtensionErrorSampler gadget secret relativeMask
  have hsource :
      evalDist (sourceMaterial >>= evaluator.evaluateFromReal relativeMask) =
        evalDist (shiftedMaterial >>= evaluator.evaluateKeyShift relativeMask) := by
    unfold evaluateFromReal
    calc
      _ = evalDist
          (transformedMaterial >>= evaluator.evaluateKeyShift relativeMask) := by
        simp only [transformedMaterial, sourceMaterial, map_eq_bind_pure_comp,
          Function.comp_apply, bind_assoc, pure_bind]
      _ = _ := by
        rw [evalDist_bind, hmaterial, ← evalDist_bind]
  unfold tvDist
  rw [show evalDist
      (sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          narrowExtensionErrorSampler gadget secret >>=
        evaluator.evaluateFromReal relativeMask) =
      evalDist (shiftedMaterial >>= evaluator.evaluateKeyShift relativeMask) by
        simpa only [sourceMaterial] using hsource]
  exact evaluator.keyShiftDistance_le secret relativeMask

/-- Package the message-normalized core as the normalized-relative material evaluator expected by
the complete tape-and-anchor compiler. -/
def toRelativeEvaluationMaterialEvaluator
    {q degree suffixRank levels eta : ℕ} [NeZero q]
    {narrowExtensionErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeKeyShiftMaterialEvaluator q degree suffixRank levels eta
      narrowExtensionErrorSampler wideBootstrapErrorSampler
      wideExtensionErrorSampler gadget) :
    RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      narrowExtensionErrorSampler wideBootstrapErrorSampler
      wideExtensionErrorSampler gadget where
  evaluateRelative := evaluator.evaluateFromReal
  error := evaluator.error
  error_nonneg := evaluator.error_nonneg
  materialDistance_le := evaluator.evaluateFromReal_distance_le

@[simp]
theorem toRelativeEvaluationMaterialEvaluator_error
    {q degree suffixRank levels eta : ℕ} [NeZero q]
    {narrowExtensionErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeKeyShiftMaterialEvaluator q degree suffixRank levels eta
      narrowExtensionErrorSampler wideBootstrapErrorSampler
      wideExtensionErrorSampler gadget) :
    evaluator.toRelativeEvaluationMaterialEvaluator.error = evaluator.error := rfl

/-- The precise key-shift core, exact tape lift, and checked global anchor together give the full
fresh-key view randomizer. -/
def toRelativeThenGlobalViewRandomization
    {q degree suffixRank levels queryCount eta : ℕ} [NeZero q]
    {narrowExtensionErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeKeyShiftMaterialEvaluator q degree suffixRank levels eta
      narrowExtensionErrorSampler wideBootstrapErrorSampler
      wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler) :=
  evaluator.toRelativeEvaluationMaterialEvaluator
    |>.toRelativeThenGlobalViewRandomization
      (queryCount := queryCount) inputErrorSampler hextensionSymmetric

@[simp]
theorem toRelativeThenGlobalViewRandomization_error
    {q degree suffixRank levels queryCount eta : ℕ} [NeZero q]
    {narrowExtensionErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeKeyShiftMaterialEvaluator q degree suffixRank levels eta
      narrowExtensionErrorSampler wideBootstrapErrorSampler
      wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler) :
    (evaluator.toRelativeThenGlobalViewRandomization
      (queryCount := queryCount) inputErrorSampler hextensionSymmetric).error =
      evaluator.error + globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler := rfl

end RelativeKeyShiftMaterialEvaluator

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
