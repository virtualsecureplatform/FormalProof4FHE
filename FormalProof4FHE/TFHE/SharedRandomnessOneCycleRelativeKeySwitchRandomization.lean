/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleCenteredBinomialRelativeView

/-!
# Arbitrary-Mask KSK Transport for One-Cycle TFHE

The suffix-only key-switch key is compatible with every coefficientwise XOR mask of the complete
shared master key, not merely with global complement.  Selected KSK source rows are negated and
receive their public gadget value; the existing target-key transport independently changes the
shared prefix key.  Any negation-symmetric scalar error law makes this joint source/target action
an exact distributional identity.  The file instantiates the law with executable centered
binomial noise.

The second half isolates the remaining relative-key randomization problem.  For a fixed master
key, the correlated centered-binomial BRK and suffix KSK are sampled independently.  Therefore a
BRK-only relative evaluator with total-variation error `epsilon`, paired with the exact KSK action,
gives a complete relative evaluation-key evaluator with the same error.  The existing exact
global-complement constructor then produces the full fresh-master-key `ViewRandomization`, still
with error exactly `epsilon`.

Consequently the shared KSK contributes neither a circular assumption nor a statistical loss for
any relative mask.  The sole construction-specific obligation left by this module is the
self-encrypted BRK marginal under the nonlinear relative-key action.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

noncomputable section

/-- Negate exactly the coordinates selected by a Boolean mask. -/
def maskNegateVector {R : Type} [Neg R] {length : ℕ}
    (mask : Fin length → Bool) (values : Fin length → R) : Fin length → R :=
  fun coordinate ↦ if mask coordinate then -values coordinate else values coordinate

@[simp]
theorem maskNegateVector_involutive {R : Type} [AddGroup R] {length : ℕ}
    (mask : Fin length → Bool) (values : Fin length → R) :
    maskNegateVector mask (maskNegateVector mask values) = values := by
  funext coordinate
  cases hmask : mask coordinate <;> simp [maskNegateVector, hmask]

theorem maskNegateVector_bijective {R : Type} [AddGroup R] {length : ℕ}
    (mask : Fin length → Bool) :
    Function.Bijective (maskNegateVector (R := R) mask) :=
  Function.Involutive.bijective (maskNegateVector_involutive mask)

/-- An IID vector from a negation-symmetric sampler is invariant under any fixed pattern of
coordinate negations. -/
theorem maskNegateVector_sampleIID_evalDist
    {R : Type} [AddCommGroup R] [Finite R] {length : ℕ}
    (sampler : ProbComp R)
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric sampler)
    (mask : Fin length → Bool) :
    evalDist (maskNegateVector mask <$> ProbComp.sampleIID length sampler) =
      evalDist (ProbComp.sampleIID length sampler) := by
  apply evalDist_ext
  intro output
  calc
    Pr[= output | maskNegateVector mask <$> ProbComp.sampleIID length sampler] =
        Pr[= maskNegateVector mask output | ProbComp.sampleIID length sampler] := by
      simpa using
        (probOutput_map_injective (ProbComp.sampleIID length sampler)
          (f := maskNegateVector mask) (maskNegateVector_bijective mask).1
          (maskNegateVector mask output))
    _ = ∏ coordinate,
        Pr[= maskNegateVector mask output coordinate | sampler] :=
      FormalProof4FHE.SharedRandomness.probOutput_sampleIID length sampler
        (maskNegateVector mask output)
    _ = ∏ coordinate, Pr[= output coordinate | sampler] := by
      apply Finset.prod_congr rfl
      intro coordinate _
      cases hmask : mask coordinate
      · simp [maskNegateVector, hmask]
      · simpa [maskNegateVector, hmask] using hsymmetric (output coordinate)
    _ = Pr[= output | ProbComp.sampleIID length sampler] :=
      (FormalProof4FHE.SharedRandomness.probOutput_sampleIID length sampler output).symm

/-- Negate exactly the selected columns of a TLWE challenge matrix. -/
def maskNegateColumns {R : Type} [Neg R] {dimension samples : ℕ}
    (mask : Fin samples → Bool)
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    Matrix (Fin dimension) (Fin samples) R :=
  fun coordinate sample ↦
    if mask sample then -challenge coordinate sample else challenge coordinate sample

@[simp]
theorem maskNegateColumns_involutive {R : Type} [AddGroup R]
    {dimension samples : ℕ} (mask : Fin samples → Bool)
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    maskNegateColumns mask (maskNegateColumns mask challenge) = challenge := by
  funext coordinate sample
  cases hmask : mask sample <;> simp [maskNegateColumns, hmask]

theorem maskNegateColumns_bijective {R : Type} [AddGroup R]
    {dimension samples : ℕ} (mask : Fin samples → Bool) :
    Function.Bijective
      (maskNegateColumns (R := R) (dimension := dimension) mask) :=
  Function.Involutive.bijective (maskNegateColumns_involutive mask)

theorem maskNegateColumns_uniform_evalDist {R : Type}
    [AddCommGroup R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ} (mask : Fin samples → Bool) :
    evalDist (maskNegateColumns mask <$>
        ($ᵗ Matrix (Fin dimension) (Fin samples) R)) =
      evalDist ($ᵗ Matrix (Fin dimension) (Fin samples) R) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin dimension) (Fin samples) R)
    (β := Matrix (Fin dimension) (Fin samples) R)
    (maskNegateColumns mask) (maskNegateColumns_bijective mask)

/-- Lift a source-key mask to the flattened KSK row layout. -/
def keySwitchRowMask {sourceDimension levels : ℕ}
    (sourceMask : BinarySecret sourceDimension) :
    Fin (sourceDimension * levels) → Bool :=
  fun row ↦ sourceMask (finProdFinEquiv.symm row).1

@[simp]
theorem keySwitchRowMask_apply {sourceDimension levels : ℕ}
    (sourceMask : BinarySecret sourceDimension)
    (coordinate : Fin sourceDimension) (level : Fin levels) :
    keySwitchRowMask sourceMask (finProdFinEquiv (coordinate, level)) =
      sourceMask coordinate := by
  simp [keySwitchRowMask]

/-- Publicly toggle arbitrary KSK source-key bits.  A selected row is negated and receives its
gadget value, changing `s_i g_l` into `(1-s_i) g_l`. -/
def transformKeySwitchSource
    {R : Type} [Ring R] {targetDimension sourceDimension levels : ℕ}
    (gadget : Fin levels → R) (sourceMask : BinarySecret sourceDimension)
    (keySwitchKey :
      TLWE.BatchCiphertext R targetDimension (sourceDimension * levels)) :
    TLWE.BatchCiphertext R targetDimension (sourceDimension * levels) :=
  (maskNegateColumns (keySwitchRowMask (levels := levels) sourceMask) keySwitchKey.1,
    fun row ↦
      let indexed := finProdFinEquiv.symm row
      if sourceMask indexed.1 then gadget indexed.2 - keySwitchKey.2 row
      else keySwitchKey.2 row)

@[simp]
theorem transformKeySwitchSource_body_apply
    {R : Type} [Ring R] {targetDimension sourceDimension levels : ℕ}
    (gadget : Fin levels → R) (sourceMask : BinarySecret sourceDimension)
    (keySwitchKey :
      TLWE.BatchCiphertext R targetDimension (sourceDimension * levels))
    (coordinate : Fin sourceDimension) (level : Fin levels) :
    (transformKeySwitchSource gadget sourceMask keySwitchKey).2
        (finProdFinEquiv (coordinate, level)) =
      if sourceMask coordinate then
        gadget level - keySwitchKey.2 (finProdFinEquiv (coordinate, level))
      else keySwitchKey.2 (finProdFinEquiv (coordinate, level)) := by
  change (if sourceMask
        (finProdFinEquiv.symm (finProdFinEquiv (coordinate, level))).1 then
      gadget (finProdFinEquiv.symm (finProdFinEquiv (coordinate, level))).2 -
        keySwitchKey.2 (finProdFinEquiv (coordinate, level))
    else keySwitchKey.2 (finProdFinEquiv (coordinate, level))) = _
  rw [Equiv.symm_apply_apply]

/-- Exact ciphertext normal form for arbitrary KSK source-key XOR transport. -/
theorem transformKeySwitchSource_batchAssemble
    {R : Type} [CommRing R]
    {targetDimension sourceDimension levels : ℕ}
    (targetSecret : Fin targetDimension → R)
    (gadget : Fin levels → R)
    (sourceSecret sourceMask : BinarySecret sourceDimension)
    (challenge : Matrix (Fin targetDimension) (Fin (sourceDimension * levels)) R)
    (error : Fin (sourceDimension * levels) → R) :
    transformKeySwitchSource gadget sourceMask
        (TLWE.batchAssemble targetSecret challenge
          (Native.keySwitchMessages sourceDimension levels gadget sourceSecret)
          error) =
      TLWE.batchAssemble targetSecret
        (maskNegateColumns (keySwitchRowMask (levels := levels) sourceMask) challenge)
        (Native.keySwitchMessages sourceDimension levels gadget
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            sourceSecret sourceMask))
        (maskNegateVector (keySwitchRowMask (levels := levels) sourceMask) error) := by
  apply Prod.ext
  · rfl
  · funext row
    obtain ⟨⟨coordinate, level⟩, rfl⟩ := finProdFinEquiv.surjective row
    cases hmask : sourceMask coordinate <;>
      cases hsecret : sourceSecret coordinate
    all_goals
      simp [TLWE.batchAssemble, Matrix.vecMul, dotProduct,
        maskNegateColumns, maskNegateVector,
        Native.keySwitchMessages_apply,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
        LWE.MultiKeyAffine.maskedBit, embedBit, hmask, hsecret]
    all_goals ring

/-- Arbitrary public source-key XOR transport preserves the KSK distribution under any
negation-symmetric IID scalar error law. -/
theorem transformKeySwitchSource_batchEncrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {targetDimension sourceDimension levels : ℕ}
    (errorSampler : ProbComp R)
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (targetSecret : Fin targetDimension → R)
    (gadget : Fin levels → R)
    (sourceSecret sourceMask : BinarySecret sourceDimension) :
    evalDist (transformKeySwitchSource gadget sourceMask <$>
        TLWE.batchEncrypt targetDimension (sourceDimension * levels) errorSampler
          targetSecret
          (Native.keySwitchMessages sourceDimension levels gadget sourceSecret)) =
      evalDist (TLWE.batchEncrypt targetDimension (sourceDimension * levels)
        errorSampler targetSecret
        (Native.keySwitchMessages sourceDimension levels gadget
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            sourceSecret sourceMask))) := by
  let samples := sourceDimension * levels
  let rowMask : Fin samples → Bool :=
    keySwitchRowMask (levels := levels) sourceMask
  let challenges : ProbComp (Matrix (Fin targetDimension) (Fin samples) R) :=
    $ᵗ Matrix (Fin targetDimension) (Fin samples) R
  let errors : ProbComp (Fin samples → R) :=
    ProbComp.sampleIID samples errorSampler
  let finish := fun (challenge : Matrix (Fin targetDimension) (Fin samples) R)
      (error : Fin samples → R) =>
    (pure (TLWE.batchAssemble targetSecret challenge
      (Native.keySwitchMessages sourceDimension levels gadget
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          sourceSecret sourceMask)) error) :
      ProbComp (TLWE.BatchCiphertext R targetDimension samples))
  rw [show TLWE.batchEncrypt targetDimension (sourceDimension * levels)
      errorSampler targetSecret
      (Native.keySwitchMessages sourceDimension levels gadget sourceSecret) =
      (challenges >>= fun challenge =>
        errors >>= fun error =>
          pure (TLWE.batchAssemble targetSecret challenge
            (Native.keySwitchMessages sourceDimension levels gadget sourceSecret)
            error)) by
    simp [TLWE.batchEncrypt, samples, challenges, errors, monad_norm]]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (challenges >>= fun challenge =>
        errors >>= fun error =>
          finish (maskNegateColumns rowMask challenge)
            (maskNegateVector rowMask error)) := by
      refine evalDist_bind_congr' challenges fun challenge => ?_
      refine evalDist_bind_congr' errors fun error => ?_
      simpa only [samples, rowMask, finish] using congrArg evalDist
        (congrArg pure
          (transformKeySwitchSource_batchAssemble targetSecret gadget
            sourceSecret sourceMask challenge error))
    _ = evalDist ((maskNegateColumns rowMask <$> challenges) >>= fun challenge =>
        (maskNegateVector rowMask <$> errors) >>= fun error =>
          finish challenge error) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (challenges >>= fun challenge =>
        (maskNegateVector rowMask <$> errors) >>= fun error =>
          finish challenge error) := by
      rw [evalDist_bind, maskNegateColumns_uniform_evalDist rowMask,
        ← evalDist_bind]
    _ = evalDist (challenges >>= fun challenge =>
        errors >>= fun error => finish challenge error) := by
      refine evalDist_bind_congr' challenges fun _challenge => ?_
      rw [evalDist_bind,
        maskNegateVector_sampleIID_evalDist errorSampler hsymmetric rowMask,
        ← evalDist_bind]
    _ = _ := by
      simp [TLWE.batchEncrypt, samples, challenges, errors, finish, monad_norm]

/-- Native KSK specialization of arbitrary source-key XOR transport. -/
theorem transformKeySwitchSource_generate_evalDist
    {q targetDimension sourceDimension levels : ℕ} [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (gadget : Fin levels → ZMod q)
    (sourceSecret sourceMask : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension) :
    evalDist (transformKeySwitchSource gadget sourceMask <$>
        Native.generateKeySwitchKey q targetDimension sourceDimension levels
          errorSampler gadget sourceSecret targetSecret) =
      evalDist (Native.generateKeySwitchKey q targetDimension sourceDimension levels
        errorSampler gadget
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          sourceSecret sourceMask)
        targetSecret) := by
  exact transformKeySwitchSource_batchEncrypt_evalDist errorSampler hsymmetric
    (embedBinarySecret targetSecret) gadget sourceSecret sourceMask

/-- Simultaneously XOR arbitrary source and target keys of a KSK. -/
def transformKeySwitchSourceTarget
    {q targetDimension sourceDimension levels : ℕ}
    (gadget : Fin levels → ZMod q)
    (sourceMask : BinarySecret sourceDimension)
    (targetMask : BinarySecret targetDimension)
    (keySwitchKey : Native.KeySwitchKey q targetDimension sourceDimension levels) :
    Native.KeySwitchKey q targetDimension sourceDimension levels :=
  FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformKeySwitchKey
    targetMask (transformKeySwitchSource gadget sourceMask keySwitchKey)

/-- The simultaneous arbitrary source/target KSK transport is exact under symmetric scalar
noise. -/
theorem transformKeySwitchSourceTarget_generate_evalDist
    {q targetDimension sourceDimension levels : ℕ} [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (gadget : Fin levels → ZMod q)
    (sourceSecret sourceMask : BinarySecret sourceDimension)
    (targetSecret targetMask : BinarySecret targetDimension) :
    evalDist (transformKeySwitchSourceTarget gadget sourceMask targetMask <$>
        Native.generateKeySwitchKey q targetDimension sourceDimension levels
          errorSampler gadget sourceSecret targetSecret) =
      evalDist (Native.generateKeySwitchKey q targetDimension sourceDimension levels
        errorSampler gadget
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          sourceSecret sourceMask)
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          targetSecret targetMask)) := by
  let targetTransform :=
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformKeySwitchKey
      (q := q) (sourceDimension := sourceDimension) (levels := levels) targetMask
  calc
    _ = evalDist (targetTransform <$>
        (transformKeySwitchSource gadget sourceMask <$>
          Native.generateKeySwitchKey q targetDimension sourceDimension levels
            errorSampler gadget sourceSecret targetSecret)) := by
      rw [Functor.map_map]
      rfl
    _ = evalDist (targetTransform <$>
        Native.generateKeySwitchKey q targetDimension sourceDimension levels
          errorSampler gadget
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            sourceSecret sourceMask)
          targetSecret) :=
      evalDist_map_eq_of_evalDist_eq
        (transformKeySwitchSource_generate_evalDist errorSampler hsymmetric gadget
          sourceSecret sourceMask targetSecret) targetTransform
    _ = _ :=
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformKeySwitchKey_generate_evalDist
        errorSampler gadget
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          sourceSecret sourceMask)
        targetSecret targetMask

/-- Apply a complete master-key mask to both the suffix source and prefix target of the shared
one-cycle KSK. -/
def transformOneCycleKeySwitchKey
    {q prefixDimension suffixDimension levels : ℕ}
    (gadget : Fin levels → ZMod q)
    (masterMask : BinarySecret (prefixDimension + suffixDimension))
    (keySwitchKey :
      Native.SharedRandomnessOneCycle.SharedKeySwitchKey q prefixDimension
        suffixDimension levels) :
    Native.SharedRandomnessOneCycle.SharedKeySwitchKey q prefixDimension
      suffixDimension levels :=
  let ringMask : RingBinarySecret 1 (prefixDimension + suffixDimension) :=
    fun _ ↦ masterMask
  transformKeySwitchSourceTarget gadget
    (suffixSecret ringMask) (prefixSecret ringMask) keySwitchKey

/-- The shared-randomness suffix KSK transports exactly under every complete master-key XOR,
not only under global complement. -/
theorem transformOneCycleKeySwitchKey_generate_evalDist
    {q prefixDimension suffixDimension levels : ℕ} [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (gadget : Fin levels → ZMod q)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (masterMask : BinarySecret (prefixDimension + suffixDimension)) :
    evalDist (transformOneCycleKeySwitchKey gadget masterMask <$>
        Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
          suffixDimension levels errorSampler gadget ringSecret) =
      evalDist (Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
        suffixDimension levels errorSampler gadget
        (maskedRingSecret ringSecret (fun _ ↦ masterMask))) := by
  let ringMask : RingBinarySecret 1 (prefixDimension + suffixDimension) :=
    fun _ ↦ masterMask
  have hprefix := prefixSecret_maskedRingSecret ringSecret ringMask
  have hsuffix := suffixSecret_maskedRingSecret ringSecret ringMask
  change evalDist (transformKeySwitchSourceTarget gadget
      (suffixSecret ringMask) (prefixSecret ringMask) <$>
        Native.generateKeySwitchKey q prefixDimension suffixDimension levels
          errorSampler gadget (suffixSecret ringSecret) (prefixSecret ringSecret)) =
    evalDist (Native.generateKeySwitchKey q prefixDimension suffixDimension levels
      errorSampler gadget
        (suffixSecret (maskedRingSecret ringSecret ringMask))
        (prefixSecret (maskedRingSecret ringSecret ringMask)))
  rw [hprefix, hsuffix]
  exact transformKeySwitchSourceTarget_generate_evalDist errorSampler hsymmetric gadget
    (suffixSecret ringSecret) (suffixSecret ringMask)
    (prefixSecret ringSecret) (prefixSecret ringMask)

/-- Executable centered-binomial specialization of arbitrary full-master KSK transport. -/
theorem transformOneCycleKeySwitchKey_centeredBinomial_evalDist
    {q prefixDimension suffixDimension levels : ℕ} [NeZero q]
    (eta : ℕ) (gadget : Fin levels → ZMod q)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (masterMask : BinarySecret (prefixDimension + suffixDimension)) :
    evalDist (transformOneCycleKeySwitchKey gadget masterMask <$>
        Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
          suffixDimension levels (CenteredBinomial.scalarSampler q eta)
          gadget ringSecret) =
      evalDist (Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
        suffixDimension levels (CenteredBinomial.scalarSampler q eta) gadget
        (maskedRingSecret ringSecret (fun _ ↦ masterMask))) :=
  transformOneCycleKeySwitchKey_generate_evalDist
    (CenteredBinomial.scalarSampler q eta)
    (CenteredBinomial.scalar_probOutput_neg q eta) gadget ringSecret masterMask

/-! ## Reduction of relative view randomization to the BRK component -/

/-- BRK marginal of the concrete correlated centered-binomial evaluation-key view. -/
noncomputable def sampleCenteredBinomialShearBootstrappingKey
    (q prefixDimension suffixTail tgswLevels : ℕ) [NeZero q]
    (ringEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (masterSecret : BinarySecret (prefixDimension + suffixTail + 1)) :
    ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
      tgswLevels prefixDimension) :=
  let ringSecret : RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
    fun _ ↦ masterSecret
  generateBootstrappingKeyWithErrorVector q (prefixDimension + suffixTail)
    tgswLevels prefixDimension
    (centeredBinomialShearErrorVector q (prefixDimension + suffixTail)
      tgswLevels ringEta)
    tgswGadget
    (prefixSecret
      (prefixDimension := prefixDimension)
      (suffixDimension := suffixTail + 1)
      ringSecret)
    ringSecret

/-- KSK marginal of the concrete correlated centered-binomial evaluation-key view. -/
noncomputable def sampleCenteredBinomialOneCycleKeySwitchKey
    (q prefixDimension suffixTail keySwitchLevels : ℕ) [NeZero q]
    (keySwitchEta : ℕ) (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (masterSecret : BinarySecret (prefixDimension + suffixTail + 1)) :
    ProbComp (Native.KeySwitchKey q prefixDimension (suffixTail + 1)
      keySwitchLevels) :=
  let ringSecret : RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
    fun _ ↦ masterSecret
  Native.generateKeySwitchKey q prefixDimension (suffixTail + 1)
    keySwitchLevels (CenteredBinomial.scalarSampler q keySwitchEta)
    keySwitchGadget
    (suffixSecret
      (prefixDimension := prefixDimension)
      (suffixDimension := suffixTail + 1)
      ringSecret)
    (prefixSecret
      (prefixDimension := prefixDimension)
      (suffixDimension := suffixTail + 1)
      ringSecret)

/-- The concrete full view is exactly the independent pairing of its BRK and KSK marginals once
the master key is fixed. -/
theorem sampleCenteredBinomialShearEvaluationKeyView_eq_independentPair
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (masterSecret : BinarySecret (prefixDimension + suffixTail + 1)) :
    sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget
        keySwitchGadget masterSecret =
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair
        (sampleCenteredBinomialShearBootstrappingKey q prefixDimension suffixTail
          tgswLevels ringEta tgswGadget masterSecret)
        (sampleCenteredBinomialOneCycleKeySwitchKey q prefixDimension suffixTail
          keySwitchLevels keySwitchEta keySwitchGadget masterSecret)
        (fun bootstrappingKey keySwitchKey ↦
          (bootstrappingKey, keySwitchKey)) := by
  unfold sampleCenteredBinomialShearEvaluationKeyView
    sampleCenteredBinomialShearBootstrappingKey
    sampleCenteredBinomialOneCycleKeySwitchKey
    FormalProof4FHE.TFHE.SamplerReplacement.independentPair
  simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- Lift a BRK-only relative evaluator to the complete evaluation-key view by applying the exact
source/target XOR transport to the shared suffix KSK. -/
noncomputable def evaluateCenteredBinomialShearRelativeView
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ}
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (evaluateBootstrappingKey : BinarySecret (prefixDimension + suffixTail) →
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension →
      ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension))
    (relativeMask : BinarySecret (prefixDimension + suffixTail))
    (view : CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
      tgswLevels keySwitchLevels) :
    ProbComp (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
      tgswLevels keySwitchLevels) := do
  let bootstrappingKey ← evaluateBootstrappingKey relativeMask view.1
  return (bootstrappingKey,
    transformOneCycleKeySwitchKey
      (prefixDimension := prefixDimension)
      (suffixDimension := suffixTail + 1)
      keySwitchGadget
      (relativeMaskLift relativeMask) view.2)

/-- Exact KSK transport removes the KSK from the relative-view error budget.  Any BRK marginal
relative evaluator with error `epsilon` induces a full-view relative evaluator with the same
error. -/
theorem evaluateCenteredBinomialShearRelativeView_tvDist_le
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (evaluateBootstrappingKey : BinarySecret (prefixDimension + suffixTail) →
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension →
      ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension))
    (epsilon : ℝ)
    (hBootstrappingKey : ∀ masterSecret relativeMask,
      tvDist
          (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget masterSecret >>=
            evaluateBootstrappingKey relativeMask)
          (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget
            (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
              masterSecret (relativeMaskLift relativeMask))) ≤ epsilon)
    (masterSecret : BinarySecret (prefixDimension + suffixTail + 1))
    (relativeMask : BinarySecret (prefixDimension + suffixTail)) :
    tvDist
        (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
          tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget
          keySwitchGadget masterSecret >>=
          evaluateCenteredBinomialShearRelativeView keySwitchGadget
            evaluateBootstrappingKey relativeMask)
        (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
          tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget
          keySwitchGadget
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            masterSecret (relativeMaskLift relativeMask))) ≤ epsilon := by
  let targetSecret :=
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
      masterSecret (relativeMaskLift relativeMask)
  let sourceBootstrappingKey :=
    sampleCenteredBinomialShearBootstrappingKey q prefixDimension suffixTail
      tgswLevels ringEta tgswGadget masterSecret
  let targetBootstrappingKey :=
    sampleCenteredBinomialShearBootstrappingKey q prefixDimension suffixTail
      tgswLevels ringEta tgswGadget targetSecret
  let evaluatedBootstrappingKey := sourceBootstrappingKey >>=
    evaluateBootstrappingKey relativeMask
  let sourceKeySwitchKey :=
    sampleCenteredBinomialOneCycleKeySwitchKey q prefixDimension suffixTail
      keySwitchLevels keySwitchEta keySwitchGadget masterSecret
  let targetKeySwitchKey :=
    sampleCenteredBinomialOneCycleKeySwitchKey q prefixDimension suffixTail
      keySwitchLevels keySwitchEta keySwitchGadget targetSecret
  let transformedKeySwitchKey :=
    transformOneCycleKeySwitchKey
      (prefixDimension := prefixDimension)
      (suffixDimension := suffixTail + 1)
      keySwitchGadget
      (relativeMaskLift relativeMask) <$> sourceKeySwitchKey
  let combine :
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
          tgswLevels prefixDimension →
        Native.KeySwitchKey q prefixDimension (suffixTail + 1) keySwitchLevels →
        CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
          tgswLevels keySwitchLevels :=
    fun bootstrappingKey keySwitchKey ↦ (bootstrappingKey, keySwitchKey)
  have hKeySwitchEvalDist :
      evalDist transformedKeySwitchKey = evalDist targetKeySwitchKey := by
    let sourceRingSecret :
        RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
      fun _ ↦ masterSecret
    let targetRingSecret :
        RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
      fun _ ↦ targetSecret
    have hring :
        maskedRingSecret sourceRingSecret
            (fun _ ↦ relativeMaskLift relativeMask) =
          targetRingSecret := by
      rfl
    have hmain := transformOneCycleKeySwitchKey_centeredBinomial_evalDist
      (prefixDimension := prefixDimension)
      (suffixDimension := suffixTail + 1)
      keySwitchEta keySwitchGadget sourceRingSecret
      (relativeMaskLift relativeMask)
    rw [hring] at hmain
    simpa only [transformedKeySwitchKey, sourceKeySwitchKey, targetKeySwitchKey,
      targetSecret, sourceRingSecret, targetRingSecret,
      sampleCenteredBinomialOneCycleKeySwitchKey,
      Native.SharedRandomnessOneCycle.generateKeySwitchKey] using hmain
  have hKeySwitch : tvDist transformedKeySwitchKey targetKeySwitchKey = 0 := by
    unfold tvDist
    rw [hKeySwitchEvalDist]
    exact SPMF.tvDist_self _
  have hPair := FormalProof4FHE.TFHE.SamplerReplacement.tvDist_independentPair_le
    evaluatedBootstrappingKey targetBootstrappingKey
    transformedKeySwitchKey targetKeySwitchKey combine
  have hBound :
      tvDist
          (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
            evaluatedBootstrappingKey transformedKeySwitchKey combine)
          (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
            targetBootstrappingKey targetKeySwitchKey combine) ≤ epsilon := by
    calc
      _ ≤ tvDist evaluatedBootstrappingKey targetBootstrappingKey +
          tvDist transformedKeySwitchKey targetKeySwitchKey := hPair
      _ ≤ epsilon + 0 := add_le_add
        (hBootstrappingKey masterSecret relativeMask) (le_of_eq hKeySwitch)
      _ = epsilon := add_zero epsilon
  have hSourceEvalDist :
      evalDist
          (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension
            suffixTail tgswLevels keySwitchLevels ringEta keySwitchEta
            tgswGadget keySwitchGadget masterSecret >>=
            evaluateCenteredBinomialShearRelativeView keySwitchGadget
              evaluateBootstrappingKey relativeMask) =
        evalDist
          (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
            evaluatedBootstrappingKey transformedKeySwitchKey combine) := by
    rw [sampleCenteredBinomialShearEvaluationKeyView_eq_independentPair]
    unfold FormalProof4FHE.TFHE.SamplerReplacement.independentPair
      evaluateCenteredBinomialShearRelativeView
    simp only [evaluatedBootstrappingKey, transformedKeySwitchKey, combine,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine evalDist_bind_congr' sourceBootstrappingKey fun bootstrappingKey => ?_
    exact evalDist_bind_bind_swap sourceKeySwitchKey
      (evaluateBootstrappingKey relativeMask bootstrappingKey)
      (fun keySwitchKey evaluatedKey =>
        pure (evaluatedKey,
          transformOneCycleKeySwitchKey
            (prefixDimension := prefixDimension)
            (suffixDimension := suffixTail + 1)
            keySwitchGadget (relativeMaskLift relativeMask) keySwitchKey))
  have hTargetEvalDist :
      evalDist
          (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension
            suffixTail tgswLevels keySwitchLevels ringEta keySwitchEta
            tgswGadget keySwitchGadget targetSecret) =
        evalDist
          (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
            targetBootstrappingKey targetKeySwitchKey combine) := by
    exact congrArg evalDist
      (sampleCenteredBinomialShearEvaluationKeyView_eq_independentPair
        ringEta keySwitchEta tgswGadget keySwitchGadget targetSecret)
  unfold tvDist at hBound ⊢
  rw [hSourceEvalDist, hTargetEvalDist]
  exact hBound

/-- A BRK-only relative evaluator certificate now suffices for complete fresh-master-key
randomization: arbitrary KSK masks and the final global complement are both exact. -/
noncomputable def centeredBinomialShearViewRandomizationOfBootstrappingRelative
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (evaluateBootstrappingKey : BinarySecret (prefixDimension + suffixTail) →
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension →
      ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension))
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
    (hBootstrappingKey : ∀ masterSecret relativeMask,
      tvDist
          (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget masterSecret >>=
            evaluateBootstrappingKey relativeMask)
          (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget
            (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
              masterSecret (relativeMaskLift relativeMask))) ≤ epsilon) :
    LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      (BinarySecret (prefixDimension + suffixTail + 1))
      (BinarySecret (prefixDimension + suffixTail) × Bool)
      (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels) :=
  centeredBinomialShearViewRandomizationOfRelative ringEta keySwitchEta
    tgswGadget keySwitchGadget
    (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
      tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget)
    (evaluateCenteredBinomialShearRelativeView keySwitchGadget
      evaluateBootstrappingKey)
    epsilon epsilon_nonneg
    (evaluateCenteredBinomialShearRelativeView_tvDist_le ringEta keySwitchEta
      tgswGadget keySwitchGadget evaluateBootstrappingKey epsilon
      hBootstrappingKey)

@[simp]
theorem centeredBinomialShearViewRandomizationOfBootstrappingRelative_error
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (evaluateBootstrappingKey : BinarySecret (prefixDimension + suffixTail) →
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension →
      ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension))
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
    (hBootstrappingKey : ∀ masterSecret relativeMask,
      tvDist
          (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget masterSecret >>=
            evaluateBootstrappingKey relativeMask)
          (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget
            (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
              masterSecret (relativeMaskLift relativeMask))) ≤ epsilon) :
    (centeredBinomialShearViewRandomizationOfBootstrappingRelative ringEta
      keySwitchEta tgswGadget keySwitchGadget evaluateBootstrappingKey epsilon
      epsilon_nonneg hBootstrappingKey).error = epsilon := by
  simp [centeredBinomialShearViewRandomizationOfBootstrappingRelative]

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
