/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleRelativeKeySwitchRandomization

/-!
# BRK Message Transport for Relative Master-Key Randomization

The correlated shear-centered-binomial row-error sampler is invariant not only under the
global-complement shear, but also under negation of its complete error vector.  Consequently the
usual public TGSW plaintext toggle remains exact for this correlated sampler.  This lifts to
arbitrary plaintext-bit XOR transport across the full bootstrapping key.

In TFHE terminology, the BRK source key is the scalar key encrypted as the plaintext vector and
the BRK target key is the ring encryption key.  Under shared randomness the former is exactly a
prefix of the latter, so the actual one-circular object is `BRK_S(prefix(S))`.

The current and shifted master keys below are instead two same-size ring keys used by a
search-to-decision randomizer; they are not TFHE's source and target keys.  A normalized relative
mask changes both the encrypted prefix and the full master key.  This module applies the prefix
message change exactly first, then exposes a certificate for the remaining current-to-shifted
master-key transport.  Composing that certificate with the exact KSK action and exact global
complement yields the full fresh-master-key `ViewRandomization` interface with no additional
statistical loss.  This is an internal route toward proving the one-circular game, not its
definition and not by itself a proof of one-circular security.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

noncomputable section

/-- The complement shear commutes with negating the complete rank-one row-error vector. -/
theorem rankOneComplementErrorShear_neg
    {R : Type} [Ring R] {levels : ℕ} (offset : R)
    (error : Fin (TGSW.rowCount 1 levels) → R) :
    rankOneComplementErrorShear offset (-error) =
      -(rankOneComplementErrorShear offset error) := by
  classical
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  fin_cases block
  · simp [rankOneComplementErrorShear, rankOneMaskRow, rankOneBodyRow,
      TGSW.rowIndex]
    abel
  · simp [rankOneComplementErrorShear, rankOneBodyRow, TGSW.rowIndex]

/-- Distributional invariance of a finite sampler under negation. -/
def EvalDistNegationInvariant {A : Type} [Neg A] (sampler : ProbComp A) : Prop :=
  evalDist ((fun value : A ↦ -value) <$> sampler) = evalDist sampler

/-- Orbit symmetrization preserves negation invariance whenever the orbit action commutes with
negation. -/
theorem involutiveSymmetrization_negationInvariant
    {A : Type} [Fintype A] [DecidableEq A] [SampleableType A] [Neg A]
    (action : A → A) (source : ProbComp A)
    (hcommute : ∀ value, action (-value) = -(action value))
    (hsource : EvalDistNegationInvariant source) :
    EvalDistNegationInvariant (involutiveSymmetrization action source) := by
  unfold EvalDistNegationInvariant involutiveSymmetrization
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  calc
    _ = evalDist (source >>= fun value ↦
        ($ᵗ Bool) >>= fun applyAction ↦
          pure (if applyAction then action (-value) else -value)) := by
      refine evalDist_bind_congr' source fun value ↦ ?_
      refine evalDist_bind_congr' ($ᵗ Bool) fun applyAction ↦ ?_
      cases applyAction
      · rfl
      · simpa only [if_true] using congrArg evalDist
          (congrArg (fun output ↦ (pure output : ProbComp A))
            (hcommute value).symm)
    _ = evalDist (((fun value : A ↦ -value) <$> source) >>= fun value ↦
        ($ᵗ Bool) >>= fun applyAction ↦
          pure (if applyAction then action value else value)) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (source >>= fun value ↦
        ($ᵗ Bool) >>= fun applyAction ↦
          pure (if applyAction then action value else value)) := by
      rw [evalDist_bind, hsource, ← evalDist_bind]

/-- Shear-orbit symmetrization preserves negation invariance of the base row-vector sampler. -/
theorem rankOneShearSymmetrizedErrorVector_negationInvariant
    {R : Type} [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (baseSampler : ProbComp (Fin (TGSW.rowCount 1 levels) → R))
    (offset : R) (hbase : EvalDistNegationInvariant baseSampler) :
    EvalDistNegationInvariant
      (rankOneShearSymmetrizedErrorVector baseSampler offset) := by
  apply involutiveSymmetrization_negationInvariant
  · exact rankOneComplementErrorShear_neg offset
  · exact hbase

/-- The concrete shear-centered-binomial row vector is exactly invariant under full negation. -/
theorem centeredBinomialShearErrorVector_negationInvariant
    (q degree levels ringEta : ℕ) [NeZero q] :
    EvalDistNegationInvariant
      (centeredBinomialShearErrorVector q degree levels ringEta) := by
  unfold centeredBinomialShearErrorVector
    rankOneShearSymmetrizedIIDErrorVector
  apply rankOneShearSymmetrizedErrorVector_negationInvariant
  exact FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negate_sampleIID_evalDist
    (TGSW.rowCount 1 levels)
    (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
    (RLWE.CenteredBinomial.probOutput_neg q (degree + 1) ringEta)

/-- A homogeneous correlated-error TLWE batch is invariant under ciphertext negation whenever
its complete error-vector sampler is negation invariant. -/
theorem negate_homogeneous_withErrorVector_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension levels : ℕ}
    (errorVectorSampler :
      ProbComp (Fin (TGSW.rowCount dimension levels) → R))
    (hsymmetric : EvalDistNegationInvariant errorVectorSampler)
    (secret : Fin dimension → R) :
    evalDist (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateCiphertext <$>
        (do
          let challenge ←
            $ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R
          let error ← errorVectorSampler
          return TLWE.batchAssemble secret challenge 0 error)) =
      evalDist (do
        let challenge ←
          $ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R
        let error ← errorVectorSampler
        return TLWE.batchAssemble secret challenge 0 error) := by
  let samples := TGSW.rowCount dimension levels
  let errors := errorVectorSampler
  let finish := fun (challenge : Matrix (Fin dimension) (Fin samples) R)
      (error : Fin samples → R) ↦
        (pure (TLWE.batchAssemble secret challenge 0 error) :
          ProbComp (TGSW.Ciphertext R dimension levels))
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge ↦
        errors >>= fun error ↦
          finish
            (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateChallenge
              challenge)
            (-error)) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R)
        fun challenge ↦ ?_
      refine evalDist_bind_congr' errors fun error ↦ ?_
      simpa only [samples, finish] using congrArg evalDist
        (congrArg pure
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateCiphertext_batchAssemble_zero
              (levels := levels) secret challenge error))
    _ = evalDist
        ((FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateChallenge <$>
            ($ᵗ Matrix (Fin dimension) (Fin samples) R)) >>= fun challenge ↦
          ((fun error : Fin samples → R ↦ -error) <$> errors) >>= fun error ↦
            finish challenge error) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      rfl
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge ↦
          ((fun error : Fin samples → R ↦ -error) <$> errors) >>= fun error ↦
            finish challenge error) := by
      rw [evalDist_bind,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateChallenge_uniform_evalDist,
        ← evalDist_bind]
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge ↦
        errors >>= fun error ↦ finish challenge error) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R)
        fun _ ↦ ?_
      rw [evalDist_bind, show evalDist
          ((fun error : Fin samples → R ↦ -error) <$> errors) =
            evalDist errors by exact hsymmetric,
        ← evalDist_bind]
    _ = _ := by
      simp [samples, errors, finish, monad_norm]

/-- Public TGSW plaintext-bit toggling remains exact for a negation-invariant correlated
row-error sampler. -/
theorem toggleTGSW_encryptWithErrorVector_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension levels : ℕ}
    (errorVectorSampler :
      ProbComp (Fin (TGSW.rowCount dimension levels) → R))
    (hsymmetric : EvalDistNegationInvariant errorVectorSampler)
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (bit mask : Bool) :
    evalDist
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.toggleTGSW
          gadget mask <$>
          TGSW.encryptWithErrorVector dimension levels errorVectorSampler
            secret gadget (embedBit bit)) =
      evalDist (TGSW.encryptWithErrorVector dimension levels errorVectorSampler
        secret gadget
        (embedBit (LWE.MultiKeyAffine.maskedBit bit mask))) := by
  cases mask with
  | false =>
      rw [show
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.toggleTGSW
            gadget false = id by
          funext ciphertext
          simp [FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.toggleTGSW]]
      simp [LWE.MultiKeyAffine.maskedBit]
  | true =>
      let homogeneous : ProbComp (TGSW.Ciphertext R dimension levels) := do
        let challenge ←
          $ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R
        let error ← errorVectorSampler
        return TLWE.batchAssemble secret challenge 0 error
      let finish := fun ciphertext : TGSW.Ciphertext R dimension levels ↦
        (pure (TGSW.addGadget gadget
          (embedBit (LWE.MultiKeyAffine.maskedBit bit true)) ciphertext) :
          ProbComp (TGSW.Ciphertext R dimension levels))
      rw [show TGSW.encryptWithErrorVector dimension levels errorVectorSampler
          secret gadget (embedBit bit) =
          homogeneous >>= fun ciphertext ↦
            pure (TGSW.addGadget gadget (embedBit bit) ciphertext) by
        simp [TGSW.encryptWithErrorVector, homogeneous, monad_norm]]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      calc
        _ = evalDist (homogeneous >>= fun ciphertext ↦
            finish
              (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateCiphertext
                ciphertext)) := by
          refine evalDist_bind_congr' homogeneous fun ciphertext ↦ ?_
          simpa [finish] using congrArg evalDist (congrArg
            (fun value ↦
              (pure value : ProbComp (TGSW.Ciphertext R dimension levels)))
            (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.toggleTGSW_addGadget
              gadget bit true ciphertext))
        _ = evalDist
            ((FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateCiphertext <$>
              homogeneous) >>= finish) := by
          simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
        _ = evalDist (homogeneous >>= finish) := by
          rw [evalDist_bind,
            show evalDist
                (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateCiphertext <$>
                  homogeneous) = evalDist homogeneous by
              exact negate_homogeneous_withErrorVector_evalDist
                errorVectorSampler hsymmetric secret,
            ← evalDist_bind]
        _ = _ := by
          simp [TGSW.encryptWithErrorVector, homogeneous, finish, monad_norm]

/-- Lift exact correlated-error TGSW plaintext toggling pointwise through a complete BRK. -/
theorem transformBootstrappingKey_generateWithErrorVector_evalDist
    {q degree levels lweDimension : ℕ} [NeZero q]
    (errorVectorSampler :
      ProbComp (Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (degree + 1)))
    (hsymmetric : EvalDistNegationInvariant errorVectorSampler)
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1)) :
    evalDist
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBootstrappingKey
          gadget mask <$>
          generateBootstrappingKeyWithErrorVector q degree levels lweDimension
            errorVectorSampler gadget lweSecret ringSecret) =
      evalDist
        (generateBootstrappingKeyWithErrorVector q degree levels lweDimension
          errorVectorSampler gadget
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            lweSecret mask)
          ringSecret) := by
  rw [show
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBootstrappingKey
        gadget mask =
      (fun bootstrappingKey coordinate ↦
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.toggleTGSW
          gadget (mask coordinate) (bootstrappingKey coordinate)) by rfl]
  simpa only [generateBootstrappingKeyWithErrorVector,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret] using
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.mOfFn_map_evalDist_congr
      lweDimension
      (fun coordinate ↦
        TGSW.encryptWithErrorVector 1 levels errorVectorSampler
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q (degree + 1) (lweSecret coordinate)))
      (fun coordinate ↦
        TGSW.encryptWithErrorVector 1 levels errorVectorSampler
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q (degree + 1)
            (LWE.MultiKeyAffine.maskedBit
              (lweSecret coordinate) (mask coordinate))))
      (fun coordinate ↦
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.toggleTGSW
          gadget (mask coordinate))
      (fun coordinate ↦ by
        rw [BlindRotation.embedConstantBit_eq_embedBit,
          BlindRotation.embedConstantBit_eq_embedBit]
        exact toggleTGSW_encryptWithErrorVector_evalDist
          errorVectorSampler hsymmetric (embedRingSecret q ringSecret)
          gadget (lweSecret coordinate) (mask coordinate))

/-- Centered-binomial shear specialization of exact arbitrary BRK plaintext-mask transport. -/
theorem transformBootstrappingKey_centeredBinomialShear_evalDist
    {q degree levels lweDimension : ℕ} [NeZero q]
    (ringEta : ℕ) (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1)) :
    evalDist
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBootstrappingKey
          gadget mask <$>
          generateBootstrappingKeyWithErrorVector q degree levels lweDimension
            (centeredBinomialShearErrorVector q degree levels ringEta)
            gadget lweSecret ringSecret) =
      evalDist
        (generateBootstrappingKeyWithErrorVector q degree levels lweDimension
          (centeredBinomialShearErrorVector q degree levels ringEta)
          gadget
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            lweSecret mask)
          ringSecret) :=
  transformBootstrappingKey_generateWithErrorVector_evalDist
    (centeredBinomialShearErrorVector q degree levels ringEta)
    (centeredBinomialShearErrorVector_negationInvariant
      q degree levels ringEta)
    gadget lweSecret mask ringSecret

/-- A BRK sampler with the plaintext vector and rank-one encryption key exposed separately. -/
noncomputable def sampleCenteredBinomialShearBootstrappingKeyWithMessage
    (q prefixDimension suffixTail tgswLevels : ℕ) [NeZero q]
    (ringEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (messageSecret : BinarySecret prefixDimension)
    (masterRingSecret : BinarySecret (prefixDimension + suffixTail + 1)) :
    ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
      tgswLevels prefixDimension) :=
  let ringSecret : RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
    fun _ ↦ masterRingSecret
  generateBootstrappingKeyWithErrorVector q (prefixDimension + suffixTail)
    tgswLevels prefixDimension
    (centeredBinomialShearErrorVector q (prefixDimension + suffixTail)
      tgswLevels ringEta)
    tgswGadget messageSecret ringSecret

/-- The original self-circular BRK sampler is the separated sampler whose message is the shared
master-key prefix. -/
theorem sampleCenteredBinomialShearBootstrappingKey_eq_withMessage
    {q prefixDimension suffixTail tgswLevels : ℕ} [NeZero q]
    (ringEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (masterSecret : BinarySecret (prefixDimension + suffixTail + 1)) :
    sampleCenteredBinomialShearBootstrappingKey q prefixDimension suffixTail
        tgswLevels ringEta tgswGadget masterSecret =
      sampleCenteredBinomialShearBootstrappingKeyWithMessage q
        prefixDimension suffixTail tgswLevels ringEta tgswGadget
        (prefixSecret
          (prefixDimension := prefixDimension)
          (suffixDimension := suffixTail + 1)
          (fun _ ↦ masterSecret))
        masterSecret := by
  rfl

/-- Exact plaintext-mask transport for the sampler with separately exposed message and ring
encryption key. -/
theorem transformBootstrappingKey_sampleWithMessage_evalDist
    {q prefixDimension suffixTail tgswLevels : ℕ} [NeZero q]
    (ringEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (messageSecret messageMask : BinarySecret prefixDimension)
    (masterRingSecret : BinarySecret (prefixDimension + suffixTail + 1)) :
    evalDist
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBootstrappingKey
          tgswGadget messageMask <$>
          sampleCenteredBinomialShearBootstrappingKeyWithMessage q
            prefixDimension suffixTail tgswLevels ringEta tgswGadget
            messageSecret masterRingSecret) =
      evalDist
        (sampleCenteredBinomialShearBootstrappingKeyWithMessage q
          prefixDimension suffixTail tgswLevels ringEta tgswGadget
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            messageSecret messageMask)
          masterRingSecret) := by
  let ringSecret : RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
    fun _ ↦ masterRingSecret
  simpa only [sampleCenteredBinomialShearBootstrappingKeyWithMessage,
      ringSecret] using
    transformBootstrappingKey_centeredBinomialShear_evalDist
      ringEta tgswGadget messageSecret messageMask ringSecret

/-- Prefix plaintext mask induced by a normalized complete relative-key mask. -/
def relativeBootstrappingMessageMask
    {prefixDimension suffixTail : ℕ}
    (relativeMask : BinarySecret (prefixDimension + suffixTail)) :
    BinarySecret prefixDimension :=
  prefixSecret
    (prefixDimension := prefixDimension)
    (suffixDimension := suffixTail + 1)
    (fun _ ↦ relativeMaskLift relativeMask)

/-- Changing every BRK plaintext bit selected by a normalized relative mask is exact.  The
current full master ring key is deliberately retained while the encrypted prefix is changed to
the prefix of the shifted master key. -/
theorem transformBootstrappingKey_relativeMessage_evalDist
    {q prefixDimension suffixTail tgswLevels : ℕ} [NeZero q]
    (ringEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (masterSecret : BinarySecret (prefixDimension + suffixTail + 1))
    (relativeMask : BinarySecret (prefixDimension + suffixTail)) :
    let shiftedMasterSecret :=
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
        masterSecret (relativeMaskLift relativeMask)
    evalDist
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBootstrappingKey
          tgswGadget (relativeBootstrappingMessageMask relativeMask) <$>
          sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget masterSecret) =
      evalDist
        (sampleCenteredBinomialShearBootstrappingKeyWithMessage q
          prefixDimension suffixTail tgswLevels ringEta tgswGadget
          (prefixSecret
            (prefixDimension := prefixDimension)
            (suffixDimension := suffixTail + 1)
            (fun _ ↦ shiftedMasterSecret))
          masterSecret) := by
  dsimp only
  let currentRingSecret :
      RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
    fun _ ↦ masterSecret
  let ringMask : RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
    fun _ ↦ relativeMaskLift relativeMask
  let shiftedMasterSecret :=
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
      masterSecret (relativeMaskLift relativeMask)
  let shiftedRingSecret :
      RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
    fun _ ↦ shiftedMasterSecret
  have hring : maskedRingSecret currentRingSecret ringMask = shiftedRingSecret := by
    rfl
  have hprefix := prefixSecret_maskedRingSecret
    (prefixDimension := prefixDimension)
    (suffixDimension := suffixTail + 1) currentRingSecret ringMask
  have hshiftedPrefix :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          (prefixSecret
            (prefixDimension := prefixDimension)
            (suffixDimension := suffixTail + 1) currentRingSecret)
          (prefixSecret
            (prefixDimension := prefixDimension)
            (suffixDimension := suffixTail + 1) ringMask) =
        prefixSecret
          (prefixDimension := prefixDimension)
          (suffixDimension := suffixTail + 1) shiftedRingSecret := by
    calc
      _ = prefixSecret
          (prefixDimension := prefixDimension)
          (suffixDimension := suffixTail + 1)
          (maskedRingSecret currentRingSecret ringMask) := hprefix.symm
      _ = prefixSecret
          (prefixDimension := prefixDimension)
          (suffixDimension := suffixTail + 1) shiftedRingSecret :=
        congrArg
          (prefixSecret
            (prefixDimension := prefixDimension)
            (suffixDimension := suffixTail + 1)) hring
  have hmain := transformBootstrappingKey_sampleWithMessage_evalDist
    ringEta tgswGadget
    (prefixSecret
      (prefixDimension := prefixDimension)
      (suffixDimension := suffixTail + 1) currentRingSecret)
    (prefixSecret
      (prefixDimension := prefixDimension)
      (suffixDimension := suffixTail + 1) ringMask)
    masterSecret
  rw [hshiftedPrefix] at hmain
  simpa only [currentRingSecret, ringMask, shiftedMasterSecret, shiftedRingSecret,
    relativeBootstrappingMessageMask,
    sampleCenteredBinomialShearBootstrappingKey_eq_withMessage] using hmain

/-- First change all public BRK plaintext bits exactly, then invoke the internal randomizer that
transports the current full master key to its shifted value.  These are not TFHE source/target
keys: the TFHE source key is the encrypted prefix inside each of these BRKs. -/
noncomputable def evaluateCenteredBinomialShearRelativeMasterShift
    {q prefixDimension suffixTail tgswLevels : ℕ}
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (evaluateMasterShift : BinarySecret (prefixDimension + suffixTail) →
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension →
      ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension))
    (relativeMask : BinarySecret (prefixDimension + suffixTail))
    (bootstrappingKey :
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension) :
    ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
      tgswLevels prefixDimension) :=
  evaluateMasterShift relativeMask
    (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBootstrappingKey
      tgswGadget (relativeBootstrappingMessageMask relativeMask)
      bootstrappingKey)

/-- A current-to-shifted master-key certificate implies the former certificate for transporting
the complete self-circular BRK view.  The encrypted-prefix change is exact. -/
theorem evaluateCenteredBinomialShearRelativeMasterShift_tvDist_le
    {q prefixDimension suffixTail tgswLevels : ℕ} [NeZero q]
    (ringEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (evaluateMasterShift : BinarySecret (prefixDimension + suffixTail) →
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension →
      ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension))
    (epsilon : ℝ)
    (hMasterShift : ∀ masterSecret relativeMask,
      let shiftedMasterSecret :=
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          masterSecret (relativeMaskLift relativeMask)
      tvDist
          (sampleCenteredBinomialShearBootstrappingKeyWithMessage q
            prefixDimension suffixTail tgswLevels ringEta tgswGadget
            (prefixSecret
              (prefixDimension := prefixDimension)
              (suffixDimension := suffixTail + 1)
              (fun _ ↦ shiftedMasterSecret))
            masterSecret >>= evaluateMasterShift relativeMask)
          (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget shiftedMasterSecret) ≤ epsilon)
    (masterSecret : BinarySecret (prefixDimension + suffixTail + 1))
    (relativeMask : BinarySecret (prefixDimension + suffixTail)) :
    tvDist
        (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
          suffixTail tgswLevels ringEta tgswGadget masterSecret >>=
          evaluateCenteredBinomialShearRelativeMasterShift
            tgswGadget evaluateMasterShift relativeMask)
        (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
          suffixTail tgswLevels ringEta tgswGadget
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            masterSecret (relativeMaskLift relativeMask))) ≤ epsilon := by
  let shiftedMasterSecret :=
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
      masterSecret (relativeMaskLift relativeMask)
  let currentBootstrappingKey :=
    sampleCenteredBinomialShearBootstrappingKey q prefixDimension suffixTail
      tgswLevels ringEta tgswGadget masterSecret
  let messageTransport :=
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBootstrappingKey
      (dimension := 1) tgswGadget
      (relativeBootstrappingMessageMask relativeMask)
  let messageTransported := messageTransport <$> currentBootstrappingKey
  let shiftedMessageCurrentMasterView :=
    sampleCenteredBinomialShearBootstrappingKeyWithMessage q
      prefixDimension suffixTail tgswLevels ringEta tgswGadget
      (prefixSecret
        (prefixDimension := prefixDimension)
        (suffixDimension := suffixTail + 1)
        (fun _ ↦ shiftedMasterSecret))
      masterSecret
  have htransport :
      evalDist messageTransported = evalDist shiftedMessageCurrentMasterView := by
    simpa only [messageTransported, messageTransport, currentBootstrappingKey,
      shiftedMessageCurrentMasterView, shiftedMasterSecret] using
      transformBootstrappingKey_relativeMessage_evalDist
        ringEta tgswGadget masterSecret relativeMask
  have hsource :
      evalDist
          (currentBootstrappingKey >>=
            evaluateCenteredBinomialShearRelativeMasterShift
              tgswGadget evaluateMasterShift relativeMask) =
        evalDist
          (shiftedMessageCurrentMasterView >>= evaluateMasterShift relativeMask) := by
    unfold evaluateCenteredBinomialShearRelativeMasterShift
    calc
      _ = evalDist (messageTransported >>= evaluateMasterShift relativeMask) := by
        simp only [messageTransported, messageTransport, currentBootstrappingKey,
          map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      _ = _ := by
        rw [evalDist_bind, htransport, ← evalDist_bind]
  unfold tvDist
  rw [show evalDist
      (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
        suffixTail tgswLevels ringEta tgswGadget masterSecret >>=
        evaluateCenteredBinomialShearRelativeMasterShift
          tgswGadget evaluateMasterShift relativeMask) =
      evalDist
        (shiftedMessageCurrentMasterView >>= evaluateMasterShift relativeMask) by
          exact hsource]
  exact hMasterShift masterSecret relativeMask

/-- Complete fresh-master-key randomization now needs only a current-to-shifted master-key
certificate after the BRK plaintext vector has already been changed exactly.  The shared KSK,
BRK messages, and final complement contribute zero additional error.  A separate
search-to-decision argument is still required to turn this compiler into one-circular security. -/
noncomputable def centeredBinomialShearViewRandomizationOfRelativeMasterShift
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (evaluateMasterShift : BinarySecret (prefixDimension + suffixTail) →
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension →
      ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension))
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
    (hMasterShift : ∀ masterSecret relativeMask,
      let shiftedMasterSecret :=
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          masterSecret (relativeMaskLift relativeMask)
      tvDist
          (sampleCenteredBinomialShearBootstrappingKeyWithMessage q
            prefixDimension suffixTail tgswLevels ringEta tgswGadget
            (prefixSecret
              (prefixDimension := prefixDimension)
              (suffixDimension := suffixTail + 1)
              (fun _ ↦ shiftedMasterSecret))
            masterSecret >>= evaluateMasterShift relativeMask)
          (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget shiftedMasterSecret) ≤ epsilon) :
    LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      (BinarySecret (prefixDimension + suffixTail + 1))
      (BinarySecret (prefixDimension + suffixTail) × Bool)
      (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels) :=
  centeredBinomialShearViewRandomizationOfBootstrappingRelative
    ringEta keySwitchEta tgswGadget keySwitchGadget
    (evaluateCenteredBinomialShearRelativeMasterShift
      tgswGadget evaluateMasterShift)
    epsilon epsilon_nonneg
    (evaluateCenteredBinomialShearRelativeMasterShift_tvDist_le
      ringEta tgswGadget evaluateMasterShift epsilon hMasterShift)

@[simp]
theorem centeredBinomialShearViewRandomizationOfRelativeMasterShift_error
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (evaluateMasterShift : BinarySecret (prefixDimension + suffixTail) →
      Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension →
      ProbComp (Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
        tgswLevels prefixDimension))
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
    (hMasterShift : ∀ masterSecret relativeMask,
      let shiftedMasterSecret :=
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          masterSecret (relativeMaskLift relativeMask)
      tvDist
          (sampleCenteredBinomialShearBootstrappingKeyWithMessage q
            prefixDimension suffixTail tgswLevels ringEta tgswGadget
            (prefixSecret
              (prefixDimension := prefixDimension)
              (suffixDimension := suffixTail + 1)
              (fun _ ↦ shiftedMasterSecret))
            masterSecret >>= evaluateMasterShift relativeMask)
          (sampleCenteredBinomialShearBootstrappingKey q prefixDimension
            suffixTail tgswLevels ringEta tgswGadget shiftedMasterSecret) ≤ epsilon) :
    (centeredBinomialShearViewRandomizationOfRelativeMasterShift
      ringEta keySwitchEta tgswGadget keySwitchGadget evaluateMasterShift epsilon
      epsilon_nonneg hMasterShift).error = epsilon := by
  simp [centeredBinomialShearViewRandomizationOfRelativeMasterShift]

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
