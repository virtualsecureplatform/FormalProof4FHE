/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveCutCycleSecurity
import FormalProof4FHE.TFHE.KeySwitchFirstCloudSecurity

/-!
# KSK-First Security for Adaptive Native TFHE

The cloud-key-only KSK-first reduction cannot directly run an adaptive encryption experiment:
the eager input tape is encrypted under the hidden scalar key.  This module exposes that bounded
tape as an explicit third component of the public decision view.  The resulting three-game path
is

* real BRK, real KSK, and real input tape;
* real BRK, uniform KSK, and the same real input-tape distribution;
* zero-message BRK, uniform KSK, and the same real input-tape distribution.

The middle hop is the existing cut-cycle BRK theorem instantiated with uniform scalar errors in
its zero-message KSK context.  At the final endpoint the BRK and KSK are independent of the scalar
secret, so the only remaining scalar-secret-dependent object is the bounded input tape.  That
endpoint is exactly one ordinary binary-secret batch-LWE game on `queryCount` rows.

This file makes the adaptive KSK-first premise a genuine public decision problem.  A subsequent
search-to-decision module must still derive that augmented decision premise from a bounded batch
of public BRK+KSK+tape views.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstSecurity

open Native

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

/-! ## Augmented public decision view -/

/-- The bounded eager encryption tape exposed as correlated public side information. -/
abbrev InputTape (q lweDimension queryCount : ℕ) :=
  FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension queryCount

/-- A public distinguisher receives the two native cloud-key components and a bounded input
tape, but neither hidden secret. -/
abbrev PublicDistinguisher
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  BootstrappingKey q degree ringRank tgswLevels lweDimension →
    KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels →
      InputTape q lweDimension queryCount → ProbComp Bool

/-- Run the complete adaptive left-or-right experiment from a supplied public cloud key and
already-sampled eager input tape. -/
noncomputable def toPublicDistinguisher
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    PublicDistinguisher q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount :=
  fun bootstrapKey keySwitchKey tape ↦ do
    let bit ← $ᵗ Bool
    let guess ← Adaptive.runFromTranscript bit encode adversary
      ⟨bootstrapKey, keySwitchKey⟩ tape
    return (bit == guess)

/-- Honest augmented public decision experiment. -/
noncomputable def realDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool := do
  let lweSecret ← sampleLweSecret lweDimension
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← generateBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget lweSecret ringSecret
  let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
    keySwitchLevels keySwitchErrorSampler keySwitchGadget
    (keyExtract ringSecret) lweSecret
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret lweSecret) 0
  distinguisher bootstrapKey keySwitchKey tape

/-- KSK-first augmented endpoint.  Sampling the uniform KSK immediately after the scalar key
matches the cut-cycle experiment instantiated with uniform scalar errors. -/
noncomputable def uniformKeySwitchDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool := do
  let lweSecret ← sampleLweSecret lweDimension
  let keySwitchKey ←
    $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← generateBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget lweSecret ringSecret
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret lweSecret) 0
  distinguisher bootstrapKey keySwitchKey tape

/-- Real versus uniform-KSK augmented public decision advantage. -/
noncomputable def keySwitchDecisionAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ℝ :=
  (realDecisionGame (queryCount := queryCount) ringErrorSampler
    keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget distinguisher).boolDistAdvantage
  (uniformKeySwitchDecisionGame (queryCount := queryCount) ringErrorSampler inputErrorSampler
    tgswGadget distinguisher)

/-! ## Exact bridges to the adaptive and cut-cycle games -/

/-- The honest adaptive game is exactly the real augmented public decision game. -/
theorem realGame_evalDist_eq_realDecisionGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary) =
      evalDist (realDecisionGame (queryCount := queryCount) ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        (toPublicDistinguisher (queryCount := queryCount) encode adversary)) := by
  rfl

/-- The augmented uniform-KSK endpoint is the real cut-cycle game with uniform scalar errors in
its generated zero-message KSK. -/
theorem realCutGame_uniformError_evalDist_eq_uniformKeySwitchDecisionGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist (BootstrapCutSecurity.realCutGame
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler ($ᵗ (ZMod q)) tgswGadget
        (Adaptive.CutCycleSecurity.cutContinuation
          queryCount inputErrorSampler encode adversary)) =
      evalDist (uniformKeySwitchDecisionGame (queryCount := queryCount)
        ringErrorSampler inputErrorSampler tgswGadget
        (toPublicDistinguisher (queryCount := queryCount) encode adversary)) := by
  unfold BootstrapCutSecurity.realCutGame BootstrapCutSecurity.zeroKeySwitchContext
    Adaptive.CutCycleSecurity.cutContinuation Adaptive.continuation
    uniformKeySwitchDecisionGame toPublicDistinguisher
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (Native.KeySwitchFirstCloudSecurity.generateZeroKeySwitchKey_uniformError_evalDist
      q lweDimension (ringRank * degree) keySwitchLevels lweSecret)
    (fun keySwitchKey ↦ do
      let ringSecret ← sampleRingSecret ringRank degree
      let bootstrapKey ← generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
        lweSecret ringSecret
      let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret lweSecret) 0
      let bit ← $ᵗ Bool
      let guess ← Adaptive.runFromTranscript bit encode adversary
        ⟨bootstrapKey, keySwitchKey⟩ tape
      return (bit == guess))

/-- Adaptive endpoint with zero-message BRK, uniform KSK, and the real bounded input tape. -/
noncomputable def zeroBootstrapUniformKeySwitchGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool := do
  let lweSecret ← sampleLweSecret lweDimension
  let keySwitchKey ←
    $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← generateZeroBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget ringSecret
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret lweSecret) 0
  toPublicDistinguisher (queryCount := queryCount) encode adversary
    bootstrapKey keySwitchKey tape

/-- The zero-BRK augmented endpoint is the zero cut-cycle game with uniform scalar errors. -/
theorem zeroCutGame_uniformError_evalDist_eq_zeroBootstrapUniformKeySwitchGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist (BootstrapCutSecurity.zeroCutGame
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler ($ᵗ (ZMod q)) tgswGadget
        (Adaptive.CutCycleSecurity.cutContinuation
          queryCount inputErrorSampler encode adversary)) =
      evalDist (zeroBootstrapUniformKeySwitchGame queryCount ringErrorSampler
        inputErrorSampler tgswGadget encode adversary) := by
  unfold BootstrapCutSecurity.zeroCutGame BootstrapCutSecurity.zeroKeySwitchContext
    Adaptive.CutCycleSecurity.cutContinuation Adaptive.continuation
    zeroBootstrapUniformKeySwitchGame toPublicDistinguisher
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (Native.KeySwitchFirstCloudSecurity.generateZeroKeySwitchKey_uniformError_evalDist
      q lweDimension (ringRank * degree) keySwitchLevels lweSecret)
    (fun keySwitchKey ↦ do
      let ringSecret ← sampleRingSecret ringRank degree
      let bootstrapKey ← generateZeroBootstrappingKey
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget ringSecret
      let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret lweSecret) 0
      let bit ← $ᵗ Bool
      let guess ← Adaptive.runFromTranscript bit encode adversary
        ⟨bootstrapKey, keySwitchKey⟩ tape
      return (bit == guess))

/-! ## Ordinary scalar-LWE endpoint -/

/-- Scalar-secret-independent zero-BRK/uniform-KSK context. -/
noncomputable def zeroBootstrapUniformKeySwitchContext
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree) :
    ProbComp (Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels) := do
  let keySwitchKey ←
    $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← generateZeroBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget ringSecret
  return ⟨bootstrapKey, keySwitchKey⟩

/-- Ordinary binary-secret batch-LWE distinguisher for the adaptive input tape alone. -/
noncomputable def inputTapeReduction
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    LearningWithErrors.Adversary
      (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler) :=
  fun tape ↦ do
    let cloudKey ← zeroBootstrapUniformKeySwitchContext
      (keySwitchLevels := keySwitchLevels) ringErrorSampler tgswGadget
    toPublicDistinguisher (queryCount := queryCount) encode adversary
      cloudKey.1 cloudKey.2 tape

/-- The zero-BRK/uniform-KSK adaptive endpoint is exactly the real branch of the ordinary
query-counted scalar LWE reduction. -/
theorem zeroBootstrapUniformKeySwitchGame_evalDist_eq_lwe_game0
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist (zeroBootstrapUniformKeySwitchGame queryCount ringErrorSampler
        inputErrorSampler tgswGadget encode adversary) =
      evalDist (LearningWithErrors.game0
        (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
        (inputTapeReduction ringErrorSampler inputErrorSampler
          tgswGadget encode adversary)) := by
  let scalarSecrets := sampleLweSecret lweDimension
  let contexts : ProbComp (Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :=
    zeroBootstrapUniformKeySwitchContext
      (ringRank := ringRank) (lweDimension := lweDimension)
      (keySwitchLevels := keySwitchLevels) ringErrorSampler tgswGadget
  let challenges : ProbComp
      (Matrix (Fin lweDimension) (Fin queryCount) (ZMod q)) :=
    $ᵗ Matrix (Fin lweDimension) (Fin queryCount) (ZMod q)
  let errors := ProbComp.sampleIID queryCount inputErrorSampler
  let finish := fun
      (lweSecret : BinarySecret lweDimension)
      (cloudKey : Encryption.NativeCloudKey q degree ringRank tgswLevels
        lweDimension keySwitchLevels)
      (challenge : Matrix (Fin lweDimension) (Fin queryCount) (ZMod q))
      (error : Fin queryCount → ZMod q) ↦
    toPublicDistinguisher (queryCount := queryCount) encode adversary cloudKey.1 cloudKey.2
      (TLWE.batchAssemble (embedBinarySecret lweSecret) challenge 0 error)
  have native_eq :
      zeroBootstrapUniformKeySwitchGame queryCount ringErrorSampler inputErrorSampler
          tgswGadget encode adversary =
        (scalarSecrets >>= fun lweSecret ↦
          contexts >>= fun cloudKey ↦
          challenges >>= fun challenge ↦
          errors >>= fun error ↦
          finish lweSecret cloudKey challenge error) := by
    simp [zeroBootstrapUniformKeySwitchGame,
      zeroBootstrapUniformKeySwitchContext, scalarSecrets, contexts, challenges, errors,
      finish, TLWE.batchEncrypt, toPublicDistinguisher, bind_assoc, monad_norm]
  have lwe_eq :
      LearningWithErrors.game0
          (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
          (inputTapeReduction ringErrorSampler inputErrorSampler
            tgswGadget encode adversary) =
        (challenges >>= fun challenge ↦
          scalarSecrets >>= fun lweSecret ↦
          errors >>= fun error ↦
          contexts >>= fun cloudKey ↦
          finish lweSecret cloudKey challenge error) := by
    simp [LearningWithErrors.game0, LearningWithErrors.distr,
      KeySwitchSecurity.binaryLweProblem, FormalProof4FHE.LWE.embeddedBatchProblem,
      inputTapeReduction, scalarSecrets, contexts, challenges, errors, finish,
      TLWE.batchAssemble, bind_assoc, monad_norm]
  rw [native_eq, lwe_eq]
  exact KeySwitchSecurity.evalDist_bind_four_reorder
    scalarSecrets contexts challenges errors finish

/-- At a fixed public cloud key, sampling the uniform tape before the fair hidden bit has the
same one-half success probability as the standard eager-tape experiment. -/
theorem uniformInputTape_toPublicDistinguisher_probOutput_true
    (queryCount : ℕ)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (cloudKey : Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : IsQueryBoundP (adversary cloudKey)
      (Adaptive.isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q) lweDimension)) queryCount) :
    Pr[= true | do
      let tape ← $ᵗ (InputTape q lweDimension queryCount)
      toPublicDistinguisher (queryCount := queryCount) encode adversary
        cloudKey.1 cloudKey.2 tape] = 1 / 2 := by
  have hswap := probOutput_bind_bind_swap
    ($ᵗ (InputTape q lweDimension queryCount)) ($ᵗ Bool)
    (fun tape bit ↦ do
      let guess ← Adaptive.runFromTranscript bit encode adversary cloudKey tape
      return (bit == guess)) true
  unfold toPublicDistinguisher
  rw [hswap]
  exact Adaptive.uniformAdaptive_probOutput_true
    queryCount encode adversary cloudKey hbound

/-- The uniform branch of the input-tape reduction succeeds with probability one half. -/
theorem inputTapeReduction_game1_probOutput_true
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    Pr[= true | LearningWithErrors.game1
      (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
      (inputTapeReduction ringErrorSampler inputErrorSampler
        tgswGadget encode adversary)] = 1 / 2 := by
  let contexts : ProbComp (Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :=
    zeroBootstrapUniformKeySwitchContext
      (ringRank := ringRank) (lweDimension := lweDimension)
      (keySwitchLevels := keySwitchLevels) ringErrorSampler tgswGadget
  let tapes : ProbComp (InputTape q lweDimension queryCount) :=
    $ᵗ (InputTape q lweDimension queryCount)
  let splitTapes : ProbComp (InputTape q lweDimension queryCount) := do
    let challenge ← $ᵗ Matrix (Fin lweDimension) (Fin queryCount) (ZMod q)
    let output ← $ᵗ (Fin queryCount → ZMod q)
    return (challenge, output)
  have hTapes : evalDist tapes = evalDist splitTapes := by
    exact (FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
      (first := Matrix (Fin lweDimension) (Fin queryCount) (ZMod q))
      (second := Fin queryCount → ZMod q)).symm
  have hgame :
      evalDist (LearningWithErrors.game1
        (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
        (inputTapeReduction ringErrorSampler inputErrorSampler
          tgswGadget encode adversary)) =
      evalDist (tapes >>= fun tape ↦
        contexts >>= fun cloudKey ↦
        toPublicDistinguisher (queryCount := queryCount) encode adversary
          cloudKey.1 cloudKey.2 tape) := by
    calc
      _ = evalDist (splitTapes >>= fun tape ↦
          contexts >>= fun cloudKey ↦
          toPublicDistinguisher (queryCount := queryCount) encode adversary
            cloudKey.1 cloudKey.2 tape) := by
        simp [LearningWithErrors.game1, LearningWithErrors.uniformDistr,
          KeySwitchSecurity.binaryLweProblem, FormalProof4FHE.LWE.embeddedBatchProblem,
          inputTapeReduction, contexts, splitTapes, bind_assoc, monad_norm]
      _ = _ := by
        rw [evalDist_bind, ← hTapes, ← evalDist_bind]
  rw [evalDist_ext_iff.mp hgame true]
  rw [probOutput_bind_bind_swap tapes contexts
    (fun tape cloudKey ↦
      toPublicDistinguisher (queryCount := queryCount) encode adversary
        cloudKey.1 cloudKey.2 tape) true]
  rw [probOutput_bind_eq_tsum]
  calc
    _ = ∑' cloudKey, Pr[= cloudKey | contexts] * (1 / 2) := by
      refine tsum_congr fun cloudKey ↦ ?_
      congr 1
      simpa [tapes] using
        (uniformInputTape_toPublicDistinguisher_probOutput_true
          queryCount encode adversary cloudKey (hbound cloudKey))
    _ = 1 / 2 := by
      rw [ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (by simp [contexts,
          zeroBootstrapUniformKeySwitchContext]), one_mul]

/-- The final adaptive endpoint has exactly one ordinary binary-secret scalar batch-LWE
advantage on the `queryCount` input rows. -/
theorem abs_signedAdvantage_zeroBootstrapUniformKeySwitchGame_eq_lwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (zeroBootstrapUniformKeySwitchGame queryCount ringErrorSampler
        inputErrorSampler tgswGadget encode adversary)| =
      LearningWithErrors.advantage
        (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
        (inputTapeReduction ringErrorSampler inputErrorSampler
          tgswGadget encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Encryption.signedAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (zeroBootstrapUniformKeySwitchGame_evalDist_eq_lwe_game0 queryCount
        ringErrorSampler inputErrorSampler tgswGadget encode adversary) true,
    inputTapeReduction_game1_probOutput_true queryCount ringErrorSampler
      inputErrorSampler tgswGadget encode adversary hbound]
  norm_num

/-! ## Three-game adaptive composition -/

/-- Middle hybrid cost: replace the real BRK by a zero-message BRK while the KSK is uniform. -/
noncomputable def uniformKeySwitchBootstrapAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (uniformKeySwitchDecisionGame (queryCount := queryCount) ringErrorSampler
    inputErrorSampler tgswGadget
    (toPublicDistinguisher (queryCount := queryCount) encode adversary)).boolDistAdvantage
  (zeroBootstrapUniformKeySwitchGame queryCount ringErrorSampler
    inputErrorSampler tgswGadget encode adversary)

/-- The middle augmented hop is exactly the existing cut-cycle BRK advantage with a uniform
KSK context. -/
theorem uniformKeySwitchBootstrapAdvantage_eq_cutBootstrapReplacementAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    uniformKeySwitchBootstrapAdvantage queryCount ringErrorSampler inputErrorSampler
        tgswGadget encode adversary =
      BootstrapCutSecurity.cutBootstrapReplacementAdvantage
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler ($ᵗ (ZMod q)) tgswGadget
        (Adaptive.CutCycleSecurity.cutContinuation
          queryCount inputErrorSampler encode adversary) := by
  unfold uniformKeySwitchBootstrapAdvantage
    BootstrapCutSecurity.cutBootstrapReplacementAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (realCutGame_uniformError_evalDist_eq_uniformKeySwitchDecisionGame
        queryCount ringErrorSampler inputErrorSampler tgswGadget encode adversary),
    probOutput_congr rfl
      (zeroCutGame_uniformError_evalDist_eq_zeroBootstrapUniformKeySwitchGame
        queryCount ringErrorSampler inputErrorSampler tgswGadget encode adversary)]

/-- The honest adaptive advantage follows the real/uniform-KSK/zero-BRK three-game path. -/
theorem abs_signedAdvantage_real_le_decision_add_bootstrap_add_endpoint
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      keySwitchDecisionAdvantage (queryCount := queryCount) ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
          (toPublicDistinguisher (queryCount := queryCount) encode adversary) +
        uniformKeySwitchBootstrapAdvantage queryCount ringErrorSampler inputErrorSampler
          tgswGadget encode adversary +
        |Encryption.signedAdvantage
          (zeroBootstrapUniformKeySwitchGame queryCount ringErrorSampler
            inputErrorSampler tgswGadget encode adversary)| := by
  unfold Encryption.signedAdvantage keySwitchDecisionAdvantage
    uniformKeySwitchBootstrapAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
    (realGame_evalDist_eq_realDecisionGame queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary)]
  have hFirst := abs_sub_le
    (Pr[= true |
      realDecisionGame (queryCount := queryCount) ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        (toPublicDistinguisher (queryCount := queryCount) encode adversary)]).toReal
    (Pr[= true |
      uniformKeySwitchDecisionGame (queryCount := queryCount) ringErrorSampler
        inputErrorSampler tgswGadget
        (toPublicDistinguisher (queryCount := queryCount) encode adversary)]).toReal
    (1 / 2 : ℝ)
  have hSecond := abs_sub_le
    (Pr[= true |
      uniformKeySwitchDecisionGame (queryCount := queryCount) ringErrorSampler
        inputErrorSampler tgswGadget
        (toPublicDistinguisher (queryCount := queryCount) encode adversary)]).toReal
    (Pr[= true |
      zeroBootstrapUniformKeySwitchGame queryCount ringErrorSampler
        inputErrorSampler tgswGadget encode adversary]).toReal
    (1 / 2 : ℝ)
  linarith

/-- **Adaptive KSK-first TFHE security bound.**  The complete honest advantage is at most one
augmented public-decision term, two ordinary ring batch-module-LWE terms, and one ordinary scalar
batch-LWE term containing exactly the bounded adaptive input rows. -/
theorem abs_signedAdvantage_real_le_decision_add_two_moduleLwe_add_inputLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      keySwitchDecisionAdvantage (queryCount := queryCount) ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
          (toPublicDistinguisher (queryCount := queryCount) encode adversary) +
        LearningWithErrors.advantage
          (BootstrapCutSecurity.batchModuleLweProblem
            q degree ringRank tgswLevels lweDimension ringErrorSampler)
          (BootstrapCutSecurity.realBatchReduction
            ringErrorSampler ($ᵗ (ZMod q)) tgswGadget
            (Adaptive.CutCycleSecurity.cutContinuation
              queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (BootstrapCutSecurity.batchModuleLweProblem
            q degree ringRank tgswLevels lweDimension ringErrorSampler)
          (BootstrapCutSecurity.zeroBatchReduction
            ringErrorSampler ($ᵗ (ZMod q))
            (Adaptive.CutCycleSecurity.cutContinuation
              queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
          (inputTapeReduction ringErrorSampler inputErrorSampler
            tgswGadget encode adversary) := by
  have hHybrid := abs_signedAdvantage_real_le_decision_add_bootstrap_add_endpoint
    queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary
  rw [uniformKeySwitchBootstrapAdvantage_eq_cutBootstrapReplacementAdvantage,
    abs_signedAdvantage_zeroBootstrapUniformKeySwitchGame_eq_lwe
      queryCount ringErrorSampler inputErrorSampler tgswGadget encode adversary hbound]
    at hHybrid
  have hCut := BootstrapCutSecurity.cutBootstrapReplacementAdvantage_le_two_batchModuleLwe
    ringErrorSampler ($ᵗ (ZMod q)) tgswGadget
    (Adaptive.CutCycleSecurity.cutContinuation
      queryCount inputErrorSampler encode adversary)
  linarith

end FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstSecurity
