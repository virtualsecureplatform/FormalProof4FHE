/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.LWE.TwoBlockConvolution
import FormalProof4FHE.TFHE.EncryptionSecurity

/-!
# Native TFHE Bootstrapping-Key Security Boundary

This file identifies the exact cryptographic assumption left by the TFHE one-time encryption
theorem.  A native TGSW ciphertext is sampled as `Z + message * H`, where `Z` is a batch of
homogeneous module-LWE rows.  Translating the uniformly sampled mask matrix by the mask part of
`message * H` is a permutation.  Consequently the native structured distribution is *exactly*
the distribution of fresh direct module-LWE rows whose messages are `TGSW.gadgetPhase`.

For a TFHE bootstrapping-key entry encrypting scalar-key bit `mu` under ring key `s`, those direct
messages have two forms:

* the final gadget block encrypts `mu * g`, an affine function of the scalar key; and
* mask block `j` encrypts `-(s_j * (mu * g))`, a bilinear function of the two key families.

Thus ciphertext layout itself causes no statistical gap in the finite native model.  The precise
remaining premise is direct bilinear cross-key module-LWE KDM security in the presence of the
real key-switch key and downstream encryption experiment.  This premise is intentionally not
claimed to follow from ordinary RLWE: that implication is the unresolved circular-security
question described in `docs/TFHECircular.md`.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE

namespace TGSW

/-- Translate the public mask matrix by the mask part of `message * H`. -/
def shiftChallenge {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (challenge : Matrix (Fin dimension) (Fin (rowCount dimension levels)) R) :
    Matrix (Fin dimension) (Fin (rowCount dimension levels)) R :=
  challenge + gadgetMaskShift gadget message

/-- Undo `shiftChallenge`. -/
def unshiftChallenge {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (challenge : Matrix (Fin dimension) (Fin (rowCount dimension levels)) R) :
    Matrix (Fin dimension) (Fin (rowCount dimension levels)) R :=
  challenge - gadgetMaskShift gadget message

@[simp]
theorem unshiftChallenge_shiftChallenge {R : Type} [Ring R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (challenge : Matrix (Fin dimension) (Fin (rowCount dimension levels)) R) :
    unshiftChallenge gadget message (shiftChallenge gadget message challenge) = challenge := by
  simp [shiftChallenge, unshiftChallenge]

@[simp]
theorem shiftChallenge_unshiftChallenge {R : Type} [Ring R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (challenge : Matrix (Fin dimension) (Fin (rowCount dimension levels)) R) :
    shiftChallenge gadget message (unshiftChallenge gadget message challenge) = challenge := by
  simp [shiftChallenge, unshiftChallenge]

/-- Translation by the gadget mask is a permutation of the complete public mask matrix. -/
theorem shiftChallenge_bijective {R : Type} [Ring R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R) :
    Function.Bijective (shiftChallenge (dimension := dimension) gadget message) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unshiftChallenge gadget message,
      unshiftChallenge_shiftChallenge gadget message,
      shiftChallenge_unshiftChallenge gadget message⟩

/-- After translating its public mask, `Z + message * H` is a direct batch of TLWE rows whose
message vector is exactly the gadget phase. -/
theorem addGadget_batchAssemble_zero {R : Type} [Ring R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (rowCount dimension levels)) R)
    (error : Fin (rowCount dimension levels) → R)
    (gadget : Fin levels → R) (message : R) :
    addGadget gadget message (TLWE.batchAssemble secret challenge 0 error) =
      TLWE.batchAssemble secret (shiftChallenge (dimension := dimension) gadget message challenge)
        (gadgetPhase secret gadget message) error := by
  apply Prod.ext
  · simp [addGadget, TLWE.batchAssemble, shiftChallenge]
  · funext row
    simp only [addGadget, TLWE.batchAssemble, shiftChallenge, gadgetPhase,
      Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Matrix.vecMul,
      dotProduct, Matrix.add_apply]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    abel

/-- Convenient normal form of `addGadget_batchAssemble_zero` after simplifying a zero-message
batch assembly. -/
theorem addGadget_homogeneous {R : Type} [Ring R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (rowCount dimension levels)) R)
    (error : Fin (rowCount dimension levels) → R)
    (gadget : Fin levels → R) (message : R) :
    addGadget gadget message (challenge, vecMul secret challenge + error) =
      TLWE.batchAssemble secret (shiftChallenge (dimension := dimension) gadget message challenge)
        (gadgetPhase secret gadget message) error := by
  simpa using
    (addGadget_batchAssemble_zero secret challenge error gadget message)

/-- Direct module-LWE-row presentation of one TGSW ciphertext. -/
def directEncrypt {R : Type} [Ring R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    ProbComp (Ciphertext R dimension levels) :=
  TLWE.batchEncrypt dimension (rowCount dimension levels) errorSampler secret
    (gadgetPhase secret gadget message)

/-- The native structured TGSW sampler and its direct gadget-phase row presentation have exactly
the same output distribution.  There is no statistical loss. -/
theorem encrypt_evalDist_eq_directEncrypt {R : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    evalDist (encrypt dimension levels errorSampler secret gadget message) =
      evalDist (directEncrypt dimension levels errorSampler secret gadget message) := by
  let challenges :
      ProbComp (Matrix (Fin dimension) (Fin (rowCount dimension levels)) R) :=
    $ᵗ Matrix (Fin dimension) (Fin (rowCount dimension levels)) R
  let errors : ProbComp (Fin (rowCount dimension levels) → R) :=
    ProbComp.sampleIID (rowCount dimension levels) errorSampler
  let finish : Matrix (Fin dimension) (Fin (rowCount dimension levels)) R →
      (Fin (rowCount dimension levels) → R) →
      ProbComp (Ciphertext R dimension levels) :=
    fun challenge error ↦ pure
      (TLWE.batchAssemble secret challenge (gadgetPhase secret gadget message) error)
  let shift : Matrix (Fin dimension) (Fin (rowCount dimension levels)) R →
      Matrix (Fin dimension) (Fin (rowCount dimension levels)) R :=
    shiftChallenge (dimension := dimension) gadget message
  have left_eq :
      encrypt dimension levels errorSampler secret gadget message =
        (challenges >>= fun challenge ↦
          errors >>= fun error ↦ finish (shift challenge) error) := by
    simp [encrypt, TLWE.batchEncrypt, challenges, errors, finish, shift,
      addGadget_homogeneous, monad_norm]
  have right_eq :
      directEncrypt dimension levels errorSampler secret gadget message =
        (challenges >>= fun challenge ↦
          errors >>= fun error ↦ finish challenge error) := by
    simp [directEncrypt, TLWE.batchEncrypt, challenges, errors, finish, monad_norm]
  rw [left_eq, right_eq]
  apply evalDist_ext
  intro ciphertext
  simpa only [challenges, shift] using
    (probOutput_bind_bijective_uniform_cross
      (α := Matrix (Fin dimension) (Fin (rowCount dimension levels)) R)
      (β := Matrix (Fin dimension) (Fin (rowCount dimension levels)) R)
      (shiftChallenge (dimension := dimension) gadget message)
      (shiftChallenge_bijective (dimension := dimension) gadget message)
      (fun challenge ↦ errors >>= fun error ↦ finish challenge error) ciphertext)

/-- A row in a mask-coordinate gadget block carries the bilinear cross-key message
`-(secret_j * (message * gadget_level))`. -/
theorem gadgetPhase_castSucc {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (coordinate : Fin dimension) (level : Fin levels) :
    gadgetPhase secret gadget message
        (finProdFinEquiv (Fin.castSucc coordinate, level)) =
      -(secret coordinate * (message * gadget level)) := by
  classical
  have hne : coordinate.val ≠ dimension := Nat.ne_of_lt coordinate.isLt
  simp [gadgetPhase, gadgetBodyShift, gadgetMaskShift, rowIndex, Matrix.vecMul,
    dotProduct, hne]
  have hself :
      (if coordinate.val = coordinate.val then
          secret coordinate * (message * gadget level) else 0) =
        secret coordinate * (message * gadget level) := by simp
  rw [← hself]
  apply Finset.sum_eq_single coordinate
  · intro other _ hother
    rw [if_neg]
    intro hval
    exact hother (Fin.ext hval.symm)
  · intro hnot
    exact (hnot (Finset.mem_univ coordinate)).elim

/-- A row in the final gadget block carries the affine message `message * gadget_level`. -/
theorem gadgetPhase_last {R : Type} [Ring R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (level : Fin levels) :
    gadgetPhase secret gadget message
      (finProdFinEquiv (Fin.last dimension, level)) = message * gadget level := by
  have hne (coordinate : Fin dimension) : dimension ≠ coordinate.val :=
    Nat.ne_of_gt coordinate.isLt
  simp [gadgetPhase, gadgetBodyShift, gadgetMaskShift, rowIndex, Matrix.vecMul,
    dotProduct, hne]

end TGSW

namespace Native.BootstrapSecurity

/-- Generate the bootstrapping key via the exactly equivalent direct gadget-phase row
presentation. -/
noncomputable def generateDirectBootstrappingKey
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
  Fin.mOfFn lweDimension fun coordinate ↦
    TGSW.directEncrypt ringRank tgswLevels errorSampler
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate))

/-- Reparameterizing every independent native TGSW entry as direct gadget-phase rows preserves
the complete bootstrapping-key distribution exactly. -/
theorem generateBootstrappingKey_evalDist_eq_direct
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      errorSampler gadget lweSecret ringSecret) =
      evalDist (generateDirectBootstrappingKey q degree ringRank tgswLevels lweDimension
        errorSampler gadget lweSecret ringSecret) := by
  classical
  apply evalDist_ext
  intro key
  simp only [generateBootstrappingKey, generateDirectBootstrappingKey,
    FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn]
  apply Finset.prod_congr rfl
  intro coordinate _
  exact evalDist_ext_iff.mp
    (TGSW.encrypt_evalDist_eq_directEncrypt ringRank tgswLevels errorSampler
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q degree (lweSecret coordinate)))
    (key coordinate)

/-- Native cycle specification with only the real bootstrapping-key sampler re-expressed as
direct module-LWE rows. -/
noncomputable def directCycleSpec
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    Circular.CycleSpec
      (BinarySecret lweDimension)
      (RingBinarySecret ringRank degree)
      (BinarySecret (ringRank * degree))
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) where
  sampleLweSecret := sampleLweSecret lweDimension
  sampleRingSecret := sampleRingSecret ringRank degree
  extractRingSecret := keyExtract
  bootstrapReal := generateDirectBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget
  bootstrapZero := generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget
  keySwitchReal := generateKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
    keySwitchErrorSampler keySwitchGadget
  keySwitchZero := generateZeroKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
    keySwitchErrorSampler

/-- Every downstream continuation sees exactly the same real-game distribution under the native
structured sampler and the direct gadget-phase sampler. -/
theorem realContinuationGame_evalDist_eq_direct
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    evalDist (Circular.realContinuationGame
      (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      continuation) =
      evalDist (Circular.realContinuationGame
        (directCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        continuation) := by
  unfold Circular.realContinuationGame
  simp only [nativeCycleSpec, directCycleSpec]
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  refine evalDist_bind_congr' (sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  rw [evalDist_bind, evalDist_bind,
    generateBootstrappingKey_evalDist_eq_direct q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret]

/-- The bootstrap-zero continuation game is definitionally unchanged by the direct
reparameterization. -/
theorem bootstrapZeroContinuationGame_eq_direct
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    Circular.bootstrapZeroContinuationGame
      (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      continuation =
      Circular.bootstrapZeroContinuationGame
        (directCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        continuation := by
  rfl

/-- Direct bilinear cross-key KDM advantage corresponding exactly to native bootstrapping-key
replacement. -/
noncomputable def directBilinearAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) : ℝ :=
  (Circular.realContinuationGame
    (directCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    continuation).boolDistAdvantage
  (Circular.bootstrapZeroContinuationGame
    (directCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    continuation)

/-- Exact identification of the native structured-TRGSW replacement cost with direct bilinear
cross-key module-LWE KDM. -/
theorem continuationBootstrapReplacementAdvantage_eq_directBilinear
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    Circular.continuationBootstrapReplacementAdvantage
      (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      continuation =
      directBilinearAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget continuation := by
  unfold Circular.continuationBootstrapReplacementAdvantage directBilinearAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (realContinuationGame_evalDist_eq_direct ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget continuation) true,
    bootstrapZeroContinuationGame_eq_direct ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget continuation]

/-- The explicit concrete hardness interface for the remaining TFHE circular-security premise. -/
def DirectBilinearHardAgainst
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation →
    directBilinearAdvantage ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget continuation ≤ bound

end Native.BootstrapSecurity

namespace Encryption.Security

section NativeBootstrapComposition

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]

/-- Concrete one-time TFHE security against a selected adversary class. -/
def OneTimeHardAgainst
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤ bound

/-- The encryption experiment's native structured bootstrap cost is exactly the direct bilinear
KDM advantage of its continuation. -/
theorem bootstrapReplacementAdvantage_eq_directBilinear
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Encryption.bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary =
      Native.BootstrapSecurity.directBilinearAdvantage
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (Encryption.oneTimeContinuation inputErrorSampler encode adversary) := by
  exact Native.BootstrapSecurity.continuationBootstrapReplacementAdvantage_eq_directBilinear
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    (Encryption.oneTimeContinuation inputErrorSampler encode adversary)

/-- If the input-ciphertext error is the KSK error plus an independent widening error, the
strongest per-adversary TFHE theorem uses one conventional binary-secret batch-LWE problem even
though the two protocol error samplers are distinct. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_input_convolution
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler inputWideningSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      inputErrorSampler keySwitchErrorSampler inputWideningSampler)
    (hWideningTotal : Pr[⊥ | inputWideningSampler] = 0) :
    |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      Encryption.bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (keySwitchSamples ringRank degree keySwitchLevels + 1) keySwitchErrorSampler)
          (FormalProof4FHE.LWE.TwoBlock.convolutionReduction
            (extraErrorSampler := inputWideningSampler)
            (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
              tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) := by
  have h := abs_signedAdvantage_real_le_bootstrap_add_jointLwe
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  have hBatch :=
    FormalProof4FHE.LWE.TwoBlock.heterogeneous_advantage_eq_batch_of_convolution
      lweDimension (keySwitchSamples ringRank degree keySwitchLevels) 1
      (Native.sampleLweSecret lweDimension) embedBinarySecret
      keySwitchErrorSampler inputErrorSampler inputWideningSampler
      hConvolution hWideningTotal
      (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)
  change |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
    Encryption.bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary +
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels) 1
          (Native.sampleLweSecret lweDimension) embedBinarySecret
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) at h
  rw [hBatch] at h
  simpa [Native.KeySwitchSecurity.binaryLweProblem] using h

/-- **Conditional native TFHE security theorem.** Direct bilinear cross-key KDM security for the
exact bootstrapping messages, together with the exact shared-secret two-noise LWE assumption for
the KSK rows and adaptive input ciphertext, implies the corresponding one-time TFHE bound. -/
theorem oneTimeHardAgainst_of_directBilinear_and_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bootstrapAllowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (jointLweAllowed : LearningWithErrors.Adversary
      (jointLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels)
        keySwitchErrorSampler inputErrorSampler) → Prop)
    (bootstrapBound jointLweBound : ℝ)
    (hBootstrapClosed : ∀ adversary, allowed adversary →
      bootstrapAllowed (Encryption.oneTimeContinuation inputErrorSampler encode adversary))
    (hJointLweClosed : ∀ adversary, allowed adversary →
      jointLweAllowed
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary))
    (hBootstrap : Native.BootstrapSecurity.DirectBilinearHardAgainst
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      bootstrapAllowed bootstrapBound)
    (hJointLwe : FormalProof4FHE.LWE.HardAgainst
      (jointLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels)
        keySwitchErrorSampler inputErrorSampler)
      jointLweAllowed jointLweBound) :
    OneTimeHardAgainst ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode allowed (bootstrapBound + jointLweBound) := by
  intro adversary hadversary
  calc
    |Encryption.signedAdvantage
        (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        Encryption.bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (jointLweProblem q lweDimension
              (keySwitchSamples ringRank degree keySwitchLevels)
              keySwitchErrorSampler inputErrorSampler)
            (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
              tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) :=
      abs_signedAdvantage_real_le_bootstrap_add_jointLwe ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary
    _ ≤ bootstrapBound + jointLweBound := add_le_add
      (by
        rw [bootstrapReplacementAdvantage_eq_directBilinear ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]
        exact hBootstrap _ (hBootstrapClosed adversary hadversary))
      (hJointLwe _ (hJointLweClosed adversary hadversary))

/-- Conditional end-to-end theorem for distinct protocol noises related by convolution. The only
computational premises are direct bilinear bootstrapping KDM and conventional binary-secret batch
LWE with KSK noise on `keySwitchSamples + 1` rows. -/
theorem oneTimeHardAgainst_of_directBilinear_and_batchLwe_input_convolution
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler inputWideningSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bootstrapAllowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (batchLweAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels + 1) keySwitchErrorSampler) → Prop)
    (bootstrapBound batchLweBound : ℝ)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      inputErrorSampler keySwitchErrorSampler inputWideningSampler)
    (hWideningTotal : Pr[⊥ | inputWideningSampler] = 0)
    (hBootstrapClosed : ∀ adversary, allowed adversary →
      bootstrapAllowed (Encryption.oneTimeContinuation inputErrorSampler encode adversary))
    (hBatchLweClosed : ∀ adversary, allowed adversary →
      batchLweAllowed
        (FormalProof4FHE.LWE.TwoBlock.convolutionReduction
          (extraErrorSampler := inputWideningSampler)
          (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)))
    (hBootstrap : Native.BootstrapSecurity.DirectBilinearHardAgainst
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      bootstrapAllowed bootstrapBound)
    (hBatchLwe : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels + 1) keySwitchErrorSampler)
      batchLweAllowed batchLweBound) :
    OneTimeHardAgainst ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode allowed (bootstrapBound + batchLweBound) := by
  intro adversary hadversary
  calc
    |Encryption.signedAdvantage
        (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        Encryption.bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
              (keySwitchSamples ringRank degree keySwitchLevels + 1) keySwitchErrorSampler)
            (FormalProof4FHE.LWE.TwoBlock.convolutionReduction
              (extraErrorSampler := inputWideningSampler)
              (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
                tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) :=
      abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_input_convolution
        ringErrorSampler keySwitchErrorSampler inputErrorSampler inputWideningSampler
        tgswGadget keySwitchGadget encode adversary hConvolution hWideningTotal
    _ ≤ bootstrapBound + batchLweBound := add_le_add
      (by
        rw [bootstrapReplacementAdvantage_eq_directBilinear ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]
        exact hBootstrap _ (hBootstrapClosed adversary hadversary))
      (hBatchLwe _ (hBatchLweClosed adversary hadversary))

/-- Equal-noise specialization of the conditional theorem.  Its conventional computational
premise is ordinary binary-secret batch LWE on all KSK rows plus one challenge row. -/
theorem oneTimeHardAgainst_of_directBilinear_and_batchLwe_same_noise
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bootstrapAllowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (batchLweAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels + 1) errorSampler) → Prop)
    (bootstrapBound batchLweBound : ℝ)
    (hBootstrapClosed : ∀ adversary, allowed adversary →
      bootstrapAllowed (Encryption.oneTimeContinuation errorSampler encode adversary))
    (hBatchLweClosed : ∀ adversary, allowed adversary →
      batchLweAllowed
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
            tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)))
    (hBootstrap : Native.BootstrapSecurity.DirectBilinearHardAgainst
      ringErrorSampler errorSampler tgswGadget keySwitchGadget
      bootstrapAllowed bootstrapBound)
    (hBatchLwe : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels + 1) errorSampler)
      batchLweAllowed batchLweBound) :
    OneTimeHardAgainst ringErrorSampler errorSampler errorSampler
      tgswGadget keySwitchGadget encode allowed (bootstrapBound + batchLweBound) := by
  intro adversary hadversary
  calc
    |Encryption.signedAdvantage
        (Encryption.realGame ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        Encryption.bootstrapReplacementAdvantage ringErrorSampler errorSampler errorSampler
            tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
              (keySwitchSamples ringRank degree keySwitchLevels + 1) errorSampler)
            (FormalProof4FHE.LWE.TwoBlock.reduction
              (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
                tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) :=
      abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise
        ringErrorSampler errorSampler tgswGadget keySwitchGadget encode adversary
    _ ≤ bootstrapBound + batchLweBound := add_le_add
      (by
        rw [bootstrapReplacementAdvantage_eq_directBilinear ringErrorSampler
          errorSampler errorSampler tgswGadget keySwitchGadget encode adversary]
        exact hBootstrap _ (hBootstrapClosed adversary hadversary))
      (hBatchLwe _ (hBatchLweClosed adversary hadversary))

end NativeBootstrapComposition

end FormalProof4FHE.TFHE.Encryption.Security
