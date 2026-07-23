/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteViewCircular

/-!
# Separating the BRK-Circular and Scalar-Search Parts of Finite TFHE Recovery

The full-transcript decision normalization replaces an entire augmented BRK+KSK+input-tape
batch at once.  This module inserts the more informative intermediate distribution in which
only every bootstrapping key is uniform.  The key-switch keys and input tapes remain real and
share the hidden scalar key.

Exact scalar recovery is consequently bounded by:

1. a same-secret multi-view BRK real-versus-uniform circular advantage; and
2. scalar-key recovery after the BRKs have become independent public randomness.

The second experiment is packaged as an ordinary auxiliary-randomness search problem.  Its
solver receives no hidden key: the uniformly sampled BRKs are merely public coins, while all
remaining secret dependence is in direct TLWE KSK and input-tape rows.  A later module can
flatten those rows to a conventional scalar search-LWE transcript.

This separation is necessary for sound information flow.  The experiment may use the hidden
key for its final equality check, but an ordinary decisional-LWE adversary cannot do so.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

open Native

variable
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds : ℕ} [NeZero q]

/-! ## Uniform-BRK intermediate -/

/-- One augmented view with an independent uniform BRK but a real KSK and real zero-message
input tape under the supplied hidden keys. -/
noncomputable def fixedUniformBootstrapView
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    ProbComp (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let bootstrapKey ←
    $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
  let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
    keySwitchLevels keySwitchErrorSampler keySwitchGadget
    (keyExtract secrets.2) secrets.1
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  return ((bootstrapKey, keySwitchKey), tape)

/-- Exact scalar-recovery experiment at the uniform-BRK/real-KSK-and-tape intermediate. -/
noncomputable def uniformBootstrapRecoveryGame
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) : ProbComp Bool := do
  let secrets ← secretSampler lweDimension ringRank degree
  let batch ← sampleBatch rounds
    (fixedUniformBootstrapView keySwitchErrorSampler inputErrorSampler
      keySwitchGadget secrets)
  let recovered ← solver batch
  return decide (recovered = secrets.1)

/-- Same-secret multi-view circular advantage for replacing only the BRKs.  Real KSK and input
tape side information is retained identically at both endpoints. -/
noncomputable def bootstrapBatchCircularAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) : ℝ :=
  (game ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds solver).boolDistAdvantage
    (uniformBootstrapRecoveryGame keySwitchErrorSampler inputErrorSampler
      keySwitchGadget rounds solver)

/-! ## Uniform-BRK endpoint as scalar search -/

/-- Scalar-key search problem whose public challenge has uniform BRKs and real same-secret KSK
and input-tape rows.  The ring key is independent auxiliary randomness sampled inside the
challenge generator. -/
noncomputable def uniformBootstrapSideSearchProblem
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ) :
    LWE.AuxiliaryInput.Search.Problem
      (BinarySecret lweDimension)
      (Batch q degree ringRank tgswLevels lweDimension
        keySwitchLevels queryCount rounds)
      Unit where
  sampleSecret := sampleLweSecret lweDimension
  sampleChallenge := fun lweSecret ↦ do
    let ringSecret ← sampleRingSecret ringRank degree
    sampleBatch rounds
      (fixedUniformBootstrapView keySwitchErrorSampler inputErrorSampler
        keySwitchGadget (lweSecret, ringSecret))
  sampleAuxiliary := fun _ ↦ pure ()
  verify := fun secret recovered ↦ decide (recovered = secret)

/-- Regard an existing augmented-batch solver as a solver for the uniform-BRK side problem. -/
def toUniformBootstrapSideSolver
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LWE.AuxiliaryInput.Search.Solver
      (BinarySecret lweDimension)
      (Batch q degree ringRank tgswLevels lweDimension
        keySwitchLevels queryCount rounds)
      Unit :=
  fun batch _ ↦ solver batch

/-- The packaged scalar-search experiment is exactly the uniform-BRK recovery endpoint. -/
theorem uniformBootstrapSideSearchGame_eq_recoveryGame
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LWE.AuxiliaryInput.Search.game
        (uniformBootstrapSideSearchProblem keySwitchErrorSampler inputErrorSampler
          keySwitchGadget rounds)
        (toUniformBootstrapSideSolver solver) =
      uniformBootstrapRecoveryGame keySwitchErrorSampler inputErrorSampler
        keySwitchGadget rounds solver := by
  simp [LWE.AuxiliaryInput.Search.game, uniformBootstrapSideSearchProblem,
    toUniformBootstrapSideSolver, uniformBootstrapRecoveryGame, secretSampler,
    bind_assoc, monad_norm]

/-! ## BRK circularity plus standard scalar search -/

/-- **Finite BRK/side separation.** Recovery from the real augmented batch is bounded by the
BRK-only multi-view circular replacement advantage plus exact scalar recovery from the remaining
direct TLWE KSK and input-tape rows. -/
theorem successProbability_le_bootstrapBatchCircular_add_sideSearch
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds solver ≤
      ENNReal.ofReal
          (bootstrapBatchCircularAdvantage ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget rounds solver) +
        LWE.AuxiliaryInput.Search.successProbability
          (uniformBootstrapSideSearchProblem keySwitchErrorSampler inputErrorSampler
            keySwitchGadget rounds)
          (toUniformBootstrapSideSolver solver) := by
  have h := ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
    (game ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds solver)
    (uniformBootstrapRecoveryGame keySwitchErrorSampler inputErrorSampler
      keySwitchGadget rounds solver)
  simpa [successProbability, bootstrapBatchCircularAdvantage,
    LWE.AuxiliaryInput.Search.successProbability,
    uniformBootstrapSideSearchGame_eq_recoveryGame, add_comm] using h

end FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView
