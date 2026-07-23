/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputSearch
import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteView

/-!
# Finite Augmented TFHE Search from Full-Transcript Circular Decision

The finite KSK-first reduction produces a scalar-key recovery solver on a polynomial batch of
same-secret BRK+KSK+input-tape views.  This module changes that remaining premise from search form
to decision form.

The real batch is compared with an independently sampled public batch.  For the recovery
continuation, generic auxiliary-input game hopping bounds real recovery by the corresponding
real-versus-uniform circular advantage plus recovery at the independent endpoint.  The latter is
exactly `1 / 2 ^ lweDimension`, for every solver.  Thus no search-hardness assumption is hidden in
the uniform baseline.

The decision problem here replaces the complete augmented view.  The subsequent
`AdaptiveKeySwitchFirstFiniteViewCircularDecomposition` and side-LWE modules give the sharper
alternative that separates the BRK-only circular term and compiles the retained KSK/input rows to
conventional scalar search LWE.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

open Native

variable
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds : ℕ} [NeZero q]

/-! ## Full-transcript circular problem -/

/-- Public batch sampler independent of both native secrets.  Independence, rather than a
particular implementation of a uniform product sampler, is the property needed for the exact
guessing bound. -/
noncomputable def independentBatch
    (rounds : ℕ) :
    ProbComp (Batch q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :=
  sampleBatch rounds
    ($ᵗ (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount))

/-- Auxiliary-input CircLWE problem whose real branch is the complete finite augmented TFHE
batch and whose uniform branch is independent of the scalar secret.  The ring key is sampled
inside the real challenge because the verifier recovers only the scalar key. -/
noncomputable def batchCircularProblem
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ) :
    LWE.AuxiliaryInput.Problem
      (BinarySecret lweDimension)
      (Batch q degree ringRank tgswLevels lweDimension
        keySwitchLevels queryCount rounds)
      Unit where
  sampleSecret := sampleLweSecret lweDimension
  sampleReal := fun lweSecret ↦ do
    let ringSecret ← sampleRingSecret ringRank degree
    sampleBatch rounds
      (fixedSecretView ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget (lweSecret, ringSecret))
  sampleZero := fun _ ↦ independentBatch rounds
  sampleUniform := independentBatch rounds
  sampleAuxiliary := fun _ ↦ pure ()

/-- Secret-aware continuation type used only by the experiment.  An admissible implementation
may use the secret for the final equality check without revealing it to its internal solver. -/
abbrev BatchCircularContinuation
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds : ℕ) :=
  BinarySecret lweDimension →
    Batch q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds →
      ProbComp Bool

/-- Package a batch continuation for the generic auxiliary-input interface. -/
def packBatchCircularContinuation
    (continuation : BatchCircularContinuation q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount rounds) :
    LWE.AuxiliaryInput.Continuation
      (BinarySecret lweDimension)
      (Batch q degree ringRank tgswLevels lweDimension
        keySwitchLevels queryCount rounds)
      Unit :=
  fun secret batch _ ↦ continuation secret batch

/-- Full-transcript real-versus-independent circular advantage. -/
noncomputable def batchCircularAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (continuation : BatchCircularContinuation q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount rounds) : ℝ :=
  LWE.AuxiliaryInput.circularLweAdvantage
    (batchCircularProblem ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds)
    (packBatchCircularContinuation continuation)

/-! ## Recovery continuation and exact baseline -/

/-- Use a public finite-batch solver and reserve the hidden scalar key solely for the final exact
recovery check. -/
def scalarRecoveryContinuation
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    BatchCircularContinuation q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds :=
  fun secret batch ↦ do
    let recovered ← solver batch
    return decide (recovered = secret)

/-- Adapt the public solver to the generic auxiliary-input search interface. -/
def toAuxiliarySolver
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LWE.AuxiliaryInput.Search.Solver
      (BinarySecret lweDimension)
      (Batch q degree ringRank tgswLevels lweDimension
        keySwitchLevels queryCount rounds)
      Unit :=
  fun batch _ ↦ solver batch

/-- The real branch of the generic exact-recovery problem is definitionally the existing finite
augmented scalar-search game. -/
theorem auxiliarySearchGame_eq_game
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LWE.AuxiliaryInput.Search.game
        (LWE.AuxiliaryInput.Search.exactRecoveryProblem
          (batchCircularProblem ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget rounds))
        (toAuxiliarySolver solver) =
      game ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds solver := by
  simp [LWE.AuxiliaryInput.Search.game,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem, batchCircularProblem,
    toAuxiliarySolver, game, secretSampler, bind_assoc, monad_norm]

omit [NeZero q] in
/-- The generic recovery continuation is the packaged scalar recovery continuation. -/
theorem recoveryContinuation_toAuxiliarySolver
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LWE.AuxiliaryInput.Search.recoveryContinuation (toAuxiliarySolver solver) =
      packBatchCircularContinuation (scalarRecoveryContinuation solver) := by
  rfl

/-- At the independent endpoint, every public solver recovers a uniform binary scalar key with
probability exactly `1 / 2 ^ lweDimension`. -/
theorem uniformRecoveryGame_probOutput_true_eq_inv_two_pow
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    Pr[= true |
        LWE.AuxiliaryInput.Search.uniformRecoveryGame
          (batchCircularProblem ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget rounds)
          (toAuxiliarySolver solver)] =
      ((2 : ENNReal) ^ lweDimension)⁻¹ := by
  have h := LWE.AuxiliaryInput.Search.probOutput_uniformSecret_recovery_eq_inv_card
    (Secret := BinarySecret lweDimension)
    (independentBatch (q := q) (degree := degree) (ringRank := ringRank)
      (tgswLevels := tgswLevels) (lweDimension := lweDimension)
      (keySwitchLevels := keySwitchLevels) (queryCount := queryCount) rounds)
    solver
  simpa [LWE.AuxiliaryInput.Search.uniformRecoveryGame,
    LWE.AuxiliaryInput.uniformGame, LWE.AuxiliaryInput.Search.recoveryContinuation,
    batchCircularProblem, toAuxiliarySolver, sampleLweSecret, bind_assoc, monad_norm,
    Fintype.card_fun] using h

/-! ## Finite decision-to-search bound -/

/-- **Finite full-transcript circular decision bound.** Scalar-key recovery from the real
augmented batch is bounded by one real-versus-independent circular distinguishing term and the
exact information-theoretic guessing probability. -/
theorem successProbability_le_batchCircularAdvantage_add_guess
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
          (batchCircularAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget rounds (scalarRecoveryContinuation solver)) +
        ((2 : ENNReal) ^ lweDimension)⁻¹ := by
  have h :=
    LWE.AuxiliaryInput.Search.successProbability_exactRecovery_le_circularLwe_add_uniform
      (batchCircularProblem ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds)
      (toAuxiliarySolver solver)
  rw [LWE.AuxiliaryInput.Search.successProbability] at h
  rw [auxiliarySearchGame_eq_game] at h
  rw [uniformRecoveryGame_probOutput_true_eq_inv_two_pow] at h
  simpa [successProbability, batchCircularAdvantage,
    recoveryContinuation_toAuxiliarySolver] using h

end FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView
