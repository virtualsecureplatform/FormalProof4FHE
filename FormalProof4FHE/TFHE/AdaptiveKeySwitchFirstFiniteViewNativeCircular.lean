/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputBatch
import FormalProof4FHE.Probability.MajorityBatchEquiv
import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteViewCircularDecomposition
import FormalProof4FHE.TFHE.MonomialKDMAuxiliaryInput

/-!
# Native CircLWE Reduction for Same-Secret Finite TFHE BRK Batches

The finite-view recovery proof uses many independently sampled BRK+KSK+input-tape views under one
fixed native key pair.  This module closes the gap between its BRK-only batch circular game and
the already defined one-challenge native auxiliary-input CircLWE game.

The reduction chooses one BRK coordinate uniformly, embeds the supplied native CircLWE challenge
there, places uniform BRKs before it and real same-secret BRKs after it, and samples all remaining
KSK and input-tape side information under the same hidden keys.  Exact majority-tree flattening
shows that this is the concrete finite batch consumed by recovery.  The resulting identity is

`BRK batch advantage = viewCount * native one-challenge CircLWE advantage`.

No ordinary-LWE claim is made for the intact circular challenge.  The theorem instead proves that
the earlier multi-view premise is the standard polynomial hybrid closure of the existing native
auxiliary-input CircLWE assumption.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

open Native

variable
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds : ℕ} [NeZero q]

/-- The one-view native CircLWE auxiliary input extended with the zero-message adaptive input
tape used by the finite recovery experiment. -/
abbrev CircularBatchAuxiliary
    (q ringRank degree lweDimension keySwitchLevels queryCount : ℕ) :=
  Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels ×
    KeySwitchFirstSecurity.InputTape q lweDimension queryCount

/-- Reassociate a BRK paired with `(KSK, tape)` into the public augmented-view layout. -/
def assembleCircularBatchView
    (view : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ×
      CircularBatchAuxiliary q ringRank degree lweDimension keySwitchLevels queryCount) :
    View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  ((view.1, view.2.1), view.2.2)

/-- Native auxiliary-input CircLWE with the input tape included in the per-view auxiliary input. -/
noncomputable def augmentedCircularProblem
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    LWE.AuxiliaryInput.Problem
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
        lweDimension ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (CircularBatchAuxiliary q ringRank degree lweDimension keySwitchLevels queryCount) where
  sampleSecret := secretSampler lweDimension ringRank degree
  sampleReal := fun secrets ↦
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      secrets.1 secrets.2
  sampleZero := fun secrets ↦
    Native.generateZeroBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget secrets.2
  sampleUniform :=
    $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
  sampleAuxiliary := fun secrets ↦ do
    let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
      keySwitchLevels keySwitchErrorSampler keySwitchGadget
      (keyExtract secrets.2) secrets.1
    let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret secrets.1) 0
    return (keySwitchKey, tape)

/-- Extend a continuation for `(KSK, tape)` auxiliary input to the existing native one-KSK
auxiliary-input problem by sampling the tape inside the experiment. -/
def addInputTapeContinuation
    (inputErrorSampler : ProbComp (ZMod q))
    (continuation : LWE.AuxiliaryInput.Continuation
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
        lweDimension ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (CircularBatchAuxiliary q ringRank degree lweDimension keySwitchLevels queryCount)) :
    Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
  fun lweSecret ringSecret bootstrapKey keySwitchKey ↦ do
    let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret lweSecret) 0
    continuation (lweSecret, ringSecret) bootstrapKey (keySwitchKey, tape)

/-- Adding the input tape to the auxiliary record does not change the underlying native
one-challenge CircLWE advantage. -/
theorem augmentedCircularLweAdvantage_eq_native
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : LWE.AuxiliaryInput.Continuation
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
        lweDimension ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (CircularBatchAuxiliary q ringRank degree lweDimension keySwitchLevels queryCount)) :
    LWE.AuxiliaryInput.circularLweAdvantage
        (augmentedCircularProblem ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget)
        continuation =
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.circularLweAdvantage
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (addInputTapeContinuation inputErrorSampler continuation) := by
  unfold LWE.AuxiliaryInput.circularLweAdvantage
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.circularLweAdvantage
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.packContinuation
  congr 1 <;>
    simp [LWE.AuxiliaryInput.realGame, LWE.AuxiliaryInput.uniformGame,
      augmentedCircularProblem,
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.problem,
      addInputTapeContinuation, secretSampler, bind_assoc, monad_norm]

/-! ## One-view distribution alignments -/

/-- The monomial native real challenge plus augmented side information is exactly the executable
native augmented view after deterministic reassociation. -/
theorem augmentedRealView_evalDist_eq_fixedSecretView
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    evalDist (assembleCircularBatchView (queryCount := queryCount) <$>
      LWE.AuxiliaryInput.Batch.realView
        (augmentedCircularProblem (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget) secrets) =
      evalDist (fixedSecretView (queryCount := queryCount)
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget secrets) := by
  have hbootstrap :
      evalDist (Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
        secrets.1 secrets.2) =
      evalDist (Native.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
        secrets.1 secrets.2) := by
    rw [Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct]
    exact (Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      secrets.1 secrets.2).symm
  rw [map_eq_bind_pure_comp]
  simp only [LWE.AuxiliaryInput.Batch.realView, augmentedCircularProblem,
    bind_assoc, pure_bind, Function.comp_apply]
  change evalDist (do
      let bootstrapKey ←
        Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
          q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
          secrets.1 secrets.2
      let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract secrets.2) secrets.1
      let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret secrets.1) 0
      return ((bootstrapKey, keySwitchKey), tape)) =
    evalDist (do
      let bootstrapKey ← Native.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
        secrets.1 secrets.2
      let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract secrets.2) secrets.1
      let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret secrets.1) 0
      return ((bootstrapKey, keySwitchKey), tape))
  rw [evalDist_bind, evalDist_bind, hbootstrap]

/-- The augmented uniform challenge is definitionally the uniform-BRK/real-KSK-and-tape view. -/
theorem augmentedUniformView_evalDist_eq_fixedUniformBootstrapView
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    evalDist (assembleCircularBatchView (queryCount := queryCount) <$>
      LWE.AuxiliaryInput.Batch.uniformView
        (augmentedCircularProblem (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget) secrets) =
      evalDist (fixedUniformBootstrapView (queryCount := queryCount)
        (tgswLevels := tgswLevels)
        keySwitchErrorSampler inputErrorSampler
        keySwitchGadget secrets) := by
  rw [map_eq_bind_pure_comp]
  simp only [LWE.AuxiliaryInput.Batch.uniformView, augmentedCircularProblem,
    bind_assoc, pure_bind, Function.comp_apply]
  rfl

/-! ## Exact flat-batch alignment -/

/-- Recovery continuation on the flat vector used by the generic batching theorem. -/
def flatCircularRecoveryContinuation
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LWE.AuxiliaryInput.Batch.BatchContinuation
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
        lweDimension ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (CircularBatchAuxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
      (viewCount lweDimension rounds) :=
  fun secrets views ↦ do
    let recovered ← solver
      ((FormalProof4FHE.MajorityAmplification.vectorMajorityBatchEquiv
        (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
        lweDimension rounds).symm
        (fun index ↦ assembleCircularBatchView (queryCount := queryCount) (views index)))
    return decide (recovered = secrets.1)

/-- Mapping and flattening an IID augmented real batch gives the concrete majority-tree batch. -/
theorem augmentedRealBatch_bind_evalDist_eq_sampleBatch
    {Output : Type}
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (postprocess : Batch q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds → ProbComp Output) :
    evalDist (Fin.mOfFn (viewCount lweDimension rounds)
        (fun _ ↦ LWE.AuxiliaryInput.Batch.realView
          (augmentedCircularProblem (queryCount := queryCount)
            ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget) secrets) >>= fun views ↦
      postprocess
        ((FormalProof4FHE.MajorityAmplification.vectorMajorityBatchEquiv
          (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
          lweDimension rounds).symm
          (fun index ↦ assembleCircularBatchView (queryCount := queryCount) (views index)))) =
      evalDist (sampleBatch rounds
        (fixedSecretView (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget secrets) >>= postprocess) := by
  let count := viewCount lweDimension rounds
  let augmentedSampler := LWE.AuxiliaryInput.Batch.realView
    (augmentedCircularProblem (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget) secrets
  let nativeSampler := fixedSecretView (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget secrets
  let assembleVector := fun views : Fin count →
      Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ×
        CircularBatchAuxiliary q ringRank degree lweDimension keySwitchLevels queryCount ↦
    fun index ↦ assembleCircularBatchView (queryCount := queryCount) (views index)
  let flatPostprocess := fun views : Fin count →
      View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ↦
    postprocess
      ((FormalProof4FHE.MajorityAmplification.vectorMajorityBatchEquiv
        (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
        lweDimension rounds).symm views)
  have hmap := FormalProof4FHE.FiniteProduct.map_fin_mOfFn_const
    count augmentedSampler (assembleCircularBatchView (queryCount := queryCount))
  have hcoordinate :
      evalDist (assembleCircularBatchView (queryCount := queryCount) <$> augmentedSampler) =
        evalDist nativeSampler := by
    exact augmentedRealView_evalDist_eq_fixedSecretView
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget secrets
  have hproduct := FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
    count
    (fun _ ↦ assembleCircularBatchView (queryCount := queryCount) <$> augmentedSampler)
    (fun _ ↦ nativeSampler)
    (fun _ ↦ hcoordinate)
  have hflatten :=
    FormalProof4FHE.MajorityAmplification.evalDist_sampleVectorMajorityBatch_bind_eq_flat
      lweDimension rounds nativeSampler postprocess
  calc
    _ = evalDist ((assembleVector <$> Fin.mOfFn count (fun _ ↦ augmentedSampler)) >>=
          flatPostprocess) := by
        rw [evalDist_bind, evalDist_bind, evalDist_map]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        apply bind_congr
        intro views
        rfl
    _ = evalDist (Fin.mOfFn count
          (fun _ ↦ assembleCircularBatchView (queryCount := queryCount) <$> augmentedSampler) >>=
          flatPostprocess) := by rw [hmap]
    _ = evalDist (Fin.mOfFn count (fun _ ↦ nativeSampler) >>=
          flatPostprocess) := by
        rw [evalDist_bind, evalDist_bind, hproduct]
    _ = _ := by
      simpa [count, nativeSampler, flatPostprocess, sampleBatch, viewCount] using hflatten.symm

/-- Mapping and flattening an IID augmented uniform batch gives the concrete uniform-BRK
majority-tree batch. -/
theorem augmentedUniformBatch_bind_evalDist_eq_sampleBatch
    {Output : Type}
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (postprocess : Batch q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds → ProbComp Output) :
    evalDist (Fin.mOfFn (viewCount lweDimension rounds)
        (fun _ ↦ LWE.AuxiliaryInput.Batch.uniformView
          (augmentedCircularProblem (queryCount := queryCount)
            ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget) secrets) >>= fun views ↦
      postprocess
        ((FormalProof4FHE.MajorityAmplification.vectorMajorityBatchEquiv
          (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
          lweDimension rounds).symm
          (fun index ↦ assembleCircularBatchView (queryCount := queryCount) (views index)))) =
      evalDist (sampleBatch rounds
        (fixedUniformBootstrapView (queryCount := queryCount)
          (tgswLevels := tgswLevels)
          keySwitchErrorSampler inputErrorSampler
          keySwitchGadget secrets) >>= postprocess) := by
  let count := viewCount lweDimension rounds
  let augmentedSampler := LWE.AuxiliaryInput.Batch.uniformView
    (augmentedCircularProblem (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget) secrets
  let nativeSampler := fixedUniformBootstrapView (queryCount := queryCount)
    (tgswLevels := tgswLevels)
    keySwitchErrorSampler inputErrorSampler
    keySwitchGadget secrets
  let assembleVector := fun views : Fin count →
      Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ×
        CircularBatchAuxiliary q ringRank degree lweDimension keySwitchLevels queryCount ↦
    fun index ↦ assembleCircularBatchView (queryCount := queryCount) (views index)
  let flatPostprocess := fun views : Fin count →
      View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ↦
    postprocess
      ((FormalProof4FHE.MajorityAmplification.vectorMajorityBatchEquiv
        (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
        lweDimension rounds).symm views)
  have hmap := FormalProof4FHE.FiniteProduct.map_fin_mOfFn_const
    count augmentedSampler (assembleCircularBatchView (queryCount := queryCount))
  have hcoordinate :
      evalDist (assembleCircularBatchView (queryCount := queryCount) <$> augmentedSampler) =
        evalDist nativeSampler := by
    exact augmentedUniformView_evalDist_eq_fixedUniformBootstrapView
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget secrets
  have hproduct := FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
    count
    (fun _ ↦ assembleCircularBatchView (queryCount := queryCount) <$> augmentedSampler)
    (fun _ ↦ nativeSampler)
    (fun _ ↦ hcoordinate)
  have hflatten :=
    FormalProof4FHE.MajorityAmplification.evalDist_sampleVectorMajorityBatch_bind_eq_flat
      lweDimension rounds nativeSampler postprocess
  calc
    _ = evalDist ((assembleVector <$> Fin.mOfFn count (fun _ ↦ augmentedSampler)) >>=
          flatPostprocess) := by
        rw [evalDist_bind, evalDist_bind, evalDist_map]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        apply bind_congr
        intro views
        rfl
    _ = evalDist (Fin.mOfFn count
          (fun _ ↦ assembleCircularBatchView (queryCount := queryCount) <$> augmentedSampler) >>=
          flatPostprocess) := by rw [hmap]
    _ = evalDist (Fin.mOfFn count (fun _ ↦ nativeSampler) >>=
          flatPostprocess) := by
        rw [evalDist_bind, evalDist_bind, hproduct]
    _ = _ := by
      simpa [count, nativeSampler, flatPostprocess, sampleBatch, viewCount] using hflatten.symm

/-! ## Batch advantage as one native CircLWE call -/

/-- The real endpoint of the generic flat batch is the existing finite augmented recovery game. -/
theorem augmentedBatchRealGame_evalDist_eq_game
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    evalDist (LWE.AuxiliaryInput.Batch.hybridGame
      (augmentedCircularProblem ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget)
      (viewCount lweDimension rounds) 0
      (flatCircularRecoveryContinuation rounds solver)) =
      evalDist (game ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds solver) := by
  simp only [LWE.AuxiliaryInput.Batch.hybridGame, augmentedCircularProblem,
    flatCircularRecoveryContinuation, Nat.not_lt_zero, ↓reduceIte, game]
  apply evalDist_bind_congr' (secretSampler lweDimension ringRank degree)
  intro secrets
  exact augmentedRealBatch_bind_evalDist_eq_sampleBatch
    ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget secrets
    (fun batch ↦ do
      let recovered ← solver batch
      return decide (recovered = secrets.1))

/-- The all-uniform endpoint of the generic flat batch is the existing uniform-BRK recovery
game. -/
theorem augmentedBatchUniformGame_evalDist_eq_recoveryGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    evalDist (LWE.AuxiliaryInput.Batch.hybridGame
      (augmentedCircularProblem ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget)
      (viewCount lweDimension rounds) (viewCount lweDimension rounds)
      (flatCircularRecoveryContinuation rounds solver)) =
      evalDist (uniformBootstrapRecoveryGame keySwitchErrorSampler inputErrorSampler
        keySwitchGadget rounds solver) := by
  simp only [LWE.AuxiliaryInput.Batch.hybridGame, augmentedCircularProblem,
    flatCircularRecoveryContinuation, Fin.isLt, ↓reduceIte,
    uniformBootstrapRecoveryGame]
  apply evalDist_bind_congr' (secretSampler lweDimension ringRank degree)
  intro secrets
  exact augmentedUniformBatch_bind_evalDist_eq_sampleBatch
    ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget secrets
    (fun batch ↦ do
      let recovered ← solver batch
      return decide (recovered = secrets.1))

/-- The concrete BRK-only circular term is exactly the generic same-secret batch advantage. -/
theorem bootstrapBatchCircularAdvantage_eq_augmentedBatch
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    bootstrapBatchCircularAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget rounds solver =
      LWE.AuxiliaryInput.Batch.advantage
        (augmentedCircularProblem ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget)
        (viewCount lweDimension rounds)
        (flatCircularRecoveryContinuation rounds solver) := by
  unfold bootstrapBatchCircularAdvantage LWE.AuxiliaryInput.Batch.advantage
    ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (augmentedBatchRealGame_evalDist_eq_game
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds solver).symm,
    probOutput_congr rfl
      (augmentedBatchUniformGame_evalDist_eq_recoveryGame
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds solver).symm]

theorem viewCount_ne_zero [NeZero lweDimension] (rounds : ℕ) :
    viewCount lweDimension rounds ≠ 0 := by
  rw [viewCount_eq]
  exact Nat.mul_ne_zero (NeZero.ne lweDimension) (pow_ne_zero _ (by norm_num))

/-- The concrete one-challenge native CircLWE continuation produced by the randomized batch
hybrid. -/
noncomputable def nativeCircularBatchReduction [NeZero lweDimension]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) := by
  letI : NeZero (viewCount lweDimension rounds) := ⟨viewCount_ne_zero rounds⟩
  exact addInputTapeContinuation inputErrorSampler
    (LWE.AuxiliaryInput.Batch.randomHybridContinuation
      (augmentedCircularProblem ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget)
      (viewCount lweDimension rounds)
      (flatCircularRecoveryContinuation rounds solver))

/-- **Finite native CircLWE batching identity.**  The full same-secret BRK-batch replacement
advantage is the exact view count times one existing native auxiliary-input CircLWE advantage. -/
theorem bootstrapBatchCircularAdvantage_eq_viewCount_mul_nativeCircularLwe
    [NeZero lweDimension]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    bootstrapBatchCircularAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget rounds solver =
      (viewCount lweDimension rounds : ℝ) *
        Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.circularLweAdvantage
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          (nativeCircularBatchReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget rounds solver) := by
  letI : NeZero (viewCount lweDimension rounds) := ⟨viewCount_ne_zero rounds⟩
  rw [bootstrapBatchCircularAdvantage_eq_augmentedBatch]
  rw [LWE.AuxiliaryInput.Batch.advantage_eq_card_mul_randomHybrid]
  rw [augmentedCircularLweAdvantage_eq_native]
  rfl

end FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView
