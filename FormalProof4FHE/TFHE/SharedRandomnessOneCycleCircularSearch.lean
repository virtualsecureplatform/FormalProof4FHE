/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputSearch
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAuxiliaryInput

/-!
# Exact Search Experiment for Shared-Randomness One-Cycle TFHE

This module instantiates auxiliary-input circular search with the exact shared-master-secret TFHE
distribution.  A public solver receives the native self-circular BRK and the correlated real
suffix-only KSK and must recover the complete rank-one master ring key.

The search game is proved equal to the native secret-continuation real game, and its fixed-secret
challenge is aligned with the explicit degree-two self-monomial BRK presentation.  The uniform-
BRK recovery endpoint is kept explicit because it still contains the real suffix KSK.  Replacing
that KSK by an independent uniform transcript leaves an exactly independent public view, whose
master-key recovery probability is proved to be `2^-(prefixDimension + suffixDimension)`.

These statements provide the search endpoint needed by a PKC-2024-style search-to-decision
argument.  They do not assume that the remaining shifted-function evaluator exists.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.AuxiliaryInput.Search

noncomputable section

abbrev Secret (prefixDimension suffixDimension : ℕ) :=
  AuxiliaryInput.Secret prefixDimension suffixDimension

abbrev Challenge
    (q prefixDimension suffixDimension tgswLevels : ℕ) :=
  AuxiliaryInput.Challenge q prefixDimension suffixDimension tgswLevels

abbrev Auxiliary
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) :=
  AuxiliaryInput.Auxiliary q prefixDimension suffixDimension keySwitchLevels

/-- A public one-cycle solver sees the BRK and real suffix KSK, but not the master key. -/
abbrev Solver
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :=
  LWE.AuxiliaryInput.Search.Solver
    (Secret prefixDimension suffixDimension)
    (Challenge q prefixDimension suffixDimension tgswLevels)
    (Auxiliary q prefixDimension suffixDimension keySwitchLevels)

/-- Exact master-key recovery problem derived from the real one-cycle CircLWE branch. -/
noncomputable def problem
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    LWE.AuxiliaryInput.Search.Problem
      (Secret prefixDimension suffixDimension)
      (Challenge q prefixDimension suffixDimension tgswLevels)
      (Auxiliary q prefixDimension suffixDimension keySwitchLevels) :=
  LWE.AuxiliaryInput.Search.exactRecoveryProblem
    (AuxiliaryInput.problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)

/-- The exact shared-master-secret recovery experiment. -/
noncomputable def game
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool :=
  LWE.AuxiliaryInput.Search.game
    (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    solver

/-- Public solver followed only by the experiment's secret-aware exact-recovery check. -/
def nativeRecoveryContinuation
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    Native.SharedRandomnessOneCycle.SecretContinuation q prefixDimension suffixDimension
      tgswLevels keySwitchLevels :=
  fun masterSecret bootstrappingKey keySwitchKey ↦ do
    let recovered ← solver bootstrappingKey keySwitchKey
    return decide (recovered = masterSecret)

/-- The search experiment is exactly the generic one-cycle auxiliary-input real game. -/
theorem game_eq_auxiliaryRealGame
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    game ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget solver =
      LWE.AuxiliaryInput.realGame
        (AuxiliaryInput.problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (LWE.AuxiliaryInput.Search.recoveryContinuation solver) := by
  simpa [game, problem] using
    (LWE.AuxiliaryInput.Search.game_exactRecoveryProblem_eq_realGame
      (AuxiliaryInput.problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      solver)

/-- The exact search game is also the native one-cycle real secret-continuation game. -/
theorem game_eq_nativeRealSecretContinuationGame
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    game ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget solver =
      Native.SharedRandomnessOneCycle.realSecretContinuationGame q prefixDimension
        suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget (nativeRecoveryContinuation solver) := by
  rw [game_eq_auxiliaryRealGame]
  change LWE.AuxiliaryInput.realGame
      (AuxiliaryInput.problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (AuxiliaryInput.packContinuation (nativeRecoveryContinuation solver)) = _
  exact AuxiliaryInput.realGame_eq_native
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    (nativeRecoveryContinuation solver)

/-- Exact success probability of a shared-master-secret recovery solver. -/
noncomputable def successProbability
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ENNReal :=
  LWE.AuxiliaryInput.Search.successProbability
    (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    solver

/-! ## Exact native and monomial fixed-secret views -/

/-- Real BRK and suffix KSK at one fixed master secret. -/
noncomputable def fixedSecretRealView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (masterSecret : Secret prefixDimension suffixDimension) :
    ProbComp
      (Challenge q prefixDimension suffixDimension tgswLevels ×
        Auxiliary q prefixDimension suffixDimension keySwitchLevels) := do
  let bootstrappingKey ←
    (AuxiliaryInput.problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleReal
      masterSecret
  let keySwitchKey ←
    (AuxiliaryInput.problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary
      masterSecret
  return (bootstrappingKey, keySwitchKey)

/-- At every fixed master secret, the real search view has the explicit native degree-two
self-monomial BRK distribution with the identical real suffix KSK. -/
theorem fixedSecretRealView_evalDist_eq_selfMonomial
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (masterSecret : Secret prefixDimension suffixDimension) :
    evalDist (fixedSecretRealView q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      masterSecret) =
      evalDist (do
        let bootstrappingKey ←
          Native.SharedRandomnessOneCycle.generateSelfMonomialBootstrappingKey q
            prefixDimension suffixDimension tgswLevels ringErrorSampler tgswGadget
            masterSecret
        let keySwitchKey ←
          Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
            suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget
            masterSecret
        return (bootstrappingKey, keySwitchKey)) := by
  unfold fixedSecretRealView AuxiliaryInput.problem
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (Native.SharedRandomnessOneCycle.generateBootstrappingKey_evalDist_eq_selfMonomial
      q prefixDimension suffixDimension tgswLevels ringErrorSampler tgswGadget
      masterSecret)
    (fun bootstrappingKey ↦
      Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
          suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget
          masterSecret >>= fun keySwitchKey ↦
        pure (bootstrappingKey, keySwitchKey))

/-! ## Uniform-BRK recovery baseline -/

/-- Recovery at the generic uniform-BRK endpoint; the real correlated suffix KSK remains. -/
noncomputable def uniformRecoveryGame
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool :=
  LWE.AuxiliaryInput.Search.uniformRecoveryGame
    (AuxiliaryInput.problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    solver

/-- The generic uniform recovery endpoint is exactly the native uniform-BRK continuation. -/
theorem uniformRecoveryGame_eq_native
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    uniformRecoveryGame ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget solver =
      Native.SharedRandomnessOneCycle.AuxiliaryInput.uniformSecretContinuationGame q
        prefixDimension suffixDimension tgswLevels keySwitchLevels keySwitchErrorSampler
        keySwitchGadget (nativeRecoveryContinuation solver) := by
  unfold uniformRecoveryGame LWE.AuxiliaryInput.Search.uniformRecoveryGame
  change LWE.AuxiliaryInput.uniformGame
      (AuxiliaryInput.problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (AuxiliaryInput.packContinuation (nativeRecoveryContinuation solver)) = _
  exact AuxiliaryInput.uniformGame_eq_native
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    (nativeRecoveryContinuation solver)

/-- Exact generic decomposition of one-cycle search success into CircLWE advantage and recovery
at the uniform-BRK, real-KSK endpoint. -/
theorem successProbability_le_circularLwe_add_uniformRecovery
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    successProbability ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        solver ≤
      ENNReal.ofReal
          (AuxiliaryInput.circularLweAdvantage ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget
            (LWE.AuxiliaryInput.Search.recoveryContinuation solver)) +
        Pr[= true | uniformRecoveryGame ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget solver] := by
  exact LWE.AuxiliaryInput.Search.successProbability_exactRecovery_le_circularLwe_add_uniform
    (AuxiliaryInput.problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    solver

/-! ## Fully independent public endpoint -/

/-- Uniform BRK and uniform KSK endpoint.  The entire public view is independent of the master
secret, so exact recovery has the information-theoretic guessing probability. -/
noncomputable def fullyUniformRecoveryGame
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool := do
  let masterSecret ← $ᵗ (Secret prefixDimension suffixDimension)
  let bootstrappingKey ← $ᵗ (Challenge q prefixDimension suffixDimension tgswLevels)
  let keySwitchKey ← $ᵗ (Auxiliary q prefixDimension suffixDimension keySwitchLevels)
  let recovered ← solver bootstrappingKey keySwitchKey
  return decide (recovered = masterSecret)

/-- The rank-one master binary secret has exactly `2^(prefixDimension + suffixDimension)`
elements. -/
theorem card_secret (prefixDimension suffixDimension : ℕ) :
    Fintype.card (Secret prefixDimension suffixDimension) =
      2 ^ (prefixDimension + suffixDimension) := by
  change Fintype.card (Fin 1 → Fin (prefixDimension + suffixDimension) → Bool) = _
  simp

/-- At the fully uniform public endpoint, every solver recovers the master key with probability
exactly `2^-(prefixDimension + suffixDimension)`. -/
theorem probOutput_fullyUniformRecoveryGame_true
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    Pr[= true | fullyUniformRecoveryGame solver] =
      ((2 ^ (prefixDimension + suffixDimension) : ℕ) : ENNReal)⁻¹ := by
  let Public :=
    Challenge q prefixDimension suffixDimension tgswLevels ×
      Auxiliary q prefixDimension suffixDimension keySwitchLevels
  let publicView : ProbComp Public := do
    let bootstrappingKey ← $ᵗ (Challenge q prefixDimension suffixDimension tgswLevels)
    let keySwitchKey ← $ᵗ (Auxiliary q prefixDimension suffixDimension keySwitchLevels)
    return (bootstrappingKey, keySwitchKey)
  have h := LWE.AuxiliaryInput.Search.probOutput_uniformSecret_recovery_eq_inv_card
    (Secret := Secret prefixDimension suffixDimension)
    publicView (fun view ↦ solver view.1 view.2)
  rw [card_secret prefixDimension suffixDimension] at h
  simpa [fullyUniformRecoveryGame, publicView, Public, bind_assoc, monad_norm] using h

/-! ## Uniform-BRK recovery as shared-KSK search LWE -/

/-- Splitting a recovered master key gives a key pair exactly when that master key is the
corresponding nested key. -/
@[simp]
theorem splitNestedSecret_eq_iff
    {prefixDimension suffixDimension : ℕ}
    (masterSecret : Secret prefixDimension suffixDimension)
    (keys : BinarySecret prefixDimension × BinarySecret suffixDimension) :
    Native.SharedRandomnessOneCycle.splitNestedSecret masterSecret = keys ↔
      masterSecret = Native.SharedRandomnessOneCycle.nestedRingSecret keys.1 keys.2 := by
  constructor
  · intro h
    rw [← h]
    exact (Native.SharedRandomnessOneCycle.nestedRingSecret_prefix_suffix
      masterSecret).symm
  · intro h
    subst masterSecret
    simp [Native.SharedRandomnessOneCycle.splitNestedSecret]

/-- Splitting the master key is injective. -/
theorem splitNestedSecret_injective (prefixDimension suffixDimension : ℕ) :
    Function.Injective
      (Native.SharedRandomnessOneCycle.splitNestedSecret
        (prefixDimension := prefixDimension) (suffixDimension := suffixDimension)) :=
  (Native.SharedRandomnessOneCycle.nestedSecretEquiv
    prefixDimension suffixDimension).injective

@[simp]
theorem splitNestedSecret_eq_splitNestedSecret_iff
    {prefixDimension suffixDimension : ℕ}
    (left right : Secret prefixDimension suffixDimension) :
    Native.SharedRandomnessOneCycle.splitNestedSecret left =
        Native.SharedRandomnessOneCycle.splitNestedSecret right ↔
      left = right :=
  (splitNestedSecret_injective prefixDimension suffixDimension).eq_iff

@[simp]
theorem masterSecret_eq_iff_prefix_suffix_eq
    {prefixDimension suffixDimension : ℕ}
    (left right : Secret prefixDimension suffixDimension) :
    left = right ↔
      Native.SharedRandomnessOneCycle.prefixSecret left =
          Native.SharedRandomnessOneCycle.prefixSecret right ∧
        Native.SharedRandomnessOneCycle.suffixSecret left =
          Native.SharedRandomnessOneCycle.suffixSecret right := by
  constructor
  · intro h
    subst right
    exact ⟨rfl, rfl⟩
  · rintro ⟨hprefix, hsuffix⟩
    apply splitNestedSecret_injective prefixDimension suffixDimension
    exact Prod.ext hprefix hsuffix

/-- Turn a master-key solver into a search adversary for the exact affine suffix-KSK LWE
problem.  The independent uniform BRK is sampled as internal public randomness. -/
noncomputable def keySwitchSearchReduction
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LearningWithErrors.SearchAdversary
      (Native.SharedRandomnessOneCycle.sharedKeySwitchProblem q prefixDimension
        suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget) :=
  fun keySwitchKey ↦ do
    let bootstrappingKey ←
      $ᵗ (Challenge q prefixDimension suffixDimension tgswLevels)
    let recovered ← solver bootstrappingKey keySwitchKey
    return Native.SharedRandomnessOneCycle.splitNestedSecret recovered

/-- The uniform-BRK, real-suffix-KSK recovery endpoint is exactly the search experiment for the
affine shared-KSK LWE problem.  Thus this endpoint contains no circular BRK assumption. -/
theorem uniformRecoveryGame_evalDist_eq_keySwitchSearchExperiment
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    evalDist (uniformRecoveryGame ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget solver) =
      evalDist (LearningWithErrors.searchExperiment
        (Native.SharedRandomnessOneCycle.sharedKeySwitchProblem q prefixDimension
          suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget)
        (keySwitchSearchReduction keySwitchErrorSampler keySwitchGadget solver)) := by
  let samples := suffixDimension * keySwitchLevels
  let Keys := BinarySecret prefixDimension × BinarySecret suffixDimension
  let Bootstrap := Challenge q prefixDimension suffixDimension tgswLevels
  let KeySwitchChallenge := Matrix (Fin prefixDimension) (Fin samples) (ZMod q)
  let KeySwitchError := Fin samples → ZMod q
  let splitSampler : ProbComp Keys := do
    let masterSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
    return Native.SharedRandomnessOneCycle.splitNestedSecret masterSecret
  let keysSampler : ProbComp Keys := do
    let prefixKey ← Native.sampleLweSecret prefixDimension
    let suffixKey ← Native.sampleLweSecret suffixDimension
    return (prefixKey, suffixKey)
  let bootstrappingKeys : ProbComp Bootstrap := $ᵗ Bootstrap
  let challenges : ProbComp KeySwitchChallenge := $ᵗ KeySwitchChallenge
  let errors : ProbComp KeySwitchError :=
    ProbComp.sampleIID samples keySwitchErrorSampler
  let finish := fun (keys : Keys) (bootstrappingKey : Bootstrap)
      (challenge : KeySwitchChallenge) (error : KeySwitchError) ↦ do
    let recovered ← solver bootstrappingKey
      (TLWE.batchAssemble (embedBinarySecret keys.1) challenge
        (Native.keySwitchMessages suffixDimension keySwitchLevels keySwitchGadget keys.2)
        error)
    return decide
      (Native.SharedRandomnessOneCycle.splitNestedSecret recovered = keys)
  have hSampler : evalDist splitSampler = evalDist keysSampler := by
    exact Native.SharedRandomnessOneCycle.sampleRingSecret_prefix_suffix_evalDist
      prefixDimension suffixDimension
  have hNative :
      evalDist (uniformRecoveryGame ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget solver) =
        evalDist (splitSampler >>= fun keys ↦
          bootstrappingKeys >>= fun bootstrappingKey ↦
          challenges >>= fun challenge ↦
          errors >>= fun error ↦
          finish keys bootstrappingKey challenge error) := by
    rw [uniformRecoveryGame_eq_native]
    simp [Native.SharedRandomnessOneCycle.AuxiliaryInput.uniformSecretContinuationGame,
      Native.SharedRandomnessOneCycle.generateKeySwitchKey, Native.generateKeySwitchKey,
      TLWE.batchEncrypt, splitSampler, bootstrappingKeys, challenges, errors, finish,
      samples, Keys, Bootstrap, KeySwitchChallenge, KeySwitchError,
      nativeRecoveryContinuation, Native.SharedRandomnessOneCycle.splitNestedSecret,
      bind_assoc, monad_norm]
  have hLWE :
      evalDist (LearningWithErrors.searchExperiment
          (Native.SharedRandomnessOneCycle.sharedKeySwitchProblem q prefixDimension
            suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget)
          (keySwitchSearchReduction keySwitchErrorSampler keySwitchGadget solver)) =
        evalDist (challenges >>= fun challenge ↦
          keysSampler >>= fun keys ↦
          errors >>= fun error ↦
          bootstrappingKeys >>= fun bootstrappingKey ↦
          finish keys bootstrappingKey challenge error) := by
    simp [LearningWithErrors.searchExperiment,
      Native.SharedRandomnessOneCycle.sharedKeySwitchProblem,
      FormalProof4FHE.SharedRandomness.KeySwitching.sharedIKSKProblem,
      FormalProof4FHE.SharedRandomness.KeySwitching.affineIKSKProblem,
      keySwitchSearchReduction, keysSampler, bootstrappingKeys, challenges, errors,
      finish, samples, Keys, Bootstrap, KeySwitchChallenge, KeySwitchError,
      TLWE.batchAssemble, add_assoc, bind_assoc, monad_norm]
  rw [hNative, hLWE]
  calc
    _ = evalDist (keysSampler >>= fun keys ↦
        bootstrappingKeys >>= fun bootstrappingKey ↦
        challenges >>= fun challenge ↦
        errors >>= fun error ↦
        finish keys bootstrappingKey challenge error) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hSampler _
    _ = _ :=
      Native.KeySwitchSecurity.evalDist_bind_four_reorder
        keysSampler bootstrappingKeys challenges errors finish

/-- The uniform-BRK baseline success probability is exactly affine shared-KSK search-LWE
success for the explicit reduction. -/
theorem probOutput_uniformRecoveryGame_true_eq_keySwitchSearchExperiment
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    Pr[= true | uniformRecoveryGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget solver] =
      Pr[= true | LearningWithErrors.searchExperiment
        (Native.SharedRandomnessOneCycle.sharedKeySwitchProblem q prefixDimension
          suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget)
        (keySwitchSearchReduction keySwitchErrorSampler keySwitchGadget solver)] := by
  exact evalDist_ext_iff.mp
    (uniformRecoveryGame_evalDist_eq_keySwitchSearchExperiment
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget solver) true

/-- One-cycle master-key recovery is bounded by the native CircLWE decision term plus an exact
affine shared-KSK search-LWE term.  The second term contains no BRK circularity. -/
theorem successProbability_le_circularLwe_add_keySwitchSearchLWE
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    successProbability ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        solver ≤
      ENNReal.ofReal
          (AuxiliaryInput.circularLweAdvantage ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget
            (LWE.AuxiliaryInput.Search.recoveryContinuation solver)) +
        Pr[= true | LearningWithErrors.searchExperiment
          (Native.SharedRandomnessOneCycle.sharedKeySwitchProblem q prefixDimension
            suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget)
          (keySwitchSearchReduction keySwitchErrorSampler keySwitchGadget solver)] := by
  rw [← probOutput_uniformRecoveryGame_true_eq_keySwitchSearchExperiment
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget solver]
  exact successProbability_le_circularLwe_add_uniformRecovery
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget solver

/-! ## Shared-KSK pair recovery reduces to ordinary prefix search LWE -/

/-- An ordinary binary-secret batch-LWE search reduction.  It independently samples the suffix,
adds its public gadget-message translation to the supplied LWE transcript, supplies an independent
uniform BRK, and returns only the prefix of the solver's recovered master key. -/
noncomputable def ordinaryPrefixSearchReduction
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LearningWithErrors.SearchAdversary
      (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
        (suffixDimension * keySwitchLevels) keySwitchErrorSampler) :=
  fun transcript ↦ do
    let suffixKey ← Native.sampleLweSecret suffixDimension
    let bootstrappingKey ←
      $ᵗ (Challenge q prefixDimension suffixDimension tgswLevels)
    let recovered ← solver bootstrappingKey
      (FormalProof4FHE.SharedRandomness.KeySwitching.addMessageToTranscript
        (Native.keySwitchMessages suffixDimension keySwitchLevels keySwitchGadget)
        suffixKey transcript)
    return Native.SharedRandomnessOneCycle.prefixSecret recovered

/-- Recovering the complete `(prefix,suffix)` pair from the affine shared KSK is no easier than
recovering the ordinary LWE prefix secret.  The implication is pointwise: correct master recovery
always gives a correct prefix, while the ordinary search reduction may additionally succeed when
the suffix guess is wrong. -/
theorem keySwitchSearch_success_le_ordinaryPrefixSearch
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    Pr[= true | LearningWithErrors.searchExperiment
      (Native.SharedRandomnessOneCycle.sharedKeySwitchProblem q prefixDimension
        suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget)
      (keySwitchSearchReduction keySwitchErrorSampler keySwitchGadget solver)] ≤
      Pr[= true | LearningWithErrors.searchExperiment
        (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
          (suffixDimension * keySwitchLevels) keySwitchErrorSampler)
        (ordinaryPrefixSearchReduction keySwitchErrorSampler keySwitchGadget solver)] := by
  let samples := suffixDimension * keySwitchLevels
  let KeySwitchChallenge := Matrix (Fin prefixDimension) (Fin samples) (ZMod q)
  let KeySwitchError := Fin samples → ZMod q
  let Bootstrap := Challenge q prefixDimension suffixDimension tgswLevels
  let challenges : ProbComp KeySwitchChallenge := $ᵗ KeySwitchChallenge
  let prefixes := Native.sampleLweSecret prefixDimension
  let suffixes := Native.sampleLweSecret suffixDimension
  let errors : ProbComp KeySwitchError :=
    ProbComp.sampleIID samples keySwitchErrorSampler
  let bootstrappingKeys : ProbComp Bootstrap := $ᵗ Bootstrap
  let keySwitchKey := fun (prefixKey : BinarySecret prefixDimension)
      (suffixKey : BinarySecret suffixDimension)
      (challenge : KeySwitchChallenge) (error : KeySwitchError) ↦
    TLWE.batchAssemble (embedBinarySecret prefixKey) challenge
      (Native.keySwitchMessages suffixDimension keySwitchLevels keySwitchGadget suffixKey)
      error
  let pairFinish := fun (challenge : KeySwitchChallenge)
      (prefixKey : BinarySecret prefixDimension)
      (suffixKey : BinarySecret suffixDimension) (error : KeySwitchError)
      (bootstrappingKey : Bootstrap) ↦ do
    let recovered ← solver bootstrappingKey
      (keySwitchKey prefixKey suffixKey challenge error)
    return decide
      (Native.SharedRandomnessOneCycle.splitNestedSecret recovered =
        (prefixKey, suffixKey))
  let prefixFinish := fun (challenge : KeySwitchChallenge)
      (prefixKey : BinarySecret prefixDimension)
      (suffixKey : BinarySecret suffixDimension) (error : KeySwitchError)
      (bootstrappingKey : Bootstrap) ↦ do
    let recovered ← solver bootstrappingKey
      (keySwitchKey prefixKey suffixKey challenge error)
    return decide (Native.SharedRandomnessOneCycle.prefixSecret recovered = prefixKey)
  have hPair :
      LearningWithErrors.searchExperiment
          (Native.SharedRandomnessOneCycle.sharedKeySwitchProblem q prefixDimension
            suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget)
          (keySwitchSearchReduction keySwitchErrorSampler keySwitchGadget solver) =
        (challenges >>= fun challenge ↦
          prefixes >>= fun prefixKey ↦
          suffixes >>= fun suffixKey ↦
          errors >>= fun error ↦
          bootstrappingKeys >>= fun bootstrappingKey ↦
          pairFinish challenge prefixKey suffixKey error bootstrappingKey) := by
    simp [LearningWithErrors.searchExperiment,
      Native.SharedRandomnessOneCycle.sharedKeySwitchProblem,
      FormalProof4FHE.SharedRandomness.KeySwitching.sharedIKSKProblem,
      FormalProof4FHE.SharedRandomness.KeySwitching.affineIKSKProblem,
      keySwitchSearchReduction, challenges, prefixes, suffixes, errors,
      bootstrappingKeys, keySwitchKey, pairFinish, samples, KeySwitchChallenge,
      KeySwitchError, Bootstrap, TLWE.batchAssemble, add_assoc, bind_assoc, monad_norm]
  have hPrefix :
      LearningWithErrors.searchExperiment
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension samples
            keySwitchErrorSampler)
          (ordinaryPrefixSearchReduction keySwitchErrorSampler keySwitchGadget solver) =
        (challenges >>= fun challenge ↦
          prefixes >>= fun prefixKey ↦
          errors >>= fun error ↦
          suffixes >>= fun suffixKey ↦
          bootstrappingKeys >>= fun bootstrappingKey ↦
          prefixFinish challenge prefixKey suffixKey error bootstrappingKey) := by
    simp [LearningWithErrors.searchExperiment,
      Native.KeySwitchSecurity.binaryLweProblem,
      FormalProof4FHE.LWE.embeddedBatchProblem,
      ordinaryPrefixSearchReduction,
      FormalProof4FHE.SharedRandomness.KeySwitching.addMessageToTranscript,
      challenges, prefixes, suffixes, errors, bootstrappingKeys, keySwitchKey,
      prefixFinish, samples, KeySwitchChallenge, KeySwitchError, Bootstrap,
      TLWE.batchAssemble, add_comm, add_left_comm, monad_norm]
  rw [hPair, hPrefix]
  calc
    Pr[= true | challenges >>= fun challenge ↦
        prefixes >>= fun prefixKey ↦
        suffixes >>= fun suffixKey ↦
        errors >>= fun error ↦
        bootstrappingKeys >>= fun bootstrappingKey ↦
        pairFinish challenge prefixKey suffixKey error bootstrappingKey] =
      Pr[= true | challenges >>= fun challenge ↦
        prefixes >>= fun prefixKey ↦
        errors >>= fun error ↦
        suffixes >>= fun suffixKey ↦
        bootstrappingKeys >>= fun bootstrappingKey ↦
        pairFinish challenge prefixKey suffixKey error bootstrappingKey] := by
      refine probOutput_bind_congr' challenges true fun challenge ↦ ?_
      refine probOutput_bind_congr' prefixes true fun prefixKey ↦ ?_
      exact probOutput_bind_bind_swap suffixes errors
        (fun suffixKey error ↦
          bootstrappingKeys >>= fun bootstrappingKey ↦
          pairFinish challenge prefixKey suffixKey error bootstrappingKey) true
    _ ≤ Pr[= true | challenges >>= fun challenge ↦
        prefixes >>= fun prefixKey ↦
        errors >>= fun error ↦
        suffixes >>= fun suffixKey ↦
        bootstrappingKeys >>= fun bootstrappingKey ↦
        prefixFinish challenge prefixKey suffixKey error bootstrappingKey] := by
      refine probOutput_bind_mono fun challenge _ ↦ ?_
      refine probOutput_bind_mono fun prefixKey _ ↦ ?_
      refine probOutput_bind_mono fun error _ ↦ ?_
      refine probOutput_bind_mono fun suffixKey _ ↦ ?_
      refine probOutput_bind_mono fun bootstrappingKey _ ↦ ?_
      unfold pairFinish prefixFinish
      refine probOutput_bind_mono fun recovered _ ↦ ?_
      simp only [probOutput_pure]
      by_cases hpair :
          Native.SharedRandomnessOneCycle.splitNestedSecret recovered =
            (prefixKey, suffixKey)
      · have hprefix :
            Native.SharedRandomnessOneCycle.prefixSecret recovered = prefixKey := by
          change (Native.SharedRandomnessOneCycle.splitNestedSecret recovered).1 =
            (prefixKey, suffixKey).1
          exact congrArg Prod.fst hpair
        simp [hpair, hprefix]
      · simp [hpair]

/-- Final search decomposition for the shared-key layout: complete master-key recovery is bounded
by one native one-cycle CircLWE decision advantage plus conventional binary-secret batch
search-LWE under the prefix key. -/
theorem successProbability_le_circularLwe_add_ordinarySearchLWE
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    successProbability ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        solver ≤
      ENNReal.ofReal
          (AuxiliaryInput.circularLweAdvantage ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget
            (LWE.AuxiliaryInput.Search.recoveryContinuation solver)) +
        Pr[= true | LearningWithErrors.searchExperiment
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (suffixDimension * keySwitchLevels) keySwitchErrorSampler)
          (ordinaryPrefixSearchReduction keySwitchErrorSampler keySwitchGadget solver)] := by
  exact (successProbability_le_circularLwe_add_keySwitchSearchLWE
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget solver).trans
      (add_le_add le_rfl
        (keySwitchSearch_success_le_ordinaryPrefixSearch
          keySwitchErrorSampler keySwitchGadget solver))

/-- Secret-aware distance between the uniform-BRK real-KSK recovery endpoint and the completely
uniform public endpoint.  This isolates the non-circular suffix-KSK search contribution. -/
noncomputable def keySwitchRecoveryAdvantage
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  (uniformRecoveryGame ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget solver).boolDistAdvantage
    (fullyUniformRecoveryGame solver)

/-- Complete search normalization: master-key recovery is bounded by the one-cycle CircLWE
decision term, the non-circular suffix-KSK recovery term, and exact uniform guessing. -/
theorem successProbability_le_circularLwe_add_keySwitchRecovery_add_guess
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    successProbability ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        solver ≤
      ENNReal.ofReal
          (AuxiliaryInput.circularLweAdvantage ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget
            (LWE.AuxiliaryInput.Search.recoveryContinuation solver)) +
        (ENNReal.ofReal
            (keySwitchRecoveryAdvantage ringErrorSampler keySwitchErrorSampler
              tgswGadget keySwitchGadget solver) +
          ((2 ^ (prefixDimension + suffixDimension) : ℕ) : ENNReal)⁻¹) := by
  have hSearch := successProbability_le_circularLwe_add_uniformRecovery
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget solver
  have hUniform := ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
    (uniformRecoveryGame ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget solver)
    (fullyUniformRecoveryGame solver)
  rw [probOutput_fullyUniformRecoveryGame_true solver] at hUniform
  have hUniform' :
      Pr[= true | uniformRecoveryGame ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget solver] ≤
        ENNReal.ofReal
            (keySwitchRecoveryAdvantage ringErrorSampler keySwitchErrorSampler
              tgswGadget keySwitchGadget solver) +
          ((2 ^ (prefixDimension + suffixDimension) : ℕ) : ENNReal)⁻¹ := by
    simpa [keySwitchRecoveryAdvantage, add_comm] using hUniform
  exact hSearch.trans (add_le_add le_rfl hUniform')

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.AuxiliaryInput.Search
