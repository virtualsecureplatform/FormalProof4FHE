/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputSearch
import FormalProof4FHE.TFHE.MonomialKDMAuxiliaryInput
import FormalProof4FHE.TFHE.ScalarSecretRandomization

/-!
# Exact Search Experiment for Native TFHE Auxiliary-Input CircLWE

This module instantiates the generic auxiliary-input search interface with the exact native TFHE
distribution used by the monomial-KDM bootstrapping-key hop.  A solver receives the native
bootstrapping key together with the correlated real key-switch key and must recover both hidden
keys.  The checked game equality connects that search experiment to the existing native real
continuation game.

The definitions and equalities here do not assert a search-to-decision reduction.  In particular,
they do not discharge the shifted-function evaluation, noise-smudging, or heterogeneous ring-key
steps needed by the PKC 2024 style reduction.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search

abbrev Secret (lweDimension ringRank degree : ℕ) :=
  AuxiliaryInput.Secret lweDimension ringRank degree

abbrev Challenge (q degree ringRank tgswLevels lweDimension : ℕ) :=
  AuxiliaryInput.Challenge q degree ringRank tgswLevels lweDimension

abbrev Auxiliary (q degree ringRank lweDimension keySwitchLevels : ℕ) :=
  AuxiliaryInput.Auxiliary q degree ringRank lweDimension keySwitchLevels

/-- A native TFHE search solver sees the BRK and its correlated real KSK, but not either secret
key. -/
abbrev Solver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  LWE.AuxiliaryInput.Search.Solver
    (Secret lweDimension ringRank degree)
    (Challenge q degree ringRank tgswLevels lweDimension)
    (Auxiliary q degree ringRank lweDimension keySwitchLevels)

/-- Exact secret-recovery problem obtained from the real branch of native auxiliary-input
CircLWE. -/
noncomputable def problem
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    LWE.AuxiliaryInput.Search.Problem
      (Secret lweDimension ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels) :=
  LWE.AuxiliaryInput.Search.exactRecoveryProblem
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)

/-- The native exact-recovery experiment. -/
noncomputable def game
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp Bool :=
  LWE.AuxiliaryInput.Search.game
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    solver

/-- View a public-input search solver as a native two-key continuation whose only secret-aware
operation is the experiment's final exact-recovery check. -/
def nativeRecoveryContinuation
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (solver : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels) :=
  fun lweSecret ringSecret bootstrappingKey keySwitchKey ↦ do
    let recovered ← solver bootstrappingKey keySwitchKey
    return decide (recovered = (lweSecret, ringSecret))

/-- The native search game is exactly the real branch of the generic auxiliary-input problem. -/
theorem game_eq_auxiliaryRealGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    game ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget solver =
      LWE.AuxiliaryInput.realGame
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (LWE.AuxiliaryInput.Search.recoveryContinuation solver) := by
  simpa [game, problem] using
    (LWE.AuxiliaryInput.Search.game_exactRecoveryProblem_eq_realGame
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      solver)

/-- The exact-recovery search game is also exactly the existing native monomial-KDM real game. -/
theorem game_eq_nativeRealContinuationGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    game ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget solver =
      Circular.realContinuationGame
        (MonomialKDM.cycleSpec
          q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (nativeRecoveryContinuation solver) := by
  rw [game_eq_auxiliaryRealGame]
  change LWE.AuxiliaryInput.realGame
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (AuxiliaryInput.packContinuation (nativeRecoveryContinuation solver)) = _
  exact AuxiliaryInput.realGame_eq_native
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    (nativeRecoveryContinuation solver)

/-- Exact success probability of a native auxiliary-input CircLWE search solver. -/
noncomputable def successProbability
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) : ENNReal :=
  LWE.AuxiliaryInput.Search.successProbability
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    solver

/-! ## Connection to checked scalar-key randomization -/

/-- The real challenge and correlated KSK at one fixed native secret pair, packaged in the same
order as the evaluation-key view used by scalar-key randomization. -/
noncomputable def fixedSecretRealView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Secret lweDimension ringRank degree) :
    ProbComp
      (Challenge q degree ringRank tgswLevels lweDimension ×
        Auxiliary q degree ringRank lweDimension keySwitchLevels) := do
  let bootstrappingKey ←
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleReal secrets
  let keySwitchKey ←
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  return (bootstrappingKey, keySwitchKey)

/-- For each fixed secret pair, the real search view has exactly the same distribution as the
native structured BRK+KSK sampler used by scalar-key randomization.  The bridge uses the common
direct gadget-phase representation of the structured and monomial BRK samplers. -/
theorem fixedSecretRealView_evalDist_eq_native
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (fixedSecretRealView q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      (lweSecret, ringSecret)) =
      evalDist (ScalarSecretRandomization.sampleRealEvaluationKeyPair
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        lweSecret ringSecret) := by
  change evalDist (do
      let bootstrappingKey ← MonomialKDM.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension
        ringErrorSampler tgswGadget lweSecret ringSecret
      let keySwitchKey ← Native.generateKeySwitchKey
        q lweDimension (ringRank * degree) keySwitchLevels
        keySwitchErrorSampler keySwitchGadget (keyExtract ringSecret) lweSecret
      return (bootstrappingKey, keySwitchKey)) =
    evalDist (do
      let bootstrappingKey ← Native.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension
        ringErrorSampler tgswGadget lweSecret ringSecret
      let keySwitchKey ← Native.generateKeySwitchKey
        q lweDimension (ringRank * degree) keySwitchLevels
        keySwitchErrorSampler keySwitchGadget (keyExtract ringSecret) lweSecret
      return (bootstrappingKey, keySwitchKey))
  rw [evalDist_bind,
    MonomialKDM.generateBootstrappingKey_eq_direct
      q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret,
    ← Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
      q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret,
    ← evalDist_bind]

/-- The checked fixed-mask transform applies directly to the real public view of the native
auxiliary-input search problem when ring noise is centered binomial. -/
theorem transform_fixedSecretRealView_centeredBinomial_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ}
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (ScalarSecretRandomization.transformEvaluationKeyPair tgswGadget mask <$>
          fixedSecretRealView q (degree + 1) ringRank tgswLevels lweDimension
            keySwitchLevels (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
            keySwitchErrorSampler tgswGadget keySwitchGadget
            (lweSecret, ringSecret)) =
      evalDist
        (fixedSecretRealView q (degree + 1) ringRank tgswLevels lweDimension
          keySwitchLevels (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget
          (ScalarSecretRandomization.maskedSecret lweSecret mask, ringSecret)) := by
  calc
    _ = evalDist
        (ScalarSecretRandomization.transformEvaluationKeyPair tgswGadget mask <$>
          ScalarSecretRandomization.sampleRealEvaluationKeyPair
            q (degree + 1) ringRank tgswLevels lweDimension keySwitchLevels
            (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
            keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret ringSecret) := by
      rw [evalDist_map, fixedSecretRealView_evalDist_eq_native, ← evalDist_map]
    _ = evalDist
        (ScalarSecretRandomization.sampleRealEvaluationKeyPair
          q (degree + 1) ringRank tgswLevels lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget
          (ScalarSecretRandomization.maskedSecret lweSecret mask) ringSecret) :=
      ScalarSecretRandomization.transform_realEvaluationKeyPair_centeredBinomial_evalDist
        keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret mask ringSecret
    _ = _ := (fixedSecretRealView_evalDist_eq_native
      (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
      keySwitchErrorSampler tgswGadget keySwitchGadget
      (ScalarSecretRandomization.maskedSecret lweSecret mask) ringSecret).symm

/-- Sampling a uniform scalar mask and transporting the native CircLWE search view is exactly
equivalent to sampling a fresh uniform scalar key and its real search view, for every fixed ring
key.  This is the scalar-key part of secret randomization; it does not randomize the ring key. -/
theorem sampleMasked_fixedSecretRealView_centeredBinomial_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ}
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist (do
        let mask ← $ᵗ BinarySecret lweDimension
        let view ← fixedSecretRealView q (degree + 1) ringRank tgswLevels
          lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget (lweSecret, ringSecret)
        return (ScalarSecretRandomization.maskedSecret lweSecret mask,
          ScalarSecretRandomization.transformEvaluationKeyPair tgswGadget mask view)) =
      evalDist (do
        let freshSecret ← $ᵗ BinarySecret lweDimension
        let view ← fixedSecretRealView q (degree + 1) ringRank tgswLevels
          lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget (freshSecret, ringSecret)
        return (freshSecret, view)) := by
  exact ScalarSecretRandomization.sampleMaskedView_evalDist lweSecret
    (fun freshSecret ↦
      fixedSecretRealView q (degree + 1) ringRank tgswLevels lweDimension
        keySwitchLevels (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
        keySwitchErrorSampler tgswGadget keySwitchGadget (freshSecret, ringSecret))
    (ScalarSecretRandomization.transformEvaluationKeyPair tgswGadget)
    (fun mask ↦ transform_fixedSecretRealView_centeredBinomial_evalDist
      keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret mask ringSecret)

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search
