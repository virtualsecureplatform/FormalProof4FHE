/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeAdaptiveShiftedDifferenceView
import FormalProof4FHE.TFHE.NativeCoupledShiftedResidualBounds
import FormalProof4FHE.TFHE.NativeOffDiagonalResidualNormalForm

/-!
# Adaptive Lift of Native Off-Diagonal TFHE Security

This module connects the fixed-secret whole-BRK diagonal-isolation theorem to the complete
adaptive public view.  Scalar transport turns a centered-binomial source BRK into the same direct
BRK law under the masked scalar secret.  The transported KSK and input tape are retained verbatim,
so the fixed-secret total-variation bound lifts by data processing and averaging.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

noncomputable section

open FormalProof4FHE.TFHE
open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Scalar transport of a native direct centered-binomial BRK is exactly a fresh direct BRK
under the XOR-masked scalar secret. -/
theorem transformDirectBootstrappingKey_centeredBinomial_evalDist
    {q degree ringRank lweDimension eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hidden mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (Native.ScalarSecretRandomization.transformBootstrappingKey
            (Gadget.Base.ringGadget params) mask <$>
          Native.BootstrapSecurity.generateDirectBootstrappingKey
            q (degree + 1) ringRank params.levels lweDimension
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            (Gadget.Base.ringGadget params) hidden ringSecret) =
      evalDist
        (Native.BootstrapSecurity.generateDirectBootstrappingKey
          q (degree + 1) ringRank params.levels lweDimension
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          (Gadget.Base.ringGadget params)
          (Native.ScalarSecretRandomization.maskedSecret hidden mask) ringSecret) := by
  let Gadget : Fin params.levels → RLWE.Rq q (degree + 1) :=
    Gadget.Base.ringGadget params
  let Transform := Native.ScalarSecretRandomization.transformBootstrappingKey
    (dimension := ringRank) Gadget mask
  let SourceNative := Native.generateBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    Gadget hidden ringSecret
  let SourceDirect := Native.BootstrapSecurity.generateDirectBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    Gadget hidden ringSecret
  let TargetNative := Native.generateBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    Gadget
    (Native.ScalarSecretRandomization.maskedSecret hidden mask) ringSecret
  let TargetDirect := Native.BootstrapSecurity.generateDirectBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    Gadget
    (Native.ScalarSecretRandomization.maskedSecret hidden mask) ringSecret
  have hSource : evalDist SourceNative = evalDist SourceDirect :=
    Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      Gadget hidden ringSecret
  have hMapped : evalDist (Transform <$> SourceNative) =
      evalDist (Transform <$> SourceDirect) :=
    evalDist_map_eq_of_evalDist_eq hSource Transform
  calc
    evalDist (Transform <$> SourceDirect) =
        evalDist (Transform <$> SourceNative) := hMapped.symm
    _ = evalDist TargetNative :=
      Native.ScalarSecretRandomization.transformBootstrappingKey_generate_centeredBinomial_evalDist
        Gadget hidden mask ringSecret
    _ = evalDist TargetDirect :=
      Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
        q (degree + 1) ringRank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        Gadget
        (Native.ScalarSecretRandomization.maskedSecret hidden mask) ringSecret

/-- The KSK-and-tape component of one real augmented source at fixed native secrets. -/
noncomputable def sourceAuxiliarySampler
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) := do
  let keySwitchKey ← Native.generateKeySwitchKey q lweDimension
    (ringRank * degree) keySwitchLevels keySwitchErrorSampler
    keySwitchGadget (keyExtract ringSecret) hidden
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret hidden) 0
  return (keySwitchKey, tape)

/-- Public scalar transport of the KSK-and-tape component. -/
def transportSourceAuxiliary
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (mask : BinarySecret lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) :
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount :=
  (Native.ScalarSecretRandomization.transformKeySwitchKey mask auxiliary.1,
    Native.ScalarSecretRandomization.transformBatch mask auxiliary.2)

/-- The actual correct adaptive evaluator, coupled to the complete latent native secret pair and
written with an independent uniform BRK difference. -/
noncomputable def coupledAveragedCorrectDifferenceView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp (PublicContext q (degree + 1) ringRank params.levels lweDimension
      keySwitchLevels queryCount) := do
  let source ← pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount)
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
    keySwitchGadget
  transformFromDifference params coordinate (source.1.1 coordinate)
    source.2.1 source.2.2

/-- Retaining the complete latent secret pair and replacing the true branch by an independent
difference does not change the averaged correct adaptive view. -/
theorem averagedCorrectTransform_evalDist_eq_coupledAveragedCorrectDifferenceView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (coupledAveragedCorrectDifferenceView (degree := degree) (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) := by
  let Source := pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount)
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
    keySwitchGadget
  let Projection := fun source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount =>
    (source.1.1 coordinate, source.2)
  let Finish := fun hiddenAndContext : Bool ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount =>
    transform params coordinate hiddenAndContext.1
      hiddenAndContext.2.1 hiddenAndContext.2.2
  have hProject : evalDist (Projection <$> Source) =
      evalDist (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
        keySwitchGadget coordinate) := by
    simpa only [Source, Projection] using
      (pairedSource_project_evalDist
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount)
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
        keySwitchGadget coordinate)
  have hProjected := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hProject Finish
  have hSourceToAveraged :
      evalDist (Source >>= fun source => Finish (Projection source)) =
        evalDist
          (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
            params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) := by
    simpa only [averagedCorrectTransform, Source, Projection, Finish,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hProjected
  calc
    _ = evalDist (Source >>= fun source => Finish (Projection source)) :=
      hSourceToAveraged.symm
    _ = evalDist (Source >>= fun source =>
        transformFromDifference params coordinate (source.1.1 coordinate)
          source.2.1 source.2.2) := by
      refine evalDist_bind_congr' Source fun source => ?_
      exact transform_evalDist_eq_transformFromDifference params coordinate
        (source.1.1 coordinate) source.2.1 source.2.2
    _ = _ := by
      rfl

/-- Fully expanded generative order of the coupled correct difference view. -/
noncomputable def expandedCoupledCorrectDifferenceView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp (PublicContext q (degree + 1) ringRank params.levels lweDimension
      keySwitchLevels queryCount) := do
  let secrets ← KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let sourceKey ← Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    (Gadget.Base.ringGadget params) secrets.1 secrets.2
  let auxiliary ← sourceAuxiliarySampler (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let mask ← $ᵗ BinarySecret lweDimension
  let difference ←
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  let transportedSource := Native.ScalarSecretRandomization.transformBootstrappingKey
    (Gadget.Base.ringGadget params) mask sourceKey
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let bootstrappingKey := Native.ShiftedCandidateEvaluator.selectBootstrappingKey
    params coordinate (targetSecret coordinate) transportedSource
    (Native.ShiftedCandidateEvaluator.addDifference transportedSource difference)
  return (bootstrappingKey, transportSourceAuxiliary mask auxiliary)

/-- Unfolding the latent source and the independent-difference evaluator gives the explicit
generative order above. -/
theorem coupledAveragedCorrectDifferenceView_evalDist_eq_expanded
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (coupledAveragedCorrectDifferenceView (degree := degree) (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (expandedCoupledCorrectDifferenceView (degree := degree) (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) := by
  simp [coupledAveragedCorrectDifferenceView, expandedCoupledCorrectDifferenceView,
    pairedSource, transformFromDifference, transformWithDifference, transformWithCoin,
    sampleCoin, transportedView, sourceAuxiliarySampler, transportSourceAuxiliary,
    problem, LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    KeySwitchFirstFiniteView.augmentedCircularProblem,
    KeySwitchFirstFiniteView.secretSampler, ScalarTransport.transformView,
    Native.ScalarSecretRandomization.transformEvaluationKeyPair,
    Native.ScalarSecretRandomization.maskedSecret, transportCandidate, monad_norm]

/-- Correct adaptive public view in a coupling where the centered-binomial source BRK has already
been transported to the masked secret and sampled in direct form. -/
noncomputable def coupledDirectCorrectView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp (PublicContext q (degree + 1) ringRank params.levels lweDimension
      keySwitchLevels queryCount) := do
  let secrets ← KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let auxiliary ← sourceAuxiliarySampler (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let mask ← $ᵗ BinarySecret lweDimension
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let bootstrappingKey ←
    Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.correctKeyExperiment
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetSecret secrets.2 coordinate
  return (bootstrappingKey, transportSourceAuxiliary mask auxiliary)

/-- After commuting independent source components, exact centered-binomial scalar transport turns
the expanded correct view into `coupledDirectCorrectView`. -/
theorem expandedCoupledCorrectDifferenceView_evalDist_eq_coupledDirectCorrectView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (expandedCoupledCorrectDifferenceView (degree := degree) (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (coupledDirectCorrectView (degree := degree) (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) := by
  let Secrets := KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let Gadget : Fin params.levels → RLWE.Rq q (degree + 1) :=
    Gadget.Base.ringGadget params
  let Source := fun secrets : Secret lweDimension ringRank (degree + 1) =>
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      Gadget secrets.1 secrets.2
  let DirectSource := fun secrets : Secret lweDimension ringRank (degree + 1) =>
    Native.BootstrapSecurity.generateDirectBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      Gadget secrets.1 secrets.2
  let Aux := fun secrets : Secret lweDimension ringRank (degree + 1) =>
    sourceAuxiliarySampler (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let Masks := $ᵗ BinarySecret lweDimension
  let Difference :=
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  let Transform := fun mask : BinarySecret lweDimension =>
    Native.ScalarSecretRandomization.transformBootstrappingKey
      (dimension := ringRank) Gadget mask
  let TargetSecret := fun (secrets : Secret lweDimension ringRank (degree + 1))
      (mask : BinarySecret lweDimension) =>
    Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let Target := fun (secrets : Secret lweDimension ringRank (degree + 1))
      (mask : BinarySecret lweDimension) =>
    Native.BootstrapSecurity.generateDirectBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      Gadget (TargetSecret secrets mask) secrets.2
  let Finish := fun (secrets : Secret lweDimension ringRank (degree + 1))
      (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
        keySwitchLevels queryCount)
      (mask : BinarySecret lweDimension)
      (sourceKey difference : Native.BootstrappingKey q (degree + 1) ringRank
        params.levels lweDimension) =>
    (pure (Native.ShiftedCandidateEvaluator.selectBootstrappingKey
          params coordinate ((TargetSecret secrets mask) coordinate) sourceKey
          (Native.ShiftedCandidateEvaluator.addDifference sourceKey difference),
        transportSourceAuxiliary mask auxiliary) :
      ProbComp (PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount))
  unfold expandedCoupledCorrectDifferenceView coupledDirectCorrectView
  simp only [Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.correctKeyExperiment,
    bind_assoc, pure_bind]
  change evalDist (Secrets >>= fun secrets =>
      Source secrets >>= fun sourceKey =>
      Aux secrets >>= fun auxiliary =>
      Masks >>= fun mask =>
      Difference >>= fun difference =>
      Finish secrets auxiliary mask (Transform mask sourceKey) difference) =
    evalDist (Secrets >>= fun secrets =>
      Aux secrets >>= fun auxiliary =>
      Masks >>= fun mask =>
      Target secrets mask >>= fun sourceKey =>
      Difference >>= fun difference =>
      Finish secrets auxiliary mask sourceKey difference)
  calc
    _ = evalDist (Secrets >>= fun secrets =>
        Aux secrets >>= fun auxiliary =>
        Source secrets >>= fun sourceKey =>
        Masks >>= fun mask =>
        Difference >>= fun difference =>
        Finish secrets auxiliary mask (Transform mask sourceKey) difference) := by
      refine evalDist_bind_congr' Secrets fun secrets => ?_
      exact evalDist_bind_bind_swap (Source secrets) (Aux secrets) _
    _ = evalDist (Secrets >>= fun secrets =>
        Aux secrets >>= fun auxiliary =>
        Masks >>= fun mask =>
        Source secrets >>= fun sourceKey =>
        Difference >>= fun difference =>
        Finish secrets auxiliary mask (Transform mask sourceKey) difference) := by
      refine evalDist_bind_congr' Secrets fun secrets => ?_
      refine evalDist_bind_congr' (Aux secrets) fun auxiliary => ?_
      exact evalDist_bind_bind_swap (Source secrets) Masks _
    _ = _ := by
      refine evalDist_bind_congr' Secrets fun secrets => ?_
      refine evalDist_bind_congr' (Aux secrets) fun auxiliary => ?_
      refine evalDist_bind_congr' Masks fun mask => ?_
      have hSource : Source secrets = DirectSource secrets :=
        Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct
          q (degree + 1) ringRank params.levels lweDimension
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          Gadget secrets.1 secrets.2
      have hTransport : evalDist (Transform mask <$> DirectSource secrets) =
          evalDist (Target secrets mask) := by
        simpa only [Transform, DirectSource, Target, TargetSecret] using
          (transformDirectBootstrappingKey_centeredBinomial_evalDist
            (degree := degree) params secrets.1 mask secrets.2)
      let continuation := fun sourceKey : Native.BootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension =>
        Difference >>= fun difference =>
          Finish secrets auxiliary mask sourceKey difference
      have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hTransport continuation
      rw [hSource]
      simpa only [continuation, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind] using hBind

/-- Complete exact identification of the actual averaged correct evaluator with the direct
centered-binomial coupling consumed by the two-sampler whole-key bound. -/
theorem averagedCorrectTransform_evalDist_eq_coupledDirectCorrectView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (coupledDirectCorrectView (degree := degree) (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) :=
  (averagedCorrectTransform_evalDist_eq_coupledAveragedCorrectDifferenceView
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
    params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
    ((coupledAveragedCorrectDifferenceView_evalDist_eq_expanded
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
      params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
      (expandedCoupledCorrectDifferenceView_evalDist_eq_coupledDirectCorrectView
        (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
        params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate))

/-- Target-noise comparison view in the same scalar-mask and transported-auxiliary coupling. -/
noncomputable def coupledDirectTargetView
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (PublicContext q (degree + 1) ringRank params.levels lweDimension
      keySwitchLevels queryCount) := do
  let secrets ← KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let auxiliary ← sourceAuxiliarySampler (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let mask ← $ᵗ BinarySecret lweDimension
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let bootstrappingKey ← Native.BootstrapSecurity.generateDirectBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension targetRingErrorSampler
    (Gadget.Base.ringGadget params) targetSecret secrets.2
  return (bootstrappingKey, transportSourceAuxiliary mask auxiliary)

/-- Fully expanded generative order of the existing coupled monomial target view. -/
noncomputable def expandedCoupledTargetView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (PublicContext q (degree + 1) ringRank params.levels lweDimension
      keySwitchLevels queryCount) := do
  let secrets ← KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let _sourceKey ← Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    (Gadget.Base.ringGadget params) secrets.1 secrets.2
  let auxiliary ← sourceAuxiliarySampler (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let mask ← $ᵗ BinarySecret lweDimension
  let _trueBranch ←
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let bootstrappingKey ← Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension targetRingErrorSampler
    (Gadget.Base.ringGadget params) targetSecret secrets.2
  return (bootstrappingKey, transportSourceAuxiliary mask auxiliary)

/-- The existing latent-source monomial comparison unfolds to `expandedCoupledTargetView`. -/
theorem coupledAveragedMonomialRealView_evalDist_eq_expandedCoupledTargetView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist
        (coupledAveragedMonomialRealView (ringRank := ringRank)
          (lweDimension := lweDimension)
          (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) =
      evalDist
        (expandedCoupledTargetView (degree := degree) (ringRank := ringRank)
          (lweDimension := lweDimension)
          (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) := by
  simp [coupledAveragedMonomialRealView, expandedCoupledTargetView,
    pairedSource, sampleCoin, coupledMonomialViewAtSourceCoin,
    transportedView, sourceAuxiliarySampler, transportSourceAuxiliary,
    problem, LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    KeySwitchFirstFiniteView.augmentedCircularProblem,
    KeySwitchFirstFiniteView.secretSampler, ScalarTransport.transformView,
    Native.ScalarSecretRandomization.transformEvaluationKeyPair, monad_norm]

/-- The unused source BRK and true branch erase exactly, and the target monomial BRK is
definitionally the direct target sampler used by `coupledDirectTargetView`. -/
theorem expandedCoupledTargetView_evalDist_eq_coupledDirectTargetView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist
        (expandedCoupledTargetView (degree := degree) (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) =
      evalDist
        (coupledDirectTargetView (degree := degree) (ringRank := ringRank)
          (lweDimension := lweDimension) (queryCount := queryCount) params
          targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget) := by
  let Secrets := KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let Source := fun secrets : Secret lweDimension ringRank (degree + 1) =>
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      (Gadget.Base.ringGadget params) secrets.1 secrets.2
  let Aux := fun secrets : Secret lweDimension ringRank (degree + 1) =>
    sourceAuxiliarySampler (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let Masks := $ᵗ BinarySecret lweDimension
  let TrueBranches :=
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  let TargetMonomial := fun (secrets : Secret lweDimension ringRank (degree + 1))
      (mask : BinarySecret lweDimension) =>
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension targetRingErrorSampler
      (Gadget.Base.ringGadget params)
      (Native.ScalarSecretRandomization.maskedSecret secrets.1 mask) secrets.2
  let TargetDirect := fun (secrets : Secret lweDimension ringRank (degree + 1))
      (mask : BinarySecret lweDimension) =>
    Native.BootstrapSecurity.generateDirectBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension targetRingErrorSampler
      (Gadget.Base.ringGadget params)
      (Native.ScalarSecretRandomization.maskedSecret secrets.1 mask) secrets.2
  let Finish := fun
      (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
        keySwitchLevels queryCount)
      (mask : BinarySecret lweDimension)
      (bootstrappingKey : Native.BootstrappingKey q (degree + 1) ringRank
        params.levels lweDimension) =>
    (pure (bootstrappingKey, transportSourceAuxiliary mask auxiliary) :
      ProbComp (PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount))
  unfold expandedCoupledTargetView coupledDirectTargetView
  change evalDist (Secrets >>= fun secrets =>
      Source secrets >>= fun _ =>
      Aux secrets >>= fun auxiliary =>
      Masks >>= fun mask =>
      TrueBranches >>= fun _ =>
      TargetMonomial secrets mask >>= Finish auxiliary mask) =
    evalDist (Secrets >>= fun secrets =>
      Aux secrets >>= fun auxiliary =>
      Masks >>= fun mask =>
      TargetDirect secrets mask >>= Finish auxiliary mask)
  calc
    _ = evalDist (Secrets >>= fun secrets =>
        Aux secrets >>= fun auxiliary =>
        Masks >>= fun mask =>
        TrueBranches >>= fun _ =>
        TargetMonomial secrets mask >>= Finish auxiliary mask) := by
      refine evalDist_bind_congr' Secrets fun secrets => ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (Source secrets) (by simp [Source]) _
    _ = evalDist (Secrets >>= fun secrets =>
        Aux secrets >>= fun auxiliary =>
        Masks >>= fun mask =>
        TargetMonomial secrets mask >>= Finish auxiliary mask) := by
      refine evalDist_bind_congr' Secrets fun secrets => ?_
      refine evalDist_bind_congr' (Aux secrets) fun auxiliary => ?_
      refine evalDist_bind_congr' Masks fun mask => ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        TrueBranches (by simp [TrueBranches]) _
    _ = _ := by
      refine evalDist_bind_congr' Secrets fun secrets => ?_
      refine evalDist_bind_congr' (Aux secrets) fun auxiliary => ?_
      refine evalDist_bind_congr' Masks fun mask => ?_
      rw [show TargetMonomial secrets mask = TargetDirect secrets mask by
        exact Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct
          q (degree + 1) ringRank params.levels lweDimension targetRingErrorSampler
          (Gadget.Base.ringGadget params)
          (Native.ScalarSecretRandomization.maskedSecret secrets.1 mask) secrets.2]

/-- The direct target coupling is exactly the ordinary augmented real public view. -/
theorem coupledDirectTargetView_evalDist_eq_realPublicView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist
        (coupledDirectTargetView (degree := degree) (ringRank := ringRank)
          (lweDimension := lweDimension) (queryCount := queryCount) params
          targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget) =
      evalDist
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) :=
  ((expandedCoupledTargetView_evalDist_eq_coupledDirectTargetView
    (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget).symm.trans
    ((coupledAveragedMonomialRealView_evalDist_eq_expandedCoupledTargetView
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget).symm.trans
      (coupledAveragedMonomialRealView_evalDist_eq_realPublicView
        (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
        keySwitchErrorSampler inputErrorSampler keySwitchGadget)))

/-- The fixed-secret two-sampler whole-key bound lifts through the retained transported
KSK-and-tape context and through averaging over native secrets, auxiliary coins, and scalar
masks. -/
theorem tvDist_coupledDirectCorrectView_coupledDirectTargetView_le
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ) (offDiagonalError : Fin lweDimension → ℝ)
    (hDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError)
    (hOffDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError outputCoordinate) :
    tvDist
        (coupledDirectCorrectView (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (coupledDirectTargetView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) params targetRingErrorSampler
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) ≤
      diagonalError +
        ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
          offDiagonalError outputCoordinate := by
  let Secrets := KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let Aux := fun secrets : Secret lweDimension ringRank (degree + 1) =>
    sourceAuxiliarySampler (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let Masks := $ᵗ BinarySecret lweDimension
  let bound := diagonalError +
    ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
      offDiagonalError outputCoordinate
  unfold coupledDirectCorrectView coupledDirectTargetView
  refine tvDist_bind_left_le_const (m := ProbComp) Secrets _ _ bound ?_
  intro secrets _hsecrets
  refine tvDist_bind_left_le_const (m := ProbComp) (Aux secrets) _ _ bound ?_
  intro auxiliary _hauxiliary
  refine tvDist_bind_left_le_const (m := ProbComp) Masks _ _ bound ?_
  intro mask _hmask
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let CorrectKey :=
    Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.correctKeyExperiment
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetSecret secrets.2 coordinate
  let TargetKey := Native.BootstrapSecurity.generateDirectBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension targetRingErrorSampler
    (Gadget.Base.ringGadget params) targetSecret secrets.2
  let finish := fun bootstrappingKey :
      Native.BootstrappingKey q (degree + 1) ringRank params.levels lweDimension =>
    (bootstrappingKey, transportSourceAuxiliary mask auxiliary)
  have hFixed : tvDist CorrectKey TargetKey ≤ bound := by
    simpa only [CorrectKey, TargetKey, targetSecret, bound] using
      (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_twoSamplers
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler targetSecret secrets.2 coordinate
        diagonalError offDiagonalError
        (hDiagonal targetSecret secrets.2)
        (hOffDiagonal targetSecret secrets.2))
  have hMap := tvDist_map_le (m := ProbComp) finish CorrectKey TargetKey
  simpa only [Secrets, Aux, Masks, targetSecret, CorrectKey, TargetKey, finish,
    map_eq_bind_pure_comp, Function.comp_def] using hMap.trans hFixed

/-- **Adaptive correct-view diagonal isolation.**  Exact source transport and exact target
identification turn the fixed-secret two-sampler theorem into a bound for the actual averaged
adaptive correct evaluator against the ordinary target real public view. -/
theorem tvDist_averagedCorrectTransform_realPublicView_le_offDiagonalIsolation
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ) (offDiagonalError : Fin lweDimension → ℝ)
    (hDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError)
    (hOffDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError outputCoordinate) :
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      diagonalError +
        ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
          offDiagonalError outputCoordinate := by
  have hCoupled :=
    tvDist_coupledDirectCorrectView_coupledDirectTargetView_le
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      diagonalError offDiagonalError hDiagonal hOffDiagonal
  unfold tvDist at hCoupled ⊢
  rw [averagedCorrectTransform_evalDist_eq_coupledDirectCorrectView
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
    params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate]
  rw [← coupledDirectTargetView_evalDist_eq_realPublicView
    (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget]
  exact hCoupled

/-- Coupled adaptive correct-view bound using the actual generated-control expectation rather
than a support-wise off-diagonal premise. -/
theorem tvDist_coupledDirectCorrectView_coupledDirectTargetView_le_averagedOffDiagonal
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ)
    (hDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError) :
    tvDist
        (coupledDirectCorrectView (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (coupledDirectTargetView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) params targetRingErrorSampler
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) ≤
      diagonalError +
        Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalReplacementDistance
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler coordinate := by
  let Secrets := KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let Aux := fun secrets : Secret lweDimension ringRank (degree + 1) =>
    sourceAuxiliarySampler (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let Masks := $ᵗ BinarySecret lweDimension
  let offDiagonalError :=
    Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalReplacementDistance
      (ringRank := ringRank) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetRingErrorSampler coordinate
  let bound := diagonalError + offDiagonalError
  unfold coupledDirectCorrectView coupledDirectTargetView
  refine tvDist_bind_left_le_const (m := ProbComp) Secrets _ _ bound ?_
  intro secrets _hsecrets
  refine tvDist_bind_left_le_const (m := ProbComp) (Aux secrets) _ _ bound ?_
  intro auxiliary _hauxiliary
  refine tvDist_bind_left_le_const (m := ProbComp) Masks _ _ bound ?_
  intro mask _hmask
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let CorrectKey :=
    Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.correctKeyExperiment
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetSecret secrets.2 coordinate
  let TargetKey := Native.BootstrapSecurity.generateDirectBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension targetRingErrorSampler
    (Gadget.Base.ringGadget params) targetSecret secrets.2
  let finish := fun bootstrappingKey :
      Native.BootstrappingKey q (degree + 1) ringRank params.levels lweDimension =>
    (bootstrappingKey, transportSourceAuxiliary mask auxiliary)
  have hFixed : tvDist CorrectKey TargetKey ≤ bound := by
    simpa only [CorrectKey, TargetKey, targetSecret, bound, offDiagonalError] using
      (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_averagedOffDiagonal
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler targetSecret secrets.2 coordinate diagonalError
        (hDiagonal targetSecret secrets.2))
  have hMap := tvDist_map_le (m := ProbComp) finish CorrectKey TargetKey
  simpa only [Secrets, Aux, Masks, targetSecret, CorrectKey, TargetKey, finish,
    map_eq_bind_pure_comp, Function.comp_def] using hMap.trans hFixed

/-- Adaptive correct-view theorem with the off-diagonal control average and finite secret maximum
fully internalized. -/
theorem tvDist_averagedCorrectTransform_realPublicView_le_averagedOffDiagonal
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ)
    (hDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError) :
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      diagonalError +
        Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalReplacementDistance
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler coordinate := by
  have hCoupled :=
    tvDist_coupledDirectCorrectView_coupledDirectTargetView_le_averagedOffDiagonal
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      diagonalError hDiagonal
  unfold tvDist at hCoupled ⊢
  rw [averagedCorrectTransform_evalDist_eq_coupledDirectCorrectView
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
    params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate]
  rw [← coupledDirectTargetView_evalDist_eq_realPublicView
    (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget]
  exact hCoupled

/-- Coupled adaptive correct-view bound through the explicit generated-control residual-vector
`L²` budget. -/
theorem tvDist_coupledDirectCorrectView_coupledDirectTargetView_le_residualL2
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ)
    (hDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError) :
    tvDist
        (coupledDirectCorrectView (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (coupledDirectTargetView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) params targetRingErrorSampler
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) ≤
      diagonalError +
        Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalResidualL2Loss
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler coordinate := by
  let Secrets := KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let Aux := fun secrets : Secret lweDimension ringRank (degree + 1) =>
    sourceAuxiliarySampler (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let Masks := $ᵗ BinarySecret lweDimension
  let offDiagonalError :=
    Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalResidualL2Loss
      (ringRank := ringRank) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetRingErrorSampler coordinate
  let bound := diagonalError + offDiagonalError
  unfold coupledDirectCorrectView coupledDirectTargetView
  refine tvDist_bind_left_le_const (m := ProbComp) Secrets _ _ bound ?_
  intro secrets _hsecrets
  refine tvDist_bind_left_le_const (m := ProbComp) (Aux secrets) _ _ bound ?_
  intro auxiliary _hauxiliary
  refine tvDist_bind_left_le_const (m := ProbComp) Masks _ _ bound ?_
  intro mask _hmask
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let CorrectKey :=
    Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.correctKeyExperiment
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetSecret secrets.2 coordinate
  let TargetKey := Native.BootstrapSecurity.generateDirectBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension targetRingErrorSampler
    (Gadget.Base.ringGadget params) targetSecret secrets.2
  let finish := fun bootstrappingKey :
      Native.BootstrappingKey q (degree + 1) ringRank params.levels lweDimension =>
    (bootstrappingKey, transportSourceAuxiliary mask auxiliary)
  have hFixed : tvDist CorrectKey TargetKey ≤ bound := by
    simpa only [CorrectKey, TargetKey, targetSecret, bound, offDiagonalError] using
      (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_residualL2
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler targetSecret secrets.2 coordinate diagonalError
        (hDiagonal targetSecret secrets.2))
  have hMap := tvDist_map_le (m := ProbComp) finish CorrectKey TargetKey
  simpa only [Secrets, Aux, Masks, targetSecret, CorrectKey, TargetKey, finish,
    map_eq_bind_pure_comp, Function.comp_def] using hMap.trans hFixed

/-- Adaptive correct-view theorem whose off-diagonal premise is now the explicit finite
effective-residual `L²` quantity. -/
theorem tvDist_averagedCorrectTransform_realPublicView_le_residualL2
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ)
    (hDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError) :
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      diagonalError +
        Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalResidualL2Loss
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler coordinate := by
  have hCoupled :=
    tvDist_coupledDirectCorrectView_coupledDirectTargetView_le_residualL2
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      diagonalError hDiagonal
  unfold tvDist at hCoupled ⊢
  rw [averagedCorrectTransform_evalDist_eq_coupledDirectCorrectView
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
    params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate]
  rw [← coupledDirectTargetView_evalDist_eq_realPublicView
    (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget]
  exact hCoupled

/-- Coupled adaptive correct-view bound with the honest control ciphertext fully eliminated from
the off-diagonal analytic quantity. -/
theorem tvDist_coupledDirectCorrectView_coupledDirectTargetView_le_errorOnlyL2
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ)
    (hDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError) :
    tvDist
        (coupledDirectCorrectView (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (coupledDirectTargetView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) params targetRingErrorSampler
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) ≤
      diagonalError +
        Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalErrorOnlyL2Loss
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler coordinate := by
  exact
    (tvDist_coupledDirectCorrectView_coupledDirectTargetView_le_residualL2
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      diagonalError hDiagonal).trans
        (add_le_add_right
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalResidualL2Loss_le_errorOnly
            (degree := degree) (ringRank := ringRank) params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            targetRingErrorSampler coordinate)
          diagonalError)

/-- Public-view form of the same error-only adaptive correct-side bound. -/
theorem tvDist_averagedCorrectTransform_realPublicView_le_errorOnlyL2
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ)
    (hDiagonal : ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError) :
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      diagonalError +
        Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalErrorOnlyL2Loss
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler coordinate := by
  have hCoupled :=
    tvDist_coupledDirectCorrectView_coupledDirectTargetView_le_errorOnlyL2
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      diagonalError hDiagonal
  unfold tvDist at hCoupled ⊢
  rw [averagedCorrectTransform_evalDist_eq_coupledDirectCorrectView
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
    params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate]
  rw [← coupledDirectTargetView_evalDist_eq_realPublicView
    (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget]
  exact hCoupled

namespace DirectStatisticalCertificate

/-- Build the concrete adaptive security certificate from exactly the remaining correct-side
rank obligations: one averaged diagonal bound and the conditionally independent off-diagonal
source-to-target bounds.  Complementary-branch freshness remains the separate wrong-candidate
obligation of the native reduction. -/
noncomputable def ofCenteredBinomialOffDiagonalIsolation
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : Fin lweDimension → ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (freshnessDistance_le : ∀ coordinate,
      tvDist
          (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
            params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
          (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
            (queryCount := queryCount)
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
            keySwitchGadget) ≤ freshnessError coordinate) :
    DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget where
  correctError := fun coordinate =>
    diagonalError coordinate +
      ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
        offDiagonalError coordinate outputCoordinate
  freshnessError := freshnessError
  correctError_nonneg := by
    intro coordinate
    exact add_nonneg (diagonalError_nonneg coordinate)
      (Finset.sum_nonneg fun outputCoordinate _ =>
        offDiagonalError_nonneg coordinate outputCoordinate)
  freshnessError_nonneg := freshnessError_nonneg
  correctDistance_le := by
    intro coordinate
    exact tvDist_averagedCorrectTransform_realPublicView_le_offDiagonalIsolation
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      (diagonalError coordinate) (offDiagonalError coordinate)
      (diagonalDistance_le coordinate) (offDiagonalDistance_le coordinate)
  freshnessDistance_le := freshnessDistance_le

/-- Build the direct adaptive certificate with the off-diagonal control average internalized.
Only a uniform selected-diagonal bound and the already-averaged wrong-view bound remain as
construction laws. -/
noncomputable def ofCenteredBinomialAveragedOffDiagonal
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError freshnessError : Fin lweDimension → ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (freshnessDistance_le : ∀ coordinate,
      tvDist
          (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
            params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
          (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
            (queryCount := queryCount)
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
            keySwitchGadget) ≤ freshnessError coordinate) :
    DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget where
  correctError := fun coordinate =>
    diagonalError coordinate +
      Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalReplacementDistance
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler coordinate
  freshnessError := freshnessError
  correctError_nonneg := by
    intro coordinate
    exact add_nonneg (diagonalError_nonneg coordinate)
      (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalReplacementDistance_nonneg
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler coordinate)
  freshnessError_nonneg := freshnessError_nonneg
  correctDistance_le := by
    intro coordinate
    exact tvDist_averagedCorrectTransform_realPublicView_le_averagedOffDiagonal
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      (diagonalError coordinate) (diagonalDistance_le coordinate)
  freshnessDistance_le := freshnessDistance_le

/-- Build the preferred direct adaptive certificate from the explicit residual-vector `L²`
off-diagonal budget.  Only the selected diagonal and the already-averaged wrong-view law are
separate proof inputs; the complete off-diagonal ciphertext reduction is internal. -/
noncomputable def ofCenteredBinomialResidualL2
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError freshnessError : Fin lweDimension → ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (freshnessDistance_le : ∀ coordinate,
      tvDist
          (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
            params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
          (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
            (queryCount := queryCount)
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
            keySwitchGadget) ≤ freshnessError coordinate) :
    DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget where
  correctError := fun coordinate =>
    diagonalError coordinate +
      Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalResidualL2Loss
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler coordinate
  freshnessError := freshnessError
  correctError_nonneg := by
    intro coordinate
    exact add_nonneg (diagonalError_nonneg coordinate)
      (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalResidualL2Loss_nonneg
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler coordinate)
  freshnessError_nonneg := freshnessError_nonneg
  correctDistance_le := by
    intro coordinate
    exact tvDist_averagedCorrectTransform_realPublicView_le_residualL2
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      (diagonalError coordinate) (diagonalDistance_le coordinate)
  freshnessDistance_le := freshnessDistance_le

/-- Build the strongest direct adaptive certificate from the error-only off-diagonal budget.
The remaining maximum ranges over a Boolean candidate rather than any secret or ciphertext. -/
noncomputable def ofCenteredBinomialErrorOnlyL2
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError freshnessError : Fin lweDimension → ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (freshnessDistance_le : ∀ coordinate,
      tvDist
          (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
            params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
          (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
            (queryCount := queryCount)
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
            keySwitchGadget) ≤ freshnessError coordinate) :
    DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget where
  correctError := fun coordinate ↦
    diagonalError coordinate +
      Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalErrorOnlyL2Loss
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler coordinate
  freshnessError := freshnessError
  correctError_nonneg := by
    intro coordinate
    exact add_nonneg (diagonalError_nonneg coordinate)
      (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalErrorOnlyL2Loss_nonneg
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler coordinate)
  freshnessError_nonneg := freshnessError_nonneg
  correctDistance_le := by
    intro coordinate
    exact tvDist_averagedCorrectTransform_realPublicView_le_errorOnlyL2
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      (diagonalError coordinate) (diagonalDistance_le coordinate)
  freshnessDistance_le := freshnessDistance_le

/-- Install a direct native statistical certificate into the finite augmented paired-search
reduction when source and target KSK samplers coincide.  Callers choose the amplification
schedule; the exact threshold loss remains visible even when the effective gap is negative. -/
noncomputable def toAveragedReductionSameKeySwitch
    {q degree ringRank lweDimension keySwitchLevels queryCount eta keySwitchEta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (certificate : DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetRingErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
      inputErrorSampler keySwitchGadget)
    (rounds : PublicDistinguisher q (degree + 1) ringRank params.levels
      lweDimension keySwitchLevels queryCount → Fin lweDimension → ℕ)
    (threshold : PublicDistinguisher q (degree + 1) ringRank params.levels
      lweDimension keySwitchLevels queryCount → Fin lweDimension → ENNReal)
    (threshold_pos : ∀ distinguisher coordinate,
      0 < threshold distinguisher coordinate)
    (threshold_le_one : ∀ distinguisher coordinate,
      threshold distinguisher coordinate ≤ 1) :
    AveragedCandidateViewTransformerReduction q (degree + 1) ringRank params.levels
      lweDimension keySwitchLevels queryCount eta keySwitchEta inputErrorSampler
      targetRingErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
      (Gadget.Base.ringGadget params) keySwitchGadget where
  toTransformer := fun _ => certificate.toAveraged
  rounds := rounds
  threshold := threshold
  threshold_pos := threshold_pos
  threshold_le_one := threshold_le_one

end DirectStatisticalCertificate

/-- Exact wrong-branch bijectivity at every fixed mask identifies the mask-averaged branch view
with its uniform-BRK comparison for every fixed public context. -/
theorem maskedBranchExperiment_evalDist_eq_maskedUniform_of_wrongBranchFresh
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (hidden : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (hFresh : WrongBranchFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params) :
    evalDist
        (maskedBranchExperiment params coordinate (!hidden) challenge auxiliary) =
      evalDist (maskedUniformExperiment params challenge auxiliary) := by
  unfold maskedBranchExperiment maskedUniformExperiment
  refine evalDist_bind_congr' ($ᵗ BinarySecret lweDimension) fun mask => ?_
  exact branchExperimentAtMask_evalDist_eq_uniform params coordinate (!hidden)
    challenge auxiliary mask (hFresh coordinate hidden challenge auxiliary mask)

/-- The corresponding contextwise statistical freshness cost is exactly zero. -/
theorem tvDist_maskedBranchExperiment_maskedUniform_eq_zero_of_wrongBranchFresh
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (hidden : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (hFresh : WrongBranchFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params) :
    tvDist
        (maskedBranchExperiment params coordinate (!hidden) challenge auxiliary)
        (maskedUniformExperiment params challenge auxiliary) = 0 := by
  unfold tvDist
  rw [maskedBranchExperiment_evalDist_eq_maskedUniform_of_wrongBranchFresh
    params coordinate hidden challenge auxiliary hFresh]
  exact SPMF.tvDist_self _

/-- Named construction-specific boundary for native shifted TFHE.  It records exactly the
averaged diagonal self-correlation, conditionally independent off-diagonal source-to-target
distances, and complementary-branch rank/freshness distance.  No ordinary-LWE implication is
asserted by this structure. -/
structure WholeKeyRankCertificate
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  diagonalError : Fin lweDimension → ℝ
  offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ
  freshnessError : Fin lweDimension → ℝ
  diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate
  offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
    0 ≤ offDiagonalError coordinate outputCoordinate
  freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate
  diagonalDistance_le : ∀ coordinate,
    ∀ hidden : BinarySecret lweDimension,
    ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      tvDist
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
            params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            hidden ringSecret coordinate)
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
            params targetRingErrorSampler hidden ringSecret coordinate) ≤
        diagonalError coordinate
  offDiagonalDistance_le : ∀ coordinate,
    ∀ hidden : BinarySecret lweDimension,
    ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
    ∀ control ∈ support
      (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        hidden ringSecret coordinate),
    ∀ outputCoordinate, outputCoordinate ≠ coordinate →
      tvDist
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
            params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            hidden ringSecret coordinate control outputCoordinate)
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
            params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
        offDiagonalError coordinate outputCoordinate
  freshnessDistance_le : ∀ coordinate,
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤ freshnessError coordinate

/-- The explicit whole-key rank certificate specialized to a certified ring discrete-Gaussian
target sampler. -/
abbrev DiscreteGaussianWholeKeyRankCertificate
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (gaussianCertificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :=
  WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params
    (DiscreteGaussianSampler.ringSampler (degree + 1) gaussianCertificate)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget

namespace WholeKeyRankCertificate

/-- Exact fixed-mask wrong-branch bijectivity discharges the whole-key certificate's freshness
component with zero loss.  Only the diagonal and conditionally residualized off-diagonal
distance bounds remain to be supplied. -/
noncomputable def ofWrongBranchFresh
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (hFresh : WrongBranchFresh (degree := degree + 1) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget where
  diagonalError := diagonalError
  offDiagonalError := offDiagonalError
  freshnessError := fun _ => 0
  diagonalError_nonneg := diagonalError_nonneg
  offDiagonalError_nonneg := offDiagonalError_nonneg
  freshnessError_nonneg := by
    intro coordinate
    exact le_rfl
  diagonalDistance_le := diagonalDistance_le
  offDiagonalDistance_le := offDiagonalDistance_le
  freshnessDistance_le := by
    intro coordinate
    unfold tvDist
    rw [averagedWrongTransform_evalDist_eq_uniformPublicView
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate hFresh]
    exact le_of_eq (SPMF.tvDist_self _)

/-- Build the whole-key certificate from explicit mask-averaged single-row branch defects.
Compared with `ofWrongBranchFresh`, this constructor permits non-bijective row maps and charges
their exact statistical cost through `freshnessError`. -/
noncomputable def ofMaskedRowBranchDistance
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : Fin lweDimension → ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (rowDistance_le : ∀ coordinate hiddenAndContext,
      hiddenAndContext ∈ support
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget coordinate) →
      maskedRowBranchDistance params coordinate (!hiddenAndContext.1)
          hiddenAndContext.2.1 hiddenAndContext.2.2 ≤
        freshnessError coordinate) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget where
  diagonalError := diagonalError
  offDiagonalError := offDiagonalError
  freshnessError := freshnessError
  diagonalError_nonneg := diagonalError_nonneg
  offDiagonalError_nonneg := offDiagonalError_nonneg
  freshnessError_nonneg := freshnessError_nonneg
  diagonalDistance_le := diagonalDistance_le
  offDiagonalDistance_le := offDiagonalDistance_le
  freshnessDistance_le := by
    intro coordinate
    exact tvDist_averagedWrongTransform_uniformPublicView_le
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
      (freshnessError coordinate) (fun hiddenAndContext hsupport =>
        tvDist_maskedBranchExperiment_maskedUniformExperiment_le_of_maskedRowBranchDistance_le
          params coordinate (!hiddenAndContext.1) hiddenAndContext.2.1
          hiddenAndContext.2.2 (freshnessError coordinate)
          (rowDistance_le coordinate hiddenAndContext hsupport))

/-- Build the whole-key certificate from the actual average-case probability that an explicit
TLWE-row branch map fails bijectivity.  The probability is taken jointly over the generated
BRK/KSK/input-tape context and the independent scalar XOR mask, so rare bad public controls are
charged rather than ruled out support-wise. -/
noncomputable def ofAveragedRowwiseFailure
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : Fin lweDimension → ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (rowwiseFailure_le : ∀ coordinate,
      averagedWrongBranchRowwiseFailure (ringRank := ringRank)
          (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate ≤
        freshnessError coordinate) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget where
  diagonalError := diagonalError
  offDiagonalError := offDiagonalError
  freshnessError := freshnessError
  diagonalError_nonneg := diagonalError_nonneg
  offDiagonalError_nonneg := offDiagonalError_nonneg
  freshnessError_nonneg := freshnessError_nonneg
  diagonalDistance_le := diagonalDistance_le
  offDiagonalDistance_le := offDiagonalDistance_le
  freshnessDistance_le := by
    intro coordinate
    exact
      (tvDist_averagedWrongTransform_uniformPublicView_le_averagedWrongBranchRowwiseFailure
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
      (rowwiseFailure_le coordinate)

/-- Build the whole-key certificate from the one normalized wrong-candidate control-map failure
probability.  Exact translation conjugacy makes this strictly sharper than summing the same event
over every BRK output coordinate and TGSW row. -/
noncomputable def ofAveragedControlFailure
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : Fin lweDimension → ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (controlFailure_le : ∀ coordinate,
      averagedWrongBranchControlFailure (ringRank := ringRank)
          (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate ≤
        freshnessError coordinate) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofAveragedRowwiseFailure params targetRingErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget diagonalError offDiagonalError freshnessError
    diagonalError_nonneg offDiagonalError_nonneg freshnessError_nonneg
    diagonalDistance_le offDiagonalDistance_le fun coordinate =>
      (averagedWrongBranchRowwiseFailure_le_controlFailure
        (ringRank := ringRank) (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
      (controlFailure_le coordinate)

/-- Build the whole-key certificate from one coordinate-free canonical control defect.  The
freshness budget is shared by every scalar coordinate because the exact selected-control
marginalization removes the KSK, input tape, coordinate name, and all unselected BRK entries. -/
noncomputable def ofCanonicalControlFailure
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (canonicalControlFailure_le :
      averagedCanonicalWrongBranchControlFailure (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) ≤ freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofAveragedControlFailure params targetRingErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget diagonalError offDiagonalError
    (fun _ ↦ freshnessError) diagonalError_nonneg offDiagonalError_nonneg
    (fun _ ↦ freshnessError_nonneg) diagonalDistance_le offDiagonalDistance_le
    fun coordinate ↦ by
      rw [averagedWrongBranchControlFailure_eq_canonical
        (ringRank := ringRank) (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate]
      exact canonicalControlFailure_le

/-- Build the whole-key certificate from the centered-binomial message-one failure probability.
This is the normalized failure interface: neither the hidden scalar bit nor a scalar coordinate
appears in its remaining freshness premise. -/
noncomputable def ofMessageOneControlFailure
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFailure_le :
      averagedCanonicalMessageOneControlFailure (degree := degree)
        (ringRank := ringRank) params eta ≤ freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofCanonicalControlFailure params targetRingErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget diagonalError offDiagonalError freshnessError
    diagonalError_nonneg offDiagonalError_nonneg freshnessError_nonneg
    diagonalDistance_le offDiagonalDistance_le (by
      rw [averagedCanonicalWrongBranchControlFailure_eq_messageOne
        (ringRank := ringRank) (eta := eta) params]
      exact messageOneControlFailure_le)

/-- Build the whole-key certificate from the direct canonical one-row TV defect rather than a
zero-one bijectivity failure.  This route remains sound when non-bijective controls still have a
small pushforward distance; the explicit multiplier counts every independently transformed BRK
data row. -/
noncomputable def ofCanonicalControlDistance
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (canonicalControlDistance_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalWrongBranchControlDistance (ringRank := ringRank) params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta) ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget where
  diagonalError := diagonalError
  offDiagonalError := offDiagonalError
  freshnessError := fun _ ↦ freshnessError
  diagonalError_nonneg := diagonalError_nonneg
  offDiagonalError_nonneg := offDiagonalError_nonneg
  freshnessError_nonneg := fun _ ↦ freshnessError_nonneg
  diagonalDistance_le := diagonalDistance_le
  offDiagonalDistance_le := offDiagonalDistance_le
  freshnessDistance_le := by
    intro coordinate
    exact
      (tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedCanonicalControlDistance
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
      canonicalControlDistance_le

/-- Build the whole-key certificate from the direct message-one control defect.  This is the
statistical fallback to `ofMessageOneControlFailure`; it requires no bijectivity event and keeps
the explicit number of transformed BRK data rows in the bound. -/
noncomputable def ofMessageOneControlDistance
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlDistance_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlDistance (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofCanonicalControlDistance params targetRingErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget diagonalError offDiagonalError freshnessError
    diagonalError_nonneg offDiagonalError_nonneg freshnessError_nonneg
    diagonalDistance_le offDiagonalDistance_le (by
      rw [averagedCanonicalWrongBranchControlDistance_eq_messageOne
        (ringRank := ringRank) (eta := eta) params]
      exact messageOneControlDistance_le)

/-- Discharge the native direct statistical certificate from the named whole-key rank premise. -/
noncomputable def toDirect
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    {params : Gadget.Base.Parameters q}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : WholeKeyRankCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) (eta := eta)
      params targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget) :
    DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget :=
  DirectStatisticalCertificate.ofCenteredBinomialOffDiagonalIsolation
    params targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
    keySwitchGadget certificate.diagonalError certificate.offDiagonalError
    certificate.freshnessError certificate.diagonalError_nonneg
    certificate.offDiagonalError_nonneg certificate.freshnessError_nonneg
    certificate.diagonalDistance_le certificate.offDiagonalDistance_le
    certificate.freshnessDistance_le

/-- Install the whole-key rank premise directly into the averaged candidate-view interface. -/
noncomputable def toAveraged
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    {params : Gadget.Base.Parameters q}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : WholeKeyRankCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) (eta := eta)
      params targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget) :
    AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      targetRingErrorSampler keySwitchErrorSampler keySwitchErrorSampler
      inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget :=
  certificate.toDirect.toAveraged

/-- Build the finite augmented paired-search reduction from the named whole-key rank premise when
the source and target KSK use the same centered-binomial sampler. -/
noncomputable def toAveragedReductionSameKeySwitch
    {q degree ringRank lweDimension keySwitchLevels queryCount eta keySwitchEta : ℕ}
    [NeZero q]
    {params : Gadget.Base.Parameters q}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    {inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : WholeKeyRankCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) (eta := eta)
      params targetRingErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
      inputErrorSampler keySwitchGadget)
    (rounds : PublicDistinguisher q (degree + 1) ringRank params.levels
      lweDimension keySwitchLevels queryCount → Fin lweDimension → ℕ)
    (threshold : PublicDistinguisher q (degree + 1) ringRank params.levels
      lweDimension keySwitchLevels queryCount → Fin lweDimension → ENNReal)
    (threshold_pos : ∀ distinguisher coordinate,
      0 < threshold distinguisher coordinate)
    (threshold_le_one : ∀ distinguisher coordinate,
      threshold distinguisher coordinate ≤ 1) :
    AveragedCandidateViewTransformerReduction q (degree + 1) ringRank params.levels
      lweDimension keySwitchLevels queryCount eta keySwitchEta inputErrorSampler
      targetRingErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
      (Gadget.Base.ringGadget params) keySwitchGadget :=
  certificate.toDirect.toAveragedReductionSameKeySwitch params targetRingErrorSampler
    inputErrorSampler keySwitchGadget rounds threshold threshold_pos threshold_le_one

end WholeKeyRankCertificate

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted
