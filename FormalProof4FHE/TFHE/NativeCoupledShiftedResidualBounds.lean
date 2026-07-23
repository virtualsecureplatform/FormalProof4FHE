/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeShiftedCenteredBinomialBounds
import FormalProof4FHE.TFHE.NativeShiftedDiscreteGaussianBounds

/-!
# Coupled Centered-Binomial Residual Bounds for the Native Shifted Evaluator

The public augmented coordinate source is sampled from a complete native scalar/ring secret
pair, but its existing security certificate later quantifies over a second independent pair.
That independence forces the conservative modular fallback.  This file retains the original
pair as a latent proof witness and couples the evaluator's target to

* the scalar secret XORed with the public evaluator mask; and
* the unchanged source ring secret.

Under this coupling, every transported source-BRK row still has centered-binomial width `eta`.
Consequently the exact correct residual and its certified discrete-Gaussian smudging cost use the
sharp construction-specific `centeredBinomialResidualBound`, not `q / 2`.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

noncomputable section

open FormalProof4FHE.TFHE
open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- The augmented real source with its complete scalar/ring secret pair retained as a latent
proof witness. -/
noncomputable def pairedSource
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank tgswLevels lweDimension
        keySwitchLevels queryCount) := do
  let secrets ←
    (problem (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (problem (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget).sampleChallenge secrets
  let auxiliary ←
    (problem (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  return (secrets, challenge, auxiliary)

/-- Projecting the latent pair down to one scalar bit recovers the existing coordinate source
distribution exactly. -/
theorem pairedSource_project_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        ((fun source : Secret lweDimension ringRank degree ×
            PublicContext q degree ringRank tgswLevels lweDimension
              keySwitchLevels queryCount ↦
            (source.1.1 coordinate, source.2)) <$>
          pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
            (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget) =
      evalDist
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget coordinate) := by
  simp [pairedSource, coordinateSource, scalarSource, monad_norm]

/-- Support of the paired centered-binomial source exposes support of its monomial-KDM BRK under
the retained source secret pair. -/
theorem pairedSource_challenge_mem_support
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    {source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount}
    (hsource : source ∈ support
      (pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount)
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget)) :
    source.2.1 ∈ support
      (Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
        q (degree + 1) ringRank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        (Gadget.Base.ringGadget params) source.1.1 source.1.2) := by
  unfold pairedSource at hsource
  rw [mem_support_bind_iff] at hsource
  obtain ⟨secrets, _hsecrets, hsource⟩ := hsource
  rw [mem_support_bind_iff] at hsource
  obtain ⟨challenge, hchallenge, hsource⟩ := hsource
  rw [mem_support_bind_iff] at hsource
  obtain ⟨auxiliary, _hauxiliary, hsource⟩ := hsource
  simp only [support_pure, Set.mem_singleton_iff] at hsource
  subst source
  exact hchallenge

/-- Every transported source row in a supported paired source retains the centered-binomial
width under the fully coupled target scalar and ring secrets. -/
theorem cInfNorm_pairedSource_transportedRowError_le_eta
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    {source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount}
    (hsource : source ∈ support
      (pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount)
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget))
    (mask : BinarySecret lweDimension)
    (coordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1))
        (embedRingSecret q source.1.2) (Gadget.Base.ringGadget params)
        (embedBit
          (Native.ScalarSecretRandomization.maskedSecret source.1.1 mask coordinate))
        ((transportedView params source.2.1 source.2.2 mask).1.1 coordinate)
        index) ≤ eta := by
  change LatticeCrypto.cInfNorm
    (TGSW.rowError (R := RLWE.Rq q (degree + 1))
      (embedRingSecret q source.1.2) (Gadget.Base.ringGadget params)
      (embedBit
        (Native.ScalarSecretRandomization.maskedSecret source.1.1 mask coordinate))
      (Native.ScalarSecretRandomization.transformBootstrappingKey
        (Gadget.Base.ringGadget params) mask source.2.1 coordinate) index) ≤ eta
  exact Native.ShiftedResidualBounds.cInfNorm_transformMonomialBootstrappingKey_centeredBinomial_le_eta
    (Gadget.Base.ringGadget params) source.1.1 mask source.1.2
    (pairedSource_challenge_mem_support params keySwitchErrorSampler
      inputErrorSampler keySwitchGadget hsource) coordinate index

/-- The exact fixed-coin correct residual uses the sharp centered-binomial budget under the
latent paired-source coupling. -/
theorem cInfNorm_correctResidualAtCoupledTarget_le_centeredBinomialBound
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    {source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount}
    (hsource : source ∈ support
      (pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount)
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget))
    (coordinate outputCoordinate : Fin lweDimension)
    (coin : Coin q (degree + 1) ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    LatticeCrypto.cInfNorm
        ((correctResidualAtTarget params coordinate
          (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
          source.2.1 source.2.2 source.1.2 coin).1
          outputCoordinate (finProdFinEquiv index)) ≤
      Native.ShiftedResidualBounds.centeredBinomialResidualBound
        params (degree + 1) ringRank eta := by
  change LatticeCrypto.cInfNorm
      (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
        (embedRingSecret q source.1.2)
        (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
        coordinate (transportedView params source.2.1 source.2.2 coin.1).1.1
        coin.2 outputCoordinate (finProdFinEquiv index)) ≤ _
  exact Native.ShiftedResidualBounds.cInfNorm_correctBootstrappingResidual_le_centeredBinomialBound_of_source
    params (embedRingSecret q source.1.2)
    (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
    coordinate outputCoordinate
    (transportedView params source.2.1 source.2.2 coin.1).1.1 coin.2 index
    (fun sourceCoordinate sourceIndex ↦
      cInfNorm_pairedSource_transportedRowError_le_eta params
        keySwitchErrorSampler inputErrorSampler keySwitchGadget hsource coin.1
        sourceCoordinate sourceIndex)

/-- The fixed-coin coupled residual's certified discrete-Gaussian smudging cost uses the sharp
centered-binomial residual envelope. -/
theorem evaluationKeySmudgingCost_correctResidualAtCoupledTarget_discreteGaussian_le
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    {source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount}
    (hsource : source ∈ support
      (pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount)
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget))
    (coordinate : Fin lweDimension)
    (coin : Coin q (degree + 1) ringRank params.levels lweDimension) :
    Native.ConditionalSmudging.evaluationKeySmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        keySwitchErrorSampler
        (correctResidualAtTarget params coordinate
          (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
          source.2.1 source.2.2 source.1.2 coin).1
        (correctResidualAtTarget params coordinate
          (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
          source.2.1 source.2.2 source.1.2 coin).2 ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta)) := by
  apply evaluationKeySmudgingCost_correctResidualAtTarget_discreteGaussian_le
  intro outputCoordinate index
  exact cInfNorm_pairedSource_transportedRowError_le_eta params
    keySwitchErrorSampler inputErrorSampler keySwitchGadget hsource coin.1
    outputCoordinate index

/-- Linear-unit-shift version of the fixed-coin coupled smudging bound. -/
theorem evaluationKeySmudgingCost_correctResidualAtCoupledTarget_discreteGaussian_le_linear
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    {source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount}
    (hsource : source ∈ support
      (pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount)
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget))
    (coordinate : Fin lweDimension)
    (coin : Coin q (degree + 1) ringRank params.levels lweDimension) :
    Native.ConditionalSmudging.evaluationKeySmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        keySwitchErrorSampler
        (correctResidualAtTarget params coordinate
          (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
          source.2.1 source.2.2 source.1.2 coin).1
        (correctResidualAtTarget params coordinate
          (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
          source.2.1 source.2.2 source.1.2 coin).2 ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta)) := by
  change Native.ConditionalSmudging.evaluationKeySmudgingCost
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchErrorSampler
      (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
        (embedRingSecret q source.1.2)
        (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
        coordinate (transportedView params source.2.1 source.2.2 coin.1).1.1
        coin.2) 0 ≤ _
  rw [Native.ConditionalSmudging.evaluationKeySmudgingCost_zeroKeySwitch]
  apply
    Native.ShiftedResidualBounds.bootstrappingSmudgingCost_correctResidual_discreteGaussian_le_linear
  intro outputCoordinate index
  exact cInfNorm_pairedSource_transportedRowError_le_eta params
    keySwitchErrorSampler inputErrorSampler keySwitchGadget hsource coin.1
    outputCoordinate index

/-! ## Coupled averaged residual endpoint -/

/-- One fixed paired source and evaluator coin, with only the residual-bearing BRK freshly
generated at the coupled target.  The KSK and input tape are the exact public scalar transports
of the source auxiliary context. -/
noncomputable def coupledResidualViewAtSourceCoin
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (coordinate : Fin lweDimension)
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) := do
  let targetSecret :=
    Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1
  let bootstrappingKey ←
    Native.ConditionalSmudging.generateResidualBootstrappingKey
      q degree ringRank params.levels lweDimension targetRingErrorSampler
      (Gadget.Base.ringGadget params) targetSecret source.1.2
      (correctResidualAtTarget params coordinate targetSecret
        source.2.1 source.2.2 source.1.2 coin).1
  return (bootstrappingKey,
    (transportedView params source.2.1 source.2.2 coin.1).1.2,
    (transportedView params source.2.1 source.2.2 coin.1).2)

/-- The fixed-source comparison view replaces the residual BRK by the exact monomial native BRK
at the same coupled target and retains the identical transported KSK and tape. -/
noncomputable def coupledMonomialViewAtSourceCoin
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) := do
  let targetSecret :=
    Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1
  let bootstrappingKey ←
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q degree ringRank params.levels lweDimension targetRingErrorSampler
      (Gadget.Base.ringGadget params) targetSecret source.1.2
  return (bootstrappingKey,
    (transportedView params source.2.1 source.2.2 coin.1).1.2,
    (transportedView params source.2.1 source.2.2 coin.1).2)

/-- Fixed-source/fixed-coin data processing lifts the native BRK smudging theorem while keeping
the transported public auxiliary context verbatim. -/
theorem tvDist_coupledResidualViewAtSourceCoin_coupledMonomialViewAtSourceCoin_le
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (coordinate : Fin lweDimension)
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    tvDist
        (coupledResidualViewAtSourceCoin params targetRingErrorSampler
          coordinate source coin)
        (coupledMonomialViewAtSourceCoin params targetRingErrorSampler
          source coin) ≤
      Native.ConditionalSmudging.bootstrappingSmudgingCost
        targetRingErrorSampler
        (correctResidualAtTarget params coordinate
          (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
          source.2.1 source.2.2 source.1.2 coin).1 := by
  let finish := fun bootstrappingKey :
      Native.BootstrappingKey q degree ringRank params.levels lweDimension =>
    (bootstrappingKey,
      (transportedView params source.2.1 source.2.2 coin.1).1.2,
      (transportedView params source.2.1 source.2.2 coin.1).2)
  let residualSampler :=
    Native.ConditionalSmudging.generateResidualBootstrappingKey
      q degree ringRank params.levels lweDimension targetRingErrorSampler
      (Gadget.Base.ringGadget params)
      (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
      source.1.2
      (correctResidualAtTarget params coordinate
        (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
        source.2.1 source.2.2 source.1.2 coin).1
  let targetSampler :=
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q degree ringRank params.levels lweDimension targetRingErrorSampler
      (Gadget.Base.ringGadget params)
      (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
      source.1.2
  have hmap := tvDist_map_le (m := ProbComp) finish residualSampler targetSampler
  have hsmudge : tvDist residualSampler targetSampler ≤
      Native.ConditionalSmudging.bootstrappingSmudgingCost
        targetRingErrorSampler
        (correctResidualAtTarget params coordinate
          (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
          source.2.1 source.2.2 source.1.2 coin).1 :=
    Native.ConditionalSmudging.tvDist_generateResidualBootstrappingKey_generateMonomial_le
      q degree ringRank params.levels lweDimension targetRingErrorSampler
      (Gadget.Base.ringGadget params)
      (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
      source.1.2
      (correctResidualAtTarget params coordinate
        (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
        source.2.1 source.2.2 source.1.2 coin).1
  simpa only [coupledResidualViewAtSourceCoin,
    coupledMonomialViewAtSourceCoin, residualSampler, targetSampler, finish,
    map_eq_bind_pure_comp, Function.comp_def] using hmap.trans hsmudge

/-- Average the coupled residual view over the actual complete paired source and the evaluator's
uniform mask/true-branch coin. -/
noncomputable def coupledAveragedResidualRealView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount) := do
  let source ← pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount)
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
    keySwitchGadget
  let coin ← sampleCoin q (degree + 1) ringRank params.levels lweDimension
  coupledResidualViewAtSourceCoin params targetRingErrorSampler coordinate source coin

/-- The corresponding averaged exact monomial comparison view at the same coupled targets. -/
noncomputable def coupledAveragedMonomialRealView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount) := do
  let source ← pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount)
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
    keySwitchGadget
  let coin ← sampleCoin q (degree + 1) ringRank params.levels lweDimension
  coupledMonomialViewAtSourceCoin params targetRingErrorSampler source coin

/-- The sharp centered-binomial/discrete-Gaussian cost survives averaging over the supported
paired source and every evaluator coin. -/
theorem tvDist_coupledAveragedResidualRealView_coupledAveragedMonomialRealView_le
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (coupledAveragedResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (coupledAveragedMonomialRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta)) := by
  let sourceSampler := pairedSource (ringRank := ringRank)
    (lweDimension := lweDimension) (queryCount := queryCount)
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
    keySwitchGadget
  let coinSampler := sampleCoin q (degree + 1) ringRank params.levels lweDimension
  let residualView := fun source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount =>
    coinSampler >>= fun coin =>
      coupledResidualViewAtSourceCoin params
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        coordinate source coin
  let targetView := fun source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount =>
    coinSampler >>= fun coin =>
      coupledMonomialViewAtSourceCoin params
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        source coin
  apply tvDist_bind_left_le_const sourceSampler residualView targetView
  intro source hsource
  apply tvDist_bind_left_le_const'
  intro coin
  refine (tvDist_coupledResidualViewAtSourceCoin_coupledMonomialViewAtSourceCoin_le
    params (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
    coordinate source coin).trans ?_
  change Native.ConditionalSmudging.bootstrappingSmudgingCost
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
        (embedRingSecret q source.1.2)
        (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
        coordinate (transportedView params source.2.1 source.2.2 coin.1).1.1
        coin.2) ≤ _
  apply Native.ShiftedResidualBounds.bootstrappingSmudgingCost_correctResidual_discreteGaussian_le
  intro outputCoordinate index
  exact cInfNorm_pairedSource_transportedRowError_le_eta params
    keySwitchErrorSampler inputErrorSampler keySwitchGadget hsource coin.1
    outputCoordinate index

/-- Averaged coupled endpoint with the sharper linear unit-shift Gaussian cost. -/
theorem tvDist_coupledAveragedResidualRealView_coupledAveragedMonomialRealView_le_linear
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (coupledAveragedResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (coupledAveragedMonomialRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta)) := by
  let sourceSampler := pairedSource (ringRank := ringRank)
    (lweDimension := lweDimension) (queryCount := queryCount)
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
    keySwitchGadget
  let coinSampler := sampleCoin q (degree + 1) ringRank params.levels lweDimension
  let residualView := fun source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount =>
    coinSampler >>= fun coin =>
      coupledResidualViewAtSourceCoin params
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        coordinate source coin
  let targetView := fun source : Secret lweDimension ringRank (degree + 1) ×
      PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount =>
    coinSampler >>= fun coin =>
      coupledMonomialViewAtSourceCoin params
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        source coin
  apply tvDist_bind_left_le_const sourceSampler residualView targetView
  intro source hsource
  apply tvDist_bind_left_le_const'
  intro coin
  refine (tvDist_coupledResidualViewAtSourceCoin_coupledMonomialViewAtSourceCoin_le
    params (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
    coordinate source coin).trans ?_
  change Native.ConditionalSmudging.bootstrappingSmudgingCost
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
        (embedRingSecret q source.1.2)
        (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
        coordinate (transportedView params source.2.1 source.2.2 coin.1).1.1
        coin.2) ≤ _
  apply
    Native.ShiftedResidualBounds.bootstrappingSmudgingCost_correctResidual_discreteGaussian_le_linear
  intro outputCoordinate index
  exact cInfNorm_pairedSource_transportedRowError_le_eta params
    keySwitchErrorSampler inputErrorSampler keySwitchGadget hsource coin.1
    outputCoordinate index

/-- The averaged coupled monomial comparison is exactly the ordinary augmented real endpoint at
the target ring-error law.  The source BRK and unused true branch erase, while uniform scalar XOR
masking transports the retained KSK and tape to a fresh uniform scalar key. -/
theorem coupledAveragedMonomialRealView_evalDist_eq_realPublicView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist
        (coupledAveragedMonomialRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
          keySwitchErrorSampler inputErrorSampler keySwitchGadget) =
      evalDist
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) := by
  let ScalarSecrets := sampleLweSecret lweDimension
  let RingSecrets := sampleRingSecret ringRank (degree + 1)
  let SourceBootstrap := fun (lweSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank (degree + 1)) =>
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      (Gadget.Base.ringGadget params) lweSecret ringSecret
  let Aux := fun (lweSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank (degree + 1)) => do
    let keySwitchKey ← Native.generateKeySwitchKey q lweDimension
      (ringRank * (degree + 1)) keySwitchLevels keySwitchErrorSampler
      keySwitchGadget (keyExtract ringSecret) lweSecret
    let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret lweSecret) 0
    return (keySwitchKey, tape)
  let Masks := $ᵗ BinarySecret lweDimension
  let TrueBranches :=
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  let TargetBootstrap := fun (lweSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank (degree + 1)) =>
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension targetRingErrorSampler
      (Gadget.Base.ringGadget params) lweSecret ringSecret
  let transformAux := fun (mask : BinarySecret lweDimension)
      (aux : Native.KeySwitchKey q lweDimension (ringRank * (degree + 1))
          keySwitchLevels × KeySwitchFirstSecurity.InputTape q lweDimension queryCount) =>
    (Native.ScalarSecretRandomization.transformKeySwitchKey mask aux.1,
      Native.ScalarSecretRandomization.transformBatch mask aux.2)
  let finish := fun
      (bootstrappingKey : Native.BootstrappingKey q (degree + 1) ringRank
        params.levels lweDimension)
      (aux : Native.KeySwitchKey q lweDimension (ringRank * (degree + 1))
          keySwitchLevels × KeySwitchFirstSecurity.InputTape q lweDimension queryCount) =>
    (bootstrappingKey, aux.1, aux.2)
  have hAuxTransport : ∀ (lweSecret mask : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank (degree + 1)),
      evalDist (transformAux mask <$> Aux lweSecret ringSecret) =
        evalDist (Aux
          (Native.ScalarSecretRandomization.maskedSecret lweSecret mask)
          ringSecret) := by
    intro lweSecret mask ringSecret
    exact Native.ScalarSecretRandomization.independentPair_map_evalDist_congr
      _ _ _ _ _ _
      (Native.ScalarSecretRandomization.transformKeySwitchKey_generate_evalDist
        keySwitchErrorSampler keySwitchGadget (keyExtract ringSecret)
        lweSecret mask)
      (Native.ScalarSecretRandomization.transformBatch_batchEncrypt_evalDist
        inputErrorSampler lweSecret mask 0)
  have hMaskedAux : ∀ (lweSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank (degree + 1)),
      evalDist (do
        let mask ← Masks
        let aux ← Aux lweSecret ringSecret
        return (Native.ScalarSecretRandomization.maskedSecret lweSecret mask,
          transformAux mask aux)) =
      evalDist (do
        let freshSecret ← ScalarSecrets
        let aux ← Aux freshSecret ringSecret
        return (freshSecret, aux)) := by
    intro lweSecret ringSecret
    simpa only [Masks, ScalarSecrets, sampleLweSecret] using
      (Native.ScalarSecretRandomization.sampleMaskedView_evalDist lweSecret
        (fun freshSecret => Aux freshSecret ringSecret) transformAux
        (hAuxTransport lweSecret · ringSecret))
  have hshape :
      evalDist
          (coupledAveragedMonomialRealView (ringRank := ringRank)
            (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
            keySwitchErrorSampler inputErrorSampler keySwitchGadget) =
        evalDist (ScalarSecrets >>= fun lweSecret =>
          RingSecrets >>= fun ringSecret =>
          SourceBootstrap lweSecret ringSecret >>= fun _ =>
          Aux lweSecret ringSecret >>= fun aux =>
          Masks >>= fun mask =>
          TrueBranches >>= fun _ =>
          TargetBootstrap
            (Native.ScalarSecretRandomization.maskedSecret lweSecret mask)
            ringSecret >>= fun bootstrappingKey =>
          pure (finish bootstrappingKey (transformAux mask aux))) := by
    simp [coupledAveragedMonomialRealView, pairedSource, sampleCoin,
      coupledMonomialViewAtSourceCoin, transportedView, problem,
      LWE.AuxiliaryInput.Search.exactRecoveryProblem,
      KeySwitchFirstFiniteView.augmentedCircularProblem,
      KeySwitchFirstFiniteView.secretSampler,
      ScalarTransport.transformView,
      Native.ScalarSecretRandomization.transformEvaluationKeyPair,
      ScalarSecrets, RingSecrets, SourceBootstrap, Aux, Masks, TrueBranches,
      TargetBootstrap, transformAux, finish, monad_norm]
  rw [hshape]
  calc
    _ = evalDist (ScalarSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        Aux lweSecret ringSecret >>= fun aux =>
        Masks >>= fun mask =>
        TrueBranches >>= fun _ =>
        TargetBootstrap
          (Native.ScalarSecretRandomization.maskedSecret lweSecret mask)
          ringSecret >>= fun bootstrappingKey =>
        pure (finish bootstrappingKey (transformAux mask aux))) := by
      refine evalDist_bind_congr' ScalarSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (SourceBootstrap lweSecret ringSecret) (by simp [SourceBootstrap]) _
    _ = evalDist (ScalarSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        Aux lweSecret ringSecret >>= fun aux =>
        Masks >>= fun mask =>
        TargetBootstrap
          (Native.ScalarSecretRandomization.maskedSecret lweSecret mask)
          ringSecret >>= fun bootstrappingKey =>
        pure (finish bootstrappingKey (transformAux mask aux))) := by
      refine evalDist_bind_congr' ScalarSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      refine evalDist_bind_congr' (Aux lweSecret ringSecret) fun aux => ?_
      refine evalDist_bind_congr' Masks fun mask => ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        TrueBranches (by simp [TrueBranches]) _
    _ = evalDist (ScalarSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        Masks >>= fun mask =>
        Aux lweSecret ringSecret >>= fun aux =>
        TargetBootstrap
          (Native.ScalarSecretRandomization.maskedSecret lweSecret mask)
          ringSecret >>= fun bootstrappingKey =>
        pure (finish bootstrappingKey (transformAux mask aux))) := by
      refine evalDist_bind_congr' ScalarSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      exact evalDist_bind_bind_swap (Aux lweSecret ringSecret) Masks _
    _ = evalDist (ScalarSecrets >>= fun _ =>
        RingSecrets >>= fun ringSecret =>
        ScalarSecrets >>= fun freshSecret =>
        Aux freshSecret ringSecret >>= fun aux =>
        TargetBootstrap freshSecret ringSecret >>= fun bootstrappingKey =>
        pure (finish bootstrappingKey aux)) := by
      refine evalDist_bind_congr' ScalarSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      let continuation := fun maskedAndAux : BinarySecret lweDimension ×
          (Native.KeySwitchKey q lweDimension (ringRank * (degree + 1))
            keySwitchLevels × KeySwitchFirstSecurity.InputTape q lweDimension queryCount) =>
        TargetBootstrap maskedAndAux.1 ringSecret >>= fun bootstrappingKey =>
          pure (finish bootstrappingKey maskedAndAux.2)
      simpa only [continuation, bind_assoc, pure_bind] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (hMaskedAux lweSecret ringSecret) continuation)
    _ = evalDist (RingSecrets >>= fun ringSecret =>
        ScalarSecrets >>= fun freshSecret =>
        Aux freshSecret ringSecret >>= fun aux =>
        TargetBootstrap freshSecret ringSecret >>= fun bootstrappingKey =>
        pure (finish bootstrappingKey aux)) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ScalarSecrets (by simp [ScalarSecrets]) _
    _ = evalDist (ScalarSecrets >>= fun freshSecret =>
        RingSecrets >>= fun ringSecret =>
        Aux freshSecret ringSecret >>= fun aux =>
        TargetBootstrap freshSecret ringSecret >>= fun bootstrappingKey =>
        pure (finish bootstrappingKey aux)) :=
      evalDist_bind_bind_swap RingSecrets ScalarSecrets _
    _ = evalDist (ScalarSecrets >>= fun freshSecret =>
        RingSecrets >>= fun ringSecret =>
        TargetBootstrap freshSecret ringSecret >>= fun bootstrappingKey =>
        Aux freshSecret ringSecret >>= fun aux =>
        pure (finish bootstrappingKey aux)) := by
      refine evalDist_bind_congr' ScalarSecrets fun freshSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      exact evalDist_bind_bind_swap (Aux freshSecret ringSecret)
        (TargetBootstrap freshSecret ringSecret) _
    _ = _ := by
      simp [realPublicView, KeySwitchFirstFiniteView.augmentedCircularProblem,
        KeySwitchFirstFiniteView.secretSampler, ScalarSecrets, RingSecrets,
        TargetBootstrap, Aux, finish, monad_norm]

/-- End-to-end correct-side smudging for the paired-source coupling: the explicit averaged
residual endpoint is close to the ordinary augmented real target with the sharp
centered-binomial residual envelope. -/
theorem tvDist_coupledAveragedResidualRealView_realPublicView_le
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (coupledAveragedResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta)) := by
  have h :=
    tvDist_coupledAveragedResidualRealView_coupledAveragedMonomialRealView_le
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
      params certificate keySwitchErrorSampler inputErrorSampler keySwitchGadget
      coordinate
  unfold tvDist at h ⊢
  rw [coupledAveragedMonomialRealView_evalDist_eq_realPublicView
    (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params
    (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget] at h
  exact h

/-- End-to-end correct-side smudging with the sharper linear unit-shift Gaussian cost. -/
theorem tvDist_coupledAveragedResidualRealView_realPublicView_le_linear
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (coupledAveragedResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta)) := by
  have h :=
    tvDist_coupledAveragedResidualRealView_coupledAveragedMonomialRealView_le_linear
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
      params certificate keySwitchErrorSampler inputErrorSampler keySwitchGadget
      coordinate
  unfold tvDist at h ⊢
  rw [coupledAveragedMonomialRealView_evalDist_eq_realPublicView
    (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params
    (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget] at h
  exact h

/-- End-to-end coupled correct-side distance with the Gaussian term reduced to an explicit
finite-window expression. -/
theorem tvDist_coupledAveragedResidualRealView_realPublicView_le_exp_half_window
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (window : ℕ)
    (hwindow : (window : ℝ) ≤ ModularGaussian.integerStddev q alpha) :
    tvDist
        (coupledAveragedResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          (2 * certificate.bound.toReal +
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta : ℝ) *
              (Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ)))) := by
  exact (tvDist_coupledAveragedResidualRealView_realPublicView_le_linear
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
    params certificate keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (DiscreteGaussianSampler.scalarLinearShiftBound_le_exp_half_window
            certificate
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta)
            window hwindow)
          (Nat.cast_nonneg (degree + 1)))
        (Nat.cast_nonneg _))

/-- The sharp correct-side loss contributed by one coupled centered-binomial source and the
certified modular discrete-Gaussian target sampler. -/
def coupledCenteredBinomialDiscreteGaussianSmudgingError
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (degree ringRank lweDimension eta : ℕ) : ℝ :=
  ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
    ((degree : ℝ) *
      DiscreteGaussianSampler.scalarShiftEnvelope certificate
        (Native.ShiftedResidualBounds.centeredBinomialResidualBound
          params degree ringRank eta))

/-- Sharper coupled correct-side loss based on one integer-Gaussian unit shift. -/
def coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (degree ringRank lweDimension eta : ℕ) : ℝ :=
  ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
    ((degree : ℝ) *
      DiscreteGaussianSampler.scalarLinearShiftBound certificate
        (Native.ShiftedResidualBounds.centeredBinomialResidualBound
          params degree ringRank eta))

/-- Explicit finite-window upper bound for the coupled centered-binomial correct-side loss. -/
theorem coupledCenteredBinomialDiscreteGaussianLinearSmudgingError_le_exp_half_window
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (degree ringRank lweDimension eta window : ℕ)
    (hwindow : (window : ℝ) ≤ ModularGaussian.integerStddev q alpha) :
    coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
        params certificate degree ringRank lweDimension eta ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        ((degree : ℝ) *
          (2 * certificate.bound.toReal +
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params degree ringRank eta : ℝ) *
              (Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ)))) := by
  unfold coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (DiscreteGaussianSampler.scalarLinearShiftBound_le_exp_half_window
        certificate
        (Native.ShiftedResidualBounds.centeredBinomialResidualBound
          params degree ringRank eta)
        window hwindow)
      (Nat.cast_nonneg degree))
    (Nat.cast_nonneg _)

namespace DirectStatisticalCertificate

/-- Build the complete direct candidate-view certificate from the two genuinely remaining
construction laws.  The correct-side arithmetic is discharged automatically by the coupled
centered-binomial/discrete-Gaussian theorem; callers provide only output normal-form freshness
for the actual CMux and the complementary-branch freshness bound. -/
noncomputable def ofCoupledCenteredBinomialDiscreteGaussian
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (normalFormError freshnessError : Fin lweDimension → ℝ)
    (normalFormError_nonneg : ∀ coordinate, 0 ≤ normalFormError coordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (normalFormDistance_le : ∀ coordinate,
      tvDist
          (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
            params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
          (coupledAveragedResidualRealView (ringRank := ringRank)
            (queryCount := queryCount) (eta := eta) params
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
        normalFormError coordinate)
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
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget where
  correctError := fun coordinate =>
    normalFormError coordinate +
      coupledCenteredBinomialDiscreteGaussianSmudgingError
        params certificate (degree + 1) ringRank lweDimension eta
  freshnessError := freshnessError
  correctError_nonneg := by
    intro coordinate
    apply add_nonneg (normalFormError_nonneg coordinate)
    apply mul_nonneg
    · positivity
    · apply mul_nonneg
      · positivity
      · exact DiscreteGaussianSampler.scalarShiftEnvelope_nonneg _ _
  freshnessError_nonneg := freshnessError_nonneg
  correctDistance_le := by
    intro coordinate
    let residualView := coupledAveragedResidualRealView (ringRank := ringRank)
      (queryCount := queryCount) (eta := eta) params
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
    have hsmudge : tvDist residualView
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
        coupledCenteredBinomialDiscreteGaussianSmudgingError
          params certificate (degree + 1) ringRank lweDimension eta := by
      simpa only [residualView,
        coupledCenteredBinomialDiscreteGaussianSmudgingError] using
        (tvDist_coupledAveragedResidualRealView_realPublicView_le
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params certificate keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
    exact (tvDist_triangle _ residualView _).trans
      (add_le_add (normalFormDistance_le coordinate) hsmudge)
  freshnessDistance_le := freshnessDistance_le

/-- Build the direct candidate-view certificate with the sharper coupled linear unit-shift
Gaussian cost.  Only output normal-form freshness and complementary-branch freshness remain. -/
noncomputable def ofCoupledCenteredBinomialDiscreteGaussianLinearSmudging
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (normalFormError freshnessError : Fin lweDimension → ℝ)
    (normalFormError_nonneg : ∀ coordinate, 0 ≤ normalFormError coordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (normalFormDistance_le : ∀ coordinate,
      tvDist
          (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
            params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
          (coupledAveragedResidualRealView (ringRank := ringRank)
            (queryCount := queryCount) (eta := eta) params
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
        normalFormError coordinate)
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
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget where
  correctError := fun coordinate =>
    normalFormError coordinate +
      coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
        params certificate (degree + 1) ringRank lweDimension eta
  freshnessError := freshnessError
  correctError_nonneg := by
    intro coordinate
    apply add_nonneg (normalFormError_nonneg coordinate)
    apply mul_nonneg
    · positivity
    · apply mul_nonneg
      · positivity
      · exact DiscreteGaussianSampler.scalarLinearShiftBound_nonneg _ _
  freshnessError_nonneg := freshnessError_nonneg
  correctDistance_le := by
    intro coordinate
    let residualView := coupledAveragedResidualRealView (ringRank := ringRank)
      (queryCount := queryCount) (eta := eta) params
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
    have hsmudge : tvDist residualView
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
        coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
          params certificate (degree + 1) ringRank lweDimension eta := by
      simpa only [residualView,
        coupledCenteredBinomialDiscreteGaussianLinearSmudgingError] using
        (tvDist_coupledAveragedResidualRealView_realPublicView_le_linear
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params certificate keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
    exact (tvDist_triangle _ residualView _).trans
      (add_le_add (normalFormDistance_le coordinate) hsmudge)
  freshnessDistance_le := freshnessDistance_le

end DirectStatisticalCertificate

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted
