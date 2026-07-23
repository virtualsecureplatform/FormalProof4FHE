/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeConditionalSmudging
import FormalProof4FHE.TFHE.AveragedCandidateView
import FormalProof4FHE.TFHE.PointwiseCandidateView
import FormalProof4FHE.TFHE.WidenedAuxiliaryInputSearchToDecision

/-!
# Native Residual Normal Forms for Conditional Candidate Views

This module connects the native BRK+KSK smudging theorem to the pointwise candidate-view
interface consumed by search-to-decision amplification.

The correct-candidate normal form samples fresh uniform scalar and ring secrets, then generates
the exact monomial-CircLWE BRK and real KSK with fixed evaluator residuals added before widened
noise.  The wrong-candidate normal form samples an exactly uniform BRK and a real KSK with a fixed
residual.  The native smudging theorems prove that these normal forms are close to the widened real
and uniform public endpoints, respectively.

`ResidualCandidateViewTransformer.toPointwise` is the main adapter.  A future homomorphic
evaluator only has to prove exact distributional equality with these residual normal forms and
bound their row residuals.  All total-variation accounting then follows automatically.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.ResidualCandidateView


/-- Native paired-secret sampler, factored out so the residual and target views share the same
outer randomness syntactically. -/
def sampleSecretPair (lweDimension ringRank degree : ℕ) :
    ProbComp (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret lweDimension ringRank degree) := do
  let lweSecret ← sampleLweSecret lweDimension
  let ringSecret ← sampleRingSecret ringRank degree
  return (lweSecret, ringSecret)

/-- Fresh-secret correct-candidate normal form with secret-dependent fixed BRK and KSK residuals. -/
noncomputable def freshResidualRealView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringResidual : BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret lweDimension ringRank degree →
      ConditionalSmudging.BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext q degree ringRank tgswLevels
      lweDimension keySwitchLevels) := do
  let secrets ← sampleSecretPair lweDimension ringRank degree
  ConditionalSmudging.generateResidualEvaluationKeyPair q degree ringRank tgswLevels
    lweDimension keySwitchLevels ringWideNoise keySwitchWideNoise
    tgswGadget keySwitchGadget secrets.1 secrets.2
    (ringResidual secrets) (keySwitchResidual secrets)

/-- Fresh-secret widened real target, in the exact monomial BRK presentation. -/
noncomputable def freshMonomialRealView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext q degree ringRank tgswLevels
      lweDimension keySwitchLevels) := do
  let secrets ← sampleSecretPair lweDimension ringRank degree
  ConditionalSmudging.generateMonomialEvaluationKeyPair q degree ringRank tgswLevels
    lweDimension keySwitchLevels ringWideNoise keySwitchWideNoise
    tgswGadget keySwitchGadget secrets.1 secrets.2

/-- The factored fresh monomial view is definitionally the public real view used by the native
search-to-decision problem. -/
theorem freshMonomialRealView_eq_realPublicView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    freshMonomialRealView q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget =
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.realPublicView ringWideNoise keySwitchWideNoise
        tgswGadget keySwitchGadget := by
  simp [freshMonomialRealView, sampleSecretPair,
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.realPublicView, BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.problem,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.problem,
    ConditionalSmudging.generateMonomialEvaluationKeyPair, monad_norm]

/-- Correct residual normal forms are close to the widened real public endpoint whenever every
fresh secret pair has a uniformly bounded native row-smudging cost. -/
theorem tvDist_freshResidualRealView_realPublicView_le
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringResidual : BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret lweDimension ringRank degree →
      ConditionalSmudging.BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels)
    (bound : ℝ)
    (hbound : ∀ secrets,
      ConditionalSmudging.evaluationKeySmudgingCost ringWideNoise keySwitchWideNoise
        (ringResidual secrets) (keySwitchResidual secrets) ≤ bound) :
    tvDist
        (freshResidualRealView q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
          ringResidual keySwitchResidual)
        (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.realPublicView ringWideNoise keySwitchWideNoise
          tgswGadget keySwitchGadget) ≤ bound := by
  let secrets := sampleSecretPair lweDimension ringRank degree
  let residualContinuation := fun secretPair :
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree ↦
    ConditionalSmudging.generateResidualEvaluationKeyPair q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringWideNoise keySwitchWideNoise
      tgswGadget keySwitchGadget secretPair.1 secretPair.2
      (ringResidual secretPair) (keySwitchResidual secretPair)
  let targetContinuation := fun secretPair :
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree ↦
    ConditionalSmudging.generateMonomialEvaluationKeyPair q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringWideNoise keySwitchWideNoise
      tgswGadget keySwitchGadget secretPair.1 secretPair.2
  have h := tvDist_bind_left_le_const' secrets residualContinuation
    targetContinuation bound (fun secretPair ↦
      (ConditionalSmudging.tvDist_generateResidualEvaluationKeyPair_generateMonomial_le
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
        secretPair.1 secretPair.2 (ringResidual secretPair)
        (keySwitchResidual secretPair)).trans (hbound secretPair))
  rw [← freshMonomialRealView_eq_realPublicView q degree ringRank tgswLevels
    lweDimension keySwitchLevels ringWideNoise keySwitchWideNoise
    tgswGadget keySwitchGadget]
  simpa [freshResidualRealView, freshMonomialRealView, secrets,
    residualContinuation, targetContinuation] using h

/-- Wrong-candidate normal form: an exactly uniform BRK together with a real KSK carrying a fixed
residual before widened scalar noise. -/
noncomputable def freshResidualUniformView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (keySwitchWideNoise : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (keySwitchResidual : BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext q degree ringRank tgswLevels
      lweDimension keySwitchLevels) := do
  let secrets ← sampleSecretPair lweDimension ringRank degree
  let bootstrappingKey ←
    $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
  let keySwitchKey ← ConditionalSmudging.generateResidualKeySwitchKey
    q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise keySwitchGadget
    secrets.2 secrets.1 (keySwitchResidual secrets)
  return (bootstrappingKey, keySwitchKey)

/-- Factored fresh-secret uniform-BRK target with an ordinary widened real KSK. -/
noncomputable def freshUniformView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (keySwitchWideNoise : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext q degree ringRank tgswLevels
      lweDimension keySwitchLevels) := do
  let secrets ← sampleSecretPair lweDimension ringRank degree
  let bootstrappingKey ←
    $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
  let keySwitchKey ← generateKeySwitchKey
    q lweDimension (ringRank * degree) keySwitchLevels
    keySwitchWideNoise keySwitchGadget (keyExtract secrets.2) secrets.1
  return (bootstrappingKey, keySwitchKey)

/-- The factored uniform target is the native uniform public view.  Its ring-error sampler is
irrelevant because the BRK branch is exactly uniform. -/
theorem freshUniformView_eq_uniformPublicView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    freshUniformView q degree ringRank tgswLevels lweDimension keySwitchLevels
        keySwitchWideNoise keySwitchGadget =
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.uniformPublicView ringWideNoise keySwitchWideNoise
        tgswGadget keySwitchGadget := by
  simp [freshUniformView, sampleSecretPair,
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.uniformPublicView,
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.problem, monad_norm]

/-- Wrong residual normal forms are close to the native uniform endpoint by only the KSK
smudging cost; the BRK is already exactly uniform. -/
theorem tvDist_freshResidualUniformView_uniformPublicView_le
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (keySwitchResidual : BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels)
    (bound : ℝ)
    (hbound : ∀ secrets,
      ConditionalSmudging.keySwitchSmudgingCost keySwitchWideNoise
        (keySwitchResidual secrets) ≤ bound) :
    tvDist
        (freshResidualUniformView q degree ringRank tgswLevels lweDimension keySwitchLevels
          keySwitchWideNoise keySwitchGadget keySwitchResidual)
        (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.uniformPublicView ringWideNoise keySwitchWideNoise
          tgswGadget keySwitchGadget) ≤ bound := by
  let secrets := sampleSecretPair lweDimension ringRank degree
  let residualContinuation := fun secretPair :
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree ↦ do
    let bootstrappingKey ←
      $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
    let keySwitchKey ← ConditionalSmudging.generateResidualKeySwitchKey
      q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise keySwitchGadget
      secretPair.2 secretPair.1 (keySwitchResidual secretPair)
    return (bootstrappingKey, keySwitchKey)
  let targetContinuation := fun secretPair :
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree ↦ do
    let bootstrappingKey ←
      $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
    let keySwitchKey ← generateKeySwitchKey
      q lweDimension (ringRank * degree) keySwitchLevels
      keySwitchWideNoise keySwitchGadget (keyExtract secretPair.2) secretPair.1
    return (bootstrappingKey, keySwitchKey)
  have hcontinuation : ∀ secretPair,
      tvDist (residualContinuation secretPair) (targetContinuation secretPair) ≤ bound := by
    intro secretPair
    let uniformBootstrap : ProbComp
        (BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
      $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
    let residualSwitch := ConditionalSmudging.generateResidualKeySwitchKey
      q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise keySwitchGadget
      secretPair.2 secretPair.1 (keySwitchResidual secretPair)
    let targetSwitch := generateKeySwitchKey
      q lweDimension (ringRank * degree) keySwitchLevels
      keySwitchWideNoise keySwitchGadget (keyExtract secretPair.2) secretPair.1
    have hpair := SamplerReplacement.tvDist_independentPair_le
      uniformBootstrap uniformBootstrap residualSwitch targetSwitch
        (fun bootstrap switchKey ↦ (bootstrap, switchKey))
    have hswitch : tvDist residualSwitch targetSwitch ≤
        ConditionalSmudging.keySwitchSmudgingCost keySwitchWideNoise
          (keySwitchResidual secretPair) :=
      ConditionalSmudging.tvDist_generateResidualKeySwitchKey_generateKeySwitchKey_le
        q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise
        keySwitchGadget secretPair.2 secretPair.1 (keySwitchResidual secretPair)
    have h := hpair.trans
      (add_le_add (le_of_eq (tvDist_self uniformBootstrap)) hswitch) |>.trans
        (by simpa using hbound secretPair)
    simpa [residualContinuation, targetContinuation,
      SamplerReplacement.independentPair, uniformBootstrap, residualSwitch,
      targetSwitch, map_eq_bind_pure_comp, monad_norm] using h
  have h := tvDist_bind_left_le_const' secrets residualContinuation
    targetContinuation bound hcontinuation
  rw [← freshUniformView_eq_uniformPublicView q degree ringRank tgswLevels
    lweDimension keySwitchLevels ringWideNoise keySwitchWideNoise
    tgswGadget keySwitchGadget]
  simpa [freshResidualUniformView, freshUniformView, secrets,
    residualContinuation, targetContinuation] using h

/-! ## Adapter to the pointwise candidate-view contract -/

/-- Scheme-specific algebraic normal-form certificate for a native candidate evaluator.

The evaluator itself remains executable.  For every supported fixed source context, a correct
candidate must have the fresh-real residual normal form, while a wrong candidate must have the
uniform-BRK residual-KSK normal form.  The last two fields bound every fresh-secret residual cost
by the advertised coordinate error. -/
structure ResidualCandidateViewTransformer
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  transform : Fin lweDimension → Bool →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      q degree ringRank tgswLevels lweDimension →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      q degree ringRank lweDimension keySwitchLevels →
    ProbComp
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext
        q degree ringRank tgswLevels lweDimension keySwitchLevels)
  correctRingResidual : Fin lweDimension → Bool →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      q degree ringRank tgswLevels lweDimension →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      q degree ringRank lweDimension keySwitchLevels →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
      lweDimension ringRank degree →
    ConditionalSmudging.BootstrappingResidual
      q degree ringRank tgswLevels lweDimension
  correctKeySwitchResidual : Fin lweDimension → Bool →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      q degree ringRank tgswLevels lweDimension →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      q degree ringRank lweDimension keySwitchLevels →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
      lweDimension ringRank degree →
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels
  wrongKeySwitchResidual : Fin lweDimension → Bool →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      q degree ringRank tgswLevels lweDimension →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      q degree ringRank lweDimension keySwitchLevels →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
      lweDimension ringRank degree →
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels
  correctError : Fin lweDimension → ℝ
  wrongError : Fin lweDimension → ℝ
  correctError_nonneg : ∀ coordinate, 0 ≤ correctError coordinate
  wrongError_nonneg : ∀ coordinate, 0 ≤ wrongError coordinate
  correctNormalForm : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
        sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate) →
    evalDist
        (transform coordinate hiddenAndContext.1 hiddenAndContext.2.1
          hiddenAndContext.2.2) =
      evalDist
        (freshResidualRealView q degree ringRank tgswLevels lweDimension keySwitchLevels
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
          (correctRingResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2)
          (correctKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2))
  wrongNormalForm : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
        sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate) →
    evalDist
        (transform coordinate (!hiddenAndContext.1) hiddenAndContext.2.1
          hiddenAndContext.2.2) =
      evalDist
        (freshResidualUniformView q degree ringRank tgswLevels lweDimension keySwitchLevels
          targetKeySwitchErrorSampler keySwitchGadget
          (wrongKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2))
  correctCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
        sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate) →
    ∀ secrets,
      ConditionalSmudging.evaluationKeySmudgingCost
          targetRingErrorSampler targetKeySwitchErrorSampler
          (correctRingResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets)
          (correctKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) ≤
        correctError coordinate
  wrongCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
        sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate) →
    ∀ secrets,
      ConditionalSmudging.keySwitchSmudgingCost targetKeySwitchErrorSampler
          (wrongKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) ≤
        wrongError coordinate

namespace ResidualCandidateViewTransformer

/-- Native residual normal forms discharge the complete pointwise conditional freshness contract
required by shared-context search-to-decision amplification. -/
noncomputable def toPointwise
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : ResidualCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension)
      sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget) :
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PointwiseCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension)
      sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget where
  transform := transformer.transform
  correctError := transformer.correctError
  wrongError := transformer.wrongError
  correctError_nonneg := transformer.correctError_nonneg
  wrongError_nonneg := transformer.wrongError_nonneg
  correctDistance := by
    intro coordinate hiddenAndContext hsupport
    change SPMF.tvDist
        (evalDist (transformer.transform coordinate hiddenAndContext.1
          hiddenAndContext.2.1 hiddenAndContext.2.2))
        (evalDist
          (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.realPublicView
            targetRingErrorSampler targetKeySwitchErrorSampler
            tgswGadget keySwitchGadget)) ≤ transformer.correctError coordinate
    rw [transformer.correctNormalForm coordinate hiddenAndContext hsupport]
    simpa only [tvDist] using
      (tvDist_freshResidualRealView_realPublicView_le
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        targetRingErrorSampler targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget
        (transformer.correctRingResidual coordinate hiddenAndContext.1
          hiddenAndContext.2.1 hiddenAndContext.2.2)
        (transformer.correctKeySwitchResidual coordinate hiddenAndContext.1
          hiddenAndContext.2.1 hiddenAndContext.2.2)
        (transformer.correctError coordinate)
        (transformer.correctCost_le coordinate hiddenAndContext hsupport))
  wrongDistance := by
    intro coordinate hiddenAndContext hsupport
    change SPMF.tvDist
        (evalDist (transformer.transform coordinate (!hiddenAndContext.1)
          hiddenAndContext.2.1 hiddenAndContext.2.2))
        (evalDist
          (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.uniformPublicView
            targetRingErrorSampler targetKeySwitchErrorSampler
            tgswGadget keySwitchGadget)) ≤ transformer.wrongError coordinate
    rw [transformer.wrongNormalForm coordinate hiddenAndContext hsupport]
    simpa only [tvDist] using
      (tvDist_freshResidualUniformView_uniformPublicView_le
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        targetRingErrorSampler targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget
        (transformer.wrongKeySwitchResidual coordinate hiddenAndContext.1
          hiddenAndContext.2.1 hiddenAndContext.2.2)
        (transformer.wrongError coordinate)
        (transformer.wrongCost_le coordinate hiddenAndContext hsupport))

/-- The same residual-normal-form certificate also supplies the weaker averaged interface.  This
adapter is useful with thresholded shared-context amplification and makes the logical implication
from pointwise to averaged freshness explicit. -/
noncomputable def toAveraged
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : ResidualCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension)
      sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget) :
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension)
      sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget :=
  transformer.toPointwise.toAveraged

end ResidualCandidateViewTransformer

/-! ## Averaged residual normal forms

The CircLWE search-to-decision argument only promises its shifted-evaluation law after averaging
over the original public evaluation-key experiment.  Requiring that law on every fixed public
context is strictly stronger and can be impossible when the hidden-bit fibers overlap.  The
following interface records the paper-level averaged obligation directly while retaining the
same checked native smudging accounting. -/

/-- Correct-candidate residual normal form averaged over the original native coordinate source.
For each source point it samples a fresh secret pair and generates the widened real evaluation-key
view with the evaluator's fixed residuals. -/
noncomputable def averagedResidualRealView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (sourceRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler : ProbComp (ZMod q))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (ringResidual : Bool →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree →
      ConditionalSmudging.BootstrappingResidual
        q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : Bool →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext
        q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let hiddenAndContext ←
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
      sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget keySwitchGadget coordinate
  freshResidualRealView q degree ringRank tgswLevels lweDimension keySwitchLevels
    targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
    (ringResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
    (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)

/-- Wrong-candidate residual normal form averaged over the original coordinate source.  Its BRK
is exactly uniform and only the fresh real KSK carries an evaluator residual. -/
noncomputable def averagedResidualUniformView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (sourceRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler : ProbComp (ZMod q))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (keySwitchResidual : Bool →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext
        q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let hiddenAndContext ←
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
      sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget keySwitchGadget coordinate
  freshResidualUniformView q degree ringRank tgswLevels lweDimension keySwitchLevels
    targetKeySwitchErrorSampler keySwitchGadget
    (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)

/-- Averaging source-dependent correct residual normal forms preserves the same uniform smudging
bound against the fresh widened real endpoint. -/
theorem tvDist_averagedResidualRealView_realPublicView_le
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (sourceRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler : ProbComp (ZMod q))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (ringResidual : Bool →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree →
      ConditionalSmudging.BootstrappingResidual
        q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : Bool →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels)
    (bound : ℝ)
    (hbound : ∀ hiddenAndContext,
      hiddenAndContext ∈ support
        (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
          sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
          keySwitchGadget coordinate) →
      ∀ secrets,
        ConditionalSmudging.evaluationKeySmudgingCost
            targetRingErrorSampler targetKeySwitchErrorSampler
            (ringResidual hiddenAndContext.1 hiddenAndContext.2.1
              hiddenAndContext.2.2 secrets)
            (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1
              hiddenAndContext.2.2 secrets) ≤ bound) :
    tvDist
        (averagedResidualRealView q degree ringRank tgswLevels lweDimension
          keySwitchLevels sourceRingErrorSampler sourceKeySwitchErrorSampler
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
          coordinate ringResidual keySwitchResidual)
        (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.realPublicView
          targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget) ≤ bound := by
  let source :=
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
      (ringRank := ringRank) (lweDimension := lweDimension)
      sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate
  let target :=
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.realPublicView
      (ringRank := ringRank) (lweDimension := lweDimension)
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
  let residualView := fun hiddenAndContext : Bool ×
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext
        q degree ringRank tgswLevels lweDimension keySwitchLevels ↦
    freshResidualRealView q degree ringRank tgswLevels lweDimension keySwitchLevels
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
      (ringResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
      (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
  have hmix := tvDist_bind_left_le_const source residualView (fun _ ↦ target) bound
    (fun hiddenAndContext hsupport ↦
      tvDist_freshResidualRealView_realPublicView_le
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
        (ringResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
        (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
        bound (hbound hiddenAndContext hsupport))
  have htarget : evalDist (source >>= fun _ ↦ target) = evalDist target :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      source (by simp [source]) target
  unfold tvDist at hmix ⊢
  rw [htarget] at hmix
  simpa [averagedResidualRealView, source, residualView, target] using hmix

/-- Averaging source-dependent wrong residual normal forms preserves the same scalar smudging
bound against the fresh uniform-BRK endpoint. -/
theorem tvDist_averagedResidualUniformView_uniformPublicView_le
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (sourceRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler : ProbComp (ZMod q))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (keySwitchResidual : Bool →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels)
    (bound : ℝ)
    (hbound : ∀ hiddenAndContext,
      hiddenAndContext ∈ support
        (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
          sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
          keySwitchGadget coordinate) →
      ∀ secrets,
        ConditionalSmudging.keySwitchSmudgingCost targetKeySwitchErrorSampler
          (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1
            hiddenAndContext.2.2 secrets) ≤ bound) :
    tvDist
        (averagedResidualUniformView q degree ringRank tgswLevels lweDimension
          keySwitchLevels sourceRingErrorSampler sourceKeySwitchErrorSampler
          targetKeySwitchErrorSampler tgswGadget keySwitchGadget coordinate
          keySwitchResidual)
        (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.uniformPublicView
          targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget) ≤ bound := by
  let source :=
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
      (ringRank := ringRank) (lweDimension := lweDimension)
      sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate
  let target :=
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.uniformPublicView
      (ringRank := ringRank) (lweDimension := lweDimension)
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
  let residualView := fun hiddenAndContext : Bool ×
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext
        q degree ringRank tgswLevels lweDimension keySwitchLevels ↦
    freshResidualUniformView q degree ringRank tgswLevels lweDimension keySwitchLevels
      targetKeySwitchErrorSampler keySwitchGadget
      (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
  have hmix := tvDist_bind_left_le_const source residualView (fun _ ↦ target) bound
    (fun hiddenAndContext hsupport ↦
      tvDist_freshResidualUniformView_uniformPublicView_le
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
        (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
        bound (hbound hiddenAndContext hsupport))
  have htarget : evalDist (source >>= fun _ ↦ target) = evalDist target :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      source (by simp [source]) target
  unfold tvDist at hmix ⊢
  rw [htarget] at hmix
  simpa [averagedResidualUniformView, source, residualView, target] using hmix

/-- Scheme-specific shifted-function evaluator certificate at the averaged level used by the
CircLWE search-to-decision proof.  Unlike `ResidualCandidateViewTransformer`, its two exact
normal-form laws are required only after sampling the original native coordinate source. -/
structure AveragedResidualCandidateViewTransformer
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  transform : Fin lweDimension → Bool →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      q degree ringRank tgswLevels lweDimension →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      q degree ringRank lweDimension keySwitchLevels →
    ProbComp
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PublicContext
        q degree ringRank tgswLevels lweDimension keySwitchLevels)
  correctRingResidual : Fin lweDimension → Bool →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      q degree ringRank tgswLevels lweDimension →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      q degree ringRank lweDimension keySwitchLevels →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
      lweDimension ringRank degree →
    ConditionalSmudging.BootstrappingResidual
      q degree ringRank tgswLevels lweDimension
  correctKeySwitchResidual : Fin lweDimension → Bool →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      q degree ringRank tgswLevels lweDimension →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      q degree ringRank lweDimension keySwitchLevels →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
      lweDimension ringRank degree →
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels
  wrongKeySwitchResidual : Fin lweDimension → Bool →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      q degree ringRank tgswLevels lweDimension →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      q degree ringRank lweDimension keySwitchLevels →
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
      lweDimension ringRank degree →
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels
  correctError : Fin lweDimension → ℝ
  wrongError : Fin lweDimension → ℝ
  correctError_nonneg : ∀ coordinate, 0 ≤ correctError coordinate
  wrongError_nonneg : ∀ coordinate, 0 ≤ wrongError coordinate
  correctNormalForm : ∀ coordinate,
    evalDist (do
        let hiddenAndContext ←
          BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
            sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
            keySwitchGadget coordinate
        transform coordinate hiddenAndContext.1 hiddenAndContext.2.1
          hiddenAndContext.2.2) =
      evalDist
        (averagedResidualRealView q degree ringRank tgswLevels lweDimension
          keySwitchLevels sourceRingErrorSampler sourceKeySwitchErrorSampler
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
          coordinate (correctRingResidual coordinate)
          (correctKeySwitchResidual coordinate))
  wrongNormalForm : ∀ coordinate,
    evalDist (do
        let hiddenAndContext ←
          BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
            sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
            keySwitchGadget coordinate
        transform coordinate (!hiddenAndContext.1) hiddenAndContext.2.1
          hiddenAndContext.2.2) =
      evalDist
        (averagedResidualUniformView q degree ringRank tgswLevels lweDimension
          keySwitchLevels sourceRingErrorSampler sourceKeySwitchErrorSampler
          targetKeySwitchErrorSampler tgswGadget keySwitchGadget coordinate
          (wrongKeySwitchResidual coordinate))
  correctCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
        sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate) →
    ∀ secrets,
      ConditionalSmudging.evaluationKeySmudgingCost
          targetRingErrorSampler targetKeySwitchErrorSampler
          (correctRingResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets)
          (correctKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) ≤
        correctError coordinate
  wrongCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
        sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate) →
    ∀ secrets,
      ConditionalSmudging.keySwitchSmudgingCost targetKeySwitchErrorSampler
          (wrongKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) ≤
        wrongError coordinate

namespace AveragedResidualCandidateViewTransformer

/-- Averaged residual normal forms discharge exactly the averaged candidate-view contract used by
thresholded shared-context amplification. -/
noncomputable def toAveraged
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedResidualCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension)
      sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget) :
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension)
      sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget where
  transform := transformer.transform
  correctError := transformer.correctError
  wrongError := transformer.wrongError
  correctError_nonneg := transformer.correctError_nonneg
  wrongError_nonneg := transformer.wrongError_nonneg
  correctDistance := by
    intro coordinate
    unfold tvDist
    rw [transformer.correctNormalForm coordinate]
    simpa only [tvDist] using
      (tvDist_averagedResidualRealView_realPublicView_le
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        sourceRingErrorSampler sourceKeySwitchErrorSampler
        targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
        coordinate (transformer.correctRingResidual coordinate)
        (transformer.correctKeySwitchResidual coordinate)
        (transformer.correctError coordinate)
        (transformer.correctCost_le coordinate))
  wrongDistance := by
    intro coordinate
    unfold tvDist
    rw [transformer.wrongNormalForm coordinate]
    simpa only [tvDist] using
      (tvDist_averagedResidualUniformView_uniformPublicView_le
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        sourceRingErrorSampler sourceKeySwitchErrorSampler
        targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
        coordinate (transformer.wrongKeySwitchResidual coordinate)
        (transformer.wrongError coordinate)
        (transformer.wrongCost_le coordinate))

end AveragedResidualCandidateViewTransformer

/-- Complete scheme-specific certificate connecting averaged native residual normal forms to the
widened CircLWE search-to-decision reduction.  Its only semantic field is the shifted evaluator
above; the remaining fields select sound shared-context amplification parameters and require that
the target decision gap exceeds the two smudging errors. -/
structure AveragedResidualCandidateViewTransformerReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toTransformer :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      AveragedResidualCandidateViewTransformer
        (ringRank := ringRank) (lweDimension := lweDimension)
        (RLWE.CenteredBinomial.sampler q degree ringEta) targetRingErrorSampler
        (CenteredBinomial.scalarSampler q keySwitchEta) targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget
  rounds :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ℕ
  threshold :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ENNReal
  threshold_pos : ∀ distinguisher coordinate, 0 < threshold distinguisher coordinate
  threshold_le_one : ∀ distinguisher coordinate, threshold distinguisher coordinate ≤ 1

namespace AveragedResidualCandidateViewTransformerReduction

/-- Forget the evaluator's exact residual normal forms only after using them to discharge the
averaged distance contract.  The resulting object is the generic widened reduction certificate. -/
noncomputable def toWidened
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedResidualCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget) :
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.SearchToDecision.Widened.AveragedCandidateViewTransformerReduction
      q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget where
  toTransformer := fun distinguisher ↦
    (reduction.toTransformer distinguisher).toAveraged
  rounds := reduction.rounds
  threshold := reduction.threshold
  threshold_pos := reduction.threshold_pos
  threshold_le_one := reduction.threshold_le_one

/-- Averaged native residual evaluation, thresholded amplification, and the whole-key union bound
produce the widened coordinate-recovery certificate without further scheme-specific proof. -/
noncomputable def toCoordinateSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedResidualCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget) :
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.SearchToDecision.Widened.CoordinateSecretReduction
      q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget :=
  reduction.toWidened.toCoordinateSecretReduction

/-- The same certificate gives complete scalar-secret recovery. -/
noncomputable def toScalarSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedResidualCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget) :
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.SearchToDecision.Widened.ScalarSecretReduction
      q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget :=
  reduction.toWidened.toScalarSecretReduction

/-- With one centered-binomial KSK decoding level satisfying the existing margin, the averaged
residual evaluator gives full paired-secret recovery. -/
noncomputable def toPairedSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedResidualCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.SearchToDecision.Widened.PairedSecretReduction
      q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget :=
  reduction.toWidened.toPairedSecretReduction level hmargin

/-- Narrow centered-binomial paired-search hardness therefore transfers directly to widened
native public CircLWE hardness through an averaged residual evaluator certificate. -/
theorem publicHardAgainst_of_search
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reduction : AveragedResidualCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (decisionAllowed : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → Prop)
    (solverAllowed : BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Solver
      q degree ringRank tgswLevels lweDimension keySwitchLevels → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : LWE.AuxiliaryInput.SearchToDecision.RealSearchHardAgainst
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.problem
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget)
      solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed ((reduction.toPairedSecretReduction level hmargin).toSolver
        distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      (reduction.toPairedSecretReduction level hmargin).loss distinguisher ≤ lossBound) :
    LWE.AuxiliaryInput.SearchToDecision.PublicHardAgainst
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.problem q degree ringRank
        tgswLevels lweDimension keySwitchLevels targetRingErrorSampler
        targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
      decisionAllowed (searchBound + lossBound) :=
  BootstrapSecurity.MonomialKDM.AuxiliaryInput.SearchToDecision.Widened.publicHardAgainst_of_pairedSecretReduction
    targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
    (reduction.toPairedSecretReduction level hmargin) decisionAllowed solverAllowed
    searchBound lossBound hSearch hClosed hLoss

end AveragedResidualCandidateViewTransformerReduction

end FormalProof4FHE.TFHE.Native.ResidualCandidateView
