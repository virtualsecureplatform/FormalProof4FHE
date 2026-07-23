/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticAuxiliaryInputCircularLWE
import FormalProof4FHE.TFHE.NativeResidualCandidateView

/-!
# Asymptotic Native CircLWE from Averaged Residual Evaluation

This module lifts the finite widened search-to-decision theorem for native TFHE to security-
parameter-indexed games.  A public distinguisher sees the bootstrapping key and retained
key-switch key but not either hidden key.  At every security parameter, an averaged residual
evaluator certificate turns that distinguisher into a paired-key solver for a possibly narrower
centered-binomial search distribution.

The resulting pointwise bound has exactly two terms:

* success of the generated narrow-search solver; and
* the explicit threshold/amplification/smudging loss of the residual reduction.

Consequently, negligible narrow-search success and negligible reduction loss imply public native
auxiliary-input CircLWE security.  The final bridge records that this public game is exactly the
existing native CircLWE game restricted to continuations that ignore both secret arguments.  It
does not silently extend the theorem to secret-aware continuations used by some same-secret batch
hybrids.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Native.ResidualCandidateView.Asymptotic

open Encryption.Adaptive.Asymptotic

/-- Public native CircLWE distinguishers at one security parameter. -/
abbrev PublicDistinguisherAt {Message : Type} (params : Parameters Message)
    (securityParameter : ℕ) :=
  FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
    (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter))
    (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter))

/-- Security-parameter-indexed public native CircLWE distinguishers. -/
abbrev PublicDistinguisherFamily {Message : Type} (params : Parameters Message) :=
  (securityParameter : ℕ) → PublicDistinguisherAt params securityParameter

/-- Public paired-key search solvers at one security parameter. -/
abbrev SearchSolverAt {Message : Type} (params : Parameters Message)
    (securityParameter : ℕ) :=
  BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Solver
    (params.q securityParameter)
    (params.degree securityParameter)
    (params.ringRank securityParameter)
    (params.tgswLevels securityParameter)
    (params.lweDimension securityParameter)
    (params.keySwitchLevels securityParameter)

/-- Security-parameter-indexed public paired-key search solvers. -/
abbrev SearchSolverFamily {Message : Type} (params : Parameters Message) :=
  (securityParameter : ℕ) → SearchSolverAt params securityParameter

/-- Averaged residual evaluator reductions for a target native family and two source
centered-binomial widths. -/
abbrev ReductionFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ) :=
  (securityParameter : ℕ) →
    FormalProof4FHE.TFHE.Native.ResidualCandidateView.AveragedResidualCandidateViewTransformerReduction
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter)
      (sourceRingEta securityParameter)
      (sourceKeySwitchEta securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)

/-- Native public auxiliary-input CircLWE, with no secret-aware continuation available to the
distinguisher. -/
noncomputable def publicCircularLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PublicDistinguisherFamily params) where
  advantage distinguisher securityParameter := ENNReal.ofReal
    (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.problem
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.ringRank securityParameter)
        (params.tgswLevels securityParameter)
        (params.lweDimension securityParameter)
        (params.keySwitchLevels securityParameter)
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter))
      (distinguisher securityParameter))

/-- Paired-key recovery for the narrow centered-binomial source distribution. -/
noncomputable def narrowSearchSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ) :
    SecurityGame (SearchSolverFamily params) where
  advantage solver securityParameter :=
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
      (BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.problem
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.ringRank securityParameter)
        (params.tgswLevels securityParameter)
        (params.lweDimension securityParameter)
        (params.keySwitchLevels securityParameter)
        (RLWE.CenteredBinomial.sampler
          (params.q securityParameter)
          (params.degree securityParameter)
          (sourceRingEta securityParameter))
        (CenteredBinomial.scalarSampler
          (params.q securityParameter)
          (sourceKeySwitchEta securityParameter))
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter))
      (solver securityParameter)

/-- The paired-secret cross-distribution reduction selected at one security parameter. -/
noncomputable def pairedReductionAt {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter)))
    (securityParameter : ℕ) :=
  (reduction securityParameter).toPairedSecretReduction
    (level securityParameter) (hmargin securityParameter)

/-- Apply the parameter-indexed residual reduction to a public distinguisher family. -/
noncomputable def toSearchSolverFamily {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter)))
    (distinguisher : PublicDistinguisherFamily params) :
    SearchSolverFamily params :=
  fun securityParameter ↦
    (pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level hmargin
      securityParameter).toSolver (distinguisher securityParameter)

/-- The exact smudging/threshold/amplification loss charged by the residual reduction family. -/
noncomputable def reductionLossSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter))) :
    SecurityGame (PublicDistinguisherFamily params) where
  advantage distinguisher securityParameter := ENNReal.ofReal
    ((pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level hmargin
      securityParameter).loss (distinguisher securityParameter))

/-- Pointwise widened search-to-decision accounting for the asymptotic games. -/
theorem publicCircularLWE_advantage_le_search_add_loss {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter)))
    (distinguisher : PublicDistinguisherFamily params)
    (securityParameter : ℕ) :
    (publicCircularLWESecurityGame params).advantage distinguisher securityParameter ≤
      (narrowSearchSecurityGame params sourceRingEta sourceKeySwitchEta).advantage
          (toSearchSolverFamily params sourceRingEta sourceKeySwitchEta reduction level
            hmargin distinguisher) securityParameter +
        (reductionLossSecurityGame params sourceRingEta sourceKeySwitchEta reduction level
          hmargin).advantage distinguisher securityParameter := by
  have h :=
    (pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level hmargin
      securityParameter).advantage_le (distinguisher securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal h
  change ENNReal.ofReal
      (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage _
        (distinguisher securityParameter)) ≤
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability _ _ + ENNReal.ofReal _
  calc
    _ ≤ ENNReal.ofReal
        ((FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability _ _).toReal +
          (pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level
            hmargin securityParameter).loss (distinguisher securityParameter)) := hLift
    _ ≤ ENNReal.ofReal
          (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability _ _).toReal +
        ENNReal.ofReal
          ((pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level
            hmargin securityParameter).loss (distinguisher securityParameter)) :=
      ENNReal.ofReal_add_le
    _ = _ := by
      simp only [FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability,
        ENNReal.ofReal_toReal probOutput_ne_top, toSearchSolverFamily]

/-- Negligible narrow-search success plus negligible evaluator/reduction loss gives public native
auxiliary-input CircLWE security. -/
theorem publicCircularLWESecurityGame_secureAgainst_of_search_and_loss
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter)))
    (decisionIsPPT : PublicDistinguisherFamily params → Prop)
    (solverIsPPT : SearchSolverFamily params → Prop)
    (hClosed : ∀ distinguisher, decisionIsPPT distinguisher →
      solverIsPPT
        (toSearchSolverFamily params sourceRingEta sourceKeySwitchEta reduction level
          hmargin distinguisher))
    (hSearch :
      (narrowSearchSecurityGame params sourceRingEta sourceKeySwitchEta).secureAgainst
        solverIsPPT)
    (hLoss :
      (reductionLossSecurityGame params sourceRingEta sourceKeySwitchEta reduction level
        hmargin).secureAgainst decisionIsPPT) :
    (publicCircularLWESecurityGame params).secureAgainst decisionIsPPT := by
  intro distinguisher hdistinguisher
  exact negligible_of_le
    (publicCircularLWE_advantage_le_search_add_loss params sourceRingEta
      sourceKeySwitchEta reduction level hmargin distinguisher)
    (negligible_add
      (hSearch _ (hClosed distinguisher hdistinguisher))
      (hLoss distinguisher hdistinguisher))

/-- Embed a public distinguisher family into the existing secret-aware continuation carrier by
ignoring both hidden secret arguments. -/
def publicContinuationFamily {Message : Type} (params : Parameters Message)
    (distinguisher : PublicDistinguisherFamily params) : ContinuationFamily params :=
  fun securityParameter _lweSecret _ringSecret bootstrappingKey keySwitchKey ↦
    distinguisher securityParameter bootstrappingKey keySwitchKey

/-- The public game is exactly the existing native auxiliary-input CircLWE game on the embedded
secret-independent continuation. -/
theorem circularLWESecurityGame_advantage_publicContinuationFamily {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (distinguisher : PublicDistinguisherFamily params)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        params).advantage (publicContinuationFamily params distinguisher) securityParameter =
      (publicCircularLWESecurityGame params).advantage distinguisher securityParameter := by
  unfold Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
    publicCircularLWESecurityGame
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.circularLweAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.packContinuation
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
    publicContinuationFamily
  rfl

/-- The image of a public distinguisher class inside the existing secret-aware continuation
carrier. -/
def PublicContinuationAllowed {Message : Type} (params : Parameters Message)
    (publicAllowed : PublicDistinguisherFamily params → Prop) :
    ContinuationFamily params → Prop :=
  fun continuation ↦ ∃ distinguisher,
    publicAllowed distinguisher ∧ continuation = publicContinuationFamily params distinguisher

/-- Public CircLWE security transfers without loss to the existing native game restricted to
secret-independent continuations. -/
theorem circularLWESecurityGame_secureAgainst_publicContinuations {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (publicAllowed : PublicDistinguisherFamily params → Prop)
    (hPublic : (publicCircularLWESecurityGame params).secureAgainst publicAllowed) :
    (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
      params).secureAgainst (PublicContinuationAllowed params publicAllowed) := by
  intro continuation hcontinuation
  obtain ⟨distinguisher, hdistinguisher, rfl⟩ := hcontinuation
  rw [show
    (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
      params).advantage (publicContinuationFamily params distinguisher) =
        (publicCircularLWESecurityGame params).advantage distinguisher from
      funext (circularLWESecurityGame_advantage_publicContinuationFamily
        params distinguisher)]
  exact hPublic distinguisher hdistinguisher

/-- Public residual-derived CircLWE security plus the existing zero-message side-information
branch gives native monomial circular/KDM security for the same public continuation class. -/
theorem monomialSecurityGame_secureAgainst_publicContinuations_of_publicCircular_and_zero
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (publicAllowed : PublicDistinguisherFamily params → Prop)
    (hPublic : (publicCircularLWESecurityGame params).secureAgainst publicAllowed)
    (hZero :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.zeroLWESecurityGame
        params).secureAgainst (PublicContinuationAllowed params publicAllowed)) :
    (Encryption.Adaptive.Asymptotic.MonomialKDM.securityGame params).secureAgainst
      (PublicContinuationAllowed params publicAllowed) := by
  apply Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.securityGame_secureAgainst_of_circularLWE_and_zeroLWE
  · exact circularLWESecurityGame_secureAgainst_publicContinuations
      params publicAllowed hPublic
  · exact hZero

end FormalProof4FHE.TFHE.Native.ResidualCandidateView.Asymptotic
