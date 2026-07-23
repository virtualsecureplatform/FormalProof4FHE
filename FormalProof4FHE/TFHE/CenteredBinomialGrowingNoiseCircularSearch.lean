/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticNativeResidualCandidateView
import FormalProof4FHE.TFHE.CenteredBinomialGrowingNoiseEndToEnd

/-!
# Public CircLWE Search-to-Decision Endpoint for the Growing TFHE Family

This module specializes the averaged residual search-to-decision interface to the concrete
growing centered-binomial TFHE family.  Gadget level one is the scalar code `2N`; its centered
distance from zero is proved exactly, and the family's existing `2(λ+1) < N` input margin
therefore discharges paired-key recovery for the native centered-binomial source width.

The final theorem states the paper-aligned computational milestone precisely: a family of
averaged shifted-evaluator certificates, negligible paired-search success, and negligible
explicit evaluator loss imply public native auxiliary-input CircLWE security for the concrete
target family.  Via the generic exact bridge, this is also the existing native CircLWE game on
secret-independent continuations.  No theorem here promotes it to arbitrary secret-aware
continuations.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd

noncomputable section

/-- Level one of the six-level base-`2N` KSK gadget. -/
def keySwitchRecoveryLevel (securityParameter : ℕ) :
    Fin (family.parameters.keySwitchLevels securityParameter) :=
  ⟨1, by simp [family, decomposition]⟩

/-- The selected KSK gadget code is exactly `2N`. -/
theorem keySwitchGadget_recoveryLevel (securityParameter : ℕ) :
    family.parameters.keySwitchGadget securityParameter
        (keySwitchRecoveryLevel securityParameter) =
      ((2 * ringDegree securityParameter : ℕ) :
        ZMod (coefficientModulus securityParameter)) := by
  simp [CenteredBinomial.Family.parameters, family, keySwitchRecoveryLevel,
    decomposition, Gadget.Base.gadget]

/-- Exact centered distance of the selected KSK code. -/
theorem centeredDistance_zero_keySwitchGadget_recoveryLevel
    (securityParameter : ℕ) :
    BootstrappingCorrectness.centeredDistance 0
        (family.parameters.keySwitchGadget securityParameter
          (keySwitchRecoveryLevel securityParameter)) =
      2 * ringDegree securityParameter := by
  rw [keySwitchGadget_recoveryLevel]
  change BootstrappingCorrectness.centeredDistance
      (0 : ZMod (coefficientModulus securityParameter))
      ((2 * ringDegree securityParameter : ℕ) :
        ZMod (coefficientModulus securityParameter)) =
    2 * ringDegree securityParameter
  rw [BootstrappingCorrectness.centeredDistance_symm]
  unfold BootstrappingCorrectness.centeredDistance
  simp only [sub_zero]
  have hdegreePos : 0 < ringDegree securityParameter :=
    ringDegree_pos securityParameter
  have hdegreeOne : 1 ≤ ringDegree securityParameter := by omega
  have hdegreePow : ringDegree securityParameter ≤ ringDegree securityParameter ^ 6 := by
    calc
      ringDegree securityParameter = ringDegree securityParameter * 1 := by omega
      _ ≤ ringDegree securityParameter * ringDegree securityParameter ^ 5 := by
        exact Nat.mul_le_mul_left _ (one_le_pow₀ hdegreeOne)
      _ = ringDegree securityParameter ^ 6 := by ring
  have htwiceLe :
      ((2 * ringDegree securityParameter : ℕ) : ℤ) * 2 ≤
        coefficientModulus securityParameter := by
    have hnat :
        (2 * ringDegree securityParameter) * 2 ≤
          coefficientModulus securityParameter := by
      unfold coefficientModulus
      calc
        (2 * ringDegree securityParameter) * 2 =
            4 * ringDegree securityParameter := by ring
        _ ≤ 64 * ringDegree securityParameter := by omega
        _ ≤ 64 * ringDegree securityParameter ^ 6 :=
          Nat.mul_le_mul_left 64 hdegreePow
    exact_mod_cast hnat
  have hnegative :
      -(coefficientModulus securityParameter : ℤ) <
        ((2 * ringDegree securityParameter : ℕ) : ℤ) * 2 := by
    have hmodulusPos : 0 < coefficientModulus securityParameter := by
      exact Nat.mul_pos (by norm_num) (Nat.pow_pos hdegreePos)
    have hmodulusPosInt : (0 : ℤ) < coefficientModulus securityParameter := by
      exact_mod_cast hmodulusPos
    have hright :
        (0 : ℤ) ≤ ((2 * ringDegree securityParameter : ℕ) : ℤ) * 2 := by
      positivity
    omega
  have hcentered := LatticeCrypto.centeredRepr_intCast_eq
    (q := coefficientModulus securityParameter)
    ((2 * ringDegree securityParameter : ℕ) : ℤ) hnegative htwiceLe
  have hcast :
      ((2 * ringDegree securityParameter : ℕ) :
          ZMod (coefficientModulus securityParameter)) =
        ((((2 * ringDegree securityParameter : ℕ) : ℤ)) :
          ZMod (coefficientModulus securityParameter)) := by
    norm_num
  rw [hcast, hcentered]
  exact Int.natAbs_natCast _

/-- The native width `λ+1` satisfies the exact KSK decoding margin at level one. -/
theorem keySwitchRecoveryMargin (securityParameter : ℕ) :
    2 * errorWidth securityParameter <
      BootstrappingCorrectness.centeredDistance 0
        (family.parameters.keySwitchGadget securityParameter
          (keySwitchRecoveryLevel securityParameter)) := by
  rw [centeredDistance_zero_keySwitchGadget_recoveryLevel]
  have hinput := inputMargin securityParameter
  rw [rotationDegree_add_one] at hinput
  omega

/-- Averaged residual evaluator certificates from the native centered-binomial search
distribution to the concrete growing-family public CircLWE distribution. -/
abbrev AveragedResidualReductionFamily :=
  Native.ResidualCandidateView.Asymptotic.ReductionFamily
    family.parameters errorWidth errorWidth

/-- Public native CircLWE distinguishers for the concrete growing family. -/
abbrev PublicCircularDistinguisherFamily :=
  Native.ResidualCandidateView.Asymptotic.PublicDistinguisherFamily family.parameters

/-- Paired-key solvers for the concrete centered-binomial source distribution. -/
abbrev CircularSearchSolverFamily :=
  Native.ResidualCandidateView.Asymptotic.SearchSolverFamily family.parameters

/-- The exact public native CircLWE game for the growing family. -/
noncomputable abbrev publicCircularLWESecurityGame :=
  Native.ResidualCandidateView.Asymptotic.publicCircularLWESecurityGame family.parameters

/-- The exact paired-key centered-binomial search game for the growing family. -/
noncomputable abbrev circularSearchSecurityGame :=
  Native.ResidualCandidateView.Asymptotic.narrowSearchSecurityGame
    family.parameters errorWidth errorWidth

/-- **Growing-family public CircLWE from averaged residual search-to-decision.**

All generic search-to-decision accounting and all concrete KSK decoding arithmetic are discharged.
The remaining inputs identify the actual shifted evaluator, prove that its explicit accumulated
loss is negligible, and state hardness of the generated native paired-search solvers. -/
theorem publicCircularLWESecurityGame_secureAgainst_of_search_and_residual
    (reduction : AveragedResidualReductionFamily)
    (decisionIsPPT : PublicCircularDistinguisherFamily → Prop)
    (solverIsPPT : CircularSearchSolverFamily → Prop)
    (hClosed : ∀ distinguisher, decisionIsPPT distinguisher →
      solverIsPPT
        (Native.ResidualCandidateView.Asymptotic.toSearchSolverFamily
          family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
          keySwitchRecoveryMargin distinguisher))
    (hSearch : circularSearchSecurityGame.secureAgainst solverIsPPT)
    (hResidualLoss :
      (Native.ResidualCandidateView.Asymptotic.reductionLossSecurityGame
        family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
        keySwitchRecoveryMargin).secureAgainst decisionIsPPT) :
    publicCircularLWESecurityGame.secureAgainst decisionIsPPT :=
  Native.ResidualCandidateView.Asymptotic.publicCircularLWESecurityGame_secureAgainst_of_search_and_loss
    family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
    keySwitchRecoveryMargin decisionIsPPT solverIsPPT hClosed hSearch hResidualLoss

/-- The same result, stated on the repository's pre-existing native CircLWE game and restricted
exactly to continuations induced by the selected public distinguisher class. -/
theorem nativeCircularLWESecurityGame_secureAgainst_publicContinuations_of_search_and_residual
    (reduction : AveragedResidualReductionFamily)
    (decisionIsPPT : PublicCircularDistinguisherFamily → Prop)
    (solverIsPPT : CircularSearchSolverFamily → Prop)
    (hClosed : ∀ distinguisher, decisionIsPPT distinguisher →
      solverIsPPT
        (Native.ResidualCandidateView.Asymptotic.toSearchSolverFamily
          family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
          keySwitchRecoveryMargin distinguisher))
    (hSearch : circularSearchSecurityGame.secureAgainst solverIsPPT)
    (hResidualLoss :
      (Native.ResidualCandidateView.Asymptotic.reductionLossSecurityGame
        family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
        keySwitchRecoveryMargin).secureAgainst decisionIsPPT) :
    (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
      family.parameters).secureAgainst
        (Native.ResidualCandidateView.Asymptotic.PublicContinuationAllowed
          family.parameters decisionIsPPT) := by
  apply Native.ResidualCandidateView.Asymptotic.circularLWESecurityGame_secureAgainst_publicContinuations
  exact publicCircularLWESecurityGame_secureAgainst_of_search_and_residual reduction
    decisionIsPPT solverIsPPT hClosed hSearch hResidualLoss

/-- Native monomial circular/KDM security for public continuations follows after separately
discharging the zero-message BRK-versus-uniform side-information branch. -/
theorem nativeMonomialSecurityGame_secureAgainst_publicContinuations_of_search_residual_and_zero
    (reduction : AveragedResidualReductionFamily)
    (decisionIsPPT : PublicCircularDistinguisherFamily → Prop)
    (solverIsPPT : CircularSearchSolverFamily → Prop)
    (hClosed : ∀ distinguisher, decisionIsPPT distinguisher →
      solverIsPPT
        (Native.ResidualCandidateView.Asymptotic.toSearchSolverFamily
          family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
          keySwitchRecoveryMargin distinguisher))
    (hSearch : circularSearchSecurityGame.secureAgainst solverIsPPT)
    (hResidualLoss :
      (Native.ResidualCandidateView.Asymptotic.reductionLossSecurityGame
        family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
        keySwitchRecoveryMargin).secureAgainst decisionIsPPT)
    (hZero :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.zeroLWESecurityGame
        family.parameters).secureAgainst
          (Native.ResidualCandidateView.Asymptotic.PublicContinuationAllowed
            family.parameters decisionIsPPT)) :
    (Encryption.Adaptive.Asymptotic.MonomialKDM.securityGame
      family.parameters).secureAgainst
        (Native.ResidualCandidateView.Asymptotic.PublicContinuationAllowed
          family.parameters decisionIsPPT) := by
  apply Native.ResidualCandidateView.Asymptotic.monomialSecurityGame_secureAgainst_publicContinuations_of_publicCircular_and_zero
  · exact publicCircularLWESecurityGame_secureAgainst_of_search_and_residual reduction
      decisionIsPPT solverIsPPT hClosed hSearch hResidualLoss
  · exact hZero

end

end FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd
