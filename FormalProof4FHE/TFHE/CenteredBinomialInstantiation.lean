/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomial
import FormalProof4FHE.TFHE.AsymptoticCutCycleSamplerReplacement
import FormalProof4FHE.TFHE.AuxiliaryInputZeroSecurity
import FormalProof4FHE.TFHE.AsymptoticMonomialKDM
import FormalProof4FHE.TFHE.GadgetDecomposition

/-!
# Finite Centered-Binomial TFHE Instantiation

This module instantiates the finite native TFHE security games with executable centered-binomial
scalar and ring errors and the checked power-of-base gadgets. It is an explicit finite-distribution
variant, not an identification of centered binomial noise with the torus Gaussian used in the
original TFHE paper.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.CenteredBinomial

/-! ## Executable scalar errors -/

/-- The scalar sampler uses the same independent bit-pair row as one coefficient of the checked
ring centered-binomial sampler. -/
abbrev ScalarCoins (eta : ℕ) := RLWE.CenteredBinomial.CoinRow eta

/-- Convert one row of centered-binomial coins to a scalar residue. -/
def scalarErrorFromCoins (q eta : ℕ) (coins : ScalarCoins eta) : ZMod q :=
  RLWE.CenteredBinomial.signedWeight coins

/-- Every scalar output has a signed representative in `[-eta, eta]`. -/
def ScalarBounded {q : ℕ} (eta : ℕ) (error : ZMod q) : Prop :=
  ∃ value : ℤ, |value| ≤ eta ∧ error = (value : ZMod q)

/-- The deterministic scalar error constructed from coins is bounded. -/
theorem scalarErrorFromCoins_bounded (q eta : ℕ) (coins : ScalarCoins eta) :
    ScalarBounded eta (scalarErrorFromCoins q eta coins) :=
  ⟨RLWE.CenteredBinomial.signedWeight coins,
    RLWE.CenteredBinomial.abs_signedWeight_le coins, rfl⟩

/-- Executable scalar centered-binomial sampler modulo `q`. -/
def scalarSampler (q eta : ℕ) [NeZero q] : ProbComp (ZMod q) := do
  let coins ← $ᵗ (ScalarCoins eta)
  return scalarErrorFromCoins q eta coins

/-- Every scalar error in the sampler support satisfies the deterministic bound. -/
theorem scalarBounded_of_mem_support {q eta : ℕ} [NeZero q] {error : ZMod q}
    (herror : error ∈ support (scalarSampler q eta)) : ScalarBounded eta error := by
  obtain ⟨coins, _, hcoins⟩ :=
    (mem_support_bind_iff ($ᵗ (ScalarCoins eta))
      (fun coins ↦ pure (scalarErrorFromCoins q eta coins)) error).mp herror
  simp only [support_pure, Set.mem_singleton_iff] at hcoins
  subst error
  exact scalarErrorFromCoins_bounded q eta coins

/-- Swapping the positive and negative coin in every pair is an involution. -/
@[simp]
theorem swapScalarCoins_swapScalarCoins {eta : ℕ} (coins : ScalarCoins eta) :
    RLWE.CenteredBinomial.swapRow (RLWE.CenteredBinomial.swapRow coins) = coins := by
  funext index
  simp [RLWE.CenteredBinomial.swapRow]

/-- The scalar coin swap is a permutation of the finite coin space. -/
theorem swapScalarCoins_bijective (eta : ℕ) :
    Function.Bijective
      (RLWE.CenteredBinomial.swapRow : ScalarCoins eta → ScalarCoins eta) :=
  Function.Involutive.bijective swapScalarCoins_swapScalarCoins

/-- Swapping the coin pairs negates the resulting scalar residue. -/
@[simp]
theorem scalarErrorFromCoins_swap (q eta : ℕ) (coins : ScalarCoins eta) :
    scalarErrorFromCoins q eta (RLWE.CenteredBinomial.swapRow coins) =
      -scalarErrorFromCoins q eta coins := by
  simp [scalarErrorFromCoins]

/-- The scalar centered-binomial distribution is exactly invariant under negation. -/
theorem scalar_probOutput_neg (q eta : ℕ) [NeZero q] (error : ZMod q) :
    Pr[= -error | scalarSampler q eta] = Pr[= error | scalarSampler q eta] := by
  have hreindex := probOutput_bind_bijective_uniform_cross
    (α := ScalarCoins eta) (β := ScalarCoins eta)
    RLWE.CenteredBinomial.swapRow (swapScalarCoins_bijective eta)
    (fun coins ↦ pure (scalarErrorFromCoins q eta coins)) (-error)
  rw [show (($ᵗ (ScalarCoins eta)) >>= fun coins ↦
      pure (scalarErrorFromCoins q eta (RLWE.CenteredBinomial.swapRow coins))) =
      (($ᵗ (ScalarCoins eta)) >>= fun coins ↦
        pure (-scalarErrorFromCoins q eta coins)) by
    apply bind_congr
    intro coins
    rw [scalarErrorFromCoins_swap]] at hreindex
  rw [show scalarSampler q eta =
      (($ᵗ (ScalarCoins eta)) >>= fun coins ↦
        pure (scalarErrorFromCoins q eta coins)) by
    simp [scalarSampler, monad_norm]]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum] at hreindex ⊢
  calc
    _ = ∑' coins : ScalarCoins eta,
        Pr[= coins | $ᵗ (ScalarCoins eta)] *
          Pr[= -error | pure (-scalarErrorFromCoins q eta coins)] := hreindex.symm
    _ = ∑' coins : ScalarCoins eta,
        Pr[= coins | $ᵗ (ScalarCoins eta)] *
          Pr[= error | pure (scalarErrorFromCoins q eta coins)] := by
      refine tsum_congr fun coins ↦ ?_
      congr 1
      by_cases h : error = scalarErrorFromCoins q eta coins
      · subst error
        rw [probOutput_pure_self, probOutput_pure_self]
      · have hn : -error ≠ -scalarErrorFromCoins q eta coins := fun heq ↦ h (neg_injective heq)
        rw [probOutput_pure, probOutput_pure, if_neg hn, if_neg h]
    _ = _ := rfl

/-! ## Native family with concrete samplers and gadgets -/

/-- Data for a finite centered-binomial native TFHE family. The two scalar error widths remain
separate, matching the general two-noise adaptive security theorem. -/
structure Family (Message : Type) where
  q : ℕ → ℕ
  degree : ℕ → ℕ
  ringRank : ℕ → ℕ
  lweDimension : ℕ → ℕ
  ringEta : ℕ → ℕ
  keySwitchEta : ℕ → ℕ
  inputEta : ℕ → ℕ
  tgswDecomposition : (securityParameter : ℕ) → Gadget.Base.Parameters (q securityParameter)
  keySwitchDecomposition :
    (securityParameter : ℕ) → Gadget.Base.Parameters (q securityParameter)
  encode : (securityParameter : ℕ) → Message → ZMod (q securityParameter)

/-- Convert the concrete centered-binomial family into the parameters consumed by the exact
adaptive and asymptotic TFHE security games. -/
noncomputable def Family.parameters {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)] :
    Encryption.Adaptive.Asymptotic.Parameters Message where
  q := family.q
  degree := family.degree
  ringRank := family.ringRank
  tgswLevels := fun securityParameter ↦
    (family.tgswDecomposition securityParameter).levels
  lweDimension := family.lweDimension
  keySwitchLevels := fun securityParameter ↦
    (family.keySwitchDecomposition securityParameter).levels
  ringErrorSampler := fun securityParameter ↦
    RLWE.CenteredBinomial.sampler
      (family.q securityParameter)
      (family.degree securityParameter)
      (family.ringEta securityParameter)
  keySwitchErrorSampler := fun securityParameter ↦
    scalarSampler (family.q securityParameter) (family.keySwitchEta securityParameter)
  inputErrorSampler := fun securityParameter ↦
    scalarSampler (family.q securityParameter) (family.inputEta securityParameter)
  tgswGadget := fun securityParameter ↦
    Gadget.Base.ringGadget (degree := family.degree securityParameter)
      (family.tgswDecomposition securityParameter)
  keySwitchGadget := fun securityParameter ↦
    Gadget.Base.gadget (family.keySwitchDecomposition securityParameter)
  encode := family.encode

@[simp]
theorem Family.parameters_q {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)] (securityParameter : ℕ) :
    (family.parameters.q securityParameter) = family.q securityParameter := rfl

/-- Nonzero source moduli induce the pointwise nonzero instance expected by the generic family. -/
instance Family.instParametersNeZero {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)] :
    ∀ securityParameter, NeZero (family.parameters.q securityParameter) :=
  fun securityParameter ↦ (inferInstance : NeZero (family.q securityParameter))

@[simp]
theorem Family.parameters_degree {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)] (securityParameter : ℕ) :
    family.parameters.degree securityParameter = family.degree securityParameter := rfl

@[simp]
theorem Family.parameters_tgswLevels {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)] (securityParameter : ℕ) :
    family.parameters.tgswLevels securityParameter =
      (family.tgswDecomposition securityParameter).levels := rfl

@[simp]
theorem Family.parameters_keySwitchLevels {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)] (securityParameter : ℕ) :
    family.parameters.keySwitchLevels securityParameter =
      (family.keySwitchDecomposition securityParameter).levels := rfl

/-- Every ring error sampled by the instantiated family is coefficientwise bounded by its
configured centered-binomial width. -/
theorem Family.ringError_coeffBounded {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (securityParameter : ℕ)
    {error : RLWE.Rq (family.q securityParameter) (family.degree securityParameter)}
    (herror : error ∈ support (family.parameters.ringErrorSampler securityParameter)) :
    RLWE.CenteredBinomial.CoeffBounded (family.ringEta securityParameter) error := by
  exact RLWE.CenteredBinomial.coeffBounded_of_mem_support herror

/-- Every key-switch error sampled by the instantiated family has a bounded signed lift. -/
theorem Family.keySwitchError_bounded {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (securityParameter : ℕ) {error : ZMod (family.q securityParameter)}
    (herror : error ∈ support (family.parameters.keySwitchErrorSampler securityParameter)) :
    ScalarBounded (family.keySwitchEta securityParameter) error := by
  exact scalarBounded_of_mem_support herror

/-- Every fresh input error sampled by the instantiated family has a bounded signed lift. -/
theorem Family.inputError_bounded {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (securityParameter : ℕ) {error : ZMod (family.q securityParameter)}
    (herror : error ∈ support (family.parameters.inputErrorSampler securityParameter)) :
    ScalarBounded (family.inputEta securityParameter) error := by
  exact scalarBounded_of_mem_support herror

/-- The concrete TGSW gadget reconstructs every ring element with the checked coefficientwise
digit algorithm. -/
theorem Family.tgswGadget_recompose {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (securityParameter : ℕ)
    (value : RLWE.Rq (family.q securityParameter) (family.degree securityParameter)) :
    Gadget.recompose (family.parameters.tgswGadget securityParameter)
        (Gadget.Base.ringDigit (family.tgswDecomposition securityParameter) value) = value := by
  exact Gadget.Base.ring_recompose (family.tgswDecomposition securityParameter) value

/-- The concrete key-switch gadget reconstructs every scalar residue with the checked digit
algorithm. -/
theorem Family.keySwitchGadget_recompose {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (securityParameter : ℕ) (value : ZMod (family.q securityParameter)) :
    Gadget.recompose (family.parameters.keySwitchGadget securityParameter)
        (Gadget.Base.digit (family.keySwitchDecomposition securityParameter) value) = value := by
  exact Gadget.Base.recompose (family.keySwitchDecomposition securityParameter) value

/-! ## Polynomial growth and asymptotic security -/

/-- Polynomial growth witnesses for the concrete KSK dimensions. -/
structure Family.PolynomialKeySwitchGrowth {Message : Type} (family : Family Message) where
  ringRankPolynomial : Polynomial ℕ
  degreePolynomial : Polynomial ℕ
  keySwitchLevelsPolynomial : Polynomial ℕ
  ringRank_le : ∀ securityParameter,
    family.ringRank securityParameter ≤ ringRankPolynomial.eval securityParameter
  degree_le : ∀ securityParameter,
    family.degree securityParameter ≤ degreePolynomial.eval securityParameter
  keySwitchLevels_le : ∀ securityParameter,
    (family.keySwitchDecomposition securityParameter).levels ≤
      keySwitchLevelsPolynomial.eval securityParameter

/-- Translate concrete growth witnesses to the generic asymptotic TFHE interface. -/
def Family.PolynomialKeySwitchGrowth.toAsymptotic {Message : Type}
    {family : Family Message}
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (growth : family.PolynomialKeySwitchGrowth) :
    Encryption.Adaptive.Asymptotic.PolynomialKeySwitchGrowth family.parameters where
  ringRankPolynomial := growth.ringRankPolynomial
  degreePolynomial := growth.degreePolynomial
  keySwitchLevelsPolynomial := growth.keySwitchLevelsPolynomial
  ringRank_le := growth.ringRank_le
  degree_le := growth.degree_le
  keySwitchLevels_le := growth.keySwitchLevels_le

/-- Polynomial growth witnesses for every BRK and KSK error draw in a concrete family. -/
structure Family.PolynomialEvaluationKeyGrowth {Message : Type} (family : Family Message)
    extends family.PolynomialKeySwitchGrowth where
  tgswLevelsPolynomial : Polynomial ℕ
  lweDimensionPolynomial : Polynomial ℕ
  tgswLevels_le : ∀ securityParameter,
    (family.tgswDecomposition securityParameter).levels ≤
      tgswLevelsPolynomial.eval securityParameter
  lweDimension_le : ∀ securityParameter,
    family.lweDimension securityParameter ≤
      lweDimensionPolynomial.eval securityParameter

/-- Translate complete concrete evaluation-key growth witnesses to the generic sampler-replacement
interface. -/
def Family.PolynomialEvaluationKeyGrowth.toAsymptotic {Message : Type}
    {family : Family Message}
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (growth : family.PolynomialEvaluationKeyGrowth) :
    Encryption.Adaptive.Asymptotic.PolynomialEvaluationKeyGrowth family.parameters where
  toPolynomialKeySwitchGrowth := growth.toPolynomialKeySwitchGrowth.toAsymptotic
  tgswLevelsPolynomial := growth.tgswLevelsPolynomial
  lweDimensionPolynomial := growth.lweDimensionPolynomial
  tgswLevels_le := growth.tgswLevels_le
  lweDimension_le := growth.lweDimension_le

/-- The concrete centered-binomial reduction has polynomially many scalar LWE rows under the
family's KSK growth witnesses and the adversary's polynomial query witness. -/
theorem Family.batchSampleCount_le_polynomial {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (growth : family.PolynomialKeySwitchGrowth)
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary family.parameters)
    (securityParameter : ℕ) :
    Encryption.Security.keySwitchSamples
          (family.ringRank securityParameter)
          (family.degree securityParameter)
          (family.keySwitchDecomposition securityParameter).levels +
        adversary.queryCount securityParameter ≤
      (Encryption.Adaptive.Asymptotic.batchSamplePolynomial
        growth.toAsymptotic adversary).eval securityParameter := by
  exact Encryption.Adaptive.Asymptotic.batchSampleCount_le_polynomial
    growth.toAsymptotic adversary securityParameter

/-- **Centered-binomial asymptotic adaptive TFHE security with distinct scalar widths.**
This is the generic negligible-advantage composition theorem instantiated with the executable
samplers and gadgets above. -/
theorem Family.secureAgainst_of_directBilinear_and_jointLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (continuationIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (jointLWEIsPPT : Encryption.Adaptive.Asymptotic.JointLWEAdversaryFamily
      family.parameters → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT
        (Encryption.Adaptive.Asymptotic.continuationReduction family.parameters adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (Encryption.Adaptive.Asymptotic.jointLWEReduction family.parameters adversary))
    (hCircular :
      (Encryption.Adaptive.Asymptotic.directBilinearSecurityGame
        family.parameters).secureAgainst continuationIsPPT)
    (hJointLWE :
      (Encryption.Adaptive.Asymptotic.jointLWESecurityGame
        family.parameters).secureAgainst jointLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.secureAgainst_of_directBilinear_and_jointLWE
    family.parameters isPPT continuationIsPPT jointLWEIsPPT
    hContinuationClosed hJointLWEClosed hCircular hJointLWE

/-- Equal centered-binomial widths give definitionally equal scalar error samplers. -/
theorem Family.scalarSamplers_eq_of_eta_eq {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (hEta : ∀ securityParameter,
      family.inputEta securityParameter = family.keySwitchEta securityParameter) :
    ∀ securityParameter,
      family.parameters.inputErrorSampler securityParameter =
        family.parameters.keySwitchErrorSampler securityParameter := by
  intro securityParameter
  simp only [Family.parameters]
  rw [hEta securityParameter]

/-- **Equal-width centered-binomial asymptotic adaptive TFHE security.** The scalar target is
ordinary binary-secret batch LWE on the exact KSK-plus-query row count. -/
theorem Family.secureAgainst_of_directBilinear_and_batchLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (hEta : ∀ securityParameter,
      family.inputEta securityParameter = family.keySwitchEta securityParameter)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (continuationIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT
        (Encryption.Adaptive.Asymptotic.continuationReduction family.parameters adversary))
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary))
    (hCircular :
      (Encryption.Adaptive.Asymptotic.directBilinearSecurityGame
        family.parameters).secureAgainst continuationIsPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        family.parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.secureAgainst_of_directBilinear_and_batchLWE
    family.parameters (family.scalarSamplers_eq_of_eta_eq hEta)
    isPPT continuationIsPPT batchLWEIsPPT hContinuationClosed hBatchLWEClosed
    hCircular hBatchLWE

/-! ## Exact native monomial-KDM presentation -/

/-- Pointwise centered-binomial TFHE bound with the exact native degree-two monomial-KDM term
exposed.  Unlike an implementation-to-reference sampler theorem, this statement has no
statistical replacement loss: the executable centered-binomial samplers are used directly in the
honest game, the KDM game, and the heterogeneous joint-LWE game. -/
theorem Family.securityGame_advantage_le_monomialKDM_add_jointLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary family.parameters)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
          family.parameters).advantage adversary securityParameter +
        (Encryption.Adaptive.Asymptotic.jointLWESecurityGame family.parameters).advantage
          (Encryption.Adaptive.Asymptotic.jointLWEReduction family.parameters adversary)
          securityParameter := by
  calc
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      (Encryption.Adaptive.Asymptotic.directBilinearSecurityGame
          family.parameters).advantage
        (Encryption.Adaptive.Asymptotic.continuationReduction family.parameters adversary)
        securityParameter +
      (Encryption.Adaptive.Asymptotic.jointLWESecurityGame family.parameters).advantage
        (Encryption.Adaptive.Asymptotic.jointLWEReduction family.parameters adversary)
        securityParameter :=
      Encryption.Adaptive.Asymptotic.securityGame_advantage_le_directBilinear_add_jointLWE
        family.parameters adversary securityParameter
    _ = (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
          family.parameters).advantage adversary securityParameter +
        (Encryption.Adaptive.Asymptotic.jointLWESecurityGame family.parameters).advantage
          (Encryption.Adaptive.Asymptotic.jointLWEReduction family.parameters adversary)
          securityParameter := by
      rw [Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame_advantage_eq_directBilinear]
      rfl

/-- Pointwise equal-width specialization.  Every scalar KSK row and adaptive input row is one
ordinary binary-secret batch-LWE instance, and the remaining first hop is exactly the native
degree-two monomial-KDM game. -/
theorem Family.securityGame_advantage_le_monomialKDM_add_batchLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (hEta : ∀ securityParameter,
      family.inputEta securityParameter = family.keySwitchEta securityParameter)
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary family.parameters)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
          family.parameters).advantage adversary securityParameter +
        (Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
          (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary)
          securityParameter := by
  calc
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      (Encryption.Adaptive.Asymptotic.directBilinearSecurityGame
          family.parameters).advantage
        (Encryption.Adaptive.Asymptotic.continuationReduction family.parameters adversary)
        securityParameter +
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
        (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary)
        securityParameter :=
      Encryption.Adaptive.Asymptotic.securityGame_advantage_le_directBilinear_add_batchLWE
        family.parameters (family.scalarSamplers_eq_of_eta_eq hEta)
        adversary securityParameter
    _ = (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
          family.parameters).advantage adversary securityParameter +
        (Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
          (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary)
          securityParameter := by
      rw [Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame_advantage_eq_directBilinear]
      rfl

/-- Pointwise equal-width centered-binomial TFHE bound in the PKC 2024-style auxiliary-input
CircLWE presentation.  The native monomial first hop is split into real-versus-uniform CircLWE
and the explicit zero-message-versus-uniform side-information term; ordinary query-counted batch
LWE handles the scalar KSK and encryption-query block. -/
theorem Family.securityGame_advantage_le_circularLWE_add_zeroLWE_add_batchLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (hEta : ∀ securityParameter,
      family.inputEta securityParameter = family.keySwitchEta securityParameter)
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary family.parameters)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
          family.parameters).advantage
          adversary securityParameter +
        (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveZeroLWESecurityGame
          family.parameters).advantage
          adversary securityParameter +
        (Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
          (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary)
          securityParameter := by
  exact (family.securityGame_advantage_le_monomialKDM_add_batchLWE
      hEta adversary securityParameter).trans
    (add_le_add
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveSecurityGame_advantage_le_circularLWE_add_zeroLWE
          family.parameters adversary securityParameter) le_rfl)

/-- **Pointwise centered-binomial TFHE security from auxiliary-input CircLWE and ordinary
LWE.**  The former zero-side assumption is discharged by two scalar batch-LWE reductions: the
usual actual zero-BRK context and an exactly uniform BRK context.  The usual honest-game scalar
reduction is then added once more. -/
theorem Family.securityGame_advantage_le_circularLWE_add_three_batchLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (hEta : ∀ securityParameter,
      family.inputEta securityParameter = family.keySwitchEta securityParameter)
    (adversary : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary family.parameters)
    (securityParameter : ℕ) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).advantage
        adversary securityParameter ≤
      ((Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
            family.parameters).advantage adversary securityParameter +
        ((Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
            (Encryption.Adaptive.Asymptotic.batchLWEReduction
              family.parameters adversary) securityParameter +
          (Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
            (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
              family.parameters adversary) securityParameter)) +
        (Encryption.Adaptive.Asymptotic.batchLWESecurityGame family.parameters).advantage
          (Encryption.Adaptive.Asymptotic.batchLWEReduction
            family.parameters adversary) securityParameter := by
  exact (family.securityGame_advantage_le_monomialKDM_add_batchLWE
      hEta adversary securityParameter).trans
    (add_le_add
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveSecurityGame_advantage_le_circularLWE_add_two_batchLWE
        family.parameters (family.scalarSamplers_eq_of_eta_eq hEta)
        adversary securityParameter)
      le_rfl)

/-- **Centered-binomial adaptive TFHE security from exact native monomial KDM and joint LWE.**

The monomial-KDM premise is already restricted to continuations induced by the same
polynomial-query adversary class, so no separate continuation-efficiency closure premise is
needed. -/
theorem Family.secureAgainst_of_monomialKDM_and_jointLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (jointLWEIsPPT : Encryption.Adaptive.Asymptotic.JointLWEAdversaryFamily
      family.parameters → Prop)
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (Encryption.Adaptive.Asymptotic.jointLWEReduction family.parameters adversary))
    (hMonomialKDM :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
        family.parameters).secureAgainst isPPT)
    (hJointLWE :
      (Encryption.Adaptive.Asymptotic.jointLWESecurityGame
        family.parameters).secureAgainst jointLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (family.securityGame_advantage_le_monomialKDM_add_jointLWE adversary)
    (negligible_add
      (hMonomialKDM adversary hadversary)
      (hJointLWE
        (Encryption.Adaptive.Asymptotic.jointLWEReduction family.parameters adversary)
        (hJointLWEClosed adversary hadversary)))

/-- **Equal-width centered-binomial adaptive TFHE security from exact native degree-two
monomial KDM and ordinary query-counted batch LWE.**

This is the sampler-exact counterpart of the discrete-Gaussian certificate theorem: there is no
replacement premise or loss because centered binomial is the reference distribution itself. -/
theorem Family.secureAgainst_of_monomialKDM_and_batchLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (hEta : ∀ securityParameter,
      family.inputEta securityParameter = family.keySwitchEta securityParameter)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary))
    (hMonomialKDM :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
        family.parameters).secureAgainst isPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        family.parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (family.securityGame_advantage_le_monomialKDM_add_batchLWE hEta adversary)
    (negligible_add
      (hMonomialKDM adversary hadversary)
      (hBatchLWE
        (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary)
        (hBatchLWEClosed adversary hadversary)))

/-- **Centered-binomial adaptive TFHE security from auxiliary-input CircLWE.**

This is the literature-aligned refinement of
`secureAgainst_of_monomialKDM_and_batchLWE`.  It replaces the single native monomial-KDM premise
by its real-versus-uniform auxiliary-input CircLWE game and the explicit zero-message-versus-
uniform side-information game.  Both use the exact executable centered-binomial native sampler;
no Gaussian or sampler-replacement loss occurs. -/
theorem Family.secureAgainst_of_circularLWE_and_zeroLWE_and_batchLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (hEta : ∀ securityParameter,
      family.inputEta securityParameter = family.keySwitchEta securityParameter)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary))
    (hCircularLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
        family.parameters).secureAgainst isPPT)
    (hZeroLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveZeroLWESecurityGame
        family.parameters).secureAgainst isPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        family.parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (family.securityGame_advantage_le_circularLWE_add_zeroLWE_add_batchLWE
      hEta adversary)
    (negligible_add
      (negligible_add
        (hCircularLWE adversary hadversary)
        (hZeroLWE adversary hadversary))
      (hBatchLWE
        (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary)
        (hBatchLWEClosed adversary hadversary)))

/-- **Centered-binomial adaptive TFHE security from one named auxiliary-input CircLWE premise
and ordinary batch LWE.**

Unlike `secureAgainst_of_circularLWE_and_zeroLWE_and_batchLWE`, this theorem has no independent
zero-message side-information premise.  The exact uniform-error BRK lemma and the adaptive fair
hidden-bit hybrid reduce that term to the two batch-LWE reductions named by the closure
hypotheses. -/
theorem Family.secureAgainst_of_circularLWE_and_batchLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (hEta : ∀ securityParameter,
      family.inputEta securityParameter = family.keySwitchEta securityParameter)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction family.parameters adversary))
    (hUniformBootstrapBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
          family.parameters adversary))
    (hCircularLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
        family.parameters).secureAgainst isPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        family.parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT := by
  have hMonomialKDM :=
    Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveSecurityGame_secureAgainst_of_circularLWE_and_batchLWE
      family.parameters (family.scalarSamplers_eq_of_eta_eq hEta)
      isPPT batchLWEIsPPT hBatchLWEClosed hUniformBootstrapBatchLWEClosed
      hCircularLWE hBatchLWE
  exact family.secureAgainst_of_monomialKDM_and_batchLWE
    hEta isPPT batchLWEIsPPT hBatchLWEClosed hMonomialKDM hBatchLWE

/-! ## Alternative-order circular-security instantiations -/

/-- **Centered-binomial adaptive TFHE security in KSK-first order.** The generic cut-cycle
theorem instantiated with the executable centered-binomial samplers and exact gadgets. -/
theorem Family.secureAgainst_of_keySwitchFirst_and_two_ringBatchLWE_and_jointLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (continuationIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (jointLWEIsPPT : Encryption.Adaptive.Asymptotic.JointLWEAdversaryFamily
      family.parameters → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT
        (Encryption.Adaptive.Asymptotic.continuationReduction family.parameters adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT
        (Encryption.Adaptive.Asymptotic.CutCycleSecurity.realRingBatchReduction
          family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT
        (Encryption.Adaptive.Asymptotic.CutCycleSecurity.zeroRingBatchReduction
          family.parameters adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (Encryption.Adaptive.Asymptotic.CutCycleSecurity.zeroCloudJointLWEReduction
          family.parameters adversary))
    (hCircular :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.keySwitchFirstSecurityGame
        family.parameters).secureAgainst continuationIsPPT)
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hJointLWE :
      (Encryption.Adaptive.Asymptotic.jointLWESecurityGame
        family.parameters).secureAgainst jointLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.CutCycleSecurity.secureAgainst_of_keySwitchFirst_and_two_ringBatchLWE_and_jointLWE
    family.parameters isPPT continuationIsPPT realRingBatchIsPPT zeroRingBatchIsPPT
    jointLWEIsPPT hContinuationClosed hRealRingBatchClosed hZeroRingBatchClosed
    hJointLWEClosed hCircular hRealRingBatch hZeroRingBatch hJointLWE

/-- **Equal-width centered-binomial KSK-first security.** Apart from the exact native intact-cycle
premise, all computational assumptions are ordinary binary-secret batch LWE: two ring batches
and one scalar KSK-plus-query batch. -/
theorem Family.secureAgainst_of_keySwitchFirst_and_three_batchLWE
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (hEta : ∀ securityParameter,
      family.inputEta securityParameter = family.keySwitchEta securityParameter)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (continuationIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (scalarBatchIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      family.parameters → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT
        (Encryption.Adaptive.Asymptotic.continuationReduction family.parameters adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT
        (Encryption.Adaptive.Asymptotic.CutCycleSecurity.realRingBatchReduction
          family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT
        (Encryption.Adaptive.Asymptotic.CutCycleSecurity.zeroRingBatchReduction
          family.parameters adversary))
    (hScalarBatchClosed : ∀ adversary, isPPT adversary →
      scalarBatchIsPPT
        (Encryption.Adaptive.Asymptotic.CutCycleSecurity.zeroCloudBatchLWEReduction
          family.parameters adversary))
    (hCircular :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.keySwitchFirstSecurityGame
        family.parameters).secureAgainst continuationIsPPT)
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hScalarBatch :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        family.parameters).secureAgainst scalarBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.CutCycleSecurity.secureAgainst_of_keySwitchFirst_and_three_batchLWE
    family.parameters (family.scalarSamplers_eq_of_eta_eq hEta) isPPT continuationIsPPT
    realRingBatchIsPPT zeroRingBatchIsPPT scalarBatchIsPPT hContinuationClosed
    hRealRingBatchClosed hZeroRingBatchClosed hScalarBatchClosed hCircular hRealRingBatch
    hZeroRingBatch hScalarBatch

/-! ## A fully specified scalable finite family -/

/-- A simple scalable finite family with modulus `securityParameter + 2`, positive degree and LWE
dimension `securityParameter + 1`, rank one, and exact base-two decompositions of length
`securityParameter + 2`. Noise widths and message encoding remain caller-selected. This is a
formal instantiation witness, not a production parameter recommendation. -/
def linearModulusFamily {Message : Type}
    (ringEta keySwitchEta inputEta : ℕ → ℕ)
    (encode : (securityParameter : ℕ) → Message → ZMod (securityParameter + 2)) :
    Family Message where
  q := fun securityParameter ↦ securityParameter + 2
  degree := fun securityParameter ↦ securityParameter + 1
  ringRank := fun _ ↦ 1
  lweDimension := fun securityParameter ↦ securityParameter + 1
  ringEta := ringEta
  keySwitchEta := keySwitchEta
  inputEta := inputEta
  tgswDecomposition := fun securityParameter ↦
    { base := 2
      levels := securityParameter + 2
      one_lt_base := by omega
      modulus_le_capacity :=
        Nat.le_of_lt
          (show securityParameter + 2 < 2 ^ (securityParameter + 2) from
            Nat.lt_two_pow_self) }
  keySwitchDecomposition := fun securityParameter ↦
    { base := 2
      levels := securityParameter + 2
      one_lt_base := by omega
      modulus_le_capacity :=
        Nat.le_of_lt
          (show securityParameter + 2 < 2 ^ (securityParameter + 2) from
            Nat.lt_two_pow_self) }
  encode := encode

/-- Every modulus in `linearModulusFamily` is nonzero. -/
instance instLinearModulusFamilyNeZero {Message : Type}
    (ringEta keySwitchEta inputEta : ℕ → ℕ)
    (encode : (securityParameter : ℕ) → Message → ZMod (securityParameter + 2)) :
    ∀ securityParameter,
      NeZero ((linearModulusFamily ringEta keySwitchEta inputEta encode).q securityParameter) :=
  fun securityParameter ↦ ⟨by simp [linearModulusFamily]⟩

/-- The KSK dimensions of the linear-modulus witness family have explicit linear bounds. -/
noncomputable def linearModulusFamily_polynomialKeySwitchGrowth {Message : Type}
    (ringEta keySwitchEta inputEta : ℕ → ℕ)
    (encode : (securityParameter : ℕ) → Message → ZMod (securityParameter + 2)) :
    (linearModulusFamily ringEta keySwitchEta inputEta encode).PolynomialKeySwitchGrowth where
  ringRankPolynomial := 1
  degreePolynomial := Polynomial.X + 1
  keySwitchLevelsPolynomial := Polynomial.X + 2
  ringRank_le := by
    intro securityParameter
    simp [linearModulusFamily]
  degree_le := by
    intro securityParameter
    simp [linearModulusFamily]
  keySwitchLevels_le := by
    intro securityParameter
    simp [linearModulusFamily]

/-- Every BRK and KSK dimension of the linear-modulus witness family has an explicit linear
bound, so polynomially amplified sampler gaps remain negligible. -/
noncomputable def linearModulusFamily_polynomialEvaluationKeyGrowth {Message : Type}
    (ringEta keySwitchEta inputEta : ℕ → ℕ)
    (encode : (securityParameter : ℕ) → Message → ZMod (securityParameter + 2)) :
    (linearModulusFamily ringEta keySwitchEta inputEta encode).PolynomialEvaluationKeyGrowth where
  toPolynomialKeySwitchGrowth :=
    linearModulusFamily_polynomialKeySwitchGrowth ringEta keySwitchEta inputEta encode
  tgswLevelsPolynomial := Polynomial.X + 2
  lweDimensionPolynomial := Polynomial.X + 1
  tgswLevels_le := by
    intro securityParameter
    simp [linearModulusFamily]
  lweDimension_le := by
    intro securityParameter
    simp [linearModulusFamily]

end FormalProof4FHE.TFHE.CenteredBinomial
