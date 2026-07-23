/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteViewSideLWEFlatten
import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteViewNativeCircular
import FormalProof4FHE.TFHE.AsymptoticAuxiliaryInputCircularLWE
import FormalProof4FHE.TFHE.AsymptoticKeySwitchFirstUniversalFiniteView

/-!
# Adaptive TFHE Security from BRK Circularity and Scalar Search LWE

This module replaces the earlier universal full-transcript circular premise by two separated
assumptions matching the native TFHE key material:

1. same-secret polynomial-view circular pseudorandomness for the bootstrapping keys only; and
2. conventional heterogeneous two-block scalar search LWE for all KSK and input-tape rows, with
   an ordinary combined-batch specialization when their error laws coincide.

The finite compilation preserves the hidden scalar key through the final search check.  The
asymptotic theorem composes the two negligible terms with the existing logarithmic majority
schedule and ordinary post-cut LWE bounds.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView

open FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

/-! ## BRK-only circular families -/

/-- Parameter-indexed recovery computations used in the BRK-only circular replacement game. -/
structure BootstrapBatchCircularAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    Solver
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter)
      (queryCount securityParameter)
      (schedule.rounds securityParameter)

/-- Security game replacing only the same-secret batch of real BRKs by independent uniform
BRKs; real KSK and input-tape side information is retained on both branches. -/
noncomputable def bootstrapBatchCircularSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) :
    SecurityGame (BootstrapBatchCircularAdversaryFamily params schedule) where
  advantage adversary securityParameter :=
    ENNReal.ofReal
      (bootstrapBatchCircularAdvantage
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (schedule.rounds securityParameter)
        (adversary.run securityParameter))

/-- Use an augmented scalar-search solver as the recovery computation in the BRK replacement
game. -/
def bootstrapBatchCircularReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (solver : SearchAdversaryFamily params schedule) :
    BootstrapBatchCircularAdversaryFamily params schedule where
  queryCount := solver.queryCount
  queryPolynomial := solver.queryPolynomial
  queryCount_le := solver.queryCount_le
  run := solver.run

/-! ## Conventional scalar search-LWE families -/

/-- Parameter-indexed conventional two-block search-LWE adversaries.  The first combined block
contains every KSK row and the second every input-tape row in the scheduled augmented views. -/
structure FlatSideSearchLWEAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    LearningWithErrors.SearchAdversary
      (flatSideLweProblem
        (q := params.q securityParameter)
        (ringRank := params.ringRank securityParameter)
        (degree := params.degree securityParameter)
        (lweDimension := params.lweDimension securityParameter)
        (keySwitchLevels := params.keySwitchLevels securityParameter)
        (queryCount := queryCount securityParameter)
        (rounds := schedule.rounds securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter))

/-- Security game for the flattened scalar search-LWE endpoint. -/
noncomputable def flatSideSearchLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) :
    SecurityGame (FlatSideSearchLWEAdversaryFamily params schedule) where
  advantage adversary securityParameter :=
    Pr[= true | LearningWithErrors.searchExperiment
      (flatSideLweProblem
        (q := params.q securityParameter)
        (ringRank := params.ringRank securityParameter)
        (degree := params.degree securityParameter)
        (lweDimension := params.lweDimension securityParameter)
        (keySwitchLevels := params.keySwitchLevels securityParameter)
        (queryCount := adversary.queryCount securityParameter)
        (rounds := schedule.rounds securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter))
      (adversary.run securityParameter)]

/-- Compile an augmented solver into the conventional two-block scalar search-LWE adversary. -/
noncomputable def flatSideSearchLWEReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (solver : SearchAdversaryFamily params schedule) :
    FlatSideSearchLWEAdversaryFamily params schedule where
  queryCount := solver.queryCount
  queryPolynomial := solver.queryPolynomial
  queryCount_le := solver.queryCount_le
  run securityParameter :=
    flatSideLweSearchReduction
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.keySwitchGadget securityParameter)
      (solver.run securityParameter)

/-! ## Equal-noise ordinary scalar search-LWE families -/

/-- Parameter-indexed ordinary combined-batch scalar search-LWE adversaries.  This is the
equal-noise specialization of the two-block family above: every retained KSK and input-tape row
is concatenated into one conventional matrix-LWE transcript. -/
structure OrdinarySideSearchLWEAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    LearningWithErrors.SearchAdversary
      (ordinarySideLweProblem
        (q := params.q securityParameter)
        (ringRank := params.ringRank securityParameter)
        (degree := params.degree securityParameter)
        (lweDimension := params.lweDimension securityParameter)
        (keySwitchLevels := params.keySwitchLevels securityParameter)
        (queryCount := queryCount securityParameter)
        (rounds := schedule.rounds securityParameter)
        (params.keySwitchErrorSampler securityParameter))

/-- Security game for the ordinary equal-noise combined scalar search-LWE endpoint. -/
noncomputable def ordinarySideSearchLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) :
    SecurityGame (OrdinarySideSearchLWEAdversaryFamily params schedule) where
  advantage adversary securityParameter :=
    Pr[= true | LearningWithErrors.searchExperiment
      (ordinarySideLweProblem
        (q := params.q securityParameter)
        (ringRank := params.ringRank securityParameter)
        (degree := params.degree securityParameter)
        (lweDimension := params.lweDimension securityParameter)
        (keySwitchLevels := params.keySwitchLevels securityParameter)
        (queryCount := adversary.queryCount securityParameter)
        (rounds := schedule.rounds securityParameter)
        (params.keySwitchErrorSampler securityParameter))
      (adversary.run securityParameter)]

/-- Compile an augmented recovery solver into the one ordinary combined-batch scalar search-LWE
adversary used when KSK and input errors have the same law. -/
noncomputable def ordinarySideSearchLWEReduction {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (solver : SearchAdversaryFamily params schedule) :
    OrdinarySideSearchLWEAdversaryFamily params schedule where
  queryCount := solver.queryCount
  queryPolynomial := solver.queryPolynomial
  queryCount_le := solver.queryCount_le
  run securityParameter :=
    ordinarySideLweSearchReduction
      (params.keySwitchErrorSampler securityParameter)
      (params.keySwitchGadget securityParameter)
      (solver.run securityParameter)

/-! ## Search security from the separated assumptions -/

/-- Pointwise augmented recovery is bounded by BRK-only circular advantage plus conventional
scalar two-block search-LWE success. -/
theorem searchSecurityGame_advantage_le_bootstrapCircular_add_flatSearchLwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (solver : SearchAdversaryFamily params schedule)
    (securityParameter : ℕ) :
    (searchSecurityGame params schedule).advantage solver securityParameter ≤
      (bootstrapBatchCircularSecurityGame params schedule).advantage
          (bootstrapBatchCircularReduction params schedule solver) securityParameter +
        (flatSideSearchLWESecurityGame params schedule).advantage
          (flatSideSearchLWEReduction params schedule solver) securityParameter := by
  simpa [searchSecurityGame, bootstrapBatchCircularSecurityGame,
    bootstrapBatchCircularReduction, flatSideSearchLWESecurityGame,
    flatSideSearchLWEReduction] using
    (successProbability_le_bootstrapBatchCircular_add_flatSearchLwe
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      (solver.run securityParameter))

/-- Pointwise equal-noise specialization: augmented recovery is bounded by the BRK circular term
plus one ordinary combined-batch scalar search-LWE success probability. -/
theorem searchSecurityGame_advantage_le_bootstrapCircular_add_ordinarySearchLwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (hScalarError : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (solver : SearchAdversaryFamily params schedule)
    (securityParameter : ℕ) :
    (searchSecurityGame params schedule).advantage solver securityParameter ≤
      (bootstrapBatchCircularSecurityGame params schedule).advantage
          (bootstrapBatchCircularReduction params schedule solver) securityParameter +
        (ordinarySideSearchLWESecurityGame params schedule).advantage
          (ordinarySideSearchLWEReduction params schedule solver) securityParameter := by
  simp only [searchSecurityGame, bootstrapBatchCircularSecurityGame,
    bootstrapBatchCircularReduction, ordinarySideSearchLWESecurityGame,
    ordinarySideSearchLWEReduction]
  rw [hScalarError securityParameter]
  exact
    (successProbability_le_bootstrapBatchCircular_add_ordinarySearchLwe
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      (solver.run securityParameter))

/-- BRK-only circular security together with conventional scalar search-LWE security implies
finite augmented-search security for a fixed polynomial-view schedule. -/
theorem searchSecurityGame_secureAgainst_of_bootstrapCircular_and_flatSearchLwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (searchIsPPT : SearchAdversaryFamily params schedule → Prop)
    (circularIsPPT : BootstrapBatchCircularAdversaryFamily params schedule → Prop)
    (flatSearchIsPPT : FlatSideSearchLWEAdversaryFamily params schedule → Prop)
    (hCircularClosed : ∀ solver, searchIsPPT solver →
      circularIsPPT (bootstrapBatchCircularReduction params schedule solver))
    (hFlatSearchClosed : ∀ solver, searchIsPPT solver →
      flatSearchIsPPT (flatSideSearchLWEReduction params schedule solver))
    (hCircular :
      (bootstrapBatchCircularSecurityGame params schedule).secureAgainst circularIsPPT)
    (hFlatSearch :
      (flatSideSearchLWESecurityGame params schedule).secureAgainst flatSearchIsPPT) :
    (searchSecurityGame params schedule).secureAgainst searchIsPPT := by
  intro solver hsolver
  exact negligible_of_le
    (fun securityParameter ↦
      searchSecurityGame_advantage_le_bootstrapCircular_add_flatSearchLwe
        params schedule solver securityParameter)
    (negligible_add
      (hCircular (bootstrapBatchCircularReduction params schedule solver)
        (hCircularClosed solver hsolver))
      (hFlatSearch (flatSideSearchLWEReduction params schedule solver)
        (hFlatSearchClosed solver hsolver)))

/-- For a fixed schedule and equal scalar noises, BRK-batch circular security together with one
ordinary combined-batch scalar search-LWE game implies finite augmented-search security. -/
theorem searchSecurityGame_secureAgainst_of_bootstrapCircular_and_ordinarySearchLwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (hScalarError : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (searchIsPPT : SearchAdversaryFamily params schedule → Prop)
    (circularIsPPT : BootstrapBatchCircularAdversaryFamily params schedule → Prop)
    (ordinarySearchIsPPT : OrdinarySideSearchLWEAdversaryFamily params schedule → Prop)
    (hCircularClosed : ∀ solver, searchIsPPT solver →
      circularIsPPT (bootstrapBatchCircularReduction params schedule solver))
    (hOrdinarySearchClosed : ∀ solver, searchIsPPT solver →
      ordinarySearchIsPPT (ordinarySideSearchLWEReduction params schedule solver))
    (hCircular :
      (bootstrapBatchCircularSecurityGame params schedule).secureAgainst circularIsPPT)
    (hOrdinarySearch :
      (ordinarySideSearchLWESecurityGame params schedule).secureAgainst
        ordinarySearchIsPPT) :
    (searchSecurityGame params schedule).secureAgainst searchIsPPT := by
  intro solver hsolver
  exact negligible_of_le
    (fun securityParameter ↦
      searchSecurityGame_advantage_le_bootstrapCircular_add_ordinarySearchLwe
        params schedule hScalarError solver securityParameter)
    (negligible_add
      (hCircular (bootstrapBatchCircularReduction params schedule solver)
        (hCircularClosed solver hsolver))
      (hOrdinarySearch (ordinarySideSearchLWEReduction params schedule solver)
        (hOrdinarySearchClosed solver hsolver)))

/-! ## Universal-schedule adaptive TFHE composition -/

abbrev UniversalBootstrapBatchCircularIsPPT {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :=
  (schedule : PolynomialViewSchedule params) →
    BootstrapBatchCircularAdversaryFamily params schedule → Prop

abbrev UniversalFlatSideSearchLWEIsPPT {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :=
  (schedule : PolynomialViewSchedule params) →
    FlatSideSearchLWEAdversaryFamily params schedule → Prop

/-- Universal admissibility predicate for the equal-noise ordinary combined-batch scalar
search-LWE endpoint. -/
abbrev UniversalOrdinarySideSearchLWEIsPPT {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :=
  (schedule : PolynomialViewSchedule params) →
    OrdinarySideSearchLWEAdversaryFamily params schedule → Prop

/-- **Adaptive TFHE security from BRK circularity, conventional scalar search LWE, and the
existing post-cut LWE assumptions.**  A separate polynomial logarithmic view schedule is selected
for every negligibility exponent by the universal finite-view composition theorem. -/
theorem secureAgainst_of_universal_bootstrapCircular_flatSearchLwe_and_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimensionUpper : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (circularIsPPT : UniversalBootstrapBatchCircularIsPPT params)
    (flatSearchIsPPT : UniversalFlatSideSearchLWEIsPPT params)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily params → Prop)
    (hCircularClosed : ∀ schedule adversary, isPPT adversary →
      circularIsPPT schedule
        (bootstrapBatchCircularReduction params schedule
          (searchReduction params schedule adversary)))
    (hFlatSearchClosed : ∀ schedule adversary, isPPT adversary →
      flatSearchIsPPT schedule
        (flatSideSearchLWEReduction params schedule
          (searchReduction params schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction params adversary))
    (hCircular : ∀ schedule,
      (bootstrapBatchCircularSecurityGame params schedule).secureAgainst
        (circularIsPPT schedule))
    (hFlatSearch : ∀ schedule,
      (flatSideSearchLWESecurityGame params schedule).secureAgainst
        (flatSearchIsPPT schedule))
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame params).secureAgainst inputBatchIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  let searchIsPPT : UniversalSearchIsPPT params := fun schedule solver ↦
    circularIsPPT schedule
        (bootstrapBatchCircularReduction params schedule solver) ∧
      flatSearchIsPPT schedule
        (flatSideSearchLWEReduction params schedule solver)
  apply secureAgainst_of_universal_finiteSearch_and_lwe
    params hError reference dimensionPolynomial hDimensionUpper isPPT searchIsPPT
    realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT
  · intro schedule adversary hadversary
    exact ⟨hCircularClosed schedule adversary hadversary,
      hFlatSearchClosed schedule adversary hadversary⟩
  · exact hRealRingBatchClosed
  · exact hZeroRingBatchClosed
  · exact hInputBatchClosed
  · intro schedule
    exact searchSecurityGame_secureAgainst_of_bootstrapCircular_and_flatSearchLwe
      params schedule (searchIsPPT schedule)
      (circularIsPPT schedule) (flatSearchIsPPT schedule)
      (fun _ h ↦ h.1) (fun _ h ↦ h.2)
      (hCircular schedule) (hFlatSearch schedule)
  · exact hRealRingBatch
  · exact hZeroRingBatch
  · exact hInputBatch

/-! ## Discharging the multi-view BRK premise by native one-challenge CircLWE -/

/-- Compile a polynomial-view BRK-batch distinguisher into one native auxiliary-input CircLWE
continuation at every security parameter.  The schedule's reference coordinate certifies that
the scalar dimension, and hence the exact batch size, is nonzero. -/
noncomputable def nativeCircularBatchReductionFamily {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (adversary : BootstrapBatchCircularAdversaryFamily params schedule) :
    ContinuationFamily params :=
  fun securityParameter ↦ by
    have hDimensionPos : 0 < params.lweDimension securityParameter := by
      exact lt_of_le_of_lt (Nat.zero_le _) (schedule.reference securityParameter).isLt
    letI : NeZero (params.lweDimension securityParameter) :=
      ⟨Nat.ne_of_gt hDimensionPos⟩
    exact
      FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView.nativeCircularBatchReduction
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (schedule.rounds securityParameter)
        (adversary.run securityParameter)

/-- Pointwise exact identity between the scheduled BRK-batch game and one native CircLWE call,
including the explicit number of stored majority-tree leaves. -/
theorem bootstrapBatchCircularSecurityGame_advantage_eq_viewCount_mul_nativeCircularLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (adversary : BootstrapBatchCircularAdversaryFamily params schedule)
    (securityParameter : ℕ) :
    (bootstrapBatchCircularSecurityGame params schedule).advantage
        adversary securityParameter =
      (viewCount (params.lweDimension securityParameter)
          (schedule.rounds securityParameter) : ENNReal) *
        (MonomialKDM.AuxiliaryInput.circularLWESecurityGame params).advantage
          (nativeCircularBatchReductionFamily params schedule adversary)
          securityParameter := by
  have hDimensionPos : 0 < params.lweDimension securityParameter := by
    exact lt_of_le_of_lt (Nat.zero_le _) (schedule.reference securityParameter).isLt
  letI : NeZero (params.lweDimension securityParameter) :=
    ⟨Nat.ne_of_gt hDimensionPos⟩
  change ENNReal.ofReal
      (bootstrapBatchCircularAdvantage
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (schedule.rounds securityParameter)
        (adversary.run securityParameter)) =
    (viewCount (params.lweDimension securityParameter)
        (schedule.rounds securityParameter) : ENNReal) *
      ENNReal.ofReal
        (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.circularLweAdvantage
          (params.ringErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.tgswGadget securityParameter)
          (params.keySwitchGadget securityParameter)
          ((nativeCircularBatchReductionFamily params schedule adversary)
            securityParameter))
  rw [FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView.bootstrapBatchCircularAdvantage_eq_viewCount_mul_nativeCircularLwe]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  simp [nativeCircularBatchReductionFamily]

/-- The scheduled batch advantage is bounded by the schedule polynomial times the corresponding
native one-challenge CircLWE advantage. -/
theorem bootstrapBatchCircularSecurityGame_advantage_le_viewPolynomial_mul_nativeCircularLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (adversary : BootstrapBatchCircularAdversaryFamily params schedule)
    (securityParameter : ℕ) :
    (bootstrapBatchCircularSecurityGame params schedule).advantage
        adversary securityParameter ≤
      ((schedule.viewPolynomial.eval securityParameter : ℕ) : ENNReal) *
        (MonomialKDM.AuxiliaryInput.circularLWESecurityGame params).advantage
          (nativeCircularBatchReductionFamily params schedule adversary)
          securityParameter := by
  rw [bootstrapBatchCircularSecurityGame_advantage_eq_viewCount_mul_nativeCircularLWE]
  gcongr
  exact_mod_cast schedule.viewCount_le securityParameter

/-- **Pointwise adaptive TFHE reduction to one native circular challenge.**

For any fixed polynomial-view schedule and admissible amplification threshold, the honest
adaptive TFHE advantage is bounded by the exact number of scheduled BRK views times one native
auxiliary-input CircLWE advantage, one ordinary combined scalar search-LWE success probability,
the explicit finite-view amplification loss, the two post-cut ring-LWE advantages, and the
adaptive input-LWE advantage.  No negligibility hypothesis is used in this quantitative theorem.
-/
theorem
    securityGame_advantage_le_nativeCircular_add_ordinarySearchLwe_add_finiteLoss_add_postCut
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (hScalarError : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (schedule : PolynomialViewSchedule params)
    (threshold : ThresholdFamily params)
    (hthreshold_pos : ∀ adversary securityParameter,
      0 < threshold adversary securityParameter)
    (hthreshold_one : ∀ adversary securityParameter,
      threshold adversary securityParameter ≤ 1)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      (viewCount (params.lweDimension securityParameter)
          (schedule.rounds securityParameter) : ENNReal) *
        (MonomialKDM.AuxiliaryInput.circularLWESecurityGame params).advantage
          (nativeCircularBatchReductionFamily params schedule
            (bootstrapBatchCircularReduction params schedule
              (searchReduction params schedule adversary))) securityParameter +
      (ordinarySideSearchLWESecurityGame params schedule).advantage
        (ordinarySideSearchLWEReduction params schedule
          (searchReduction params schedule adversary)) securityParameter +
      (lossSecurityGame params schedule threshold).advantage
        adversary securityParameter +
      (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
        (realRingBatchReduction params adversary) securityParameter +
      (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
        (zeroRingBatchReduction params adversary) securityParameter +
      (inputBatchLWESecurityGame params).advantage
        (inputBatchLWEReduction params adversary) securityParameter := by
  have hMain :=
    securityGame_advantage_le_finiteSearch_add_loss_add_two_ringBatchLWE_add_inputLWE
      params hError schedule threshold hthreshold_pos hthreshold_one adversary
        securityParameter
  have hSearch :=
    searchSecurityGame_advantage_le_bootstrapCircular_add_ordinarySearchLwe
      params schedule hScalarError (searchReduction params schedule adversary)
        securityParameter
  calc
    (securityGame params).advantage adversary securityParameter ≤
        (searchSecurityGame params schedule).advantage
              (searchReduction params schedule adversary) securityParameter +
            (lossSecurityGame params schedule threshold).advantage
              adversary securityParameter +
            (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
              (realRingBatchReduction params adversary) securityParameter +
            (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
              (zeroRingBatchReduction params adversary) securityParameter +
            (inputBatchLWESecurityGame params).advantage
              (inputBatchLWEReduction params adversary) securityParameter := hMain
    _ ≤ ((bootstrapBatchCircularSecurityGame params schedule).advantage
              (bootstrapBatchCircularReduction params schedule
                (searchReduction params schedule adversary)) securityParameter +
            (ordinarySideSearchLWESecurityGame params schedule).advantage
              (ordinarySideSearchLWEReduction params schedule
                (searchReduction params schedule adversary)) securityParameter) +
            (lossSecurityGame params schedule threshold).advantage
              adversary securityParameter +
            (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
              (realRingBatchReduction params adversary) securityParameter +
            (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
              (zeroRingBatchReduction params adversary) securityParameter +
            (inputBatchLWESecurityGame params).advantage
              (inputBatchLWEReduction params adversary) securityParameter := by
      gcongr
    _ = _ := by
      rw [bootstrapBatchCircularSecurityGame_advantage_eq_viewCount_mul_nativeCircularLWE]

/-- Native one-challenge auxiliary-input CircLWE security implies security of the complete
same-secret polynomial BRK batch.  Polynomial view growth is absorbed by negligibility. -/
theorem bootstrapBatchCircularSecurityGame_secureAgainst_of_nativeCircularLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (batchIsPPT : BootstrapBatchCircularAdversaryFamily params schedule → Prop)
    (nativeIsPPT : ContinuationFamily params → Prop)
    (hClosed : ∀ adversary, batchIsPPT adversary →
      nativeIsPPT (nativeCircularBatchReductionFamily params schedule adversary))
    (hNative :
      (MonomialKDM.AuxiliaryInput.circularLWESecurityGame params).secureAgainst
        nativeIsPPT) :
    (bootstrapBatchCircularSecurityGame params schedule).secureAgainst batchIsPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (bootstrapBatchCircularSecurityGame_advantage_le_viewPolynomial_mul_nativeCircularLWE
      params schedule adversary)
    (negligible_polynomial_mul
      (hNative (nativeCircularBatchReductionFamily params schedule adversary)
        (hClosed adversary hadversary))
      schedule.viewPolynomial)

/-- **Adaptive TFHE security from the existing native one-challenge auxiliary-input CircLWE
assumption.**  The formerly separate same-secret multi-view BRK premise is discharged by the
exact randomized hybrid above.  The remaining non-circular terms are conventional scalar search
LWE and the existing post-cut ring/scalar LWE games. -/
theorem secureAgainst_of_universal_nativeCircular_flatSearchLwe_and_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimensionUpper : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (nativeCircularIsPPT : ContinuationFamily params → Prop)
    (flatSearchIsPPT : UniversalFlatSideSearchLWEIsPPT params)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily params → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily params schedule
          (bootstrapBatchCircularReduction params schedule
            (searchReduction params schedule adversary))))
    (hFlatSearchClosed : ∀ schedule adversary, isPPT adversary →
      flatSearchIsPPT schedule
        (flatSideSearchLWEReduction params schedule
          (searchReduction params schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction params adversary))
    (hNativeCircular :
      (MonomialKDM.AuxiliaryInput.circularLWESecurityGame params).secureAgainst
        nativeCircularIsPPT)
    (hFlatSearch : ∀ schedule,
      (flatSideSearchLWESecurityGame params schedule).secureAgainst
        (flatSearchIsPPT schedule))
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame params).secureAgainst inputBatchIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  let circularIsPPT : UniversalBootstrapBatchCircularIsPPT params :=
    fun schedule adversary ↦
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily params schedule adversary)
  apply secureAgainst_of_universal_bootstrapCircular_flatSearchLwe_and_lwe
    params hError reference dimensionPolynomial hDimensionUpper isPPT
    circularIsPPT flatSearchIsPPT realRingBatchIsPPT zeroRingBatchIsPPT
    inputBatchIsPPT
  · intro schedule adversary hadversary
    exact hNativeCircularClosed schedule adversary hadversary
  · exact hFlatSearchClosed
  · exact hRealRingBatchClosed
  · exact hZeroRingBatchClosed
  · exact hInputBatchClosed
  · intro schedule
    exact bootstrapBatchCircularSecurityGame_secureAgainst_of_nativeCircularLWE
      params schedule (circularIsPPT schedule) nativeCircularIsPPT
      (fun _ h ↦ h) hNativeCircular
  · exact hFlatSearch
  · exact hRealRingBatch
  · exact hZeroRingBatch
  · exact hInputBatch

/-- **Adaptive TFHE security from native one-challenge auxiliary-input CircLWE and one ordinary
combined-batch scalar search-LWE assumption.**

When KSK and input-tape errors have the same law, their retained rows are concatenated exactly
into a conventional matrix-LWE transcript.  The polynomial same-secret BRK batch is reduced to
one native CircLWE challenge by the exact randomized hybrid; the remaining terms are the existing
post-cut ring/scalar LWE games. -/
theorem secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (hScalarError : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimensionUpper : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (nativeCircularIsPPT : ContinuationFamily params → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT params)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily params → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily params schedule
          (bootstrapBatchCircularReduction params schedule
            (searchReduction params schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction params schedule
          (searchReduction params schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction params adversary))
    (hNativeCircular :
      (MonomialKDM.AuxiliaryInput.circularLWESecurityGame params).secureAgainst
        nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame params schedule).secureAgainst
        (ordinarySearchIsPPT schedule))
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame params).secureAgainst inputBatchIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  let circularIsPPT : UniversalBootstrapBatchCircularIsPPT params :=
    fun schedule adversary ↦
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily params schedule adversary)
  let searchIsPPT : UniversalSearchIsPPT params := fun schedule solver ↦
    circularIsPPT schedule
        (bootstrapBatchCircularReduction params schedule solver) ∧
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction params schedule solver)
  apply secureAgainst_of_universal_finiteSearch_and_lwe
    params hError reference dimensionPolynomial hDimensionUpper isPPT searchIsPPT
    realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT
  · intro schedule adversary hadversary
    exact ⟨hNativeCircularClosed schedule adversary hadversary,
      hOrdinarySearchClosed schedule adversary hadversary⟩
  · exact hRealRingBatchClosed
  · exact hZeroRingBatchClosed
  · exact hInputBatchClosed
  · intro schedule
    exact searchSecurityGame_secureAgainst_of_bootstrapCircular_and_ordinarySearchLwe
      params schedule hScalarError (searchIsPPT schedule)
      (circularIsPPT schedule) (ordinarySearchIsPPT schedule)
      (fun _ h ↦ h.1) (fun _ h ↦ h.2)
      (bootstrapBatchCircularSecurityGame_secureAgainst_of_nativeCircularLWE
        params schedule (circularIsPPT schedule) nativeCircularIsPPT
        (fun _ h ↦ h) hNativeCircular)
      (hOrdinarySearch schedule)
  · exact hRealRingBatch
  · exact hZeroRingBatch
  · exact hInputBatch

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView
