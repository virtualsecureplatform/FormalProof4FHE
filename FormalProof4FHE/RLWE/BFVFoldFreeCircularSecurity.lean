/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BFVCircularSecurityCorrected
import FormalProof4FHE.RLWE.RNSSplitSearchToDecisionCorrelated

/-!
# Fold-free conditional framework for stock BFV circular security

This file formalizes the sound algebraic and quantitative core of
`sketch/BFVStandardAssumptionCircularSecurity_Corrected.tex`.

The existing BFV modules already provide the adjacent normal form, point-mass-preserving source
equivalence, corrected general-distribution/HNF interface, and exact split-RNS candidate test with
arbitrary coherent side information.  This file adds the new fold-free components:

* the manuscript's direct one-slot candidate randomization and exact wrong-candidate bijection;
* shared-pivot elimination and recovery over arbitrary modules;
* exact uniformity of a derived mask coordinate after an invertible public row transform;
* a bijective grouped correlated-error compiler; and
* proof-carrying interfaces for M-SIS absorption and the resulting conditional bound.

No unconditional standard-assumption theorem is asserted.  Applicability of the published
general-distribution theorem, shared-context amplification, automorphism transport, pivot abort
accounting, and the exact M-SIS matrix interface remain explicit certificate obligations.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurity

noncomputable section

namespace BFV

export FormalProof4FHE.RLWE.BFVQuadraticCircularSecurity (Batch)

end BFV

namespace Standard

export FormalProof4FHE.RLWE.BFVStandardAssumptionCircularSecurity
  (gammaCorrelatedError gammaSourceEquiv)

end Standard

/-! ## Direct CRT-slot candidate randomization -/

/-- Fixed-error affine HNF row at one split-field coordinate. -/
def coordinateRow {K : Type} [CommRing K]
    (secret error coefficient : K) : K × K :=
  (coefficient, coefficient * secret + error)

/-- Add fresh field randomness to the public coefficient and candidate times the same randomness
to the body. -/
def candidateRandomize {K : Type} [Add K] [Mul K]
    (candidate randomizer : K) (row : K × K) : K × K :=
  (row.1 + randomizer, row.2 + randomizer * candidate)

/-- A correct candidate preserves the exact fixed error. -/
theorem candidateRandomize_correct
    {K : Type} [CommRing K]
    (secret error coefficient randomizer : K) :
    candidateRandomize secret randomizer (coordinateRow secret error coefficient) =
      coordinateRow secret error (coefficient + randomizer) := by
  apply Prod.ext
  · rfl
  · simp [candidateRandomize, coordinateRow]
    ring

/-- Complete coin-to-output map for a wrong candidate, conditioned on the secret and error. -/
def candidateCoinMap {K : Type} [CommRing K]
    (secret candidate error : K) (coins : K × K) : K × K :=
  candidateRandomize candidate coins.2 (coordinateRow secret error coins.1)

/-- Explicit inverse of the candidate coin map. -/
def candidateCoinMapInv {K : Type} [Field K]
    (secret candidate error : K) (output : K × K) : K × K :=
  let randomizer := (candidate - secret)⁻¹ *
    (output.2 - output.1 * secret - error)
  (output.1 - randomizer, randomizer)

@[simp]
theorem candidateCoinMapInv_candidateCoinMap
    {K : Type} [Field K]
    (secret candidate error : K) (hWrong : candidate ≠ secret)
    (coins : K × K) :
    candidateCoinMapInv secret candidate error
        (candidateCoinMap secret candidate error coins) = coins := by
  have hDifference : candidate - secret ≠ 0 := sub_ne_zero.mpr hWrong
  rcases coins with ⟨coefficient, randomizer⟩
  apply Prod.ext
  · simp [candidateCoinMapInv, candidateCoinMap, candidateRandomize, coordinateRow]
    field_simp
    ring
  · simp [candidateCoinMapInv, candidateCoinMap, candidateRandomize, coordinateRow]
    field_simp
    ring

@[simp]
theorem candidateCoinMap_candidateCoinMapInv
    {K : Type} [Field K]
    (secret candidate error : K) (hWrong : candidate ≠ secret)
    (output : K × K) :
    candidateCoinMap secret candidate error
        (candidateCoinMapInv secret candidate error output) = output := by
  have hDifference : candidate - secret ≠ 0 := sub_ne_zero.mpr hWrong
  rcases output with ⟨coefficient, body⟩
  apply Prod.ext
  · simp [candidateCoinMapInv, candidateCoinMap, candidateRandomize, coordinateRow]
  · simp [candidateCoinMapInv, candidateCoinMap, candidateRandomize, coordinateRow]
    field_simp
    ring

/-- For a wrong candidate, the fresh `(coefficient,randomizer)` coins and the output pair are in
explicit bijection. -/
theorem candidateCoinMap_bijective
    {K : Type} [Field K]
    (secret candidate error : K) (hWrong : candidate ≠ secret) :
    Function.Bijective (candidateCoinMap secret candidate error) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨candidateCoinMapInv secret candidate error,
      candidateCoinMapInv_candidateCoinMap secret candidate error hWrong,
      candidateCoinMap_candidateCoinMapInv secret candidate error hWrong⟩

/-- Wrong-candidate randomization is exactly uniform even after conditioning on the complete
secret and error state. -/
theorem candidateCoinMap_uniform_evalDist
    {K : Type} [Field K] [Fintype K] [DecidableEq K] [SampleableType K]
    (secret candidate error : K) (hWrong : candidate ≠ secret) :
    evalDist (candidateCoinMap secret candidate error <$> ($ᵗ (K × K))) =
      evalDist ($ᵗ (K × K)) :=
  evalDist_map_bijective_uniform_cross
    (α := K × K) (β := K × K)
    (candidateCoinMap secret candidate error)
    (candidateCoinMap_bijective secret candidate error hWrong)

/-- Retain arbitrary conditioned side information alongside the direct wrong-candidate output. -/
def candidateCoinMapWithSideInfo
    {K SideInfo : Type} [CommRing K]
    (secret candidate error : K) (sideInfo : SideInfo) (coins : K × K) :
    SideInfo × (K × K) :=
  (sideInfo, candidateCoinMap secret candidate error coins)

/-- Exact wrong-candidate uniformity remains true with any fixed side information attached. -/
theorem candidateCoinMapWithSideInfo_uniform_evalDist
    {K SideInfo : Type}
    [Field K] [Fintype K] [DecidableEq K] [SampleableType K]
    (secret candidate error : K) (sideInfo : SideInfo)
    (hWrong : candidate ≠ secret) :
    evalDist (candidateCoinMapWithSideInfo secret candidate error sideInfo <$>
        ($ᵗ (K × K))) =
      evalDist ((fun output : K × K ↦ (sideInfo, output)) <$> ($ᵗ (K × K))) := by
  have hOutput := candidateCoinMap_uniform_evalDist secret candidate error hWrong
  let finish := fun output : K × K ↦
    (pure (sideInfo, output) : ProbComp (SideInfo × (K × K)))
  calc
    evalDist (candidateCoinMapWithSideInfo secret candidate error sideInfo <$>
        ($ᵗ (K × K))) =
      evalDist ((candidateCoinMap secret candidate error <$> ($ᵗ (K × K))) >>=
        finish) := by
          simp [candidateCoinMapWithSideInfo, finish, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ (K × K)) >>= finish) := by
      rw [evalDist_bind, hOutput, ← evalDist_bind]
    _ = evalDist ((fun output : K × K ↦ (sideInfo, output)) <$>
        ($ᵗ (K × K))) := by
      simp [finish, map_eq_bind_pure_comp]

/-- The conditioning statement also transports through an arbitrary joint state sampler.  The
state may contain every other CRT slot, all errors, and arbitrary leakage. -/
theorem candidateCoinMap_jointState_uniform_evalDist
    {K State : Type}
    [Field K] [Fintype K] [DecidableEq K] [SampleableType K]
    (stateSampler : ProbComp State)
    (secret candidate error : State → K)
    (hWrong : ∀ state, candidate state ≠ secret state) :
    evalDist (stateSampler >>= fun state ↦
        candidateCoinMapWithSideInfo (secret state) (candidate state) (error state) state <$>
          ($ᵗ (K × K))) =
      evalDist (stateSampler >>= fun state ↦
        (fun output : K × K ↦ (state, output)) <$> ($ᵗ (K × K))) := by
  refine evalDist_bind_congr' stateSampler fun state ↦ ?_
  exact candidateCoinMapWithSideInfo_uniform_evalDist
    (secret state) (candidate state) (error state) state (hWrong state)

/-! ## Shared-pivot algebra -/

section SharedPivot

variable {R V W : Type}
variable [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Public target-row map composed with the inverse pivot map. -/
def normalizedTargetMap
    (pivot : V ≃ₗ[R] V) (target : V →ₗ[R] W) : V →ₗ[R] W :=
  target.comp pivot.symm.toLinearMap

/-- Derived auxiliary-secret coefficient `-C u`. -/
def derivedCoefficient
    (pivot : V ≃ₗ[R] V) (target : V →ₗ[R] W) (selector : V) : W :=
  -normalizedTargetMap pivot target selector

/-- Public residual `y-Ct`. -/
def sharedPivotResidual
    (pivot : V ≃ₗ[R] V) (target : V →ₗ[R] W)
    (pivotBody : V) (targetBody : W) : W :=
  targetBody - normalizedTargetMap pivot target pivotBody

/-- Eliminating the common module secret leaves exactly a fresh BFV-style affine row in the
auxiliary secret. -/
theorem sharedPivotResidual_eq_derived
    (pivot : V ≃ₗ[R] V) (target : V →ₗ[R] W)
    (commonSecret selector : V) (auxiliarySecret : R) (error : W) :
    sharedPivotResidual pivot target
        (pivot commonSecret + auxiliarySecret • selector)
        (target commonSecret + error) =
      auxiliarySecret • derivedCoefficient pivot target selector + error := by
  simp [sharedPivotResidual, normalizedTargetMap, derivedCoefficient,
    map_add, map_smul]
  module

/-- Once the auxiliary pivot error is recovered, inversion of the public pivot recovers the
common module secret exactly. -/
theorem recoverCommonSecret
    (pivot : V ≃ₗ[R] V) (commonSecret selector : V) (auxiliarySecret : R) :
    pivot.symm
        (pivot commonSecret + auxiliarySecret • selector - auxiliarySecret • selector) =
      commonSecret := by
  simp

end SharedPivot

/-! ## Uniform derived row masks -/

/-- A public invertible row transformation followed by coordinate projection and negation. -/
def derivedMaskCoordinate
    {R Coordinate : Type} [AddGroup R]
    (rowTransform : (Coordinate → R) ≃ (Coordinate → R))
    (pivot : Coordinate) (row : Coordinate → R) : R :=
  -(rowTransform row pivot)

/-- The derived mask coordinate is exactly uniform.  This is the finite distributional content
of right multiplication by an invertible pivot matrix followed by selecting its pivot column. -/
theorem derivedMaskCoordinate_uniform_evalDist
    {R Coordinate : Type}
    [AddGroup R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (rowTransform : (Coordinate → R) ≃ (Coordinate → R))
    (pivot : Coordinate) :
    evalDist (derivedMaskCoordinate rowTransform pivot <$>
        ($ᵗ (Coordinate → R))) =
      evalDist ($ᵗ R) := by
  have hTransform :
      evalDist (rowTransform <$> ($ᵗ (Coordinate → R))) =
        evalDist ($ᵗ (Coordinate → R)) :=
    evalDist_map_bijective_uniform_cross
      (α := Coordinate → R) (β := Coordinate → R)
      rowTransform rowTransform.bijective
  have hCoordinate := FormalProof4FHE.FiniteProduct.evalDist_map_apply_uniformSample_fun
    (codomain := R) pivot
  have hNegation :
      evalDist ((fun value : R ↦ -value) <$> ($ᵗ R)) = evalDist ($ᵗ R) :=
    evalDist_map_bijective_uniform_cross
      (α := R) (β := R) (fun value : R ↦ -value)
      (Equiv.neg R).bijective
  calc
    evalDist (derivedMaskCoordinate rowTransform pivot <$>
        ($ᵗ (Coordinate → R))) =
      evalDist ((fun row : Coordinate → R ↦ -row pivot) <$>
        (rowTransform <$> ($ᵗ (Coordinate → R)))) := by
          change evalDist ((fun row : Coordinate → R ↦ -rowTransform row pivot) <$>
              ($ᵗ (Coordinate → R))) = _
          simp only [Functor.map_map]
    _ = evalDist ((fun row : Coordinate → R ↦ -row pivot) <$>
        ($ᵗ (Coordinate → R))) := by
          simpa only [evalDist_map] using congrArg
            (fun distribution ↦ (fun row : Coordinate → R ↦ -row pivot) <$> distribution)
            hTransform
    _ = evalDist ((fun value : R ↦ -value) <$>
        ((fun row : Coordinate → R ↦ row pivot) <$>
          ($ᵗ (Coordinate → R)))) := by
          simp [Functor.map_map]
    _ = evalDist ((fun value : R ↦ -value) <$> ($ᵗ R)) := by
          simpa only [evalDist_map] using congrArg
            (fun distribution ↦ (fun value : R ↦ -value) <$> distribution)
            hCoordinate
    _ = evalDist ($ᵗ R) := hNegation

/-! ## Grouped correlated-error source -/

section GroupedSource

variable {R Group Block Padding : Type}
variable [CommRing R]

/-- Compile independently indexed ordinary BFV errors into the complete grouped correlated-error
source used by the shared-pivot construction.  Auxiliary secrets and optional padding remain
visible coordinates; only each block's error vector is changed. -/
def groupedCorrelatedSource
    (levels : ℕ) (radix gamma : R)
    (source :
      (Group → R) × ((Group → Block → BFV.Batch R levels) × Padding)) :
    (Group → R) × ((Group → Block → BFV.Batch R levels) × Padding) :=
  (source.1,
    ((fun group block ↦
      Standard.gammaCorrelatedError levels radix gamma
        (source.1 group) (source.2.1 group block)), source.2.2))

/-- The grouped source compiler is an equivalence.  This is stronger than a bare entropy lower
bound: it records an explicit inverse simultaneously for every group and block. -/
def groupedCorrelatedSourceEquiv
    (levels : ℕ) (radix gamma : R) :
    ((Group → R) × ((Group → Block → BFV.Batch R levels) × Padding)) ≃
      ((Group → R) × ((Group → Block → BFV.Batch R levels) × Padding)) where
  toFun := groupedCorrelatedSource levels radix gamma
  invFun output :=
    (output.1,
      ((fun group block ↦
        ((Standard.gammaSourceEquiv levels radix gamma).symm
          (output.1 group, output.2.1 group block)).2), output.2.2))
  left_inv source := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext group block
        exact congrArg Prod.snd
          ((Standard.gammaSourceEquiv levels radix gamma).symm_apply_apply
            (source.1 group, source.2.1 group block))
      · rfl
  right_inv output := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext group block
        exact congrArg Prod.snd
          ((Standard.gammaSourceEquiv levels radix gamma).apply_symm_apply
            (output.1 group, output.2.1 group block))
      · rfl

@[simp]
theorem groupedCorrelatedSourceEquiv_apply
    (levels : ℕ) (radix gamma : R)
    (source :
      (Group → R) × ((Group → Block → BFV.Batch R levels) × Padding)) :
    groupedCorrelatedSourceEquiv levels radix gamma source =
      groupedCorrelatedSource levels radix gamma source :=
  rfl

/-- Every grouped correlated source point has exactly the probability of its unique ordinary
source preimage.  In particular, the compiler introduces no statistical or min-entropy loss. -/
theorem groupedCorrelatedSource_probOutput
    (levels : ℕ) (radix gamma : R)
    (sourceSampler : ProbComp
      ((Group → R) × ((Group → Block → BFV.Batch R levels) × Padding)))
    (source :
      (Group → R) × ((Group → Block → BFV.Batch R levels) × Padding)) :
    Pr[= groupedCorrelatedSourceEquiv levels radix gamma source |
        groupedCorrelatedSourceEquiv levels radix gamma <$> sourceSampler] =
      Pr[= source | sourceSampler] := by
  exact probOutput_map_injective sourceSampler
    (groupedCorrelatedSourceEquiv levels radix gamma).injective source

end GroupedSource

/-! ## Compatible dual absorption -/

/-- Quantitative output of an imported general-distribution search-to-decision theorem.  The
coefficients are kept explicit because the manuscript's absorption step changes the coefficient
of decisional M-LWE; it does not make the M-SIS term disappear at unit cost. -/
structure WeightedGeneralDistributionReduction where
  searchBound : ℝ
  decisionMLWEBound : ℝ
  moduleSISBound : ℝ
  statisticalLoss : ℝ
  decisionCoefficient : ℝ
  moduleSISCoefficient : ℝ
  search_nonneg : 0 ≤ searchBound
  decisionMLWE_nonneg : 0 ≤ decisionMLWEBound
  moduleSIS_nonneg : 0 ≤ moduleSISBound
  statisticalLoss_nonneg : 0 ≤ statisticalLoss
  decisionCoefficient_nonneg : 0 ≤ decisionCoefficient
  moduleSISCoefficient_nonneg : 0 ≤ moduleSISCoefficient
  reduces :
    searchBound ≤
      decisionCoefficient * decisionMLWEBound +
        moduleSISCoefficient * moduleSISBound + statisticalLoss

/-- Conditional acceptance gap of the short-kernel dual test.  In the manuscript,
`uniformWindowMass` is the cardinality of the centered interval divided by the field modulus. -/
def dualTestGap (tailLoss uniformWindowMass : ℝ) : ℝ :=
  1 - tailLoss - uniformWindowMass

/-- Exact probability arithmetic behind the dual test.  The hypotheses deliberately expose the
two cryptographic obligations: a lower bound in the real branch and an upper bound in the
uniform branch, both conditional on solver success. -/
theorem dualTest_success_mul_gap_le_difference
    (successProbability tailLoss uniformWindowMass
      realAcceptProbability uniformAcceptProbability : ℝ)
    (hReal :
      successProbability * (1 - tailLoss) ≤ realAcceptProbability)
    (hUniform :
      uniformAcceptProbability ≤
        successProbability * uniformWindowMass) :
    successProbability * dualTestGap tailLoss uniformWindowMass ≤
      realAcceptProbability - uniformAcceptProbability := by
  dsimp [dualTestGap]
  nlinarith

/-- The same dual-test lower bound in the usual absolute distinguishing-advantage form. -/
theorem dualTest_success_mul_gap_le_absAdvantage
    (successProbability tailLoss uniformWindowMass
      realAcceptProbability uniformAcceptProbability : ℝ)
    (hReal :
      successProbability * (1 - tailLoss) ≤ realAcceptProbability)
    (hUniform :
      uniformAcceptProbability ≤
        successProbability * uniformWindowMass) :
    successProbability * dualTestGap tailLoss uniformWindowMass ≤
      |realAcceptProbability - uniformAcceptProbability| := by
  exact (dualTest_success_mul_gap_le_difference successProbability tailLoss
    uniformWindowMass realAcceptProbability uniformAcceptProbability hReal hUniform).trans
      (le_abs_self (realAcceptProbability - uniformAcceptProbability))

/-- A positive dual gap turns the lower bound `MSIS · gap ≤ dMLWE` into the advertised division
bound.  The premise is exactly where matrix-distribution and norm compatibility must be proved. -/
theorem moduleSISBound_le_decisionMLWEBound_div
    (moduleSISBound decisionMLWEBound gap : ℝ)
    (hGap : 0 < gap)
    (hCompatibleDualTest : moduleSISBound * gap ≤ decisionMLWEBound) :
    moduleSISBound ≤ decisionMLWEBound / gap := by
  exact (le_div_iff₀ hGap).2 hCompatibleDualTest

/-- Substitute a compatible positive-gap dual test into the full weighted
general-distribution bound. -/
theorem weightedGeneralDistribution_absorb_moduleSIS
    (reduction : WeightedGeneralDistributionReduction)
    (gap : ℝ) (hGap : 0 < gap)
    (hCompatibleDualTest :
      reduction.moduleSISBound * gap ≤ reduction.decisionMLWEBound) :
    reduction.searchBound ≤
      (reduction.decisionCoefficient + reduction.moduleSISCoefficient / gap) *
          reduction.decisionMLWEBound +
        reduction.statisticalLoss := by
  have hModuleSIS :
      reduction.moduleSISBound ≤ reduction.decisionMLWEBound / gap :=
    moduleSISBound_le_decisionMLWEBound_div reduction.moduleSISBound
      reduction.decisionMLWEBound gap hGap hCompatibleDualTest
  calc
    reduction.searchBound ≤
        reduction.decisionCoefficient * reduction.decisionMLWEBound +
          reduction.moduleSISCoefficient * reduction.moduleSISBound +
            reduction.statisticalLoss := reduction.reduces
    _ ≤ reduction.decisionCoefficient * reduction.decisionMLWEBound +
          reduction.moduleSISCoefficient *
              (reduction.decisionMLWEBound / gap) +
            reduction.statisticalLoss := by
      gcongr
      exact reduction.moduleSISCoefficient_nonneg
    _ = (reduction.decisionCoefficient + reduction.moduleSISCoefficient / gap) *
          reduction.decisionMLWEBound + reduction.statisticalLoss := by
      ring

/-- Honest two-branch endpoint for the fold-free framework.  `externalLoss` retains partial-CRT
estimation, pivot abort, automorphism transport, and amplification losses.  The two compatibility
hypotheses are not ordinary hardness assumptions: they are the exact interface obligations that
must connect the imported M-SIS challenges to the dual tests. -/
theorem foldFree_twoBranch_bound
    (circularAdvantage externalLoss : ℝ)
    (oneBranch zeroBranch : WeightedGeneralDistributionReduction)
    (oneGap zeroGap : ℝ)
    (hOneGap : 0 < oneGap) (hZeroGap : 0 < zeroGap)
    (hOneCompatible :
      oneBranch.moduleSISBound * oneGap ≤ oneBranch.decisionMLWEBound)
    (hZeroCompatible :
      zeroBranch.moduleSISBound * zeroGap ≤ zeroBranch.decisionMLWEBound)
    (hBranchReduction :
      circularAdvantage ≤
        oneBranch.searchBound + zeroBranch.searchBound + externalLoss) :
    circularAdvantage ≤
      (oneBranch.decisionCoefficient + oneBranch.moduleSISCoefficient / oneGap) *
          oneBranch.decisionMLWEBound + oneBranch.statisticalLoss +
        ((zeroBranch.decisionCoefficient + zeroBranch.moduleSISCoefficient / zeroGap) *
          zeroBranch.decisionMLWEBound + zeroBranch.statisticalLoss) +
        externalLoss := by
  have hOne := weightedGeneralDistribution_absorb_moduleSIS
    oneBranch oneGap hOneGap hOneCompatible
  have hZero := weightedGeneralDistribution_absorb_moduleSIS
    zeroBranch zeroGap hZeroGap hZeroCompatible
  linarith

end

end FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurity
