/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CoefficientStructuredLWE
import FormalProof4FHE.TFHE.RingSquareBinarySelectorSecurity
import FormalProof4FHE.TFHE.RingSquarePowerOfTwoLiftingSelector

/-!
# Production Power-of-Two Selector for `RGSW_S(-S)`

This file connects the coefficientwise two-adic lifting construction to the actual negacyclic
ring and anchored selector interface consumed by the `RGSW_S(-S)` compiler.  The first public
mask is assigned weight one.  The lifting selector runs on the remaining masks with target
`gadget - firstMask`.

For modulus `2^(depth+1)`, degree `2^degreeExponent`, and
`sourceCount depth (2^degreeExponent) slack` non-anchor masks, selector failure is therefore
contained in the recursive binary-rank failure event proved in the coefficient model.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting

noncomputable section

open FormalProof4FHE.LeftoverHash
open FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE
open BinaryPreimageExistence
open BinarySelectorSecurity

/-- The actual negacyclic ring at the two-adic depth used by the lifting selector. -/
abbrev ProductionRing (depth degreeExponent : ℕ) :=
  SingleSourceInverse.PowerOfTwo.Ring (depth + 1) degreeExponent

/-- The proof-facing commutative-ring dictionary used by the RGSW compiler. -/
abbrev productionCommRing (depth degreeExponent : ℕ) :
    CommRing (ProductionRing depth degreeExponent) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing
    (ZMod (2 ^ (depth + 1))) (2 ^ degreeExponent)

/-- The production polynomial degree. -/
abbrev productionDegree (degreeExponent : ℕ) := 2 ^ degreeExponent

/-- The number of non-anchor public masks consumed by the lifting selector. -/
abbrev productionExtraCount (depth degreeExponent slack : ℕ) :=
  sourceCount depth (productionDegree degreeExponent) slack

/-- Coefficients of the non-anchor portion of a production mask vector. -/
def productionTailCoefficients (depth degreeExponent slack : ℕ)
    (masks : MultiSourceCounting.Vectors
      (ProductionRing depth degreeExponent)
      (productionExtraCount depth degreeExponent slack + 1)) :
    Fin (productionExtraCount depth degreeExponent slack) →
      CoefficientVector (depth + 1) (productionDegree degreeExponent) :=
  fun index ↦ coefficientEquiv
    (2 ^ (depth + 1)) (productionDegree degreeExponent) (masks index.succ)

/-- The inhomogeneous target after reserving the first mask with coefficient one. -/
def productionResidualTarget (depth degreeExponent slack : ℕ)
    (target : ProductionRing depth degreeExponent)
    (masks : MultiSourceCounting.Vectors
      (ProductionRing depth degreeExponent)
      (productionExtraCount depth degreeExponent slack + 1)) :
    CoefficientVector (depth + 1) (productionDegree degreeExponent) :=
  coefficientEquiv (2 ^ (depth + 1)) (productionDegree degreeExponent) target -
    coefficientEquiv (2 ^ (depth + 1)) (productionDegree degreeExponent) (masks 0)

/-- The concrete anchored bit selector.  It reserves mask zero and solves the residual target on
the remaining public masks by recursive two-adic lifting. -/
noncomputable def productionBitSelector (depth degreeExponent slack : ℕ)
    (target : ProductionRing depth degreeExponent) :
    BitSelector (ProductionRing depth degreeExponent)
      (productionExtraCount depth degreeExponent slack) :=
  fun masks ↦
    powerOfTwoSelector depth (productionDegree degreeExponent) slack
      (productionTailCoefficients depth degreeExponent slack masks)
      (productionResidualTarget depth degreeExponent slack target masks)

/-- Coefficient presentation of one production ring element. -/
def productionCoefficientEquiv (depth degreeExponent : ℕ) :
    ProductionRing depth degreeExponent ≃
      CoefficientVector (depth + 1) (productionDegree degreeExponent) :=
  coefficientEquiv (2 ^ (depth + 1)) (productionDegree degreeExponent)

/-- Coefficient presentation of a whole non-anchor mask table. -/
def productionTailTableEquiv (depth degreeExponent slack : ℕ) :
    (Fin (productionExtraCount depth degreeExponent slack) →
        ProductionRing depth degreeExponent) ≃
      (Fin (productionExtraCount depth degreeExponent slack) →
        CoefficientVector (depth + 1) (productionDegree degreeExponent)) :=
  Equiv.piCongrRight fun _index ↦ productionCoefficientEquiv depth degreeExponent

/-- Restrict a complete anchored mask vector to its non-anchor tail. -/
def productionTailMasks (depth degreeExponent slack : ℕ)
    (masks : MultiSourceCounting.Vectors
      (ProductionRing depth degreeExponent)
      (productionExtraCount depth degreeExponent slack + 1)) :
    Fin (productionExtraCount depth degreeExponent slack) →
      ProductionRing depth degreeExponent :=
  fun index ↦ masks index.succ

/-- A uniform complete production mask vector induces an exactly uniform coefficient table on
the non-anchor masks. -/
theorem productionTailCoefficients_uniform_evalDist
    (depth degreeExponent slack : ℕ) :
    evalDist
        (productionTailCoefficients depth degreeExponent slack <$>
          ($ᵗ MultiSourceCounting.Vectors
            (ProductionRing depth degreeExponent)
            (productionExtraCount depth degreeExponent slack + 1))) =
      evalDist
        ($ᵗ (Fin (productionExtraCount depth degreeExponent slack) →
          CoefficientVector (depth + 1) (productionDegree degreeExponent))) := by
  let Extra := productionExtraCount depth degreeExponent slack
  let Ring := ProductionRing depth degreeExponent
  let RingTable := Fin Extra → Ring
  let CoefficientTable := Fin Extra →
    CoefficientVector (depth + 1) (productionDegree degreeExponent)
  let FullMasks := MultiSourceCounting.Vectors Ring (Extra + 1)
  let restrict : FullMasks → RingTable :=
    productionTailMasks depth degreeExponent slack
  let coefficients : RingTable ≃ CoefficientTable :=
    productionTailTableEquiv depth degreeExponent slack
  have hrestrict :
      evalDist (restrict <$> ($ᵗ FullMasks)) = evalDist ($ᵗ RingTable) := by
    change evalDist
        ((fun masks : FullMasks ↦ masks ∘ Fin.succ) <$> ($ᵗ FullMasks)) = _
    simpa only [bind_pure_comp] using
      (evalDist_uniformSample_map_comp_injective
        (A := Fin Extra) (B := Fin (Extra + 1)) (R := Ring)
        (Fin.succ_injective Extra))
  have hcoefficients :
      evalDist (coefficients <$> ($ᵗ RingTable)) =
        evalDist ($ᵗ CoefficientTable) :=
    evalDist_map_bijective_uniform_cross
      (α := RingTable) (β := CoefficientTable)
      coefficients coefficients.bijective
  calc
    evalDist
        (productionTailCoefficients depth degreeExponent slack <$>
          ($ᵗ FullMasks)) =
      evalDist (coefficients <$> (restrict <$> ($ᵗ FullMasks))) := by
        simp only [Functor.map_map]
        congr 2
    _ = evalDist (coefficients <$> ($ᵗ RingTable)) :=
      evalDist_map_eq_of_evalDist_eq hrestrict coefficients
    _ = evalDist ($ᵗ CoefficientTable) := hcoefficients

/-- The recursive rank condition fails on a uniform production tail with the same bound as in
the coefficient model. -/
theorem productionTail_liftingGood_failure_le
    (depth degreeExponent slack : ℕ) :
    Pr[(fun masks : MultiSourceCounting.Vectors
          (ProductionRing depth degreeExponent)
          (productionExtraCount depth degreeExponent slack + 1) ↦
        ¬ LiftingGood (productionDegree degreeExponent) slack depth
          (productionTailCoefficients depth degreeExponent slack masks)) |
      ($ᵗ MultiSourceCounting.Vectors
        (ProductionRing depth degreeExponent)
        (productionExtraCount depth degreeExponent slack + 1))] ≤
      (depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by
  let FullMasks := MultiSourceCounting.Vectors
    (ProductionRing depth degreeExponent)
    (productionExtraCount depth degreeExponent slack + 1)
  let CoefficientTable :=
    Fin (productionExtraCount depth degreeExponent slack) →
      CoefficientVector (depth + 1) (productionDegree degreeExponent)
  let bad : CoefficientTable → Prop := fun masks ↦
    ¬ LiftingGood (productionDegree degreeExponent) slack depth masks
  calc
    Pr[(fun masks : FullMasks ↦
          bad (productionTailCoefficients depth degreeExponent slack masks)) |
        ($ᵗ FullMasks)] =
      Pr[bad |
        productionTailCoefficients depth degreeExponent slack <$> ($ᵗ FullMasks)] := by
          exact (probEvent_map
            ($ᵗ FullMasks)
            (productionTailCoefficients depth degreeExponent slack) bad).symm
    _ = Pr[bad | ($ᵗ CoefficientTable)] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl)
        (productionTailCoefficients_uniform_evalDist
          depth degreeExponent slack)
    _ ≤ (depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) :=
      liftingGood_failure_le (productionDegree degreeExponent) slack depth

/-- Taking coefficients commutes with a binary subset sum in the production ring. -/
theorem coefficientEquiv_binarySubsetSum
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (q degree : ℕ) (masks : Index → RLWE.Rq q degree)
    (bits : Index → Bool) :
    coefficientEquiv q degree (binarySubsetSum masks bits) =
      binarySubsetSum (coefficientEquiv q degree ∘ masks) bits := by
  exact map_binarySubsetSum (coefficientAddMonoidHom q degree) masks bits

/-- An exact residual subset sum gives the anchored production mask equation. -/
theorem maskCombination_anchored_eq_target_of_tail_coefficients
    (depth degreeExponent slack : ℕ)
    (target : ProductionRing depth degreeExponent)
    (masks : MultiSourceCounting.Vectors
      (ProductionRing depth degreeExponent)
      (productionExtraCount depth degreeExponent slack + 1))
    (bits : Fin (productionExtraCount depth degreeExponent slack) → Bool)
    (hbits :
      binarySubsetSum
          (productionTailCoefficients depth degreeExponent slack masks) bits =
        productionResidualTarget depth degreeExponent slack target masks) :
    @MultiSourceCounting.maskCombination
        (ProductionRing depth degreeExponent)
        (productionCommRing depth degreeExponent)
        (productionExtraCount depth degreeExponent slack + 1)
        (@anchoredBinaryWeight
          (ProductionRing depth degreeExponent)
          (productionCommRing depth degreeExponent)
          (productionExtraCount depth degreeExponent slack) bits)
        masks = target := by
  letI : CommRing (ProductionRing depth degreeExponent) :=
    productionCommRing depth degreeExponent
  let tail : Fin (productionExtraCount depth degreeExponent slack) →
      ProductionRing depth degreeExponent := fun index ↦ masks index.succ
  have hmasks : masks = anchoredMasks (masks 0, tail) := by
    funext index
    refine Fin.cases ?_ (fun tailIndex ↦ ?_) index <;>
      simp [anchoredMasks, tail]
  rw [hmasks, maskCombination_anchoredBinaryWeight_eq]
  apply (coefficientEquiv
    (2 ^ (depth + 1)) (productionDegree degreeExponent)).injective
  unfold anchoredHash
  let tailSum : ProductionRing depth degreeExponent :=
    @binarySubsetSum
      (Fin (productionExtraCount depth degreeExponent slack))
      (ProductionRing depth degreeExponent)
      inferInstance inferInstance
      (productionCommRing depth degreeExponent).toAddCommMonoid tail bits
  change coefficientEquiv (2 ^ (depth + 1)) (productionDegree degreeExponent)
      (@Add.add (ProductionRing depth degreeExponent)
        (productionCommRing depth degreeExponent).toAdd (masks 0) tailSum) =
    coefficientEquiv (2 ^ (depth + 1)) (productionDegree degreeExponent) target
  have hsum :
      coefficientEquiv (2 ^ (depth + 1)) (productionDegree degreeExponent)
          tailSum =
        binarySubsetSum
          (coefficientEquiv
            (2 ^ (depth + 1)) (productionDegree degreeExponent) ∘ tail) bits :=
    map_binarySubsetSum
      (coefficientAddMonoidHom
        (2 ^ (depth + 1)) (productionDegree degreeExponent)) tail bits
  rw [coefficientEquiv_semiring_add, hsum]
  change
    coefficientEquiv (2 ^ (depth + 1)) (productionDegree degreeExponent) (masks 0) +
        binarySubsetSum
          (productionTailCoefficients depth degreeExponent slack masks) bits =
      coefficientEquiv (2 ^ (depth + 1)) (productionDegree degreeExponent) target
  rw [hbits]
  simp [productionResidualTarget]

/-- On every recursively good mask table, the production selector reaches its gadget target. -/
theorem productionBitSelector_succeeds_of_good
    (depth degreeExponent slack : ℕ)
    (target : ProductionRing depth degreeExponent)
    (masks : MultiSourceCounting.Vectors
      (ProductionRing depth degreeExponent)
      (productionExtraCount depth degreeExponent slack + 1))
    (hgood : LiftingGood (productionDegree degreeExponent) slack depth
      (productionTailCoefficients depth degreeExponent slack masks)) :
    @MultiSourceCounting.maskCombination
        (ProductionRing depth degreeExponent)
        (productionCommRing depth degreeExponent)
        (productionExtraCount depth degreeExponent slack + 1)
        (@binarySelectorWeights
          (ProductionRing depth degreeExponent)
          (productionCommRing depth degreeExponent)
          (productionExtraCount depth degreeExponent slack)
          (productionBitSelector depth degreeExponent slack target) masks)
        masks = target := by
  letI : CommRing (ProductionRing depth degreeExponent) :=
    productionCommRing depth degreeExponent
  apply maskCombination_anchored_eq_target_of_tail_coefficients
  exact powerOfTwoSelector_spec_of_good depth (productionDegree degreeExponent) slack
    (productionTailCoefficients depth degreeExponent slack masks)
    (productionResidualTarget depth degreeExponent slack target masks) hgood

/-- The actual anchored production selector fails with only the explicit two-adic rank loss. -/
theorem productionBitSelector_failure_le
    (depth degreeExponent slack : ℕ)
    (target : ProductionRing depth degreeExponent) :
    Pr[(fun masks : MultiSourceCounting.Vectors
          (ProductionRing depth degreeExponent)
          (productionExtraCount depth degreeExponent slack + 1) ↦
        ¬ @MultiSourceCounting.maskCombination
          (ProductionRing depth degreeExponent)
          (productionCommRing depth degreeExponent)
          (productionExtraCount depth degreeExponent slack + 1)
          (@binarySelectorWeights
            (ProductionRing depth degreeExponent)
            (productionCommRing depth degreeExponent)
            (productionExtraCount depth degreeExponent slack)
            (productionBitSelector depth degreeExponent slack target) masks)
          masks = target) |
      ($ᵗ MultiSourceCounting.Vectors
        (ProductionRing depth degreeExponent)
        (productionExtraCount depth degreeExponent slack + 1))] ≤
      (depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by
  apply le_trans (probEvent_mono (mx :=
    ($ᵗ MultiSourceCounting.Vectors
      (ProductionRing depth degreeExponent)
      (productionExtraCount depth degreeExponent slack + 1))) ?_)
  · exact productionTail_liftingGood_failure_le depth degreeExponent slack
  · intro masks _ hfailure
    by_contra hnotBad
    have hgood : LiftingGood (productionDegree degreeExponent) slack depth
        (productionTailCoefficients depth degreeExponent slack masks) := hnotBad
    exact hfailure
      (productionBitSelector_succeeds_of_good
        depth degreeExponent slack target masks hgood)

/-- Install the concrete lifting selector independently at every RGSW gadget level. -/
noncomputable def productionBitSelectors
    (depth degreeExponent slack levels : ℕ)
    (gadget : Fin levels → ProductionRing depth degreeExponent) :
    Fin levels → BitSelector
      (ProductionRing depth degreeExponent)
      (productionExtraCount depth degreeExponent slack) :=
  fun level ↦ productionBitSelector depth degreeExponent slack (gadget level)

/-- Union bound across all RGSW gadget levels for the concrete production selector. -/
theorem productionChallengeSelectors_failure_le
    (depth degreeExponent slack levels : ℕ)
    (gadget : Fin levels → ProductionRing depth degreeExponent) :
    Pr[(fun challenge : Matrix (Fin 1)
          (Fin (levels *
            (productionExtraCount depth degreeExponent slack + 1)))
          (ProductionRing depth degreeExponent) ↦
        ¬ @ChallengeSelectorsSucceed
          (ProductionRing depth degreeExponent)
          (productionCommRing depth degreeExponent)
          levels (productionExtraCount depth degreeExponent slack)
          gadget
          (productionBitSelectors depth degreeExponent slack levels gadget)
          challenge) |
      ($ᵗ Matrix (Fin 1)
        (Fin (levels *
          (productionExtraCount depth degreeExponent slack + 1)))
        (ProductionRing depth degreeExponent))] ≤
      (levels : ℕ) *
        ((depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1))) := by
  let Extra := productionExtraCount depth degreeExponent slack
  let Ring := ProductionRing depth degreeExponent
  let Challenge := Matrix (Fin 1) (Fin (levels * (Extra + 1))) Ring
  let sampler : ProbComp Challenge := $ᵗ Challenge
  let selectors : Fin levels → BitSelector Ring Extra :=
    productionBitSelectors depth degreeExponent slack levels gadget
  let failure : Fin levels → Challenge → Prop := fun level challenge ↦
    ¬ @MultiSourceCounting.maskCombination
        Ring (productionCommRing depth degreeExponent) (Extra + 1)
        (@binarySelectorWeights
          Ring (productionCommRing depth degreeExponent) Extra
          (selectors level) (sourceChallengeMasks level challenge))
        (sourceChallengeMasks level challenge) = gadget level
  have hlevel (level : Fin levels) :
      Pr[failure level | sampler] ≤
        (depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by
    calc
      Pr[failure level | sampler] =
        Pr[(fun masks : MultiSourceCounting.Vectors Ring (Extra + 1) ↦
            ¬ @MultiSourceCounting.maskCombination
              Ring (productionCommRing depth degreeExponent) (Extra + 1)
              (@binarySelectorWeights
                Ring (productionCommRing depth degreeExponent) Extra
                (selectors level) masks)
              masks = gadget level) |
          ($ᵗ MultiSourceCounting.Vectors Ring (Extra + 1))] :=
        probEvent_sourceChallengeMasks_uniform_eq
          (R := Ring) levels (Extra + 1) level
          (fun masks ↦
            ¬ @MultiSourceCounting.maskCombination
              Ring (productionCommRing depth degreeExponent) (Extra + 1)
              (@binarySelectorWeights
                Ring (productionCommRing depth degreeExponent) Extra
                (selectors level) masks)
              masks = gadget level)
      _ ≤ (depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by
        exact productionBitSelector_failure_le
          depth degreeExponent slack (gadget level)
  have hUnion :
      Pr[(fun challenge : Challenge ↦
          ¬ @ChallengeSelectorsSucceed
            Ring (productionCommRing depth degreeExponent) levels Extra
            gadget selectors challenge) | sampler] ≤
        ∑ level : Fin levels, Pr[failure level | sampler] := by
    calc
      _ ≤ Pr[(fun challenge : Challenge ↦
          ∃ level ∈ (Finset.univ : Finset (Fin levels)), failure level challenge) |
          sampler] := by
        apply probEvent_mono
        intro challenge _ hfailure
        simp only [ChallengeSelectorsSucceed, not_forall] at hfailure
        obtain ⟨level, hlevelFailure⟩ := hfailure
        exact ⟨level, Finset.mem_univ _, hlevelFailure⟩
      _ ≤ _ := probEvent_exists_finset_le_sum
        (Finset.univ : Finset (Fin levels)) sampler failure
  calc
    Pr[(fun challenge : Challenge ↦
        ¬ @ChallengeSelectorsSucceed
          Ring (productionCommRing depth degreeExponent) levels Extra
          gadget selectors challenge) | sampler] ≤
      ∑ level : Fin levels, Pr[failure level | sampler] := hUnion
    _ ≤ ∑ _level : Fin levels,
        ((depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1))) := by
      apply Finset.sum_le_sum
      intro level _
      exact hlevel level
    _ = (levels : ℕ) *
        ((depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1))) := by
      simp

/-- Real-valued form used directly by the finite RGSW distinguishing bound. -/
theorem productionChallengeSelectors_failure_toReal_le
    (depth degreeExponent slack levels : ℕ)
    (gadget : Fin levels → ProductionRing depth degreeExponent) :
    (Pr[(fun challenge : Matrix (Fin 1)
          (Fin (levels *
            (productionExtraCount depth degreeExponent slack + 1)))
          (ProductionRing depth degreeExponent) ↦
        ¬ @ChallengeSelectorsSucceed
          (ProductionRing depth degreeExponent)
          (productionCommRing depth degreeExponent)
          levels (productionExtraCount depth degreeExponent slack)
          gadget
          (productionBitSelectors depth degreeExponent slack levels gadget)
          challenge) |
      ($ᵗ Matrix (Fin 1)
        (Fin (levels *
          (productionExtraCount depth degreeExponent slack + 1)))
        (ProductionRing depth degreeExponent))]).toReal ≤
      (levels : ℝ) * (depth + 1 : ℝ) *
        (2 / (2 : ℝ) ^ (slack + 1)) := by
  have hreal := ENNReal.toReal_mono (by finiteness)
    (productionChallengeSelectors_failure_le
      depth degreeExponent slack levels gadget)
  calc
    _ ≤ (((levels : ℕ) : ℝ≥0∞) *
        (((depth + 1 : ℕ) : ℝ≥0∞) *
          (2 / (2 : ℝ≥0∞) ^ (slack + 1)))).toReal := hreal
    _ = (levels : ℝ) * (depth + 1 : ℝ) *
        (2 / (2 : ℝ) ^ (slack + 1)) := by
      simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_pow,
        Nat.cast_add, Nat.cast_one]
      rw [ENNReal.toReal_add (by simp) (by simp)]
      simp
      ring

/-! ## Finite RGSW(-S) security theorem with the proved selector -/

/-- The finite `RGSW_S(-S)` reduction with the abstract selector-failure term discharged by the
two-adic lifting construction.  The remaining terms are the explicit Gaussian smudging loss and
ordinary batch-RLWE advantage. -/
theorem rgswMinusSecretAdvantage_centeredBinomial_widenedDiscreteGaussian_le
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (distinguisher : Full.Distinguisher
      (ProductionRing depth degreeExponent) levels)
    (secretBound : ℕ)
    (hSecret : ∀ secretValue, secretValue ∈ support secretSampler →
      LatticeCrypto.cInfNorm (embed secretValue 0) ≤ secretBound) :
    let extraCount := productionExtraCount depth degreeExponent slack
    let sourceErrorSampler := RLWE.CenteredBinomial.sampler
      (2 ^ (depth + 1)) (2 ^ degreeExponent) eta
    let wideningSampler := DiscreteGaussianSampler.ringSampler
      (2 ^ degreeExponent) certificate
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
        gadget distinguisher ≤
      (levels : ℝ) * (depth + 1 : ℝ) *
          (2 / (2 : ℝ) ^ (slack + 1)) +
        (levels : ℝ) *
          (((2 ^ degreeExponent : ℕ) : ℝ) *
            DiscreteGaussianSampler.scalarLinearShiftBound certificate
              (SelectorNoise.Native.inducedShiftBoundForDegree
                (2 ^ degreeExponent) (extraCount + 1) secretBound 1 eta)) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * (extraCount + 1) + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler :=
              Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
            (extraErrorSampler := wideningSampler)
            (Heterogeneous.reduction
              (targetErrorSampler :=
                Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
              (binarySelectors
                (productionBitSelectors
                  depth degreeExponent slack levels gadget))
              (Full.restoreDistinguisher gadget distinguisher))) := by
  dsimp only
  have hbase :=
    production_rgswMinusSecretAdvantage_centeredBinomial_widenedDiscreteGaussian_le_of_binarySelectors
      (depth + 1) degreeExponent levels
      (productionExtraCount depth degreeExponent slack) eta
      certificate secretSampler embed gadget
      (productionBitSelectors depth degreeExponent slack levels gadget)
      distinguisher secretBound hSecret
  have hfailure := productionChallengeSelectors_failure_toReal_le
    depth degreeExponent slack levels gadget
  exact hbase.trans (by
    gcongr)

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting
