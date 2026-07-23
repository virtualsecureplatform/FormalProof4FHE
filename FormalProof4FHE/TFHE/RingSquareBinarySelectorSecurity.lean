/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareBinaryPreimageExistence
import FormalProof4FHE.TFHE.RingSquareSelectorNoiseBound

/-!
# Binary-Selector Security Boundary for `RGSW_S(-S)`

This file lifts the one-target binary-preimage theorem to every gadget level used by the hidden
ring-square compiler.  Each level receives an independent slice of one uniform source-challenge
matrix.  Restricting that matrix to a fixed slice is proved exactly uniform, and a finite union
bound charges all selector failures.

The result is deliberately parameterized by pointwise-complete bit selectors.  It does not claim
that such selectors are polynomial time.  Replacing this interface by a proved efficient
algorithm is the remaining inhomogeneous subset-sum/Ring-SIS research step.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BinarySelectorSecurity

noncomputable section

open BinaryPreimageExistence

/-- The row of a rank-one source-challenge matrix. -/
def matrixOneEquiv (R : Type) (samples : ℕ) :
    Matrix (Fin 1) (Fin samples) R ≃ (Fin samples → R) where
  toFun matrix := matrix 0
  invFun row := fun _index ↦ row
  left_inv matrix := by
    funext row column
    rw [Subsingleton.elim row 0]
  right_inv _row := rfl

/-- The source-mask vector assigned to one gadget level inside the flattened challenge matrix. -/
def sourceChallengeMasks {R : Type} {levels sourceCount : ℕ}
    (level : Fin levels)
    (challenge : Matrix (Fin 1) (Fin (levels * sourceCount)) R) :
    MultiSourceCounting.Vectors R sourceCount :=
  fun source ↦ challenge 0 (finProdFinEquiv (level, source))

/-- The flattened indices belonging to one level are distinct. -/
theorem sourceIndex_injective {levels sourceCount : ℕ} (level : Fin levels) :
    Function.Injective
      (fun source : Fin sourceCount ↦ finProdFinEquiv (level, source)) := by
  intro left right heq
  exact congrArg Prod.snd (finProdFinEquiv.injective heq)

/-- A fixed level slice of the uniform full source-challenge matrix is an exactly uniform mask
vector. -/
theorem sourceChallengeMasks_uniform_evalDist
    {R : Type} [SampleableType R]
    (levels sourceCount : ℕ) (level : Fin levels)
    [SampleableType (Matrix (Fin 1) (Fin (levels * sourceCount)) R)]
    [SampleableType (MultiSourceCounting.Vectors R sourceCount)] :
    evalDist
        (sourceChallengeMasks level <$>
          ($ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R)) =
      evalDist ($ᵗ MultiSourceCounting.Vectors R sourceCount) := by
  let Row := Fin (levels * sourceCount) → R
  let Masks := MultiSourceCounting.Vectors R sourceCount
  let rowEquiv := matrixOneEquiv R (levels * sourceCount)
  let sourceIndex : Fin sourceCount → Fin (levels * sourceCount) :=
    fun source ↦ finProdFinEquiv (level, source)
  let restrict : Row → Masks := fun row ↦ row ∘ sourceIndex
  have hrow :
      evalDist
          (rowEquiv <$>
            ($ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R)) =
        evalDist ($ᵗ Row) :=
    evalDist_map_bijective_uniform_cross
      (Matrix (Fin 1) (Fin (levels * sourceCount)) R)
      (f := rowEquiv) rowEquiv.bijective
  have hrestrict :
      evalDist (restrict <$> ($ᵗ Row)) = evalDist ($ᵗ Masks) := by
    simpa [restrict, Row, Masks, sourceIndex] using
      (evalDist_uniformSample_map_comp_injective
        (R := R) (e := sourceIndex) (sourceIndex_injective level))
  calc
    evalDist
        (sourceChallengeMasks level <$>
          ($ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R)) =
        evalDist
          (restrict <$>
            (rowEquiv <$>
              ($ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R))) := by
      simp only [Functor.map_map]
      rfl
    _ = evalDist (restrict <$> ($ᵗ Row)) := by
      rw [evalDist_map, hrow, ← evalDist_map]
    _ = evalDist ($ᵗ Masks) := hrestrict

/-- Event probabilities on a fixed challenge slice are therefore the corresponding probabilities
under the compiler's native uniform mask-vector law. -/
theorem probEvent_sourceChallengeMasks_uniform_eq
    {R : Type} [SampleableType R]
    (levels sourceCount : ℕ) (level : Fin levels)
    [SampleableType (Matrix (Fin 1) (Fin (levels * sourceCount)) R)]
    [SampleableType (MultiSourceCounting.Vectors R sourceCount)]
    (event : MultiSourceCounting.Vectors R sourceCount → Prop) :
    Pr[(fun challenge : Matrix (Fin 1) (Fin (levels * sourceCount)) R ↦
          event (sourceChallengeMasks level challenge)) |
        ($ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R)] =
      Pr[event | ($ᵗ MultiSourceCounting.Vectors R sourceCount)] := by
  calc
    _ = Pr[event |
        sourceChallengeMasks level <$>
          ($ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R)] := by
      simpa only [Function.comp_def] using
        (probEvent_map
          (mx := ($ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R))
          (f := sourceChallengeMasks level) event).symm
    _ = _ := by
      unfold probEvent
      rw [sourceChallengeMasks_uniform_evalDist levels sourceCount level]

/-- Install one bit-selection algorithm at every gadget level. -/
def binarySelectors {R : Type} [CommRing R] {levels extraCount : ℕ}
    (bitSelectors : Fin levels → BitSelector R extraCount) :
    Full.Selectors R levels (extraCount + 1) :=
  fun level ↦ binarySelectorWeights (bitSelectors level)

/-- All selected mask combinations hit their requested gadget values in the public source
challenge. -/
def ChallengeSelectorsSucceed {R : Type} [CommRing R] {levels extraCount : ℕ}
    (gadget : Fin levels → R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (challenge : Matrix (Fin 1) (Fin (levels * (extraCount + 1))) R) : Prop :=
  ∀ level,
    MultiSourceCounting.maskCombination
        (binarySelectorWeights (bitSelectors level)
          (sourceChallengeMasks level challenge))
        (sourceChallengeMasks level challenge) = gadget level

/-- One complete level selector has the explicit binary-preimage failure bound on its matrix
slice. -/
theorem production_levelSelector_failure_toReal_le_card_div_add
    (modulusExponent degreeExponent levels extraCount : ℕ)
    (level : Fin levels)
    (gadget : Fin levels →
      SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]
    [SampleableType
      (MultiSourceCounting.Vectors
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
        (extraCount + 1))]
    [SampleableType
      (Matrix (Fin 1) (Fin (levels * (extraCount + 1)))
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]
    (bitSelectors : Fin levels → BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) extraCount)
    (hcomplete : IsCompleteBinarySelector (gadget level) (bitSelectors level)) :
    (Pr[(fun challenge : Matrix (Fin 1) (Fin (levels * (extraCount + 1)))
          (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
        ¬ MultiSourceCounting.maskCombination
            (binarySelectorWeights (bitSelectors level)
              (sourceChallengeMasks level challenge))
            (sourceChallengeMasks level challenge) = gadget level) |
      ($ᵗ Matrix (Fin 1) (Fin (levels * (extraCount + 1)))
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]).toReal ≤
      (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ) /
        (((2 ^ extraCount : ℕ) : ℝ) +
          (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ)) := by
  calc
    _ = (Pr[(fun masks : MultiSourceCounting.Vectors
          (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
          (extraCount + 1) ↦
        ¬ MultiSourceCounting.maskCombination
            (binarySelectorWeights (bitSelectors level) masks) masks = gadget level) |
      ($ᵗ MultiSourceCounting.Vectors
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
        (extraCount + 1))]).toReal :=
      congrArg ENNReal.toReal
        (probEvent_sourceChallengeMasks_uniform_eq
          (R := SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
          levels (extraCount + 1) level
          (fun masks ↦
            ¬ MultiSourceCounting.maskCombination
                (binarySelectorWeights (bitSelectors level) masks) masks = gadget level))
    _ ≤ _ :=
      production_completeBinarySelector_uniformMasks_failure_toReal_le_card_div_add
        modulusExponent degreeExponent extraCount (gadget level) (bitSelectors level) hcomplete

/-- Union bound across every gadget level. -/
theorem production_challengeSelectors_failure_toReal_le_levels_mul_card_div_add
    (modulusExponent degreeExponent levels extraCount : ℕ)
    (gadget : Fin levels →
      SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]
    [SampleableType
      (MultiSourceCounting.Vectors
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
        (extraCount + 1))]
    [SampleableType
      (Matrix (Fin 1) (Fin (levels * (extraCount + 1)))
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]
    (bitSelectors : Fin levels → BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) extraCount)
    (hcomplete : ∀ level,
      IsCompleteBinarySelector (gadget level) (bitSelectors level)) :
    (Pr[(fun challenge : Matrix (Fin 1) (Fin (levels * (extraCount + 1)))
          (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
        ¬ ChallengeSelectorsSucceed gadget bitSelectors challenge) |
      ($ᵗ Matrix (Fin 1) (Fin (levels * (extraCount + 1)))
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]).toReal ≤
      (levels : ℝ) *
        ((((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ) /
          (((2 ^ extraCount : ℕ) : ℝ) +
            (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ))) := by
  let Challenge := Matrix (Fin 1) (Fin (levels * (extraCount + 1)))
    (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
  let sampler : ProbComp Challenge := $ᵗ Challenge
  let failure : Fin levels → Challenge → Prop := fun level challenge ↦
    ¬ MultiSourceCounting.maskCombination
        (binarySelectorWeights (bitSelectors level)
          (sourceChallengeMasks level challenge))
        (sourceChallengeMasks level challenge) = gadget level
  have hUnion :
      Pr[(fun challenge : Challenge ↦
          ¬ ChallengeSelectorsSucceed gadget bitSelectors challenge) | sampler] ≤
        ∑ level : Fin levels, Pr[failure level | sampler] := by
    calc
      _ ≤ Pr[(fun challenge : Challenge ↦
          ∃ level ∈ (Finset.univ : Finset (Fin levels)), failure level challenge) |
          sampler] := by
        apply probEvent_mono
        intro challenge _ hfailure
        simp only [ChallengeSelectorsSucceed, not_forall] at hfailure
        obtain ⟨level, hlevel⟩ := hfailure
        exact ⟨level, Finset.mem_univ _, hlevel⟩
      _ ≤ _ := probEvent_exists_finset_le_sum
        (Finset.univ : Finset (Fin levels)) sampler failure
  have hReal := ENNReal.toReal_mono (by simp) hUnion
  rw [ENNReal.toReal_sum (fun _ _ ↦ probEvent_ne_top)] at hReal
  calc
    (Pr[(fun challenge : Challenge ↦
        ¬ ChallengeSelectorsSucceed gadget bitSelectors challenge) | sampler]).toReal ≤
        ∑ level : Fin levels, (Pr[failure level | sampler]).toReal := hReal
    _ ≤ ∑ _level : Fin levels,
        (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ) /
          (((2 ^ extraCount : ℕ) : ℝ) +
            (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro level _
      exact production_levelSelector_failure_toReal_le_card_div_add
        modulusExponent degreeExponent levels extraCount level gadget
        bitSelectors (hcomplete level)
    _ = _ := by simp

/-- Adding `securityMargin` binary coordinates beyond the exact output bit length
`modulusExponent * 2^degreeExponent` makes the one-level counting ratio at most
`2^(-securityMargin)`. -/
theorem production_failureFraction_entropyMargin_le_inv_twoPow
    (modulusExponent degreeExponent securityMargin : ℕ) :
    ((((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ) /
        (((2 ^ (modulusExponent * (2 ^ degreeExponent) + securityMargin) : ℕ) : ℝ) +
          (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ))) ≤
      (((2 ^ securityMargin : ℕ) : ℝ))⁻¹ := by
  have hOutput :
      ((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) =
        2 ^ (modulusExponent * (2 ^ degreeExponent)) := by
    exact (pow_mul 2 modulusExponent (2 ^ degreeExponent)).symm
  rw [hOutput, pow_add, Nat.cast_mul]
  let outputSize : ℝ := ((2 ^ (modulusExponent * (2 ^ degreeExponent)) : ℕ) : ℝ)
  let marginSize : ℝ := ((2 ^ securityMargin : ℕ) : ℝ)
  have hOutputPositive : 0 < outputSize := by
    dsimp [outputSize]
    positivity
  have hMarginPositive : 0 < marginSize := by
    dsimp [marginSize]
    positivity
  calc
    outputSize / (outputSize * marginSize + outputSize) ≤
        outputSize / (outputSize * marginSize) := by
      exact div_le_div_of_nonneg_left (le_of_lt hOutputPositive)
        (mul_pos hOutputPositive hMarginPositive)
        (by linarith)
    _ = marginSize⁻¹ := by
      field_simp

/-! ## Hidden compiler context -/

/-- Assembling bodies and errors does not change the source masks read by one level selector. -/
@[simp]
theorem sourceMasks_sourceRowsAt_batchAssemble
    {R : Type} [Semiring R] {levels sourceCount : ℕ}
    (secret : Fin 1 → R)
    (challenge : Matrix (Fin 1) (Fin (levels * sourceCount)) R)
    (message error : Fin (levels * sourceCount) → R)
    (level : Fin levels) :
    sourceMasks
        (Full.sourceRowsAt
          (TLWE.batchAssemble secret challenge message error) level) =
      sourceChallengeMasks level challenge := by
  rfl

/-- The selector-visible masks are the challenge component of a source batch; its body vector is
irrelevant. -/
@[simp]
theorem sourceMasks_sourceRowsAt_pair
    {R : Type} {levels sourceCount : ℕ}
    (challenge : Matrix (Fin 1) (Fin (levels * sourceCount)) R)
    (body : Fin (levels * sourceCount) → R)
    (level : Fin levels) :
    sourceMasks (Full.sourceRowsAt (challenge, body) level) =
      sourceChallengeMasks level challenge := by
  rfl

/-- Challenge-level success is exactly the success predicate retained by the hidden compiler
context, independently of the sampled secret and errors. -/
theorem selectorsSucceed_assembled_of_challenge
    {R Secret : Type} [CommRing R] {levels extraCount : ℕ}
    (gadget : Fin levels → R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (challenge : Matrix (Fin 1) (Fin (levels * (extraCount + 1))) R)
    (secretValue : Secret) (embed : Secret → Fin 1 → R)
    (sourceError : Fin (levels * (extraCount + 1)) → R)
    (hchallenge : ChallengeSelectorsSucceed gadget bitSelectors challenge) :
    CompilerNormalForm.SelectorsSucceed gadget (binarySelectors bitSelectors)
      ⟨secretValue,
        TLWE.batchAssemble (embed secretValue) challenge 0 sourceError⟩ := by
  intro level
  change SelectorSucceeds (gadget level)
    (binarySelectorWeights (bitSelectors level))
    (Full.sourceRowsAt
      (TLWE.batchAssemble (embed secretValue) challenge 0 sourceError) level)
  apply selectorSucceeds_of_binarySelectorWeights_combination_eq
  rw [sourceMasks_sourceRowsAt_batchAssemble]
  exact hchallenge level

/-- Sampling the secret and source errors after the public challenge cannot introduce a selector
failure.  This ring-generic prefix lemma avoids any production-ring representation choices. -/
theorem contextSelectors_failure_le_challenge
    {R Secret : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (levels extraCount : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (bitSelectors : Fin levels → BitSelector R extraCount) :
    Pr[(fun context ↦
        ¬ CompilerNormalForm.SelectorsSucceed gadget
          (binarySelectors bitSelectors) context) |
      CompilerNormalForm.contextSampler levels (extraCount + 1)
        secretSampler embed sourceErrorSampler] ≤
      Pr[(fun challenge : Matrix (Fin 1) (Fin (levels * (extraCount + 1))) R ↦
          ¬ ChallengeSelectorsSucceed gadget bitSelectors challenge) |
        ($ᵗ Matrix (Fin 1) (Fin (levels * (extraCount + 1))) R)] := by
  let Challenge := Matrix (Fin 1) (Fin (levels * (extraCount + 1))) R
  let Context := CompilerNormalForm.Context R Secret levels (extraCount + 1)
  let challengeSampler : ProbComp Challenge := $ᵗ Challenge
  let contextFailure : Context → Prop := fun context ↦
    ¬ CompilerNormalForm.SelectorsSucceed gadget
      (binarySelectors bitSelectors) context
  let challengeFailure : Challenge → Prop := fun challenge ↦
    ¬ ChallengeSelectorsSucceed gadget bitSelectors challenge
  let continuation : Challenge → ProbComp Context := fun challenge ↦ do
    let secretValue ← secretSampler
    let sourceError ← ProbComp.sampleIID (levels * (extraCount + 1)) sourceErrorSampler
    return ⟨secretValue,
      TLWE.batchAssemble (embed secretValue) challenge 0 sourceError⟩
  have hContextSampler :
      CompilerNormalForm.contextSampler levels (extraCount + 1)
          secretSampler embed sourceErrorSampler =
        challengeSampler >>= continuation := by
    rfl
  rw [hContextSampler]
  apply probEvent_bind_le_probEvent
  intro challenge _hChallenge hgood
  rw [probEvent_eq_zero_iff]
  intro context hcontext hfailure
  unfold continuation at hcontext
  rw [mem_support_bind_iff] at hcontext
  obtain ⟨secretValue, _hSecret, hcontext⟩ := hcontext
  rw [mem_support_bind_iff] at hcontext
  obtain ⟨sourceError, _hSourceError, hcontext⟩ := hcontext
  simp only [support_pure, Set.mem_singleton_iff] at hcontext
  subst context
  exact hfailure
    (selectorsSucceed_assembled_of_challenge gadget bitSelectors challenge
      secretValue embed sourceError (not_not.mp hgood))

/-- The hidden context can fail only if the public source-challenge matrix already fails.  Secret
or error sampler failure can only reduce this probability, so no totality premise is needed. -/
theorem production_contextSelectors_failure_toReal_le_levels_mul_card_div_add
    (modulusExponent degreeExponent levels extraCount : ℕ)
    {Secret : Type}
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 →
      SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    (sourceErrorSampler : ProbComp
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))
    (gadget : Fin levels →
      SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]
    [SampleableType
      (MultiSourceCounting.Vectors
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
        (extraCount + 1))]
    (bitSelectors : Fin levels → BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) extraCount)
    (hcomplete : ∀ level,
      IsCompleteBinarySelector (gadget level) (bitSelectors level)) :
    (Pr[(fun context ↦
        ¬ CompilerNormalForm.SelectorsSucceed gadget
          (binarySelectors bitSelectors) context) |
      CompilerNormalForm.contextSampler levels (extraCount + 1)
        secretSampler embed sourceErrorSampler]).toReal ≤
      (levels : ℝ) *
        ((((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ) /
          (((2 ^ extraCount : ℕ) : ℝ) +
            (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ))) := by
  have hPrefix := contextSelectors_failure_le_challenge
    levels extraCount secretSampler embed sourceErrorSampler gadget bitSelectors
  have hPrefixReal := ENNReal.toReal_mono probEvent_ne_top hPrefix
  exact hPrefixReal.trans
    (production_challengeSelectors_failure_toReal_le_levels_mul_card_div_add
      modulusExponent degreeExponent levels extraCount gadget bitSelectors hcomplete)

/-! ## Conditional finite-game security theorem -/

/-- An arbitrary binary selector gives a finite-game `RGSW_S(-S)` bound in terms of its
*actual average-case failure probability* on the uniform public source masks.  Unlike the
complete-selector corollary below, this theorem does not require the algorithm to find every
existing preimage.  It is therefore the natural entry point for a future PPT algorithm that
succeeds with overwhelming probability on the random anchored binary Ring-ISIS distribution. -/
theorem production_rgswMinusSecretAdvantage_centeredBinomial_widenedDiscreteGaussian_le_of_binarySelectors
    (modulusExponent degreeExponent levels extraCount eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ modulusExponent) alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 →
      SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    (gadget : Fin levels →
      SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    (bitSelectors : Fin levels → BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) extraCount)
    (distinguisher : Full.Distinguisher
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) levels)
    (secretBound : ℕ)
    (hSecret : ∀ secretValue, secretValue ∈ support secretSampler →
      LatticeCrypto.cInfNorm (embed secretValue 0) ≤ secretBound) :
    let sourceErrorSampler := RLWE.CenteredBinomial.sampler
      (2 ^ modulusExponent) (2 ^ degreeExponent) eta
    let wideningSampler := DiscreteGaussianSampler.ringSampler
      (2 ^ degreeExponent) certificate
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
        gadget distinguisher ≤
      (Pr[(fun challenge : Matrix (Fin 1) (Fin (levels * (extraCount + 1)))
            (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
          ¬ ChallengeSelectorsSucceed gadget bitSelectors challenge) |
        ($ᵗ Matrix (Fin 1) (Fin (levels * (extraCount + 1)))
          (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]).toReal +
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
              (binarySelectors bitSelectors)
              (Full.restoreDistinguisher gadget distinguisher))) := by
  dsimp only
  let productionCommRing : CommRing
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) :=
    LatticeCrypto.vectorNegacyclicRing_instCommRing
      (ZMod (2 ^ modulusExponent)) (2 ^ degreeExponent)
  letI := productionCommRing
  have hWeight : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels (extraCount + 1) secretSampler embed
          (RLWE.CenteredBinomial.sampler
            (2 ^ modulusExponent) (2 ^ degreeExponent) eta)) →
      CompilerNormalForm.SelectorsSucceed gadget (binarySelectors bitSelectors) context →
      ∀ level index,
        LatticeCrypto.cInfNorm
            ((@binarySelectors
                (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
                productionCommRing levels extraCount bitSelectors) level
              (sourceMasks (Full.sourceRowsAt context.sourceBatch level)) index) ≤ 1 := by
    intro context _hContext _hSuccess level index
    exact production_cInfNorm_binarySelectorWeights_le_one
      modulusExponent degreeExponent extraCount (bitSelectors level)
      (sourceMasks (Full.sourceRowsAt context.sourceBatch level)) index
  have hNoise :=
    SelectorNoise.Native.rgswMinusSecretAdvantage_centeredBinomialSource_widenedDiscreteGaussian_le_of_degree_pos
      (q := 2 ^ modulusExponent) (ringDegree := 2 ^ degreeExponent)
      (levels := levels) (sourceCount := extraCount + 1) (eta := eta)
      (pow_pos (by omega) degreeExponent) certificate secretSampler embed gadget
      (binarySelectors bitSelectors) distinguisher secretBound 1 hSecret hWeight
  have hFailure := contextSelectors_failure_le_challenge
    levels extraCount secretSampler embed
      (RLWE.CenteredBinomial.sampler
        (2 ^ modulusExponent) (2 ^ degreeExponent) eta)
      gadget bitSelectors
  have hFailureReal := ENNReal.toReal_mono probEvent_ne_top hFailure
  exact hNoise.trans (by
    gcongr)

/-- A complete binary selector gives the full finite-game `RGSW_S(-S)` bound.  The three terms
are, respectively, the explicit selector-failure probability, the widened-discrete-Gaussian
translation loss for norm-one weights, and ordinary batch-RLWE advantage under the narrow
centered-binomial source law.

This is intentionally conditional on the supplied selectors.  The function type and completeness
predicate do not assert polynomial running time; proving an efficient complete (or suitably
failure-bounded) inhomogeneous subset-sum/Ring-SIS algorithm remains the computational gap. -/
theorem production_rgswMinusSecretAdvantage_centeredBinomial_widenedDiscreteGaussian_le_of_completeBinarySelectors
    (modulusExponent degreeExponent levels extraCount eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ modulusExponent) alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 →
      SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    (gadget : Fin levels →
      SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    (bitSelectors : Fin levels → BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) extraCount)
    (hcomplete : ∀ level,
      IsCompleteBinarySelector (gadget level) (bitSelectors level))
    (distinguisher : Full.Distinguisher
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) levels)
    (secretBound : ℕ)
    (hSecret : ∀ secretValue, secretValue ∈ support secretSampler →
      LatticeCrypto.cInfNorm (embed secretValue 0) ≤ secretBound) :
    let sourceErrorSampler := RLWE.CenteredBinomial.sampler
      (2 ^ modulusExponent) (2 ^ degreeExponent) eta
    let wideningSampler := DiscreteGaussianSampler.ringSampler
      (2 ^ degreeExponent) certificate
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (Heterogeneous.convolutionSampler sourceErrorSampler wideningSampler)
        gadget distinguisher ≤
      ((levels : ℝ) *
          ((((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ) /
            (((2 ^ extraCount : ℕ) : ℝ) +
              (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ))) +
        (levels : ℝ) *
          ((((2 ^ degreeExponent : ℕ) : ℝ) *
            DiscreteGaussianSampler.scalarLinearShiftBound certificate
              (SelectorNoise.Native.inducedShiftBoundForDegree
                (2 ^ degreeExponent) (extraCount + 1) secretBound 1 eta)))) +
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
              (binarySelectors bitSelectors)
              (Full.restoreDistinguisher gadget distinguisher))) := by
  dsimp only
  let productionCommRing : CommRing
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) :=
    LatticeCrypto.vectorNegacyclicRing_instCommRing
      (ZMod (2 ^ modulusExponent)) (2 ^ degreeExponent)
  letI := productionCommRing
  have hWeight : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels (extraCount + 1) secretSampler embed
          (RLWE.CenteredBinomial.sampler
            (2 ^ modulusExponent) (2 ^ degreeExponent) eta)) →
      CompilerNormalForm.SelectorsSucceed gadget (binarySelectors bitSelectors) context →
      ∀ level index,
        LatticeCrypto.cInfNorm
            ((@binarySelectors
                (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
                productionCommRing levels extraCount bitSelectors) level
              (sourceMasks (Full.sourceRowsAt context.sourceBatch level)) index) ≤ 1 := by
    intro context _hContext _hSuccess level index
    exact production_cInfNorm_binarySelectorWeights_le_one
      modulusExponent degreeExponent extraCount (bitSelectors level)
      (sourceMasks (Full.sourceRowsAt context.sourceBatch level)) index
  have hNoise :=
    SelectorNoise.Native.rgswMinusSecretAdvantage_centeredBinomialSource_widenedDiscreteGaussian_le_of_degree_pos
      (q := 2 ^ modulusExponent) (ringDegree := 2 ^ degreeExponent)
      (levels := levels) (sourceCount := extraCount + 1) (eta := eta)
      (pow_pos (by omega) degreeExponent) certificate secretSampler embed gadget
      (binarySelectors bitSelectors) distinguisher secretBound 1 hSecret hWeight
  have hFailure :=
    production_contextSelectors_failure_toReal_le_levels_mul_card_div_add
      modulusExponent degreeExponent levels extraCount secretSampler embed
      (RLWE.CenteredBinomial.sampler
        (2 ^ modulusExponent) (2 ^ degreeExponent) eta)
      gadget bitSelectors hcomplete
  calc
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (Heterogeneous.convolutionSampler
          (RLWE.CenteredBinomial.sampler
            (2 ^ modulusExponent) (2 ^ degreeExponent) eta)
          (DiscreteGaussianSampler.ringSampler (2 ^ degreeExponent) certificate))
        gadget distinguisher ≤
      (Pr[fun context ↦
            ¬ CompilerNormalForm.SelectorsSucceed gadget
              (binarySelectors bitSelectors) context |
          CompilerNormalForm.contextSampler levels (extraCount + 1) secretSampler embed
            (RLWE.CenteredBinomial.sampler
              (2 ^ modulusExponent) (2 ^ degreeExponent) eta)].toReal +
        (levels : ℝ) *
          (((2 ^ degreeExponent : ℕ) : ℝ) *
            DiscreteGaussianSampler.scalarLinearShiftBound certificate
              (SelectorNoise.Native.inducedShiftBoundForDegree
                (2 ^ degreeExponent) (extraCount + 1) secretBound 1 eta))) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * (extraCount + 1) + TGSW.rowCount 1 levels)
            secretSampler embed
            (RLWE.CenteredBinomial.sampler
              (2 ^ modulusExponent) (2 ^ degreeExponent) eta))
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler := Heterogeneous.convolutionSampler
              (RLWE.CenteredBinomial.sampler
                (2 ^ modulusExponent) (2 ^ degreeExponent) eta)
              (DiscreteGaussianSampler.ringSampler (2 ^ degreeExponent) certificate))
            (extraErrorSampler :=
              DiscreteGaussianSampler.ringSampler (2 ^ degreeExponent) certificate)
            (Heterogeneous.reduction
              (targetErrorSampler := Heterogeneous.convolutionSampler
                (RLWE.CenteredBinomial.sampler
                  (2 ^ modulusExponent) (2 ^ degreeExponent) eta)
                (DiscreteGaussianSampler.ringSampler (2 ^ degreeExponent) certificate))
              (binarySelectors bitSelectors)
              (Full.restoreDistinguisher gadget distinguisher))) := hNoise
    _ ≤ _ := by
      gcongr

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BinarySelectorSecurity
