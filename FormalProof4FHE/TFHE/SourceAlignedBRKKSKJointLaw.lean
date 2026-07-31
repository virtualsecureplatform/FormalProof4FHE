/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BoundedMoment
import FormalProof4FHE.Probability.FiniteSurjectiveFiber
import FormalProof4FHE.TFHE.DirectSubsetKeyBRK
import FormalProof4FHE.TFHE.SourceAlignedNativeGadgetDistribution
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Source-Aligned BRK/KSK Joint-Law Theorems

This file formalizes the finite and algebraic content of
`sketch/source_aligned_brk_ksk_joint_law.tex`.

The concrete coefficient identity uses the two native TFHE coefficient conventions correctly:
ring masks and propagated factors use reciprocal coefficients, whereas extracted secrets and
ring bodies use ordinary coefficients.  It proves that the transpose of the induced scalar
gadget applied to the extracted ring secret is the ordinary coefficient vector of the complete
ring adjoint body.

The game layer composes one complete suffix-source constructor, the prefix-LWE constructor that
controls its random-source branch gap, and a second prefix-LWE constructor.  All source problems,
samplers, public constructors, and total-variation defects remain explicit.  Thus the final
theorem is a reduction theorem, not an unconditional assertion of RLWE or LWE hardness.

The native-compiler layer proves exact mask/body algebra, the support-cardinality obstruction to
fresh uniform masks, and the exact evaluator residual.  The analytic subgaussian tail remains a
proof-carrying finite certificate because the repository does not identify a concrete finite
sampler with a continuous Gaussian merely from covariance data.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.SourceAlignedBRKKSKJointLaw

noncomputable section

/-! ## Pairing-compatible coefficient scalarization -/

namespace Algebra

open SourceAlignedFactorPropagation
open SourceAlignedFactorPropagation.Extraction

/-- Ordinary coefficient scalarization used for extracted secrets and ring bodies.  This differs
from `extractVector`, which applies the reciprocal-coefficient convention to masks and factors. -/
abbrev bodyCoefficients {q degree rank : ℕ}
    (vector : Fin rank → RLWE.Rq q (degree + 1)) :
    Fin (rank * (degree + 1)) → ZMod q :=
  SampleExtraction.extractedSecret vector

/-- Pairing-compatible adjoint identity for the concretely induced scalar gadget.

If `A` collects ring masks as columns, then `Aᵀ z` is the complete vector of noiseless ring
bodies.  Its ordinary coefficient vector is exactly `Gᵀ ExtSecret(z)`, where `G` is obtained by
conjugating `A` through reciprocal-coefficient mask extraction. -/
theorem inducedScalarGadget_transpose_mulVec
    {q degree suffixRank factorRank : ℕ} [NeZero q]
    (ringGadget : Matrix (Fin suffixRank) (Fin factorRank)
      (RLWE.Rq q (degree + 1)))
    (suffixSecret : Fin suffixRank → RLWE.Rq q (degree + 1)) :
    (inducedScalarGadget ringGadget).transpose *ᵥ
        bodyCoefficients suffixSecret =
      bodyCoefficients (ringGadget.transpose *ᵥ suffixSecret) := by
  apply funext
  intro coordinate
  let basis : Fin (factorRank * (degree + 1)) → ZMod q := Pi.single coordinate 1
  let factor : Fin factorRank → RLWE.Rq q (degree + 1) :=
    (extractVectorAddEquiv q degree factorRank).symm basis
  have hfactor : extractVector factor = basis := by
    change extractVectorAddEquiv q degree factorRank factor = basis
    exact (extractVectorAddEquiv q degree factorRank).apply_symm_apply basis
  have hscalar :
      dotProduct basis
          ((inducedScalarGadget ringGadget).transpose *ᵥ
            bodyCoefficients suffixSecret) =
        dotProduct (bodyCoefficients suffixSecret)
          (inducedScalarGadget ringGadget *ᵥ basis) := by
    exact Matrix.dotProduct_transpose_mulVec
      (inducedScalarGadget ringGadget) basis (bodyCoefficients suffixSecret)
  have hcompatible :
      inducedScalarGadget ringGadget *ᵥ basis =
        extractVector (ringGadget *ᵥ factor) := by
    rw [← hfactor]
    exact inducedScalarGadget_compatible ringGadget factor
  have hring :
      dotProduct suffixSecret (ringGadget *ᵥ factor) =
        dotProduct (ringGadget.transpose *ᵥ suffixSecret) factor := by
    calc
      _ = dotProduct factor (ringGadget.transpose *ᵥ suffixSecret) :=
        (Matrix.dotProduct_transpose_mulVec ringGadget factor suffixSecret).symm
      _ = _ := dotProduct_comm _ _
  have hpairing :
      dotProduct (bodyCoefficients suffixSecret)
          (inducedScalarGadget ringGadget *ᵥ basis) =
        dotProduct basis
          (bodyCoefficients (ringGadget.transpose *ᵥ suffixSecret)) := by
    rw [hcompatible]
    rw [dotProduct_extractedSecret_extractVector]
    rw [hring]
    rw [← dotProduct_extractedSecret_extractVector
      (ringGadget.transpose *ᵥ suffixSecret) factor]
    rw [hfactor]
    exact dotProduct_comm _ _
  have heq := hscalar.trans hpairing
  simpa [basis, dotProduct, Pi.single_apply] using heq

end Algebra

/-! ## Complete-view two-source branch composition -/

namespace CompleteView

open DirectSubsetKeyBRK
open DirectSubsetKeyBRK.PublicViewConstructor

/-- Complete-vector error-replacement defect, including every retained correlated public
variable in `State`. -/
def completeVectorSmudgingDefect {State : Type}
    (derived prescribed : ProbComp State) : ℝ :=
  tvDist derived prescribed

/-- Deterministic assembly of the retained cloud-key view cannot amplify the complete-vector
smudging defect. -/
theorem completeVectorSmudging_postprocess_le
    {State View : Type} (assemble : State → View)
    (derived prescribed : ProbComp State) :
    tvDist (assemble <$> derived) (assemble <$> prescribed) ≤
      completeVectorSmudgingDefect derived prescribed := by
  exact JointSubsetKeyBRK.tvDist_postprocess_jointError_le
    assemble derived prescribed

/-- Select the first sampler on the real branch and the second sampler on the zero branch. -/
def branchView {View : Type} (real zero : ProbComp View) (branch : Bool) : ProbComp View :=
  if branch then real else zero

@[simp]
theorem branchView_true {View : Type} (real zero : ProbComp View) :
    branchView real zero true = real := by
  rfl

@[simp]
theorem branchView_false {View : Type} (real zero : ProbComp View) :
    branchView real zero false = zero := by
  rfl

/-- The two constructed views obtained when the outer constructor receives its uniform source. -/
def uniformConstructedTarget
    {Sample Secret Output Prefix View : Type} [Add Output]
    {problem : LearningWithErrors.Problem Sample Secret Output}
    {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}
    (constructor : PublicViewConstructor problem prefixSampler targetView) :
    Bool → ProbComp View :=
  fun branch ↦ constructedView prefixSampler
    (LearningWithErrors.uniformDistr problem) constructor.build branch

/-- Sharpen the public branch-constructor theorem by retaining the distinguisher's actual gap
between the two constructed uniform-source branches instead of upper-bounding it by their total
variation distance.  This is the computational branch-constructor lemma in the sketch. -/
theorem targetAdvantage_le_two_source_add_realErrors_add_uniformGap
    {Sample Secret Output Prefix View : Type} [Add Output]
    {problem : LearningWithErrors.Problem Sample Secret Output}
    {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        constructor.realError true + constructor.realError false +
        targetAdvantage (uniformConstructedTarget constructor) distinguisher := by
  let selectedOrientation := constructor.orientation distinguisher
  let realOne := constructedDecision prefixSampler (LearningWithErrors.distr problem)
    constructor.build true distinguisher
  let realZero := constructedDecision prefixSampler (LearningWithErrors.distr problem)
    constructor.build false distinguisher
  let uniformOne := constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
    constructor.build true distinguisher
  let uniformZero := constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
    constructor.build false distinguisher
  let targetOne := targetView true >>= distinguisher
  let targetZero := targetView false >>= distinguisher
  let realGap := orientedGap selectedOrientation realOne realZero
  let uniformGap := orientedGap selectedOrientation uniformOne uniformZero
  have hOrientation : if selectedOrientation then
      (Pr[= true | targetZero]).toReal ≤ (Pr[= true | targetOne]).toReal
    else (Pr[= true | targetOne]).toReal ≤ (Pr[= true | targetZero]).toReal := by
    exact constructor.orientation_le distinguisher
  have hRealOne : tvDist realOne targetOne ≤ constructor.realError true := by
    exact constructor.decisionRealDistance distinguisher true
  have hRealZero : tvDist realZero targetZero ≤ constructor.realError false := by
    exact constructor.decisionRealDistance distinguisher false
  have hGap :
      targetAdvantage targetView distinguisher - constructor.realError true -
          constructor.realError false ≤ realGap := by
    have h := FormalProof4FHE.BinaryGuessCheck.orientedAcceptanceGap_lowerBound_of_tvDist
      realOne realZero targetOne targetZero selectedOrientation
      (constructor.realError true) (constructor.realError false)
      hOrientation hRealOne hRealZero
    simpa only [targetAdvantage, realGap, selectedOrientation, targetOne, targetZero, orientedGap]
      using h
  have hUniformAbs :
      |uniformGap| = targetAdvantage (uniformConstructedTarget constructor) distinguisher := by
    unfold uniformGap orientedGap targetAdvantage uniformConstructedTarget
    by_cases horientation : selectedOrientation = true
    · rw [if_pos horientation]
      rfl
    · rw [if_neg horientation, abs_sub_comm]
      rfl
  have hAdvantage :
      LearningWithErrors.advantage problem (constructor.reduction distinguisher) =
        |realGap - uniformGap| / 2 := by
    simpa only [realGap, uniformGap, selectedOrientation, realOne, realZero, uniformOne,
      uniformZero] using constructor.reduction_advantage_eq distinguisher
  have hRealGap : realGap ≤ |realGap - uniformGap| + |uniformGap| := by
    have hFirst : realGap - uniformGap ≤ |realGap - uniformGap| := le_abs_self _
    have hSecond : uniformGap ≤ |uniformGap| := le_abs_self _
    linarith
  rw [hUniformAbs] at hRealGap
  linarith

/-- Compose the outer suffix-source reduction with a second public constructor that explains its
uniform-source branch gap using a prefix-LWE problem.  Both reductions act on the complete view;
there is no rowwise hybrid. -/
theorem targetAdvantage_le_two_sources_add_errors
    {SuffixSample SuffixSecret SuffixOutput SuffixPrefix : Type}
    {PrefixSample PrefixSecret PrefixOutput PrefixPrefix View : Type}
    [Add SuffixOutput] [Add PrefixOutput]
    {suffixProblem : LearningWithErrors.Problem
      SuffixSample SuffixSecret SuffixOutput}
    {prefixProblem : LearningWithErrors.Problem
      PrefixSample PrefixSecret PrefixOutput}
    {suffixPrefixSampler : ProbComp SuffixPrefix}
    {prefixPrefixSampler : ProbComp PrefixPrefix}
    {targetView : Bool → ProbComp View}
    (outer : PublicViewConstructor suffixProblem suffixPrefixSampler targetView)
    (inner : PublicViewConstructor prefixProblem prefixPrefixSampler
      (uniformConstructedTarget outer))
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage suffixProblem (outer.reduction distinguisher) +
      2 * LearningWithErrors.advantage prefixProblem (inner.reduction distinguisher) +
      outer.realError true + outer.realError false +
      inner.realError true + inner.realError false + inner.uniformError := by
  have houter :=
    targetAdvantage_le_two_source_add_realErrors_add_uniformGap outer distinguisher
  have hinner := inner.targetAdvantage_le_two_source_add_errors distinguisher
  linarith

/-- Three complete cloud-key endpoints used by the source-aligned proof. -/
structure AlignedViews (View : Type) where
  real : ProbComp View
  middle : ProbComp View
  zero : ProbComp View

namespace AlignedViews

def first {View : Type} (views : AlignedViews View) : Bool → ProbComp View :=
  branchView views.real views.middle

def second {View : Type} (views : AlignedViews View) : Bool → ProbComp View :=
  branchView views.middle views.zero

def endpoints {View : Type} (views : AlignedViews View) : Bool → ProbComp View :=
  branchView views.real views.zero

/-- Triangle inequality through the zero-BRK/real-KSK middle view. -/
theorem endpointAdvantage_le
    {View : Type} (views : AlignedViews View) (distinguisher : Distinguisher View) :
    targetAdvantage views.endpoints distinguisher ≤
      targetAdvantage views.first distinguisher +
        targetAdvantage views.second distinguisher := by
  exact ProbComp.boolDistAdvantage_triangle
    (views.real >>= distinguisher) (views.middle >>= distinguisher)
      (views.zero >>= distinguisher)

end AlignedViews

/-- Complete source-aligned joint-law composition.  The first hop uses one suffix-source
reduction and one prefix-source reduction for its random-source branch.  The second hop uses a
second prefix-source reduction.  Every constructor defect is visible exactly once. -/
theorem alignedJointSecurity
    {SuffixSample SuffixSecret SuffixOutput SuffixPrefix : Type}
    {PrefixSample₁ PrefixSecret₁ PrefixOutput₁ PrefixPrefix₁ : Type}
    {PrefixSample₂ PrefixSecret₂ PrefixOutput₂ PrefixPrefix₂ View : Type}
    [Add SuffixOutput] [Add PrefixOutput₁] [Add PrefixOutput₂]
    {suffixProblem : LearningWithErrors.Problem
      SuffixSample SuffixSecret SuffixOutput}
    {prefixProblem₁ : LearningWithErrors.Problem
      PrefixSample₁ PrefixSecret₁ PrefixOutput₁}
    {prefixProblem₂ : LearningWithErrors.Problem
      PrefixSample₂ PrefixSecret₂ PrefixOutput₂}
    {suffixPrefixSampler : ProbComp SuffixPrefix}
    {prefixPrefixSampler₁ : ProbComp PrefixPrefix₁}
    {prefixPrefixSampler₂ : ProbComp PrefixPrefix₂}
    (views : AlignedViews View)
    (suffixConstructor : PublicViewConstructor suffixProblem suffixPrefixSampler views.first)
    (randomPrefixConstructor : PublicViewConstructor prefixProblem₁ prefixPrefixSampler₁
      (uniformConstructedTarget suffixConstructor))
    (secondPrefixConstructor : PublicViewConstructor prefixProblem₂ prefixPrefixSampler₂
      views.second)
    (distinguisher : Distinguisher View) :
    targetAdvantage views.endpoints distinguisher ≤
      2 * LearningWithErrors.advantage suffixProblem
        (suffixConstructor.reduction distinguisher) +
      2 * LearningWithErrors.advantage prefixProblem₁
        (randomPrefixConstructor.reduction distinguisher) +
      2 * LearningWithErrors.advantage prefixProblem₂
        (secondPrefixConstructor.reduction distinguisher) +
      suffixConstructor.realError true + suffixConstructor.realError false +
      randomPrefixConstructor.realError true + randomPrefixConstructor.realError false +
      randomPrefixConstructor.uniformError +
      secondPrefixConstructor.realError true + secondPrefixConstructor.realError false +
      secondPrefixConstructor.uniformError := by
  have htriangle := views.endpointAdvantage_le distinguisher
  have hfirst := targetAdvantage_le_two_sources_add_errors
    suffixConstructor randomPrefixConstructor distinguisher
  have hsecond := secondPrefixConstructor.targetAdvantage_le_two_source_add_errors distinguisher
  linarith

/-- The paper bound when the two first real-branch errors are each at most the complete-vector
smudging defect, the random-source prefix constructor is exact, and every remaining auxiliary
defect is charged once in the second hop. -/
theorem alignedJointSecurity_le_smudging_aux
    {SuffixSample SuffixSecret SuffixOutput SuffixPrefix : Type}
    {PrefixSample₁ PrefixSecret₁ PrefixOutput₁ PrefixPrefix₁ : Type}
    {PrefixSample₂ PrefixSecret₂ PrefixOutput₂ PrefixPrefix₂ View : Type}
    [Add SuffixOutput] [Add PrefixOutput₁] [Add PrefixOutput₂]
    {suffixProblem : LearningWithErrors.Problem
      SuffixSample SuffixSecret SuffixOutput}
    {prefixProblem₁ : LearningWithErrors.Problem
      PrefixSample₁ PrefixSecret₁ PrefixOutput₁}
    {prefixProblem₂ : LearningWithErrors.Problem
      PrefixSample₂ PrefixSecret₂ PrefixOutput₂}
    {suffixPrefixSampler : ProbComp SuffixPrefix}
    {prefixPrefixSampler₁ : ProbComp PrefixPrefix₁}
    {prefixPrefixSampler₂ : ProbComp PrefixPrefix₂}
    (views : AlignedViews View)
    (suffixConstructor : PublicViewConstructor suffixProblem suffixPrefixSampler views.first)
    (randomPrefixConstructor : PublicViewConstructor prefixProblem₁ prefixPrefixSampler₁
      (uniformConstructedTarget suffixConstructor))
    (secondPrefixConstructor : PublicViewConstructor prefixProblem₂ prefixPrefixSampler₂
      views.second)
    (distinguisher : Distinguisher View) (smudging auxiliary : ℝ)
    (hSuffixReal : ∀ branch, suffixConstructor.realError branch ≤ smudging)
    (hRandomReal : ∀ branch, randomPrefixConstructor.realError branch = 0)
    (hRandomUniform : randomPrefixConstructor.uniformError = 0)
    (hSecondErrors : secondPrefixConstructor.realError true +
        secondPrefixConstructor.realError false +
        secondPrefixConstructor.uniformError ≤ auxiliary) :
    targetAdvantage views.endpoints distinguisher ≤
      2 * LearningWithErrors.advantage suffixProblem
        (suffixConstructor.reduction distinguisher) +
      2 * LearningWithErrors.advantage prefixProblem₁
        (randomPrefixConstructor.reduction distinguisher) +
      2 * LearningWithErrors.advantage prefixProblem₂
        (secondPrefixConstructor.reduction distinguisher) +
      2 * smudging + auxiliary := by
  have h := alignedJointSecurity views suffixConstructor randomPrefixConstructor
    secondPrefixConstructor distinguisher
  rw [hRandomReal true, hRandomReal false, hRandomUniform] at h
  have htrue := hSuffixReal true
  have hfalse := hSuffixReal false
  linarith

/-- Uniform hardness bounds give the simplified `2 ε_Z + 4 ε_P` conclusion. -/
theorem alignedJointSecurity_le_hardness
    {SuffixSample SuffixSecret SuffixOutput SuffixPrefix : Type}
    {PrefixSample₁ PrefixSecret₁ PrefixOutput₁ PrefixPrefix₁ : Type}
    {PrefixSample₂ PrefixSecret₂ PrefixOutput₂ PrefixPrefix₂ View : Type}
    [Add SuffixOutput] [Add PrefixOutput₁] [Add PrefixOutput₂]
    {suffixProblem : LearningWithErrors.Problem
      SuffixSample SuffixSecret SuffixOutput}
    {prefixProblem₁ : LearningWithErrors.Problem
      PrefixSample₁ PrefixSecret₁ PrefixOutput₁}
    {prefixProblem₂ : LearningWithErrors.Problem
      PrefixSample₂ PrefixSecret₂ PrefixOutput₂}
    {suffixPrefixSampler : ProbComp SuffixPrefix}
    {prefixPrefixSampler₁ : ProbComp PrefixPrefix₁}
    {prefixPrefixSampler₂ : ProbComp PrefixPrefix₂}
    (views : AlignedViews View)
    (suffixConstructor : PublicViewConstructor suffixProblem suffixPrefixSampler views.first)
    (randomPrefixConstructor : PublicViewConstructor prefixProblem₁ prefixPrefixSampler₁
      (uniformConstructedTarget suffixConstructor))
    (secondPrefixConstructor : PublicViewConstructor prefixProblem₂ prefixPrefixSampler₂
      views.second)
    (distinguisher : Distinguisher View) (epsilonSuffix epsilonPrefix smudging auxiliary : ℝ)
    (hSuffixReal : ∀ branch, suffixConstructor.realError branch ≤ smudging)
    (hRandomReal : ∀ branch, randomPrefixConstructor.realError branch = 0)
    (hRandomUniform : randomPrefixConstructor.uniformError = 0)
    (hSecondErrors : secondPrefixConstructor.realError true +
        secondPrefixConstructor.realError false +
        secondPrefixConstructor.uniformError ≤ auxiliary)
    (hSuffixHard : LearningWithErrors.advantage suffixProblem
      (suffixConstructor.reduction distinguisher) ≤ epsilonSuffix)
    (hPrefixHard₁ : LearningWithErrors.advantage prefixProblem₁
      (randomPrefixConstructor.reduction distinguisher) ≤ epsilonPrefix)
    (hPrefixHard₂ : LearningWithErrors.advantage prefixProblem₂
      (secondPrefixConstructor.reduction distinguisher) ≤ epsilonPrefix) :
    targetAdvantage views.endpoints distinguisher ≤
      2 * epsilonSuffix + 4 * epsilonPrefix + 2 * smudging + auxiliary := by
  have h := alignedJointSecurity_le_smudging_aux views suffixConstructor
    randomPrefixConstructor secondPrefixConstructor distinguisher smudging auxiliary
    hSuffixReal hRandomReal hRandomUniform hSecondErrors
  linarith

/-- Exact correlated-error specialization.  When the first-hop constructors reproduce the
derived BRK/KSK error correlation exactly, the complete-vector smudging term vanishes. -/
theorem alignedJointSecurity_correlated
    {SuffixSample SuffixSecret SuffixOutput SuffixPrefix : Type}
    {PrefixSample₁ PrefixSecret₁ PrefixOutput₁ PrefixPrefix₁ : Type}
    {PrefixSample₂ PrefixSecret₂ PrefixOutput₂ PrefixPrefix₂ View : Type}
    [Add SuffixOutput] [Add PrefixOutput₁] [Add PrefixOutput₂]
    {suffixProblem : LearningWithErrors.Problem
      SuffixSample SuffixSecret SuffixOutput}
    {prefixProblem₁ : LearningWithErrors.Problem
      PrefixSample₁ PrefixSecret₁ PrefixOutput₁}
    {prefixProblem₂ : LearningWithErrors.Problem
      PrefixSample₂ PrefixSecret₂ PrefixOutput₂}
    {suffixPrefixSampler : ProbComp SuffixPrefix}
    {prefixPrefixSampler₁ : ProbComp PrefixPrefix₁}
    {prefixPrefixSampler₂ : ProbComp PrefixPrefix₂}
    (views : AlignedViews View)
    (suffixConstructor : PublicViewConstructor suffixProblem suffixPrefixSampler views.first)
    (randomPrefixConstructor : PublicViewConstructor prefixProblem₁ prefixPrefixSampler₁
      (uniformConstructedTarget suffixConstructor))
    (secondPrefixConstructor : PublicViewConstructor prefixProblem₂ prefixPrefixSampler₂
      views.second)
    (distinguisher : Distinguisher View) (auxiliary : ℝ)
    (hSuffixReal : ∀ branch, suffixConstructor.realError branch = 0)
    (hRandomReal : ∀ branch, randomPrefixConstructor.realError branch = 0)
    (hRandomUniform : randomPrefixConstructor.uniformError = 0)
    (hSecondErrors : secondPrefixConstructor.realError true +
        secondPrefixConstructor.realError false +
        secondPrefixConstructor.uniformError ≤ auxiliary) :
    targetAdvantage views.endpoints distinguisher ≤
      2 * LearningWithErrors.advantage suffixProblem
        (suffixConstructor.reduction distinguisher) +
      2 * LearningWithErrors.advantage prefixProblem₁
        (randomPrefixConstructor.reduction distinguisher) +
      2 * LearningWithErrors.advantage prefixProblem₂
        (secondPrefixConstructor.reduction distinguisher) + auxiliary := by
  have h := alignedJointSecurity_le_smudging_aux views suffixConstructor
    randomPrefixConstructor secondPrefixConstructor distinguisher 0 auxiliary
    (fun branch ↦ by simp [hSuffixReal branch])
    hRandomReal hRandomUniform hSecondErrors
  linarith

end CompleteView

/-! ## Deterministic native compiler and evaluator coupling -/

namespace NativeCompiler

set_option linter.unusedSectionVars false

/-- Appending any deterministic public derivation to a view is data processing and cannot
increase statistical distance.  This is the precise information-theoretic content of saying that
publishing a compiled object alongside its native source is harmless. -/
theorem tvDist_append_deterministic_le
    {View Derived : Type} (derive : View → Derived)
    (left right : ProbComp View) :
    tvDist ((fun view ↦ (view, derive view)) <$> left)
        ((fun view ↦ (view, derive view)) <$> right) ≤ tvDist left right :=
  tvDist_map_le (fun view ↦ (view, derive view)) left right

/-! ### Uniform distributions supported on a public finite subset -/

section UniformSubset

variable {Omega : Type} [Fintype Omega] [DecidableEq Omega] [SampleableType Omega]

/-- Uniform sampling from a nonempty finite subset, embedded in the ambient type. -/
def uniformFinset (support : Finset Omega) [Nonempty support] : ProbComp Omega := by
  letI : SampleableType support := SampleableType.ofFintype _
  exact (fun value : support ↦ value.1) <$> ($ᵗ support)

/-- Exact point mass of `uniformFinset`. -/
theorem probOutput_uniformFinset
    (support : Finset Omega) [Nonempty support] (output : Omega) :
    Pr[= output | uniformFinset support] =
      if output ∈ support then (support.card : ENNReal)⁻¹ else 0 := by
  classical
  letI : SampleableType support := SampleableType.ofFintype _
  unfold uniformFinset
  rw [FormalProof4FHE.LeftoverHash.probOutput_map_uniform_eq_fiberCard]
  by_cases houtput : output ∈ support
  · rw [if_pos houtput]
    have hfilter :
        (Finset.univ.filter fun value : support ↦ (value : Omega) = output) =
          {⟨output, houtput⟩} := by
      ext value
      simp [Subtype.ext_iff]
    rw [hfilter]
    simp
  · rw [if_neg houtput]
    have hfilter :
        (Finset.univ.filter fun value : support ↦ (value : Omega) = output) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro value _ heq
      exact houtput (heq ▸ value.2)
    rw [hfilter]
    simp

/-- Uniform-on-subset versus ambient-uniform total variation is exactly the missing ambient
mass. -/
theorem tvDist_uniformFinset_uniform
    (support : Finset Omega) [Nonempty support] :
    tvDist (uniformFinset support) ($ᵗ Omega) =
      1 - (support.card : ℝ) / Fintype.card Omega := by
  classical
  rw [FormalProof4FHE.LeftoverHash.tvDist_eq_half_sum_abs]
  simp_rw [probOutput_uniformFinset]
  have hsupportPos : (0 : ℝ) < support.card := by
    have hnonempty : support.Nonempty := by
      obtain ⟨value, hvalue⟩ := (inferInstance : Nonempty support)
      exact ⟨value, hvalue⟩
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have homegaPos : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  have hcard : (support.card : ℝ) ≤ Fintype.card Omega := by
    exact_mod_cast Finset.card_le_univ support
  have hinSupport :
      ∀ output ∈ support,
        |(support.card : ENNReal)⁻¹.toReal -
            Pr[= output | ($ᵗ Omega : ProbComp Omega)].toReal| =
          (support.card : ℝ)⁻¹ - (Fintype.card Omega : ℝ)⁻¹ := by
    intro output _
    rw [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [abs_of_nonneg]
    exact sub_nonneg.mpr (by
      simpa only [one_div] using one_div_le_one_div_of_le hsupportPos hcard)
  have houtside :
      ∀ output ∉ support,
        |(0 : ENNReal).toReal -
            Pr[= output | ($ᵗ Omega : ProbComp Omega)].toReal| =
          (Fintype.card Omega : ℝ)⁻¹ := by
    intro output _
    rw [probOutput_uniformSample, ENNReal.toReal_zero, zero_sub, abs_neg,
      abs_of_nonneg, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    positivity
  let summand : Omega → ℝ := fun output ↦
    |(if output ∈ support then (support.card : ENNReal)⁻¹ else 0).toReal -
      Pr[= output | ($ᵗ Omega : ProbComp Omega)].toReal|
  have hsplit :
      (∑ output, summand output) =
        (∑ output ∈ (Finset.univ : Finset Omega).filter (fun value ↦ value ∈ support),
          summand output) +
        ∑ output ∈ (Finset.univ : Finset Omega).filter (fun value ↦ value ∉ support),
          summand output := by
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun value : Omega ↦ value ∈ support) summand).symm
  have hinside :
      (∑ output ∈ (Finset.univ : Finset Omega).filter (fun value ↦ value ∈ support),
          summand output) =
        support.card * ((support.card : ℝ)⁻¹ - (Fintype.card Omega : ℝ)⁻¹) := by
    have hfilter :
        (Finset.univ : Finset Omega).filter (fun value ↦ value ∈ support) = support := by
      ext value
      simp
    rw [hfilter]
    calc
      (∑ output ∈ support, summand output) =
          ∑ _output ∈ support,
            ((support.card : ℝ)⁻¹ - (Fintype.card Omega : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro output houtput
        dsimp only [summand]
        rw [if_pos houtput]
        exact hinSupport output houtput
      _ = support.card *
          ((support.card : ℝ)⁻¹ - (Fintype.card Omega : ℝ)⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have houtsideSum :
      (∑ output ∈ (Finset.univ : Finset Omega).filter (fun value ↦ value ∉ support),
          summand output) =
        (Fintype.card Omega - support.card) * (Fintype.card Omega : ℝ)⁻¹ := by
    calc
      (∑ output ∈ (Finset.univ : Finset Omega).filter (fun value ↦ value ∉ support),
          summand output) =
          ∑ _output ∈ (Finset.univ : Finset Omega).filter
              (fun value ↦ value ∉ support),
            (Fintype.card Omega : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro output houtput
        have hnot := (Finset.mem_filter.mp houtput).2
        dsimp only [summand]
        rw [if_neg hnot]
        exact houtside output hnot
      _ = ((Finset.univ : Finset Omega).filter
            (fun value ↦ value ∉ support)).card *
          (Fintype.card Omega : ℝ)⁻¹ := by
        simp
      _ = (Fintype.card Omega - support.card) *
          (Fintype.card Omega : ℝ)⁻¹ := by
        congr 1
        have hfilter :
            (Finset.univ : Finset Omega).filter (fun value ↦ value ∉ support) =
              Finset.univ \ support := by
          ext value
          simp
        rw [hfilter, Finset.card_sdiff_of_subset support.subset_univ]
        simp
        exact Nat.cast_sub (Finset.card_le_univ support)
  change (1 / 2 : ℝ) * ∑ output, summand output = _
  rw [hsplit, hinside, houtsideSum]
  field_simp
  ring

/-- Ambient finite support of the range of an additive homomorphism. -/
def rangeSupport
    {Domain Codomain : Type} [AddGroup Domain] [Fintype Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    (transform : Domain →+ Codomain) : Finset Codomain :=
  Finset.univ.filter fun output ↦ output ∈ transform.range

/-- The algebraic range subtype is equivalent to the subtype of its ambient support finset. -/
def rangeEquivSupport
    {Domain Codomain : Type} [AddGroup Domain] [Fintype Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    (transform : Domain →+ Codomain) :
    transform.range ≃ rangeSupport transform where
  toFun value := ⟨value.1, by
    simp only [rangeSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact value.2⟩
  invFun value := ⟨value.1, by simpa [rangeSupport] using value.2⟩
  left_inv value := by ext; rfl
  right_inv value := by ext; rfl

/-- The range support is nonempty because it contains zero. -/
theorem rangeSupport_nonempty
    {Domain Codomain : Type} [AddGroup Domain] [Fintype Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    (transform : Domain →+ Codomain) : Nonempty (rangeSupport transform) := by
  refine ⟨⟨0, ?_⟩⟩
  simp only [rangeSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨0, transform.map_zero⟩

/-- A uniform finite input mapped through an additive homomorphism is uniform on the ambient
support of its range. -/
theorem evalDist_map_uniform_addHom_eq_uniformFinset
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain] [SampleableType Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    [SampleableType Codomain]
    (transform : Domain →+ Codomain) :
    letI : Nonempty (rangeSupport transform) := rangeSupport_nonempty transform
    evalDist (transform <$> ($ᵗ Domain)) =
      evalDist (uniformFinset (rangeSupport transform)) := by
  letI : SampleableType transform.range := SampleableType.ofFintype _
  letI : Nonempty (rangeSupport transform) := rangeSupport_nonempty transform
  letI : SampleableType (rangeSupport transform) := SampleableType.ofFintype _
  have hrange :=
    JointSubsetKeyBRKRefined.evalDist_map_surjective_addHom_uniform
      transform.rangeRestrict (AddMonoidHom.rangeRestrict_surjective transform)
  have hambient := evalDist_map_eq_of_evalDist_eq hrange
    (fun value : transform.range ↦ (value : Codomain))
  have hequiv := evalDist_map_bijective_uniform_cross
    (α := transform.range) (β := rangeSupport transform)
    (rangeEquivSupport transform) (rangeEquivSupport transform).bijective
  have hequivAmbient := evalDist_map_eq_of_evalDist_eq hequiv
    (fun value : rangeSupport transform ↦ (value : Codomain))
  simp only [Functor.map_map] at hequivAmbient
  have hcoe' :
      (fun value : transform.range ↦
          ((rangeEquivSupport transform value : rangeSupport transform) : Codomain)) =
        fun value : transform.range ↦ (value : Codomain) := by
    funext value
    rfl
  rw [hcoe'] at hequivAmbient
  calc
    evalDist (transform <$> ($ᵗ Domain)) =
        evalDist ((fun value : transform.range ↦ (value : Codomain)) <$>
          ($ᵗ transform.range)) := by
      simpa only [Functor.map_map, Function.comp_apply,
        AddMonoidHom.coe_rangeRestrict] using hambient
    _ = evalDist (uniformFinset (rangeSupport transform)) := by
      simpa only [uniformFinset] using hequivAmbient

/-- Exact support-distance formula for a deterministic additive image of uniform. -/
theorem tvDist_map_uniform_addHom_eq
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain] [SampleableType Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    [SampleableType Codomain]
    (transform : Domain →+ Codomain) :
    tvDist (transform <$> ($ᵗ Domain)) ($ᵗ Codomain) =
      1 - (Fintype.card transform.range : ℝ) / Fintype.card Codomain := by
  letI : Nonempty (rangeSupport transform) := rangeSupport_nonempty transform
  have hdist := evalDist_map_uniform_addHom_eq_uniformFinset transform
  have htv :
      tvDist (transform <$> ($ᵗ Domain)) ($ᵗ Codomain) =
        tvDist (uniformFinset (rangeSupport transform)) ($ᵗ Codomain) := by
    unfold tvDist
    rw [hdist]
  rw [htv, tvDist_uniformFinset_uniform]
  congr 2
  have hcard :
      (rangeSupport transform).card = Fintype.card transform.range := by
    simpa only [Fintype.card_coe] using
      (Fintype.card_congr (rangeEquivSupport transform).symm)
  exact_mod_cast hcard

end UniformSubset

section Algebra

variable {R Prefix Suffix Native Aligned : Type} [CommRing R]
  [Fintype Prefix] [Fintype Suffix] [Fintype Native] [Fintype Aligned]

/-- Public masks produced by linearly compiling the native KSK rows. -/
def compiledMask
    (nativeMask : Matrix Prefix Native R) (compiler : Matrix Native Aligned R) :
    Matrix Prefix Aligned R :=
  nativeMask * compiler

/-- Native KSK body `Uᵀp + Hᵀs + η`. -/
def nativeBody
    (nativeMask : Matrix Prefix Native R) (nativeGadget : Matrix Suffix Native R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (error : Native → R) : Native → R :=
  nativeMask.transpose *ᵥ prefixSecret +
    nativeGadget.transpose *ᵥ suffixSecret + error

/-- Deterministically compile every native KSK body through the public matrix `D`. -/
def compiledBody (compiler : Matrix Native Aligned R) (body : Native → R) : Aligned → R :=
  compiler.transpose *ᵥ body

/-- Exact deterministic-compiler identity

`Dᵀ(Uᵀp + Hᵀs + η) = (UD)ᵀp + (HD)ᵀs + Dᵀη`. -/
theorem compiledBody_eq
    (nativeMask : Matrix Prefix Native R) (nativeGadget : Matrix Suffix Native R)
    (compiler : Matrix Native Aligned R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (error : Native → R) :
    compiledBody compiler
        (nativeBody nativeMask nativeGadget prefixSecret suffixSecret error) =
      (compiledMask nativeMask compiler).transpose *ᵥ prefixSecret +
        (nativeGadget * compiler).transpose *ᵥ suffixSecret +
        compiler.transpose *ᵥ error := by
  simp only [compiledBody, nativeBody, compiledMask, Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mulVec_mulVec,
    ← Matrix.transpose_mul]

/-- If `HD = G`, the deterministic compiler has the exact source-aligned noiseless message. -/
theorem compiledBody_eq_of_factorization
    (nativeMask : Matrix Prefix Native R) (nativeGadget : Matrix Suffix Native R)
    (alignedGadget : Matrix Suffix Aligned R) (compiler : Matrix Native Aligned R)
    (factorization : nativeGadget * compiler = alignedGadget)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (error : Native → R) :
    compiledBody compiler
        (nativeBody nativeMask nativeGadget prefixSecret suffixSecret error) =
      (compiledMask nativeMask compiler).transpose *ᵥ prefixSecret +
        alignedGadget.transpose *ᵥ suffixSecret + compiler.transpose *ᵥ error := by
  rw [compiledBody_eq, factorization]

/-- Public factorization residual `G - HD` for an approximate native compiler. -/
def compilerResidual
    (nativeGadget : Matrix Suffix Native R) (alignedGadget : Matrix Suffix Aligned R)
    (compiler : Matrix Native Aligned R) : Matrix Suffix Aligned R :=
  alignedGadget - nativeGadget * compiler

/-- Approximate compilation exposes exactly the missing residual-secret message. -/
theorem compiledBody_eq_with_residual
    (nativeMask : Matrix Prefix Native R) (nativeGadget : Matrix Suffix Native R)
    (alignedGadget : Matrix Suffix Aligned R) (compiler : Matrix Native Aligned R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (error : Native → R) :
    compiledBody compiler
        (nativeBody nativeMask nativeGadget prefixSecret suffixSecret error) =
      (compiledMask nativeMask compiler).transpose *ᵥ prefixSecret +
        alignedGadget.transpose *ᵥ suffixSecret -
        (compilerResidual nativeGadget alignedGadget compiler).transpose *ᵥ suffixSecret +
        compiler.transpose *ᵥ error := by
  rw [compiledBody_eq]
  unfold compilerResidual
  rw [Matrix.transpose_sub, Matrix.sub_mulVec]
  abel

end Algebra

/-! ### Exact support of deterministic mask compilation -/

section MaskSupport

variable {R Prefix Native Aligned : Type} [CommRing R]
  [Fintype R] [DecidableEq R] [SampleableType R]
  [Fintype Prefix] [DecidableEq Prefix]
  [Fintype Native] [DecidableEq Native]
  [Fintype Aligned] [DecidableEq Aligned]
  [SampleableType (Matrix Prefix Native R)]
  [SampleableType (Matrix Prefix Aligned R)]

/-- The one-row compiler `u ↦ uD`. -/
def rowCompilerAddHom (compiler : Matrix Native Aligned R) :
    (Native → R) →+ (Aligned → R) :=
  compiler.vecMulLinear.toAddMonoidHom

@[simp]
theorem rowCompilerAddHom_apply
    (compiler : Matrix Native Aligned R) (row : Native → R) :
    rowCompilerAddHom compiler row = row ᵥ* compiler :=
  rfl

/-- The complete public-mask compiler, regarded as an additive homomorphism. -/
def compiledMaskAddHom (compiler : Matrix Native Aligned R) :
    Matrix Prefix Native R →+ Matrix Prefix Aligned R where
  toFun nativeMask rowIndex := rowCompilerAddHom compiler (nativeMask rowIndex)
  map_zero' := by
    funext rowIndex
    exact map_zero (rowCompilerAddHom compiler)
  map_add' left right := by
    funext rowIndex
    change rowCompilerAddHom compiler (left rowIndex + right rowIndex) =
      rowCompilerAddHom compiler (left rowIndex) +
        rowCompilerAddHom compiler (right rowIndex)
    exact map_add (rowCompilerAddHom compiler) (left rowIndex) (right rowIndex)

@[simp]
theorem compiledMaskAddHom_apply
    (compiler : Matrix Native Aligned R) (nativeMask : Matrix Prefix Native R) :
    compiledMaskAddHom compiler nativeMask = compiledMask nativeMask compiler := by
  ext rowIndex aligned
  change (nativeMask rowIndex ᵥ* compiler) aligned =
    (nativeMask * compiler) rowIndex aligned
  rw [Matrix.mul_apply]
  rfl

/-- The range of complete row-wise compilation is the product of the one-row image. -/
noncomputable def compiledMaskRangeEquivRowRange
    (compiler : Matrix Native Aligned R) :
    (compiledMaskAddHom (Prefix := Prefix) compiler).range ≃
      (Prefix → (rowCompilerAddHom compiler).range) where
  toFun output rowIndex := ⟨output.1 rowIndex, by
    obtain ⟨nativeMask, hnativeMask⟩ := output.2
    refine ⟨nativeMask rowIndex, ?_⟩
    exact congrFun hnativeMask rowIndex⟩
  invFun output := ⟨fun rowIndex ↦ (output rowIndex).1, by
    let preimage : Matrix Prefix Native R := fun rowIndex ↦
      Classical.choose (output rowIndex).2
    refine ⟨preimage, ?_⟩
    funext rowIndex
    change rowCompilerAddHom compiler (preimage rowIndex) = (output rowIndex).1
    exact Classical.choose_spec (output rowIndex).2⟩
  left_inv output := by
    apply Subtype.ext
    rfl
  right_inv output := by
    funext rowIndex
    apply Subtype.ext
    rfl

/-- The complete compiler image has one independent copy of the row image per prefix row. -/
theorem card_compiledMaskAddHom_range_eq_rowRange_pow
    (compiler : Matrix Native Aligned R) :
    Fintype.card (compiledMaskAddHom (Prefix := Prefix) compiler).range =
      Fintype.card (rowCompilerAddHom compiler).range ^ Fintype.card Prefix := by
  rw [Fintype.card_congr (compiledMaskRangeEquivRowRange compiler),
    Fintype.card_fun]

/-- Exact statistical distance between a deterministically compiled uniform native mask and an
ambient-uniform aligned mask. -/
theorem tvDist_compiledMask_uniform_eq
    (compiler : Matrix Native Aligned R) :
    tvDist
        (compiledMaskAddHom (Prefix := Prefix) compiler <$>
          ($ᵗ Matrix Prefix Native R))
        ($ᵗ Matrix Prefix Aligned R) =
      1 - ((Fintype.card (rowCompilerAddHom compiler).range : ℝ) /
          Fintype.card (Aligned → R)) ^ Fintype.card Prefix := by
  calc
    tvDist
        (compiledMaskAddHom (Prefix := Prefix) compiler <$>
          ($ᵗ Matrix Prefix Native R))
        ($ᵗ Matrix Prefix Aligned R) =
        1 - (Fintype.card
            (compiledMaskAddHom (Prefix := Prefix) compiler).range : ℝ) /
          Fintype.card (Matrix Prefix Aligned R) :=
      tvDist_map_uniform_addHom_eq (compiledMaskAddHom compiler)
    _ = 1 - ((Fintype.card (rowCompilerAddHom compiler).range : ℝ) /
          Fintype.card (Aligned → R)) ^ Fintype.card Prefix := by
      rw [card_compiledMaskAddHom_range_eq_rowRange_pow]
      have hmatrix :
          Fintype.card (Matrix Prefix Aligned R) =
            (Fintype.card R ^ Fintype.card Aligned) ^ Fintype.card Prefix := by
        change Fintype.card (Prefix → Aligned → R) = _
        rw [Fintype.card_fun, Fintype.card_fun]
      rw [hmatrix]
      simp only [Fintype.card_fun, Nat.cast_pow]
      rw [div_pow]

/-- The same exact formula stated directly with matrix multiplication `U ↦ UD`. -/
theorem tvDist_compiledMask_uniform_eq_image_ratio
    (compiler : Matrix Native Aligned R) :
    tvDist
        ((fun nativeMask ↦ compiledMask nativeMask compiler) <$>
          ($ᵗ Matrix Prefix Native R))
        ($ᵗ Matrix Prefix Aligned R) =
      1 - ((Fintype.card (rowCompilerAddHom compiler).range : ℝ) /
          Fintype.card (Aligned → R)) ^ Fintype.card Prefix := by
  have h := tvDist_compiledMask_uniform_eq (Prefix := Prefix) compiler
  have hmap :
      (compiledMaskAddHom (Prefix := Prefix) compiler :
          Matrix Prefix Native R → Matrix Prefix Aligned R) =
        fun nativeMask ↦ compiledMask nativeMask compiler := by
    funext nativeMask
    exact compiledMaskAddHom_apply compiler nativeMask
  rw [hmap] at h
  exact h

/-- The row image cannot contain more points than the native row domain. -/
theorem card_rowCompilerAddHom_range_le
    (compiler : Matrix Native Aligned R) :
    Fintype.card (rowCompilerAddHom compiler).range ≤ Fintype.card (Native → R) := by
  exact Fintype.card_le_of_surjective
    (rowCompilerAddHom compiler).rangeRestrict
    (AddMonoidHom.rangeRestrict_surjective (rowCompilerAddHom compiler))

/-- Dimension-only lower bound for the compiled-mask support obstruction. -/
theorem tvDist_compiledMask_uniform_ge_domain_ratio
    (compiler : Matrix Native Aligned R) :
    1 - ((Fintype.card (Native → R) : ℝ) /
          Fintype.card (Aligned → R)) ^ Fintype.card Prefix ≤
      tvDist
        (compiledMaskAddHom (Prefix := Prefix) compiler <$>
          ($ᵗ Matrix Prefix Native R))
        ($ᵗ Matrix Prefix Aligned R) := by
  rw [tvDist_compiledMask_uniform_eq]
  have hcard :
      (Fintype.card (rowCompilerAddHom compiler).range : ℝ) ≤
        Fintype.card (Native → R) := by
    exact_mod_cast card_rowCompilerAddHom_range_le compiler
  have hambient : (0 : ℝ) < Fintype.card (Aligned → R) := by positivity
  have hratio :
      (Fintype.card (rowCompilerAddHom compiler).range : ℝ) /
          Fintype.card (Aligned → R) ≤
        (Fintype.card (Native → R) : ℝ) /
          Fintype.card (Aligned → R) := by
    exact div_le_div_of_nonneg_right hcard hambient.le
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      (Fintype.card (rowCompilerAddHom compiler).range : ℝ) /
        Fintype.card (Aligned → R)) hratio (Fintype.card Prefix)
  linarith

end MaskSupport

/-! ### Concrete finite-modulus form of the support barrier -/

section ZModMaskSupport

variable {q rowCount nativeWidth alignedWidth : ℕ} [NeZero q]

noncomputable local instance nativeZModMatrixSampleable :
    SampleableType (Matrix (Fin rowCount) (Fin nativeWidth) (ZMod q)) :=
  instSampleableTypePiFintype

noncomputable local instance alignedZModMatrixSampleable :
    SampleableType (Matrix (Fin rowCount) (Fin alignedWidth) (ZMod q)) :=
  instSampleableTypePiFintype

/-- Over `ZMod q`, the ambient row cardinality in the exact support formula is `q^M`. -/
theorem tvDist_compiledMask_zmod_uniform_eq
    (compiler : Matrix (Fin nativeWidth) (Fin alignedWidth) (ZMod q)) :
    tvDist
        ((fun nativeMask ↦ compiledMask nativeMask compiler) <$>
          ($ᵗ Matrix (Fin rowCount) (Fin nativeWidth) (ZMod q)))
        ($ᵗ Matrix (Fin rowCount) (Fin alignedWidth) (ZMod q)) =
      1 - ((Fintype.card (rowCompilerAddHom compiler).range : ℝ) /
          q ^ alignedWidth) ^ rowCount := by
  simpa only [Fintype.card_fin, Fintype.card_fun, ZMod.card, Nat.cast_pow] using
    (tvDist_compiledMask_uniform_eq_image_ratio
      (Prefix := Fin rowCount) compiler)

/-- Since a one-row image has at most `q^K` elements, width expansion forces the stated
dimension-only statistical-distance lower bound. -/
theorem tvDist_compiledMask_zmod_uniform_ge_width_ratio
    (compiler : Matrix (Fin nativeWidth) (Fin alignedWidth) (ZMod q)) :
    1 - (((q ^ nativeWidth : ℕ) : ℝ) /
          q ^ alignedWidth) ^ rowCount ≤
      tvDist
        (compiledMaskAddHom (Prefix := Fin rowCount) compiler <$>
          ($ᵗ Matrix (Fin rowCount) (Fin nativeWidth) (ZMod q)))
        ($ᵗ Matrix (Fin rowCount) (Fin alignedWidth) (ZMod q)) := by
  simpa only [Fintype.card_fin, Fintype.card_fun, ZMod.card, Nat.cast_pow] using
    (tvDist_compiledMask_uniform_ge_domain_ratio
      (Prefix := Fin rowCount) compiler)

/-- Arithmetic normalization of the width ratio.  This is the formal meaning of
`q^{-n(M-K)}` in the paper. -/
theorem zmod_width_ratio_pow_eq_inv
    (hq : 0 < q) (hwidth : nativeWidth ≤ alignedWidth) :
    ((((q ^ nativeWidth : ℕ) : ℝ) /
        q ^ alignedWidth) ^ rowCount) =
      ((q : ℝ) ^ ((alignedWidth - nativeWidth) * rowCount))⁻¹ := by
  have hqReal : (q : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_pow]
  have halignedPow :
      (q : ℝ) ^ alignedWidth =
        (q : ℝ) ^ nativeWidth * (q : ℝ) ^ (alignedWidth - nativeWidth) := by
    nth_rewrite 1 [show alignedWidth =
      nativeWidth + (alignedWidth - nativeWidth) by omega]
    rw [pow_add]
  rw [halignedPow]
  have hcancel :
      (q : ℝ) ^ nativeWidth /
          ((q : ℝ) ^ nativeWidth * (q : ℝ) ^ (alignedWidth - nativeWidth)) =
        ((q : ℝ) ^ (alignedWidth - nativeWidth))⁻¹ := by
    field_simp
  rw [hcancel, inv_pow, ← pow_mul]

/-- If the aligned width exceeds the native width, the public-mask marginal alone obeys the
paper's `1 - q^{-n(M-K)}` lower bound. -/
theorem tvDist_compiledMask_zmod_uniform_ge_inv_width_gap
    (compiler : Matrix (Fin nativeWidth) (Fin alignedWidth) (ZMod q))
    (hq : 0 < q) (hwidth : nativeWidth < alignedWidth) :
    1 - ((q : ℝ) ^ ((alignedWidth - nativeWidth) * rowCount))⁻¹ ≤
      tvDist
        (compiledMaskAddHom (Prefix := Fin rowCount) compiler <$>
          ($ᵗ Matrix (Fin rowCount) (Fin nativeWidth) (ZMod q)))
        ($ᵗ Matrix (Fin rowCount) (Fin alignedWidth) (ZMod q)) := by
  rw [← zmod_width_ratio_pow_eq_inv hq hwidth.le]
  exact tvDist_compiledMask_zmod_uniform_ge_width_ratio compiler

/-- With a nontrivial modulus, at least one public row, and strict width expansion, the compiled
mask law is not the ambient fresh-uniform law. -/
theorem evalDist_compiledMask_zmod_ne_uniform
    (compiler : Matrix (Fin nativeWidth) (Fin alignedWidth) (ZMod q))
    (hq : 1 < q) (hrows : 0 < rowCount)
    (hwidth : nativeWidth < alignedWidth) :
    evalDist
        (compiledMaskAddHom (Prefix := Fin rowCount) compiler <$>
          ($ᵗ Matrix (Fin rowCount) (Fin nativeWidth) (ZMod q))) ≠
      evalDist ($ᵗ Matrix (Fin rowCount) (Fin alignedWidth) (ZMod q)) := by
  have hdistance := tvDist_compiledMask_zmod_uniform_ge_inv_width_gap
    (rowCount := rowCount) compiler (by omega) hwidth
  have hexponent : 0 < (alignedWidth - nativeWidth) * rowCount :=
    Nat.mul_pos (Nat.sub_pos_iff_lt.mpr hwidth) hrows
  have hqReal : (1 : ℝ) < q := by exact_mod_cast hq
  have hpow :
      (1 : ℝ) < (q : ℝ) ^ ((alignedWidth - nativeWidth) * rowCount) :=
    one_lt_pow₀ hqReal (Nat.ne_of_gt hexponent)
  have hlower :
      0 < 1 - ((q : ℝ) ^ ((alignedWidth - nativeWidth) * rowCount))⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ hpow)
  intro heval
  have hzero :
      tvDist
          (compiledMaskAddHom (Prefix := Fin rowCount) compiler <$>
            ($ᵗ Matrix (Fin rowCount) (Fin nativeWidth) (ZMod q)))
          ($ᵗ Matrix (Fin rowCount) (Fin alignedWidth) (ZMod q)) = 0 :=
    (tvDist_eq_zero_iff _ _).2 heval
  rw [hzero] at hdistance
  linarith

end ZModMaskSupport

section Evaluator

variable {R Suffix Native Aligned : Type} [CommRing R]
  [Fintype Suffix] [Fintype Native] [Fintype Aligned]

/-- Difference between native decomposition of the final mask and linear compilation of the
source-aligned factor. -/
def evaluatorResidual
    (alignedGadget : Matrix Suffix Aligned R) (compiler : Matrix Native Aligned R)
    (decompose : (Suffix → R) → (Native → R)) (factor : Aligned → R) : Native → R :=
  decompose (alignedGadget *ᵥ factor) - compiler *ᵥ factor

/-- Under exact native decomposition and exact factorization, the evaluator residual lies in the
kernel of the native gadget. -/
theorem nativeGadget_mulVec_evaluatorResidual_eq_zero
    (nativeGadget : Matrix Suffix Native R) (alignedGadget : Matrix Suffix Aligned R)
    (compiler : Matrix Native Aligned R)
    (decompose : (Suffix → R) → (Native → R))
    (decompose_exact : ∀ vector, nativeGadget *ᵥ decompose vector = vector)
    (factorization : nativeGadget * compiler = alignedGadget)
    (factor : Aligned → R) :
    nativeGadget *ᵥ evaluatorResidual alignedGadget compiler decompose factor = 0 := by
  rw [evaluatorResidual, Matrix.mulVec_sub, decompose_exact, Matrix.mulVec_mulVec,
    factorization, sub_self]

/-- Difference between the native and compiled KSK error contributions. -/
theorem evaluatorError_sub_eq
    (alignedGadget : Matrix Suffix Aligned R) (compiler : Matrix Native Aligned R)
    (decompose : (Suffix → R) → (Native → R))
    (factor : Aligned → R) (error : Native → R) :
    dotProduct (decompose (alignedGadget *ᵥ factor)) error -
        dotProduct (compiler *ᵥ factor) error =
      dotProduct (evaluatorResidual alignedGadget compiler decompose factor) error := by
  rw [evaluatorResidual]
  rw [dotProduct_comm (decompose (alignedGadget *ᵥ factor) - compiler *ᵥ factor) error,
    dotProduct_sub]
  rw [dotProduct_comm error (decompose (alignedGadget *ᵥ factor)),
    dotProduct_comm error (compiler *ᵥ factor)]

/-- Residual of an approximate native decomposition, with convention `H Dec(v) = v - r(v)`. -/
def decompositionResidual
    (nativeGadget : Matrix Suffix Native R)
    (decompose : (Suffix → R) → (Native → R)) (vector : Suffix → R) : Suffix → R :=
  vector - nativeGadget *ᵥ decompose vector

/-- Exact approximate-gadget identity from the sketch:

`H ρ(x) = -r_H(Gx) + (G-HD)x`. -/
theorem nativeGadget_mulVec_evaluatorResidual
    (nativeGadget : Matrix Suffix Native R) (alignedGadget : Matrix Suffix Aligned R)
    (compiler : Matrix Native Aligned R)
    (decompose : (Suffix → R) → (Native → R)) (factor : Aligned → R) :
    nativeGadget *ᵥ evaluatorResidual alignedGadget compiler decompose factor =
      -decompositionResidual nativeGadget decompose (alignedGadget *ᵥ factor) +
        compilerResidual nativeGadget alignedGadget compiler *ᵥ factor := by
  rw [evaluatorResidual, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  simp only [decompositionResidual, compilerResidual, Matrix.sub_mulVec]
  abel

end Evaluator

/-! ### Finite subgaussian evaluator certificate -/

namespace EvaluatorTail

open FormalProof4FHE.BoundedMoment

/-- Exponential Markov inequality for a finite `ProbComp`.  This elementary finite lemma is the
only probabilistic ingredient needed to turn an MGF certificate into a Chernoff tail. -/
theorem probEvent_ge_le_exp_mul_expectation
    {Noise : Type} [Fintype Noise]
    (sampler : ProbComp Noise) (observable : Noise → ℝ)
    (threshold rate : ℝ) (hrate : 0 ≤ rate) :
    Pr[(fun noise ↦ threshold ≤ observable noise) | sampler].toReal ≤
      Real.exp (-rate * threshold) *
        expectation sampler (fun noise ↦ Real.exp (rate * observable noise)) := by
  classical
  rw [probEvent_eq_sum_fintype_ite]
  rw [ENNReal.toReal_sum]
  · simp only [apply_ite, ENNReal.toReal_zero]
    unfold expectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro noise _
    by_cases hnoise : threshold ≤ observable noise
    · rw [if_pos hnoise]
      have hexponent : 0 ≤ rate * (observable noise - threshold) :=
        mul_nonneg hrate (sub_nonneg.mpr hnoise)
      have hone : 1 ≤ Real.exp (rate * (observable noise - threshold)) :=
        Real.one_le_exp_iff.mpr hexponent
      have hprobability : 0 ≤ Pr[= noise | sampler].toReal := ENNReal.toReal_nonneg
      calc
        Pr[= noise | sampler].toReal ≤
            Pr[= noise | sampler].toReal *
              Real.exp (rate * (observable noise - threshold)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hprobability
        _ = Real.exp (-rate * threshold) *
            (Pr[= noise | sampler].toReal *
              Real.exp (rate * observable noise)) := by
          have hexpEq :
              Real.exp (rate * (observable noise - threshold)) =
                Real.exp (-rate * threshold) *
                  Real.exp (rate * observable noise) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexpEq]
          ring
    · rw [if_neg hnoise]
      positivity
  · intro noise _
    by_cases hnoise : threshold ≤ observable noise
    · simp [hnoise, probOutput_ne_top]
    · simp [hnoise]

/-- Quadratic covariance-proxy energy `ρᵀΣρ`. -/
def covarianceEnergy {Native : Type} [Fintype Native]
    (covariance : Matrix Native Native ℝ) (residual : Native → ℝ) : ℝ :=
  dotProduct residual (covariance *ᵥ residual)

/-- Proof-carrying finite version of the sketch's centered subgaussian premise.  `Noise` is finite,
while `noiseVector` interprets its outputs as real native-error vectors. -/
structure Certificate
    (Noise Native Factor : Type) [Fintype Noise] [Fintype Native]
    (sampler : ProbComp Noise) (noiseVector : Noise → Native → ℝ)
    (residual : Factor → Native → ℝ) (covariance : Matrix Native Native ℝ) where
  covarianceEnergy_nonneg : ∀ factor,
    0 ≤ covarianceEnergy covariance (residual factor)
  mgf_le : ∀ factor rate,
    expectation sampler (fun noise ↦
        Real.exp (rate * dotProduct (residual factor) (noiseVector noise))) ≤
      Real.exp (rate ^ 2 * covarianceEnergy covariance (residual factor) / 2)

/-- One-sided evaluator Chernoff bound obtained from the finite MGF certificate. -/
theorem Certificate.upperTail
    {Noise Native Factor : Type} [Fintype Noise] [Fintype Native]
    {sampler : ProbComp Noise} {noiseVector : Noise → Native → ℝ}
    {residual : Factor → Native → ℝ} {covariance : Matrix Native Native ℝ}
    (certificate : Certificate Noise Native Factor sampler noiseVector residual covariance)
    (factor : Factor) (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (hvariance : 0 < covarianceEnergy covariance (residual factor)) :
    Pr[(fun noise ↦ threshold ≤
        dotProduct (residual factor) (noiseVector noise)) | sampler].toReal ≤
      Real.exp (-(threshold ^ 2) /
        (2 * covarianceEnergy covariance (residual factor))) := by
  let variance := covarianceEnergy covariance (residual factor)
  let rate := threshold / variance
  have hrate : 0 ≤ rate := div_nonneg hthreshold hvariance.le
  have hmarkov := probEvent_ge_le_exp_mul_expectation sampler
    (fun noise ↦ dotProduct (residual factor) (noiseVector noise))
    threshold rate hrate
  calc
    Pr[(fun noise ↦ threshold ≤
        dotProduct (residual factor) (noiseVector noise)) | sampler].toReal ≤
        Real.exp (-rate * threshold) *
          expectation sampler (fun noise ↦ Real.exp
            (rate * dotProduct (residual factor) (noiseVector noise))) := hmarkov
    _ ≤ Real.exp (-rate * threshold) *
        Real.exp (rate ^ 2 * variance / 2) := by
      exact mul_le_mul_of_nonneg_left (certificate.mgf_le factor rate)
        (Real.exp_nonneg _)
    _ = Real.exp (-(threshold ^ 2) / (2 * variance)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [rate]
      field_simp
      ring

/-- The matching lower-tail estimate, using the same MGF certificate at the negative rate. -/
theorem Certificate.lowerTail
    {Noise Native Factor : Type} [Fintype Noise] [Fintype Native]
    {sampler : ProbComp Noise} {noiseVector : Noise → Native → ℝ}
    {residual : Factor → Native → ℝ} {covariance : Matrix Native Native ℝ}
    (certificate : Certificate Noise Native Factor sampler noiseVector residual covariance)
    (factor : Factor) (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (hvariance : 0 < covarianceEnergy covariance (residual factor)) :
    Pr[(fun noise ↦ threshold ≤
        -dotProduct (residual factor) (noiseVector noise)) | sampler].toReal ≤
      Real.exp (-(threshold ^ 2) /
        (2 * covarianceEnergy covariance (residual factor))) := by
  let variance := covarianceEnergy covariance (residual factor)
  let rate := threshold / variance
  have hrate : 0 ≤ rate := div_nonneg hthreshold hvariance.le
  have hmarkov := probEvent_ge_le_exp_mul_expectation sampler
    (fun noise ↦ -dotProduct (residual factor) (noiseVector noise))
    threshold rate hrate
  have hmgf :
      expectation sampler (fun noise ↦
          Real.exp (rate * -dotProduct (residual factor) (noiseVector noise))) ≤
        Real.exp (rate ^ 2 * variance / 2) := by
    have h := certificate.mgf_le factor (-rate)
    have hobservable :
        (fun noise ↦ Real.exp
          (rate * -dotProduct (residual factor) (noiseVector noise))) =
          fun noise ↦ Real.exp
            ((-rate) * dotProduct (residual factor) (noiseVector noise)) := by
      funext noise
      congr 1
      ring
    rw [hobservable]
    simpa only [neg_sq, variance] using h
  calc
    Pr[(fun noise ↦ threshold ≤
        -dotProduct (residual factor) (noiseVector noise)) | sampler].toReal ≤
        Real.exp (-rate * threshold) *
          expectation sampler (fun noise ↦ Real.exp
            (rate * -dotProduct (residual factor) (noiseVector noise))) := hmarkov
    _ ≤ Real.exp (-rate * threshold) *
        Real.exp (rate ^ 2 * variance / 2) := by
      exact mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-(threshold ^ 2) / (2 * variance)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [rate]
      field_simp
      ring

/-- Two-sided subgaussian evaluator bound from the two Chernoff tails. -/
theorem Certificate.absTail
    {Noise Native Factor : Type} [Fintype Noise] [Fintype Native]
    {sampler : ProbComp Noise} {noiseVector : Noise → Native → ℝ}
    {residual : Factor → Native → ℝ} {covariance : Matrix Native Native ℝ}
    (certificate : Certificate Noise Native Factor sampler noiseVector residual covariance)
    (factor : Factor) (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (hvariance : 0 < covarianceEnergy covariance (residual factor)) :
    Pr[(fun noise ↦ threshold ≤
        |dotProduct (residual factor) (noiseVector noise)|) | sampler].toReal ≤
      2 * Real.exp (-(threshold ^ 2) /
        (2 * covarianceEnergy covariance (residual factor))) := by
  let upperEvent := fun noise ↦ threshold ≤
    dotProduct (residual factor) (noiseVector noise)
  let lowerEvent := fun noise ↦ threshold ≤
    -dotProduct (residual factor) (noiseVector noise)
  have hunion := probEvent_or_le sampler upperEvent lowerEvent
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) hunion
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at hreal
  have hupper := certificate.upperTail factor threshold hthreshold hvariance
  have hlower := certificate.lowerTail factor threshold hthreshold hvariance
  have habs :
      Pr[(fun noise ↦ threshold ≤
          |dotProduct (residual factor) (noiseVector noise)|) | sampler].toReal ≤
        Pr[upperEvent | sampler].toReal + Pr[lowerEvent | sampler].toReal := by
    simpa only [upperEvent, lowerEvent, le_abs] using hreal
  linarith

/-- Union bound over a finite set of evaluator-reachable factors. -/
theorem Certificate.reachableUnionTail
    {Noise Native Factor : Type} [Fintype Noise] [Fintype Native]
    [DecidableEq Factor]
    {sampler : ProbComp Noise} {noiseVector : Noise → Native → ℝ}
    {residual : Factor → Native → ℝ} {covariance : Matrix Native Native ℝ}
    (certificate : Certificate Noise Native Factor sampler noiseVector residual covariance)
    (factors : Finset Factor) (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (hvariance : ∀ factor ∈ factors,
      0 < covarianceEnergy covariance (residual factor)) :
    Pr[(fun noise ↦ ∃ factor ∈ factors, threshold ≤
        |dotProduct (residual factor) (noiseVector noise)|) | sampler].toReal ≤
      2 * ∑ factor ∈ factors,
        Real.exp (-(threshold ^ 2) /
          (2 * covarianceEnergy covariance (residual factor))) := by
  let event := fun factor noise ↦ threshold ≤
    |dotProduct (residual factor) (noiseVector noise)|
  have hunion := probEvent_exists_finset_le_sum factors sampler event
  have hsumNotTop :
      (∑ factor ∈ factors, Pr[event factor | sampler]) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr fun factor _ ↦ probEvent_ne_top
  have hreal := ENNReal.toReal_mono hsumNotTop hunion
  rw [ENNReal.toReal_sum (fun factor _ ↦ probEvent_ne_top)] at hreal
  calc
    Pr[(fun noise ↦ ∃ factor ∈ factors, threshold ≤
        |dotProduct (residual factor) (noiseVector noise)|) | sampler].toReal ≤
        ∑ factor ∈ factors, Pr[event factor | sampler].toReal := by
      simpa only [event] using hreal
    _ ≤ ∑ factor ∈ factors,
        2 * Real.exp (-(threshold ^ 2) /
          (2 * covarianceEnergy covariance (residual factor))) := by
      apply Finset.sum_le_sum
      intro factor hfactor
      exact certificate.absTail factor threshold hthreshold
        (hvariance factor hfactor)
    _ = 2 * ∑ factor ∈ factors,
        Real.exp (-(threshold ^ 2) /
          (2 * covarianceEnergy covariance (residual factor))) := by
      rw [Finset.mul_sum]

end EvaluatorTail

end NativeCompiler

end

end FormalProof4FHE.TFHE.SourceAlignedBRKKSKJointLaw
