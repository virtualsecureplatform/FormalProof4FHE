/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SourceAlignedBRKKSKJointLaw
import FormalProof4FHE.TFHE.TFHEppSourceAlignedParameterScreen
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps

/-!
# Suffix-RLWE and Public-Seed Mask Expansion

This file formalizes the technical statements in `sketch/proofsuffixrlweprng.md`.

The known-prefix transport, the public-seed recognition attack, finite random-oracle table
programming, correlated-error cancellation, and complete-view loss accounting are theorems.
Hardness of the ternary suffix-subspace RLWE source and of a standard-model public-seed
structured-matrix LWE source remain explicit computational premises.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped ENNReal

namespace FormalProof4FHE.TFHE.SuffixRLWEPRG

noncomputable section

/-! ## Exact known-prefix transport -/

namespace KnownPrefix

open DirectSubsetKeyBRK

/-- Tag a complete batch transcript by the independently sampled prefix and add its public
contribution to every body. -/
def addOffset {R Prefix : Type} [Semiring R] {dimension samples : ℕ}
    (offset : Prefix → Fin dimension → R)
    (view : Prefix × LWE.BatchTranscript R dimension samples) :
    Prefix × LWE.BatchTranscript R dimension samples :=
  (view.1, addKnownOffsetTranscript (offset view.1) view.2)

/-- Remove the tagged known-prefix contribution. -/
def removeOffset {R Prefix : Type} [Ring R] {dimension samples : ℕ}
    (offset : Prefix → Fin dimension → R)
    (view : Prefix × LWE.BatchTranscript R dimension samples) :
    Prefix × LWE.BatchTranscript R dimension samples :=
  (view.1, removeKnownOffsetTranscript (offset view.1) view.2)

@[simp]
theorem removeOffset_addOffset {R Prefix : Type} [Ring R] {dimension samples : ℕ}
    (offset : Prefix → Fin dimension → R)
    (view : Prefix × LWE.BatchTranscript R dimension samples) :
    removeOffset offset (addOffset offset view) = view := by
  rcases view with ⟨prefixValue, transcript⟩
  simp [addOffset, removeOffset]

@[simp]
theorem addOffset_removeOffset {R Prefix : Type} [Ring R] {dimension samples : ℕ}
    (offset : Prefix → Fin dimension → R)
    (view : Prefix × LWE.BatchTranscript R dimension samples) :
    addOffset offset (removeOffset offset view) = view := by
  rcases view with ⟨prefixValue, transcript⟩
  simp [addOffset, removeOffset]

/-- The complete tagged known-prefix transform is a public permutation. -/
theorem addOffset_bijective {R Prefix : Type} [Ring R] {dimension samples : ℕ}
    (offset : Prefix → Fin dimension → R) :
    Function.Bijective
      (addOffset (samples := samples) offset) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨removeOffset offset, removeOffset_addOffset offset, addOffset_removeOffset offset⟩

/-- Pointwise real-source identity: adding the known prefix changes the hidden suffix secret
from `suffixSecret` to `suffixSecret + offset prefix` and leaves the complete error unchanged. -/
theorem addOffset_real {R Prefix : Type} [CommSemiring R] {dimension samples : ℕ}
    (offset : Prefix → Fin dimension → R) (prefixValue : Prefix)
    (suffixSecret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) :
    addOffset offset
        (prefixValue, challenge, vecMul suffixSecret challenge + error) =
      (prefixValue, challenge,
        vecMul (suffixSecret + offset prefixValue) challenge + error) := by
  simp only [addOffset]
  rw [addKnownOffsetTranscript_real]

/-- For a fixed prefix, adding its known contribution preserves a uniform complete transcript
exactly, even when the prefix tag is retained. -/
theorem fixedPrefix_uniform_evalDist {R Prefix : Type}
    [Ring R] [Fintype R] [SampleableType R]
    (dimension samples : ℕ) (offset : Prefix → Fin dimension → R) (prefixValue : Prefix) :
    evalDist ((fun transcript ↦
        (prefixValue, addKnownOffsetTranscript (offset prefixValue) transcript)) <$>
          ($ᵗ (LWE.BatchTranscript R dimension samples))) =
      evalDist ((fun transcript ↦ (prefixValue, transcript)) <$>
        ($ᵗ (LWE.BatchTranscript R dimension samples))) := by
  simpa only [Functor.map_map, Function.comp_apply] using
    evalDist_map_eq_of_evalDist_eq
      (addKnownOffsetTranscript_uniform_evalDist dimension samples (offset prefixValue))
      (fun transcript ↦ (prefixValue, transcript))

/-- Appending an arbitrary independently sampled prefix and applying its known translation
preserves the uniform transcript branch exactly. -/
theorem independentPrefix_uniform_evalDist {R Prefix : Type}
    [Ring R] [Fintype R] [SampleableType R]
    (dimension samples : ℕ) (prefixSampler : ProbComp Prefix)
    (offset : Prefix → Fin dimension → R) :
    evalDist (do
      let prefixValue ← prefixSampler
      let transcript ← $ᵗ (LWE.BatchTranscript R dimension samples)
      return addOffset offset (prefixValue, transcript)) =
    evalDist (do
      let prefixValue ← prefixSampler
      let transcript ← $ᵗ (LWE.BatchTranscript R dimension samples)
      return (prefixValue, transcript)) := by
  refine evalDist_bind_congr' prefixSampler fun prefixValue ↦ ?_
  simpa only [addOffset, bind_pure_comp] using
    fixedPrefix_uniform_evalDist dimension samples offset prefixValue

end KnownPrefix

/-! ## Exact recognition of a deterministic public-seed expansion -/

namespace PublicSeed

/-- The recognizably correlated public seed/expansion pair. -/
def real {Seed Output : Type} [SampleableType Seed]
    (expand : Seed → Output) : ProbComp (Seed × Output) := do
  let seed ← $ᵗ Seed
  return (seed, expand seed)

/-- The comparison distribution has an independent uniform seed and output. -/
def ideal {Seed Output : Type} [SampleableType Seed] [SampleableType Output] :
    ProbComp (Seed × Output) :=
  $ᵗ (Seed × Output)

/-- Efficient recomputation test for a public deterministic expander. -/
def recognizer {Seed Output : Type} [DecidableEq Output]
    (expand : Seed → Output) : DirectSubsetKeyBRK.Distinguisher (Seed × Output) :=
  fun pair ↦ pure (decide (pair.2 = expand pair.1))

/-- Recomputing the expansion accepts the correlated branch with probability one. -/
theorem probOutput_real_recognizer_true
    {Seed Output : Type} [Fintype Seed] [SampleableType Seed]
    [DecidableEq Output] (expand : Seed → Output) :
    Pr[= true | real expand >>= recognizer expand] = 1 := by
  simp [real, recognizer]

/-- Against an independent uniform output, the recomputation test accepts with exactly the
inverse output-space cardinality. -/
theorem probOutput_ideal_recognizer_true
    {Seed Output : Type} [Fintype Seed] [Fintype Output]
    [SampleableType Seed] [SampleableType Output] [DecidableEq Output]
    (expand : Seed → Output) :
    Pr[= true | (ideal : ProbComp (Seed × Output)) >>= recognizer expand] =
      (Fintype.card Output : ENNReal)⁻¹ := by
  classical
  change Pr[= true | ($ᵗ (Seed × Output)) >>= fun pair ↦
    pure (decide (pair.2 = expand pair.1))] = _
  rw [show (($ᵗ (Seed × Output)) >>= fun pair ↦
      pure (decide (pair.2 = expand pair.1))) =
      (fun pair : Seed × Output ↦ decide (pair.2 = expand pair.1)) <$>
        ($ᵗ (Seed × Output)) by
      simp [map_eq_bind_pure_comp]]
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq]
  rw [probEvent_uniformSample]
  have hfilter :
      (Finset.univ.filter fun pair : Seed × Output ↦
        pair.2 = expand pair.1).card = Fintype.card Seed := by
    let graphEmbedding : Seed ↪ Seed × Output :=
      ⟨fun seed ↦ (seed, expand seed), fun left right h ↦ congrArg Prod.fst h⟩
    have hset :
        Finset.univ.filter (fun pair : Seed × Output ↦
          pair.2 = expand pair.1) =
        Finset.univ.map graphEmbedding := by
      ext pair
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hpair
        refine ⟨pair.1, ?_⟩
        apply Prod.ext
        · rfl
        · exact hpair.symm
      · rintro ⟨seed, rfl⟩
        rfl
    rw [hset, Finset.card_map, Finset.card_univ]
  rw [hfilter, Fintype.card_prod, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _)),
    ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

/-- The two public-seed experiments, arranged as the branches expected by
`DirectSubsetKeyBRK.targetAdvantage`. -/
def comparisonViews {Seed Output : Type}
    [SampleableType Seed] [SampleableType Output]
    (expand : Seed → Output) : Bool → ProbComp (Seed × Output) :=
  fun branch ↦ if branch then real expand else ideal

/-- **Exact public-seed recognition advantage.**  Publishing a deterministic seed together
with its expansion is distinguishable from publishing the same seed with an independent
uniform output with advantage `1 - 1 / |Output|`. -/
theorem recognizer_advantage_eq
    {Seed Output : Type} [Fintype Seed] [Fintype Output]
    [SampleableType Seed] [SampleableType Output] [DecidableEq Output]
    (expand : Seed → Output) :
    DirectSubsetKeyBRK.targetAdvantage (comparisonViews expand) (recognizer expand) =
      1 - ((Fintype.card Output : ENNReal)⁻¹).toReal := by
  have hinverse_le_one :
      ((Fintype.card Output : ENNReal)⁻¹).toReal ≤ 1 := by
    rw [← probOutput_ideal_recognizer_true expand]
    exact ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one
  unfold DirectSubsetKeyBRK.targetAdvantage ProbComp.boolDistAdvantage comparisonViews
  simp only [Bool.false_eq_true, if_true, if_false]
  rw [probOutput_real_recognizer_true, probOutput_ideal_recognizer_true]
  simp only [ENNReal.toReal_one]
  rw [abs_of_nonneg (sub_nonneg.mpr hinverse_le_one)]

end PublicSeed

/-! ## Finite eager-table formulation of programmable random-oracle expansion -/

namespace ProgrammableRandomOracle

/-- Coordinates outside the image of the block embedded into a random-oracle table. -/
abbrev Complement {Coordinate Query : Type} (embed : Coordinate → Query) :=
  {query : Query // query ∉ Set.range embed}

/-- Split a complete answer table into its restriction along an injective block embedding and
the table on the complementary coordinates. -/
noncomputable def splitTableEquiv {Coordinate Query Answer : Type}
    (embed : Coordinate → Query) (injective : Function.Injective embed) :
    (Query → Answer) ≃
      (Coordinate → Answer) × (Complement embed → Answer) := by
  classical
  exact (Equiv.arrowCongr
      ((Equiv.Set.sumCompl (Set.range embed)).symm.trans
        ((Equiv.ofInjective embed injective).symm.sumCongr
          (Equiv.refl (Complement embed))))
      (Equiv.refl Answer)).trans
    (Equiv.sumArrowEquivProdArrow Coordinate (Complement embed) Answer)

/-- The first component of `splitTableEquiv` is exactly restriction along the embedded block. -/
@[simp]
theorem splitTableEquiv_fst {Coordinate Query Answer : Type}
    (embed : Coordinate → Query) (injective : Function.Injective embed)
    (table : Query → Answer) :
    (splitTableEquiv embed injective table).1 = table ∘ embed := by
  classical
  funext coordinate
  simp [splitTableEquiv, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]

/-- Honest eager-table experiment: draw one uniform full random-oracle table and expose its
embedded mask block to an arbitrary probabilistic continuation.  The continuation also receives
the complete table, so it models all subsequent oracle queries. -/
def honestTableView {Coordinate Query Answer View : Type}
    [SampleableType (Query → Answer)]
    (embed : Coordinate → Query)
    (finish : (Coordinate → Answer) → (Query → Answer) → ProbComp View) : ProbComp View := do
  let table ← $ᵗ (Query → Answer)
  finish (table ∘ embed) table

/-- Programmed eager-table experiment: draw the dense mask block together with an independent
complement table, reconstruct the unique full table, and run the same continuation. -/
def programmedTableView {Coordinate Query Answer View : Type}
    (embed : Coordinate → Query)
    [SampleableType ((Coordinate → Answer) × (Complement embed → Answer))]
    (injective : Function.Injective embed)
    (finish : (Coordinate → Answer) → (Query → Answer) → ProbComp View) : ProbComp View := do
  let pieces ← $ᵗ ((Coordinate → Answer) × (Complement embed → Answer))
  finish pieces.1 ((splitTableEquiv embed injective).symm pieces)

/-- **Exact finite programmable-random-oracle theorem.**  Sampling a uniform dense block and a
uniform complementary table, then programming the block, has exactly the same complete-view law
as sampling one honest uniform oracle table.  The arbitrary continuation may depend on both the
programmed block and the entire table. -/
theorem programmedTableView_evalDist_eq_honest
    {Coordinate Query Answer View : Type}
    [Finite Coordinate] [Finite Query] [Finite Answer] [Nonempty Answer]
    [SampleableType (Query → Answer)]
    (embed : Coordinate → Query)
    [SampleableType ((Coordinate → Answer) × (Complement embed → Answer))]
    (injective : Function.Injective embed)
    (finish : (Coordinate → Answer) → (Query → Answer) → ProbComp View) :
    evalDist (programmedTableView embed injective finish) =
      evalDist (honestTableView embed finish) := by
  let split : (Query → Answer) ≃
      (Coordinate → Answer) × (Complement embed → Answer) :=
    splitTableEquiv embed injective
  let continuation :
      ((Coordinate → Answer) × (Complement embed → Answer)) → ProbComp View :=
    fun pieces ↦ finish pieces.1 (split.symm pieces)
  have huniform :
      evalDist (split <$> ($ᵗ (Query → Answer))) =
        evalDist ($ᵗ ((Coordinate → Answer) × (Complement embed → Answer))) :=
    evalDist_map_bijective_uniform_cross
      (α := Query → Answer)
      (β := (Coordinate → Answer) × (Complement embed → Answer))
      split split.bijective
  have hbind :
      evalDist ((split <$> ($ᵗ (Query → Answer))) >>= continuation) =
        evalDist (($ᵗ ((Coordinate → Answer) × (Complement embed → Answer))) >>=
          continuation) := by
    rw [evalDist_bind, huniform, ← evalDist_bind]
  have hhonest :
      (($ᵗ (Query → Answer)) >>= fun table ↦ finish (table ∘ embed) table) =
        (split <$> ($ᵗ (Query → Answer))) >>= continuation := by
    rw [bind_map_left]
    simp only [split, splitTableEquiv_fst, Equiv.symm_apply_apply]
  rw [programmedTableView, honestTableView, hhonest]
  exact hbind.symm

/-- Prior guesses against a uniformly sampled seed are bounded by the number of guesses times
the inverse seed-space cardinality.  This is the first-fire term charged before programming a
fresh seed-indexed oracle block. -/
theorem priorQueryBad_uniform_le
    {Seed : Type} [Fintype Seed] [DecidableEq Seed] [SampleableType Seed]
    (queryCount : ℕ) (strategy : List Bool → Seed) :
    Pr[(fun bad : Bool ↦ bad = true) |
        hiddenReadMany ($ᵗ Seed) queryCount strategy] ≤
      (queryCount : ENNReal) * (Fintype.card Seed : ENNReal)⁻¹ := by
  apply probEvent_hiddenReadMany_le
  intro seed
  rw [probOutput_uniformSample]

end ProgrammableRandomOracle

/-! ## Complete-view compactness accounting -/

namespace WholeView

open DirectSubsetKeyBRK

/-- Replacing compact views by dense views on both branches costs the sum of the two
complete-view total-variation defects.  The hypothesis deliberately concerns the whole public
view; closeness of the mask marginal alone is not enough. -/
theorem compactAdvantage_le_dense_add
    {View : Type} (compact dense : Bool → ProbComp View)
    (distinguisher : Distinguisher View) (epsilonTrue epsilonFalse : ℝ)
    (htrue : tvDist (compact true) (dense true) ≤ epsilonTrue)
    (hfalse : tvDist (compact false) (dense false) ≤ epsilonFalse) :
    targetAdvantage compact distinguisher ≤
      targetAdvantage dense distinguisher + epsilonTrue + epsilonFalse := by
  let compactTrue := compact true >>= distinguisher
  let compactFalse := compact false >>= distinguisher
  let denseTrue := dense true >>= distinguisher
  let denseFalse := dense false >>= distinguisher
  have htrueDecision : compactTrue.boolDistAdvantage denseTrue ≤ epsilonTrue := by
    exact (abs_probOutput_toReal_sub_le_tvDist compactTrue denseTrue).trans
      ((tvDist_bind_right_le distinguisher (compact true) (dense true)).trans htrue)
  have hfalseDecision : denseFalse.boolDistAdvantage compactFalse ≤ epsilonFalse := by
    exact (abs_probOutput_toReal_sub_le_tvDist denseFalse compactFalse).trans
      ((tvDist_bind_right_le distinguisher (dense false) (compact false)).trans
        ((tvDist_comm (compact false) (dense false)) ▸ hfalse))
  have hfirst := ProbComp.boolDistAdvantage_triangle compactTrue denseTrue compactFalse
  have hsecond := ProbComp.boolDistAdvantage_triangle denseTrue denseFalse compactFalse
  unfold targetAdvantage
  change compactTrue.boolDistAdvantage compactFalse ≤
    denseTrue.boolDistAdvantage denseFalse + epsilonTrue + epsilonFalse
  linarith

end WholeView

/-! ## Shared-error cancellation -/

namespace CorrelatedError

/-- The cancellation statement from the suffix/seeded-mask proof, exposed without any
independence hypothesis on the transcript-dependent factor or the reused BRK error. -/
theorem reusedError_cancels
    {R Factor : Type} [CommRing R] [Fintype Factor]
    (message : R) (factor brkError freshError : Factor → R) :
    message + dotProduct factor brkError -
        dotProduct factor (brkError + freshError) =
      message - dotProduct factor freshError := by
  exact TFHEppSourceAlignedParameterScreen.CorrelatedCorrectness.error_pairing_cancels
    message factor brkError freshError

end CorrelatedError

/-! ## Conditional suffix/seeded-mask complete-view theorem -/

namespace ConditionalSecurity

open DirectSubsetKeyBRK
open DirectSubsetKeyBRK.PublicViewConstructor
open SourceAlignedBRKKSKJointLaw.CompleteView

/-- **Conditional suffix/seeded-mask theorem.**  Once the complete-view suffix constructor and
the two complete-view prefix constructors satisfy their stated source-hardness bounds, and all
remaining constructor defects total at most `auxiliary`, the endpoint advantage has exactly the
three-source loss stated in the proof note.  In particular, each hardness term is charged once
per branch, not once per row or mask entry. -/
theorem endpointAdvantage_le
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
    (distinguisher : Distinguisher View)
    (epsilonSuffix epsilonPrefix₁ epsilonPrefix₂ auxiliary : ℝ)
    (hSuffixReal : ∀ branch, suffixConstructor.realError branch = 0)
    (hRandomReal : ∀ branch, randomPrefixConstructor.realError branch = 0)
    (hRandomUniform : randomPrefixConstructor.uniformError = 0)
    (hSecondErrors : secondPrefixConstructor.realError true +
        secondPrefixConstructor.realError false +
        secondPrefixConstructor.uniformError ≤ auxiliary)
    (hSuffixHard : LearningWithErrors.advantage suffixProblem
      (suffixConstructor.reduction distinguisher) ≤ epsilonSuffix)
    (hPrefixHard₁ : LearningWithErrors.advantage prefixProblem₁
      (randomPrefixConstructor.reduction distinguisher) ≤ epsilonPrefix₁)
    (hPrefixHard₂ : LearningWithErrors.advantage prefixProblem₂
      (secondPrefixConstructor.reduction distinguisher) ≤ epsilonPrefix₂) :
    targetAdvantage views.endpoints distinguisher ≤
      2 * epsilonSuffix + 2 * epsilonPrefix₁ + 2 * epsilonPrefix₂ + auxiliary := by
  have h := SourceAlignedBRKKSKJointLaw.CompleteView.alignedJointSecurity_correlated
    views suffixConstructor randomPrefixConstructor secondPrefixConstructor distinguisher
    auxiliary hSuffixReal hRandomReal hRandomUniform hSecondErrors
  linarith

/-- When both prefix source advantages use a common bound, their total contribution is
`4 * epsilonPrefix`. -/
theorem endpointAdvantage_le_commonPrefix
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
    (distinguisher : Distinguisher View)
    (epsilonSuffix epsilonPrefix auxiliary : ℝ)
    (hSuffixReal : ∀ branch, suffixConstructor.realError branch = 0)
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
      2 * epsilonSuffix + 4 * epsilonPrefix + auxiliary := by
  have h := endpointAdvantage_le views suffixConstructor randomPrefixConstructor
    secondPrefixConstructor distinguisher epsilonSuffix epsilonPrefix epsilonPrefix auxiliary
    hSuffixReal hRandomReal hRandomUniform hSecondErrors hSuffixHard hPrefixHard₁ hPrefixHard₂
  linarith

end ConditionalSecurity

end

end FormalProof4FHE.TFHE.SuffixRLWEPRG
