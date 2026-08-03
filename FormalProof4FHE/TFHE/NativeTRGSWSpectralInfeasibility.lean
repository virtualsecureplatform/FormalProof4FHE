/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWCompleteChannel
import FormalProof4FHE.TFHE.RingSquareUnitMaskObstruction

/-!
# Native TRGSW statistical spectral infeasibility

This module formalizes the finite theorems in `sketch/nativetrgsw.md`.  A typical-set exhaustive
decoder for the native suffix KSK recovers the shared prefix/suffix key except on the explicit
error-tail and false-candidate events.  Any subsequent BRK message decoder therefore predicts
every diagonal Walsh parity, forcing a large posterior spectral radius and an aggregate
high-frequency lower bound.  The module also records the exact marginal-security counterexample
and the two-hop random-message/zero-message endpoint.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.TFHE.NativeTRGSWSpectralInfeasibility

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open NativeTRGSWCompleteChannel
open Native.SharedRandomnessOneCycle
open TGSW.RingSquare.PreimageCompiler.MultiSourceCounting

/-! ## Uniform affine dot products -/

/-- A dot product having one unit coefficient, followed by an arbitrary translation, is uniform. -/
theorem evalDist_maskCombination_add_uniform_of_isUnit
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {count : ℕ} [SampleableType (Vectors R count)] [SampleableType R]
    (weight : Vectors R count) (selected : Fin count)
    (hunit : IsUnit (weight selected)) (offset : R) :
    evalDist ((fun masks ↦ maskCombination weight masks + offset) <$>
        ($ᵗ Vectors R count)) =
      evalDist ($ᵗ R) := by
  apply evalDist_ext
  intro output
  rw [probOutput_map]
  have hevent :
      (fun masks : Vectors R count ↦
        maskCombination weight masks + offset = output) =
      (fun masks ↦ maskCombination weight masks = output - offset) := by
    funext masks
    apply propext
    constructor <;> intro h
    · exact eq_sub_of_add_eq h
    · exact add_eq_of_eq_sub h
  rw [hevent,
    TGSW.RingSquare.PreimageCompiler.MultiSourceCounting.probEvent_maskCombination_eq_of_isUnit
      weight selected hunit (output - offset), probOutput_uniformSample]

/-- Evaluation-distribution equality transports every event probability. -/
theorem probEvent_eq_of_evalDist_eq
    {Output : Type} {left right : ProbComp Output}
    (h : evalDist left = evalDist right) (event : Output → Prop) :
    Pr[event | left] = Pr[event | right] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro output
  rw [evalDist_ext_iff.mp h output]

/-- Row-major family of independent public KSK columns. -/
def columnSampler (R : Type) (dimension rows : ℕ)
    [SampleableType (Fin dimension → R)] :
    ProbComp (Fin rows → Fin dimension → R) :=
  Fin.mOfFn rows fun _ ↦ $ᵗ (Fin dimension → R)

/-- Affine residual vector obtained by applying the same nonzero key difference to every
independent public column. -/
def affineResiduals
    {R : Type} [CommRing R] {dimension rows : ℕ}
    (weight : Fin dimension → R) (offset : Fin rows → R)
    (columns : Fin rows → Fin dimension → R) : Fin rows → R :=
  fun row ↦ maskCombination weight (columns row) + offset row

/-- Independent affine residuals are a uniform complete vector when the key difference has one
unit coordinate. -/
theorem affineResiduals_columnSampler_evalDist_eq_uniform
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension rows : ℕ} [SampleableType (Fin dimension → R)] [SampleableType R]
    (weight : Fin dimension → R) (selected : Fin dimension)
    (hunit : IsUnit (weight selected)) (offset : Fin rows → R) :
    evalDist (affineResiduals weight offset <$> columnSampler R dimension rows) =
      evalDist ($ᵗ (Fin rows → R)) := by
  rw [show affineResiduals weight offset <$> columnSampler R dimension rows =
      Fin.mOfFn rows (fun row ↦
        (fun column ↦ maskCombination weight column + offset row) <$>
          ($ᵗ (Fin dimension → R))) by
    exact FormalProof4FHE.FiniteProduct.map_fin_mOfFn rows
      (fun _ ↦ $ᵗ (Fin dimension → R))
      (fun row column ↦ maskCombination weight column + offset row)]
  calc
    _ = evalDist (Fin.mOfFn rows fun _ ↦ $ᵗ R) := by
      apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
      intro row
      exact evalDist_maskCombination_add_uniform_of_isUnit
        weight selected hunit (offset row)
    _ = _ := by
      simpa only [ProbComp.sampleIID] using
        (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform (alpha := R) rows)

/-- Exact probability that a uniform finite vector lies in a coordinatewise family of typical
sets. -/
theorem probEvent_uniform_forall_mem_eq
    {R : Type} [Fintype R] [DecidableEq R] [SampleableType R]
    (rows : ℕ) (typical : Fin rows → Finset R) :
    Pr[(fun values : Fin rows → R ↦ ∀ row, values row ∈ typical row) |
        Fin.mOfFn rows (fun _ ↦ $ᵗ R)] =
      ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal) := by
  rw [FormalProof4FHE.FiniteProduct.probEvent_fin_mOfFn_forall]
  change (∏ coordinate, Pr[(fun value ↦ value ∈ typical coordinate) | $ᵗ R]) =
    ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal)
  apply Finset.prod_congr rfl
  intro row _
  rw [probEvent_uniformSample]
  congr 1
  simp

/-- A wrong-key affine residual passes every coordinatewise typical-set check with the exact
product density. -/
theorem probEvent_affineResiduals_forall_mem_eq
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension rows : ℕ} [SampleableType (Fin dimension → R)] [SampleableType R]
    (weight : Fin dimension → R) (selected : Fin dimension)
    (hunit : IsUnit (weight selected)) (offset : Fin rows → R)
    (typical : Fin rows → Finset R) :
    Pr[(fun columns ↦ ∀ row, affineResiduals weight offset columns row ∈ typical row) |
        columnSampler R dimension rows] =
      ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal) := by
  change Pr[((fun values : Fin rows → R ↦
      ∀ row, values row ∈ typical row) ∘ affineResiduals weight offset) |
      columnSampler R dimension rows] = _
  rw [← probEvent_map (mx := columnSampler R dimension rows)
    (f := affineResiduals weight offset)
    (q := fun values ↦ ∀ row, values row ∈ typical row)]
  have hproduct :
      evalDist ($ᵗ (Fin rows → R)) =
        evalDist (Fin.mOfFn rows (fun _ ↦ $ᵗ R)) := by
    symm
    simpa only [ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := R) rows)
  calc
    _ = Pr[(fun values : Fin rows → R ↦ ∀ row, values row ∈ typical row) |
        Fin.mOfFn rows (fun _ ↦ $ᵗ R)] :=
      probEvent_eq_of_evalDist_eq
        ((affineResiduals_columnSampler_evalDist_eq_uniform weight selected hunit offset).trans
          hproduct)
        (fun values ↦ ∀ row, values row ∈ typical row)
    _ = _ := probEvent_uniform_forall_mem_eq rows typical

/-! ## Abstract native suffix-KSK rows -/

/-- The binary prefix used by the native suffix key-switch key. -/
abbrev Prefix (dimension : ℕ) := Fin dimension → Bool

/-- Coefficientwise difference of two embedded binary prefixes. -/
def prefixDifference
    {R : Type} [Ring R] {dimension : ℕ}
    (actual candidate : Prefix dimension) : Fin dimension → R :=
  fun coordinate ↦ embedBit (actual coordinate) - embedBit (candidate coordinate)

/-- Two distinct binary prefixes differ by `1` or `-1` in some coordinate.  That coefficient is
a unit over every nontrivial or trivial commutative ring alike. -/
theorem exists_isUnit_prefixDifference_of_ne
    {R : Type} [Ring R] {dimension : ℕ}
    (actual candidate : Prefix dimension) (hne : candidate ≠ actual) :
    ∃ coordinate, IsUnit (prefixDifference (R := R) actual candidate coordinate) := by
  obtain ⟨coordinate, hcoordinate⟩ := Function.ne_iff.mp hne
  refine ⟨coordinate, ?_⟩
  cases hactual : actual coordinate <;>
    cases hcandidate : candidate coordinate <;>
    simp [prefixDifference, embedBit, hactual, hcandidate] at hcoordinate ⊢

/-- Body of one native suffix-KSK row in the abstract model from the note. -/
def kskBody
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    (message : Fin rows → Suffix → R)
    (columns : Fin rows → Fin dimension → R)
    (actual : Prefix dimension) (suffix : Suffix)
    (error : Fin rows → R) (row : Fin rows) : R :=
  maskCombination (embedBinarySecret actual) (columns row) +
    message row suffix + error row

/-- Residual tested by the exhaustive decoder for a candidate prefix/suffix pair. -/
def candidateResidual
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    (message : Fin rows → Suffix → R)
    (columns : Fin rows → Fin dimension → R)
    (body : Fin rows → R)
    (candidate : Prefix dimension) (candidateSuffix : Suffix)
    (row : Fin rows) : R :=
  body row - maskCombination (embedBinarySecret candidate) (columns row) -
    message row candidateSuffix

/-- After fixing the actual error and the two suffix candidates, a wrong-prefix consistency
residual is precisely an affine residual with weight `actual - candidate`. -/
theorem candidateResidual_kskBody_eq_affineResiduals
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    (message : Fin rows → Suffix → R)
    (columns : Fin rows → Fin dimension → R)
    (actual candidate : Prefix dimension) (suffix candidateSuffix : Suffix)
    (error : Fin rows → R) :
    candidateResidual message columns
        (kskBody message columns actual suffix error) candidate candidateSuffix =
      affineResiduals (prefixDifference (R := R) actual candidate)
        (fun row ↦ message row suffix - message row candidateSuffix + error row) columns := by
  classical
  funext row
  unfold candidateResidual kskBody affineResiduals prefixDifference
    embedBinarySecret maskCombination
  have hsum :
      (∑ coordinate,
          (embedBit (actual coordinate) - embedBit (candidate coordinate)) *
            columns row coordinate) =
        (∑ coordinate, embedBit (actual coordinate) * columns row coordinate) -
          ∑ coordinate, embedBit (candidate coordinate) * columns row coordinate := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  rw [hsum]
  ring

/-- Exact fixed-candidate false-consistency probability for every wrong binary prefix. -/
theorem probEvent_wrongPrefix_candidateResidual_forall_mem_eq
    {R Suffix : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension rows : ℕ} [SampleableType (Fin dimension → R)] [SampleableType R]
    (message : Fin rows → Suffix → R)
    (actual candidate : Prefix dimension) (suffix candidateSuffix : Suffix)
    (error : Fin rows → R) (typical : Fin rows → Finset R)
    (hne : candidate ≠ actual) :
    Pr[(fun columns ↦ ∀ row,
        candidateResidual message columns
          (kskBody message columns actual suffix error) candidate candidateSuffix row ∈
            typical row) |
      columnSampler R dimension rows] =
      ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal) := by
  obtain ⟨selected, hunit⟩ :=
    exists_isUnit_prefixDifference_of_ne (R := R) actual candidate hne
  rw [show (fun columns ↦ ∀ row,
      candidateResidual message columns
        (kskBody message columns actual suffix error) candidate candidateSuffix row ∈
          typical row) =
      (fun columns ↦ ∀ row,
        affineResiduals (prefixDifference (R := R) actual candidate)
          (fun row ↦ message row suffix - message row candidateSuffix + error row)
          columns row ∈ typical row) by
    funext columns
    apply propext
    rw [candidateResidual_kskBody_eq_affineResiduals]]
  exact probEvent_affineResiduals_forall_mem_eq
    (prefixDifference (R := R) actual candidate) selected hunit _ typical

/-- A prefix/suffix candidate is consistent when every decoded row error is typical. -/
def kskConsistent
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    (typical : Fin rows → Finset R)
    (message : Fin rows → Suffix → R)
    (columns : Fin rows → Fin dimension → R) (body : Fin rows → R)
    (candidate : Prefix dimension) (candidateSuffix : Suffix) : Prop :=
  ∀ row, candidateResidual message columns body candidate candidateSuffix row ∈ typical row

/-- The actual error vector belongs to the product typical set. -/
def errorsTypical
    {R : Type} {rows : ℕ} (typical : Fin rows → Finset R)
    (error : Fin rows → R) : Prop :=
  ∀ row, error row ∈ typical row

/-- Unique-decoding separation for the public suffix gadget messages. -/
def SuffixSeparated
    {R Suffix : Type} [Add R] {rows : ℕ}
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R) : Prop :=
  ∀ actual candidate, candidate ≠ actual →
    ∃ row, ∀ actualError ∈ typical row, ∀ candidateError ∈ typical row,
      message row actual + actualError ≠ message row candidate + candidateError

/-- On the typical-error event, the true native KSK key pair is consistent. -/
theorem kskConsistent_actual_of_errorsTypical
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (columns : Fin rows → Fin dimension → R)
    (actual : Prefix dimension) (suffix : Suffix) (error : Fin rows → R)
    (herror : errorsTypical typical error) :
    kskConsistent typical message columns
      (kskBody message columns actual suffix error) actual suffix := by
  intro row
  change
    (kskBody message columns actual suffix error row -
      maskCombination (embedBinarySecret actual) (columns row) -
        message row suffix) ∈ typical row
  convert herror row using 1
  unfold kskBody
  ring

/-- Suffix separation eliminates every wrong suffix paired with the correct prefix. -/
theorem not_kskConsistent_samePrefix_wrongSuffix
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (columns : Fin rows → Fin dimension → R)
    (actual : Prefix dimension) (suffix candidateSuffix : Suffix)
    (error : Fin rows → R)
    (herror : errorsTypical typical error)
    (hseparated : SuffixSeparated typical message)
    (hne : candidateSuffix ≠ suffix) :
    ¬kskConsistent typical message columns
      (kskBody message columns actual suffix error) actual candidateSuffix := by
  intro hconsistent
  obtain ⟨row, hrow⟩ := hseparated suffix candidateSuffix hne
  apply hrow (error row) (herror row)
    (candidateResidual message columns
      (kskBody message columns actual suffix error) actual candidateSuffix row)
    (hconsistent row)
  unfold candidateResidual kskBody
  ring

/-- All candidate pairs whose prefix differs from the actual prefix. -/
def wrongPrefixCandidates
    (dimension : ℕ) (Suffix : Type) [Fintype Suffix] [DecidableEq Suffix]
    (actual : Prefix dimension) : Finset (Prefix dimension × Suffix) :=
  ((Finset.univ : Finset (Prefix dimension)).erase actual).product Finset.univ

theorem card_wrongPrefixCandidates
    (dimension : ℕ) (Suffix : Type) [Fintype Suffix] [DecidableEq Suffix]
    (actual : Prefix dimension) :
    (wrongPrefixCandidates dimension Suffix actual).card =
      (2 ^ dimension - 1) * Fintype.card Suffix := by
  classical
  simp [wrongPrefixCandidates]

/-- Union bound for all false KSK candidates having a wrong binary prefix. -/
theorem probEvent_exists_wrongPrefix_consistent_le
    {R Suffix : Type} [CommRing R] [Fintype R] [DecidableEq R]
    [Fintype Suffix] [DecidableEq Suffix]
    {dimension rows : ℕ} [SampleableType (Fin dimension → R)] [SampleableType R]
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (actual : Prefix dimension) (suffix : Suffix) (error : Fin rows → R) :
    Pr[(fun columns ↦ ∃ candidate ∈ wrongPrefixCandidates dimension Suffix actual,
        kskConsistent typical message columns
          (kskBody message columns actual suffix error) candidate.1 candidate.2) |
      columnSampler R dimension rows] ≤
      ((2 ^ dimension - 1) * Fintype.card Suffix : ℕ) *
        ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal) := by
  classical
  let candidates := wrongPrefixCandidates dimension Suffix actual
  let density : ENNReal :=
    ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal)
  have hfixed (candidate : Prefix dimension × Suffix) (hcandidate : candidate ∈ candidates) :
      Pr[(fun columns ↦ kskConsistent typical message columns
          (kskBody message columns actual suffix error) candidate.1 candidate.2) |
        columnSampler R dimension rows] = density := by
    have hne : candidate.1 ≠ actual := by
      exact (Finset.mem_erase.mp (Finset.mem_product.mp hcandidate).1).1
    exact probEvent_wrongPrefix_candidateResidual_forall_mem_eq
      message actual candidate.1 suffix candidate.2 error typical hne
  calc
    _ ≤ ∑ candidate ∈ candidates,
        Pr[(fun columns ↦ kskConsistent typical message columns
            (kskBody message columns actual suffix error) candidate.1 candidate.2) |
          columnSampler R dimension rows] :=
      probEvent_exists_finset_le_sum candidates (columnSampler R dimension rows)
        (fun candidate columns ↦ kskConsistent typical message columns
          (kskBody message columns actual suffix error) candidate.1 candidate.2)
    _ = ∑ _candidate ∈ candidates, density := by
      apply Finset.sum_congr rfl
      intro candidate hcandidate
      exact hfixed candidate hcandidate
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, card_wrongPrefixCandidates]

/-! ## Exhaustive recovery and the native KSK bound -/

/-- Public native KSK transcript: independent public columns and their noisy bodies. -/
structure KSKTranscript (R : Type) (dimension rows : ℕ) where
  columns : Fin rows → Fin dimension → R
  body : Fin rows → R

/-- Candidate consistency stated directly on a public transcript. -/
def transcriptConsistent
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (transcript : KSKTranscript R dimension rows)
    (candidate : Prefix dimension × Suffix) : Prop :=
  kskConsistent typical message transcript.columns transcript.body candidate.1 candidate.2

/-- The transcript uniquely identifies a specified prefix/suffix pair. -/
def uniquelyIdentifies
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (transcript : KSKTranscript R dimension rows)
    (actual : Prefix dimension) (suffix : Suffix) : Prop :=
  transcriptConsistent typical message transcript (actual, suffix) ∧
    ∀ candidate : Prefix dimension × Suffix,
      transcriptConsistent typical message transcript candidate →
        candidate = (actual, suffix)

/-- The specification-level exhaustive decoder: return the unique consistent pair, and return
`none` if the consistency relation does not have exactly one solution. -/
noncomputable def exhaustiveKSKDecoder
    {R Suffix : Type} [CommRing R] [Fintype Suffix] [DecidableEq Suffix]
    {dimension rows : ℕ}
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (transcript : KSKTranscript R dimension rows) : Option (Prefix dimension × Suffix) :=
  by
    classical
    exact if h : ∃! candidate : Prefix dimension × Suffix,
        transcriptConsistent typical message transcript candidate then
      some (Classical.choose h)
    else none

/-- A uniquely identifying transcript is decoded to its specified key pair. -/
theorem exhaustiveKSKDecoder_eq_some_of_uniquelyIdentifies
    {R Suffix : Type} [CommRing R] [Fintype Suffix] [DecidableEq Suffix]
    {dimension rows : ℕ}
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (transcript : KSKTranscript R dimension rows)
    (actual : Prefix dimension) (suffix : Suffix)
    (hunique : uniquelyIdentifies typical message transcript actual suffix) :
    exhaustiveKSKDecoder typical message transcript = some (actual, suffix) := by
  classical
  obtain ⟨hidentified, honly⟩ := hunique
  have hexists : ∃! candidate : Prefix dimension × Suffix,
      transcriptConsistent typical message transcript candidate := by
    refine ⟨(actual, suffix), hidentified, ?_⟩
    intro candidate hcandidate
    exact honly candidate hcandidate
  rw [exhaustiveKSKDecoder, dif_pos hexists]
  congr 1
  exact honly (Classical.choose hexists) (Classical.choose_spec hexists).1

/-- Good actual errors and absence of a wrong-prefix consistent pair make the true pair the
unique exhaustive-decoder solution.  Separation rules out the remaining same-prefix candidates. -/
theorem uniquelyIdentifies_of_errorsTypical_of_noWrongPrefix
    {R Suffix : Type} [CommRing R] [Fintype Suffix] [DecidableEq Suffix]
    {dimension rows : ℕ}
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (columns : Fin rows → Fin dimension → R)
    (actual : Prefix dimension) (suffix : Suffix) (error : Fin rows → R)
    (herror : errorsTypical typical error)
    (hseparated : SuffixSeparated typical message)
    (hnoWrong : ∀ candidate ∈ wrongPrefixCandidates dimension Suffix actual,
      ¬kskConsistent typical message columns
        (kskBody message columns actual suffix error) candidate.1 candidate.2) :
    uniquelyIdentifies typical message
      ⟨columns, kskBody message columns actual suffix error⟩ actual suffix := by
  classical
  let transcript : KSKTranscript R dimension rows :=
    ⟨columns, kskBody message columns actual suffix error⟩
  have hactual : transcriptConsistent typical message transcript (actual, suffix) :=
    kskConsistent_actual_of_errorsTypical typical message columns actual suffix error herror
  refine ⟨hactual, ?_⟩
  rintro ⟨candidate, candidateSuffix⟩ hconsistent
  by_cases hprefix : candidate = actual
  · subst candidate
    by_cases hsuffix : candidateSuffix = suffix
    · subst candidateSuffix
      rfl
    · exact False.elim
        (not_kskConsistent_samePrefix_wrongSuffix typical message columns actual
          suffix candidateSuffix error herror hseparated hsuffix hconsistent)
  · exact False.elim (hnoWrong (candidate, candidateSuffix)
      (by simp [wrongPrefixCandidates, hprefix]) hconsistent)

/-- Conditioned on a fixed good error vector, failure of unique identification is no more likely
than the union of all wrong-prefix consistency events. -/
theorem probEvent_not_uniquelyIdentifies_le_of_errorsTypical
    {R Suffix : Type} [CommRing R] [Fintype R] [DecidableEq R]
    [Fintype Suffix] [DecidableEq Suffix]
    {dimension rows : ℕ} [SampleableType (Fin dimension → R)] [SampleableType R]
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (actual : Prefix dimension) (suffix : Suffix) (error : Fin rows → R)
    (herror : errorsTypical typical error)
    (hseparated : SuffixSeparated typical message) :
    Pr[(fun columns ↦ ¬uniquelyIdentifies typical message
        ⟨columns, kskBody message columns actual suffix error⟩ actual suffix) |
      columnSampler R dimension rows] ≤
      ((2 ^ dimension - 1) * Fintype.card Suffix : ℕ) *
        ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal) := by
  calc
    _ ≤ Pr[(fun columns ↦ ∃ candidate ∈ wrongPrefixCandidates dimension Suffix actual,
        kskConsistent typical message columns
          (kskBody message columns actual suffix error) candidate.1 candidate.2) |
      columnSampler R dimension rows] := by
      apply probEvent_mono
      intro columns _ hfailure
      by_contra hnone
      apply hfailure
      exact uniquelyIdentifies_of_errorsTypical_of_noWrongPrefix
        typical message columns actual suffix error herror hseparated (by
          intro candidate hcandidate hconsistent
          exact hnone ⟨candidate, hcandidate, hconsistent⟩)
    _ ≤ _ := probEvent_exists_wrongPrefix_consistent_le
      typical message actual suffix error

/-- Sampling the complete native KSK transcript from an error sampler and independent uniform
public columns. -/
def nativeKSKTranscriptSampler
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    [SampleableType (Fin dimension → R)]
    (message : Fin rows → Suffix → R) (actual : Prefix dimension) (suffix : Suffix)
    (errorSampler : ProbComp (Fin rows → R)) : ProbComp (KSKTranscript R dimension rows) := do
  let error ← errorSampler
  let columns ← columnSampler R dimension rows
  return ⟨columns, kskBody message columns actual suffix error⟩

/-- Information-theoretic native KSK recovery theorem.  The error tail is paid once; on every
good error fiber, the false-candidate term is exactly the number of wrong-prefix/suffix pairs
times the product typical-set density. -/
theorem probEvent_exhaustiveKSKDecoder_failure_le
    {R Suffix : Type} [CommRing R] [Fintype R] [DecidableEq R]
    [Fintype Suffix] [DecidableEq Suffix]
    {dimension rows : ℕ} [SampleableType (Fin dimension → R)] [SampleableType R]
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (actual : Prefix dimension) (suffix : Suffix)
    (errorSampler : ProbComp (Fin rows → R)) (errorTail : ENNReal)
    (herrorTail : Pr[(fun error ↦ ¬errorsTypical typical error) | errorSampler] ≤ errorTail)
    (hseparated : SuffixSeparated typical message) :
    Pr[(fun transcript ↦ exhaustiveKSKDecoder typical message transcript ≠
          some (actual, suffix)) |
      nativeKSKTranscriptSampler message actual suffix errorSampler] ≤
      errorTail +
        ((2 ^ dimension - 1) * Fintype.card Suffix : ℕ) *
          ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal) := by
  let collision : ENNReal :=
    ((2 ^ dimension - 1) * Fintype.card Suffix : ℕ) *
      ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal)
  have hidentify :
      Pr[(fun transcript ↦ ¬uniquelyIdentifies typical message transcript actual suffix) |
        nativeKSKTranscriptSampler message actual suffix errorSampler] ≤
        Pr[(fun error ↦ ¬errorsTypical typical error) | errorSampler] + collision := by
    unfold nativeKSKTranscriptSampler
    apply probEvent_bind_le_probEvent_add
    intro error _ hgood
    simp only [not_not] at hgood
    rw [show (fun columns ↦
        pure (KSKTranscript.mk columns
          (kskBody message columns actual suffix error))) =
        pure ∘ (fun columns ↦ KSKTranscript.mk columns
          (kskBody message columns actual suffix error)) by rfl,
      probEvent_bind_pure_comp]
    exact probEvent_not_uniquelyIdentifies_le_of_errorsTypical
      typical message actual suffix error hgood hseparated
  calc
    _ ≤ Pr[(fun transcript ↦ ¬uniquelyIdentifies typical message transcript actual suffix) |
        nativeKSKTranscriptSampler message actual suffix errorSampler] := by
      apply probEvent_mono
      intro transcript _ hdecoder hunique
      exact hdecoder
        (exhaustiveKSKDecoder_eq_some_of_uniquelyIdentifies
          typical message transcript actual suffix hunique)
    _ ≤ Pr[(fun error ↦ ¬errorsTypical typical error) | errorSampler] + collision := hidentify
    _ ≤ errorTail + collision := add_le_add herrorTail le_rfl
    _ = _ := rfl

/-- Full native KSK experiment with independently sampled hidden prefix and suffix. -/
def nativeKSKKeyedSampler
    {R Suffix : Type} [CommRing R] {dimension rows : ℕ}
    [SampleableType (Fin dimension → R)]
    (message : Fin rows → Suffix → R)
    (prefixSampler : ProbComp (Prefix dimension)) (suffixSampler : ProbComp Suffix)
    (errorSampler : ProbComp (Fin rows → R)) :
    ProbComp ((Prefix dimension × Suffix) × KSKTranscript R dimension rows) := do
  let actual ← prefixSampler
  let suffix ← suffixSampler
  let transcript ← nativeKSKTranscriptSampler message actual suffix errorSampler
  return ((actual, suffix), transcript)

/-- The same recovery bound holds after independently sampling the hidden prefix and suffix,
because the fixed-secret estimate is uniform over every outer support fiber. -/
theorem probEvent_exhaustiveKSKDecoder_keyed_failure_le
    {R Suffix : Type} [CommRing R] [Fintype R] [DecidableEq R]
    [Fintype Suffix] [DecidableEq Suffix]
    {dimension rows : ℕ} [SampleableType (Fin dimension → R)] [SampleableType R]
    (typical : Fin rows → Finset R) (message : Fin rows → Suffix → R)
    (prefixSampler : ProbComp (Prefix dimension)) (suffixSampler : ProbComp Suffix)
    (errorSampler : ProbComp (Fin rows → R)) (errorTail : ENNReal)
    (herrorTail : Pr[(fun error ↦ ¬errorsTypical typical error) | errorSampler] ≤ errorTail)
    (hseparated : SuffixSeparated typical message) :
    Pr[(fun sample ↦ exhaustiveKSKDecoder typical message sample.2 ≠ some sample.1) |
      nativeKSKKeyedSampler message prefixSampler suffixSampler errorSampler] ≤
      errorTail +
        ((2 ^ dimension - 1) * Fintype.card Suffix : ℕ) *
          ∏ row, ((typical row).card : ENNReal) / (Fintype.card R : ENNReal) := by
  unfold nativeKSKKeyedSampler
  apply probEvent_bind_le_of_forall_le
  intro actual _
  apply probEvent_bind_le_of_forall_le
  intro suffix _
  rw [show (fun transcript ↦ pure ((actual, suffix), transcript)) =
      pure ∘ (fun transcript ↦ ((actual, suffix), transcript)) by rfl,
    probEvent_bind_pure_comp]
  exact probEvent_exhaustiveKSKDecoder_failure_le
    typical message actual suffix errorSampler errorTail herrorTail hseparated

/-- Native modulus specialization: the denominator in each row is literally `q`. -/
theorem probEvent_exhaustiveKSKDecoder_keyed_failure_le_zmod
    {q : ℕ} [NeZero q] {Suffix : Type}
    [Fintype Suffix] [DecidableEq Suffix]
    {dimension rows : ℕ}
    (typical : Fin rows → Finset (ZMod q))
    (message : Fin rows → Suffix → ZMod q)
    (prefixSampler : ProbComp (Prefix dimension)) (suffixSampler : ProbComp Suffix)
    (errorSampler : ProbComp (Fin rows → ZMod q)) (errorTail : ENNReal)
    (herrorTail : Pr[(fun error ↦ ¬errorsTypical typical error) | errorSampler] ≤ errorTail)
    (hseparated : SuffixSeparated typical message) :
    Pr[(fun sample ↦ exhaustiveKSKDecoder typical message sample.2 ≠ some sample.1) |
      nativeKSKKeyedSampler message prefixSampler suffixSampler errorSampler] ≤
      errorTail +
        ((2 ^ dimension - 1) * Fintype.card Suffix : ℕ) *
          ∏ row, ((typical row).card : ENNReal) / (q : ENNReal) := by
  simpa only [ZMod.card] using
    (probEvent_exhaustiveKSKDecoder_keyed_failure_le
      typical message prefixSampler suffixSampler errorSampler errorTail
      herrorTail hseparated)

/-! ## Adding BRK decoding failure -/

/-- A sampled full-recovery trial, keeping the hidden key/message and complete public view. -/
structure RecoveryTrial (Secret Message View : Type) where
  secret : Secret
  message : Message
  view : View

/-- Two-stage decoder: first recover the key, then decode the BRK message using that key. -/
def twoStageDecoder
    {Secret Message View : Type}
    (keyDecoder : View → Secret) (messageDecoder : Secret → View → Message)
    (view : View) : Secret × Message :=
  (keyDecoder view, messageDecoder (keyDecoder view) view)

/-- The elementary union bound `ε_dec ≤ ε_K + τ_B`: full two-stage failure implies either key
recovery failure or BRK failure under the correct key. -/
theorem probEvent_twoStageDecoder_failure_le
    {Secret Message View : Type} [DecidableEq Secret] [DecidableEq Message]
    (sampler : ProbComp (RecoveryTrial Secret Message View))
    (keyDecoder : View → Secret) (messageDecoder : Secret → View → Message) :
    Pr[(fun trial ↦ twoStageDecoder keyDecoder messageDecoder trial.view ≠
        (trial.secret, trial.message)) | sampler] ≤
      Pr[(fun trial ↦ keyDecoder trial.view ≠ trial.secret) | sampler] +
        Pr[(fun trial ↦ messageDecoder trial.secret trial.view ≠ trial.message) | sampler] := by
  calc
    _ ≤ Pr[(fun trial ↦ keyDecoder trial.view ≠ trial.secret ∨
        messageDecoder trial.secret trial.view ≠ trial.message) | sampler] := by
      apply probEvent_mono
      intro trial _ hfailure
      by_contra hnone
      simp only [not_or, not_ne_iff] at hnone
      apply hfailure
      simp [twoStageDecoder, hnone.1, hnone.2]
    _ ≤ _ := probEvent_or_le sampler _ _

/-- Insert separate key and correct-key BRK bounds into the two-stage union theorem. -/
theorem probEvent_twoStageDecoder_failure_le_add
    {Secret Message View : Type} [DecidableEq Secret] [DecidableEq Message]
    (sampler : ProbComp (RecoveryTrial Secret Message View))
    (keyDecoder : View → Secret) (messageDecoder : Secret → View → Message)
    (keyError messageError : ENNReal)
    (hkey : Pr[(fun trial ↦ keyDecoder trial.view ≠ trial.secret) | sampler] ≤ keyError)
    (hmessage : Pr[(fun trial ↦ messageDecoder trial.secret trial.view ≠ trial.message) |
      sampler] ≤ messageError) :
    Pr[(fun trial ↦ twoStageDecoder keyDecoder messageDecoder trial.view ≠
        (trial.secret, trial.message)) | sampler] ≤ keyError + messageError := by
  exact (probEvent_twoStageDecoder_failure_le sampler keyDecoder messageDecoder).trans
    (add_le_add hkey hmessage)

/-! ## Complete recovery forces a large posterior spectrum -/

/-- Boolean sign corresponding to the diagonal Walsh parity of the pair returned by a full
secret/message decoder. -/
def pairDecoderParityPredictor
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index)
    (decoder : View → BitVector Index × BitVector Index) (view : View) : Bool :=
  decide (walsh frequency (decoder view).1 * walsh frequency (decoder view).2 = -1)

/-- The predictor above has exactly the decoded pair's Walsh sign. -/
theorem decoderSign_pairDecoderParityPredictor
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index)
    (decoder : View → BitVector Index × BitVector Index) (view : View) :
    decoderSign (pairDecoderParityPredictor frequency decoder) view =
      walsh frequency (decoder view).1 * walsh frequency (decoder view).2 := by
  have hsecret := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp
    (abs_walsh frequency (decoder view).1)
  have hmessage := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp
    (abs_walsh frequency (decoder view).2)
  rcases hsecret with hsecret | hsecret <;>
    rcases hmessage with hmessage | hmessage <;>
    simp [pairDecoderParityPredictor, decoderSign, bitSign, hsecret, hmessage] <;>
    norm_num

/-- Uniform-input probability that a full decoder recovers both the secret and independent BRK
message from the complete channel. -/
def completeChannelPairDecoderSuccess
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (decoder : View → BitVector Index × BitVector Index) : ℝ :=
  (∑ secret : BitVector Index, ∑ message : BitVector Index, ∑ view : View,
      channel view secret message *
        if decoder view = (secret, message) then 1 else 0) / cubeSize Index ^ 2

/-- Correct recovery of the full pair implies correct prediction of every diagonal Walsh parity. -/
theorem completeChannelPairDecoderSuccess_le_paritySuccess
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (frequency : BitVector Index)
    (decoder : View → BitVector Index × BitVector Index) :
    completeChannelPairDecoderSuccess channel decoder ≤
      completeChannelDecoderSuccess channel frequency
        (pairDecoderParityPredictor frequency decoder) := by
  unfold completeChannelPairDecoderSuccess completeChannelDecoderSuccess
  apply div_le_div_of_nonneg_right _ (sq_nonneg (cubeSize Index))
  apply Finset.sum_le_sum
  intro secret _
  apply Finset.sum_le_sum
  intro message _
  apply Finset.sum_le_sum
  intro view _
  by_cases hdecoded : decoder view = (secret, message)
  · rw [if_pos hdecoded]
    have hsign :
        decoderSign (pairDecoderParityPredictor frequency decoder) view =
          walsh frequency secret * walsh frequency message := by
      rw [decoderSign_pairDecoderParityPredictor, hdecoded]
    rw [if_pos hsign]
  · rw [if_neg hdecoded]
    split <;> simp [hchannel view secret message]

/-- A full pair decoder with failure at most `ε` forces every posterior diagonal radius to be at
least `1 - 2ε`. -/
theorem one_sub_two_mul_le_posteriorSpectralRadius_of_pairDecoder
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (hnormalized : ∀ secret message, ∑ view, channel view secret message = 1)
    (decoder : View → BitVector Index × BitVector Index) (ε : ℝ)
    (hsuccess : 1 - ε ≤ completeChannelPairDecoderSuccess channel decoder)
    (frequency : BitVector Index) :
    1 - 2 * ε ≤ posteriorSpectralRadius (completeChannelViewMass channel)
      (completeChannelPosteriorParity channel frequency) := by
  apply one_sub_two_mul_le_posteriorSpectralRadius_of_decoder
    channel hchannel hnormalized frequency
      (pairDecoderParityPredictor frequency decoder) ε
  exact hsuccess.trans
    (completeChannelPairDecoderSuccess_le_paritySuccess channel hchannel frequency decoder)

/-- Summing a common pointwise lower bound over all high-degree frequencies multiplies it by the
exact number of such frequencies. -/
theorem card_highFrequencies_mul_le_sum_posteriorSpectralRadius
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View) (degree : ℕ) (lower : ℝ)
    (hlower : ∀ frequency ∈ highFrequencies Index degree,
      lower ≤ posteriorSpectralRadius (completeChannelViewMass channel)
        (completeChannelPosteriorParity channel frequency)) :
    ((highFrequencies Index degree).card : ℝ) * lower ≤
      ∑ frequency ∈ highFrequencies Index degree,
        posteriorSpectralRadius (completeChannelViewMass channel)
          (completeChannelPosteriorParity channel frequency) := by
  calc
    ((highFrequencies Index degree).card : ℝ) * lower =
        ∑ _frequency ∈ highFrequencies Index degree, lower := by simp
    _ ≤ _ := Finset.sum_le_sum fun frequency hfrequency ↦ hlower frequency hfrequency

/-- Exact real-valued high-frequency count: all nonzero characters minus the bounded-degree
nonzero characters. -/
theorem card_highFrequencies_eq_cube_sub_one_sub_binomialLowFrequencyCount
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    ((highFrequencies Index degree).card : ℝ) =
      (2 : ℝ) ^ Fintype.card Index - 1 - binomialLowFrequencyCount Index degree := by
  have hpartition := sum_nonzero_eq_sum_low_add_sum_high
    (Index := Index) degree (fun _frequency ↦ (1 : ℝ))
  have hlow := lowFrequencyCount_eq_binomialLowFrequencyCount Index degree
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hpartition
  have hnonzero : ((nonzeroFrequencies Index).card : ℝ) =
      (2 : ℝ) ^ Fintype.card Index - 1 := by
    classical
    simp [nonzeroFrequencies]
  rw [hnonzero, show ((lowFrequencies Index degree).card : ℝ) =
      binomialLowFrequencyCount Index degree by exact_mod_cast hlow] at hpartition
  linarith

/-- The sketch's spectral infeasibility theorem.  A full decoder with error `ε` gives the exact
binomial high-degree lower bound. -/
theorem binomial_spectralTail_lowerBound_of_pairDecoder
    {Index View : Type} [Fintype Index] [DecidableEq Index] [Fintype View]
    (channel : CompleteChannel Index View)
    (hchannel : ∀ view secret message, 0 ≤ channel view secret message)
    (hnormalized : ∀ secret message, ∑ view, channel view secret message = 1)
    (decoder : View → BitVector Index × BitVector Index) (ε : ℝ)
    (hsuccess : 1 - ε ≤ completeChannelPairDecoderSuccess channel decoder)
    (degree : ℕ) :
    ((2 : ℝ) ^ Fintype.card Index - 1 - binomialLowFrequencyCount Index degree) *
        (1 - 2 * ε) ≤
      ∑ frequency ∈ highFrequencies Index degree,
        posteriorSpectralRadius (completeChannelViewMass channel)
          (completeChannelPosteriorParity channel frequency) := by
  rw [← card_highFrequencies_eq_cube_sub_one_sub_binomialLowFrequencyCount]
  apply card_highFrequencies_mul_le_sum_posteriorSpectralRadius
  intro frequency _
  exact one_sub_two_mul_le_posteriorSpectralRadius_of_pairDecoder
    channel hchannel hnormalized decoder ε hsuccess frequency

/-! ## One complete heterogeneous affine source -/

/-- A complete-batch noisy linear source whose output may itself be a heterogeneous product
module (for example, ring-valued BRK rows together with scalar KSK rows).  The error sampler is a
single sampler for the entire output, so arbitrary within-batch BRK/KSK error correlations are
retained. -/
structure HeterogeneousAffineSource
    (Secret Challenge Output : Type) [Add Output] where
  secretSampler : ProbComp Secret
  challengeSampler : ProbComp Challenge
  errorSampler : ProbComp Output
  linear : Challenge → Secret → Output

/-- The complete real source `(A, A x + E)`. -/
def heterogeneousAffineReal
    {Secret Challenge Output : Type} [Add Output]
    (source : HeterogeneousAffineSource Secret Challenge Output) :
    ProbComp (Challenge × Output) := do
  let secret ← source.secretSampler
  let challenge ← source.challengeSampler
  let error ← source.errorSampler
  return (challenge, source.linear challenge secret + error)

/-- The complete common reference `(A,W)`, with one uniform element of the same heterogeneous
output module. -/
def heterogeneousAffineUniform
    {Secret Challenge Output : Type} [Add Output] [SampleableType Output]
    (source : HeterogeneousAffineSource Secret Challenge Output) :
    ProbComp (Challenge × Output) := do
  let challenge ← source.challengeSampler
  let value ← $ᵗ Output
  return (challenge, value)

/-- Complete-batch joint affine-source advantage.  This definition deliberately exposes no
separate BRK and KSK games and therefore incurs no rowwise or marginal hybrid. -/
noncomputable def heterogeneousAffineAdvantage
    {Secret Challenge Output : Type} [Add Output] [SampleableType Output]
    (source : HeterogeneousAffineSource Secret Challenge Output)
    (adversary : Challenge × Output → ProbComp Bool) : ℝ :=
  (heterogeneousAffineReal source >>= adversary).boolDistAdvantage
    (heterogeneousAffineUniform source >>= adversary)

/-- A named complete-batch hardness premise for a selected adversary class. -/
def HeterogeneousAffineHardAgainst
    {Secret Challenge Output : Type} [Add Output] [SampleableType Output]
    (source : HeterogeneousAffineSource Secret Challenge Output)
    (allowed : (Challenge × Output → ProbComp Bool) → Prop) (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary → heterogeneousAffineAdvantage source adversary ≤ bound

/-- Low-degree bounded leakage costs exactly the squared-bias factor from the sketch.  The two
challenge blocks represented by `leakageRemovalAdvantage` retain the same complete heterogeneous
source and hence all BRK/KSK correlations. -/
theorem jointAffine_leakageRemoval_binaryBound
    {Secret Leakage : Type} [Fintype Secret]
    [Fintype Leakage] [Nonempty Leakage] [SampleableType Leakage]
    (secretSampler : ProbComp Secret) (leakage : Secret → Leakage)
    (real ideal : Leakage → Secret → ProbComp Bool) (degree : ℕ) (delta : ℝ)
    (hcard : Fintype.card Leakage ≤ 2 ^ degree)
    (hremoval :
      RGSWCoefficientCircularSecurity.leakageRemovalAdvantage
        secretSampler ($ᵗ Leakage) real ideal ≤ delta) :
    RGSWCoefficientCircularSecurity.leakedAdvantage
        secretSampler leakage real ideal ≤
      Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) :=
  finiteRangeLeakageRemoval_binaryBound
    secretSampler leakage real ideal degree delta hcard hremoval

/-! ## Why separate marginals cannot prove joint security -/

/-- The information-theoretic counterexample transcript `(R, R xor B)`. -/
def marginalCounterexampleJoint (hidden : Bool) : ProbComp (Bool × Bool) :=
  (fun randomness ↦
    (randomness, LWE.MultiKeyAffine.maskedBit hidden randomness)) <$> ($ᵗ Bool)

/-- The first marginal is exactly uniform for either hidden bit. -/
theorem marginalCounterexample_first_evalDist (hidden : Bool) :
    evalDist (Prod.fst <$> marginalCounterexampleJoint hidden) =
      evalDist ($ᵗ Bool) := by
  simp [marginalCounterexampleJoint]

/-- The second marginal is also exactly uniform for either hidden bit. -/
theorem marginalCounterexample_second_evalDist (hidden : Bool) :
    evalDist (Prod.snd <$> marginalCounterexampleJoint hidden) =
      evalDist ($ᵗ Bool) := by
  rw [show Prod.snd <$> marginalCounterexampleJoint hidden =
      LWE.MultiKeyAffine.maskedBit hidden <$> ($ᵗ Bool) by
    simp [marginalCounterexampleJoint]]
  exact evalDist_map_bijective_uniform_cross
    (α := Bool) (β := Bool)
    (LWE.MultiKeyAffine.maskedBit hidden)
    ⟨fun left right heq ↦ by
        simpa using congrArg (LWE.MultiKeyAffine.maskedBit hidden) heq,
      fun output ↦ ⟨LWE.MultiKeyAffine.maskedBit hidden output, by simp⟩⟩

/-- Nevertheless the complete pair recovers the hidden bit with certainty. -/
theorem marginalCounterexample_joint_recovers
    (hidden randomness : Bool) :
    LWE.MultiKeyAffine.maskedBit randomness
      (LWE.MultiKeyAffine.maskedBit hidden randomness) = hidden := by
  cases hidden <;> cases randomness <;> rfl

/-- Distributional form: mapping the joint transcript through the public xor decoder gives the
point mass at the hidden bit. -/
theorem marginalCounterexample_decoder_evalDist (hidden : Bool) :
    evalDist ((fun transcript ↦
        LWE.MultiKeyAffine.maskedBit transcript.1 transcript.2) <$>
      marginalCounterexampleJoint hidden) = evalDist (pure hidden : ProbComp Bool) := by
  unfold marginalCounterexampleJoint
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  simp_rw [marginalCounterexample_joint_recovers hidden]
  simpa only using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      ($ᵗ Bool) (by simp) (pure hidden : ProbComp Bool))

/-! ## Random-message/zero-message endpoint -/

/-- Symmetry of Boolean distinguishing advantage, used to orient the common-reference hop. -/
theorem boolDistAdvantage_comm (left right : ProbComp Bool) :
    left.boolDistAdvantage right = right.boolDistAdvantage left := by
  unfold ProbComp.boolDistAdvantage
  rw [abs_sub_comm]

/-- Any random-message affine game and zero-message affine game that are each within `delta` of
one common reference are within `2*delta` of one another.  The first game may already include
independent sampling and normalization of the random message, so no additional assumption is
introduced at this endpoint. -/
theorem randomMessage_zero_endpoint_le_two_mul
    (randomMessage commonReference zeroMessage : ProbComp Bool) (delta : ℝ)
    (hrandom : randomMessage.boolDistAdvantage commonReference ≤ delta)
    (hzero : zeroMessage.boolDistAdvantage commonReference ≤ delta) :
    randomMessage.boolDistAdvantage zeroMessage ≤ 2 * delta := by
  have htriangle := ProbComp.boolDistAdvantage_triangle
    randomMessage commonReference zeroMessage
  rw [boolDistAdvantage_comm commonReference zeroMessage] at htriangle
  linarith

/-- Concrete two-hop form for independently sampled known messages followed by any Boolean
distinguisher. -/
theorem sampledKnownMessage_zero_endpoint_le_two_mul
    {Message View : Type}
    (messageSampler : ProbComp Message) (affineView : Message → ProbComp View)
    (zeroView commonReference : ProbComp View)
    (adversary : View → ProbComp Bool) (delta : ℝ)
    (hrandom :
      (messageSampler >>= fun message ↦ affineView message >>= adversary).boolDistAdvantage
        (commonReference >>= adversary) ≤ delta)
    (hzero :
      (zeroView >>= adversary).boolDistAdvantage
        (commonReference >>= adversary) ≤ delta) :
    (messageSampler >>= fun message ↦ affineView message >>= adversary).boolDistAdvantage
        (zeroView >>= adversary) ≤ 2 * delta :=
  randomMessage_zero_endpoint_le_two_mul
    (messageSampler >>= fun message ↦ affineView message >>= adversary)
    (commonReference >>= adversary) (zeroView >>= adversary) delta hrandom hzero

end

end FormalProof4FHE.TFHE.NativeTRGSWSpectralInfeasibility
