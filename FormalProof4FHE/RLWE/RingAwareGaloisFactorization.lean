/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.MaskedGalois
import FormalProof4FHE.LWE.ParallelBatch
import FormalProof4FHE.SubspaceLWE.Security

/-!
# Ring-aware factorization path for Galois KDM

This file checks a direct ring-aware route from ordinary common-secret RLWE samples to Galois
evaluation-key rows.  Besides one primary row `(A, A*S + e)`, give the reduction auxiliary
ordinary rows `(C_i, C_i*S + f_i)`.  If public coefficients `r_i` satisfy

`sum_i r_i * sigma(C_i) = g`,

then the reduction can add the automorphed auxiliary bodies and obtain

`A*S + g*sigma(S) + e + sum_i r_i*sigma(f_i)`.

The uniform branch is exact because the primary body is uniform and is only translated by a
function of the auxiliary transcript.  Thus the construction is a genuine ordinary-RLWE
reduction, not an automorphism-KDM assumption in disguise.

It also exposes the two remaining obstacles precisely:

* no total factorizer can represent a nonzero gadget weight on the all-zero auxiliary mask; and
* even on successful masks, the induced error contains the factorization coefficients.

The final theorems isolate these costs in one explicit factorization/noise gap.  Making that gap
small with an efficient short factorizer is the cryptographic part still missing.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.RingAwareGaloisFactorization

noncomputable section

open GaloisKDM

/-! ## Ordinary source batch and public compiler -/

/-- Auxiliary public ring masks, grouped by target row. -/
abbrev AuxiliaryMask (R : Type) (rows : ℕ) (Aux : Type) :=
  Fin rows → Aux → R

/-- Auxiliary bodies and errors have the same shape as the auxiliary masks. -/
abbrev AuxiliaryBody (R : Type) (rows : ℕ) (Aux : Type) :=
  Fin rows → Aux → R

/-- One primary ordinary row per target row, plus auxiliary ordinary rows. -/
abbrev SourceChallenge (R : Type) (rows : ℕ) (Aux : Type) :=
  Challenge R rows × AuxiliaryMask R rows Aux

/-- Primary and auxiliary ordinary-RLWE bodies. -/
abbrev SourceOutput (R : Type) (rows : ℕ) (Aux : Type) :=
  Output R rows × AuxiliaryBody R rows Aux

/-- Complete ordinary source transcript. -/
abbrev SourceTranscript (R : Type) (rows : ℕ) (Aux : Type) :=
  SourceChallenge R rows Aux × SourceOutput R rows Aux

/-- A factorizer sees only public auxiliary masks and returns public ring coefficients. -/
abbrev Factorizer (R : Type) (rows : ℕ) (Aux : Type) :=
  AuxiliaryMask R rows Aux → AuxiliaryMask R rows Aux

/-- Weight represented by one factorizer row after applying its public automorphism. -/
def representedWeight {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (auxiliaryMask : AuxiliaryMask R rows Aux) (row : Fin rows) : R :=
  ∑ index, factorizer auxiliaryMask row index *
    spec.automorphism row (auxiliaryMask row index)

/-- The challenge-dependent Galois specification synthesized by a factorizer. -/
def representedSpec {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (auxiliaryMask : AuxiliaryMask R rows Aux) : Spec R rows where
  automorphism := spec.automorphism
  weight := representedWeight spec factorizer auxiliaryMask

/-- A public auxiliary-mask family is successful when it represents every requested gadget
weight simultaneously. -/
def Good {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (auxiliaryMask : AuxiliaryMask R rows Aux) : Prop :=
  ∀ row, representedWeight spec factorizer auxiliaryMask row = spec.weight row

/-- Factorization correction constructed from automorphed auxiliary bodies. -/
def correction {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (auxiliaryMask : AuxiliaryMask R rows Aux)
    (auxiliaryBody : AuxiliaryBody R rows Aux) : Output R rows :=
  fun row ↦ ∑ index, factorizer auxiliaryMask row index *
    spec.automorphism row (auxiliaryBody row index)

/-- The public compiler keeps the primary masks, drops the auxiliary transcript, and adds the
ring-aware correction to every primary body. -/
def compile {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (source : SourceTranscript R rows Aux) : Transcript R rows :=
  (source.1.1,
    source.2.1 + correction spec factorizer source.1.2 source.2.2)

/-- Exact primary and auxiliary noiseless ordinary-RLWE products. -/
def sourceNoiseless {R Aux : Type} [CommRing R] {rows : ℕ}
    (secret : Secret R) (challenge : SourceChallenge R rows Aux) :
    SourceOutput R rows Aux :=
  (vecMul secret challenge.1,
    fun row index ↦ challenge.2 row index * secret 0)

/-- The ordinary common-secret source problem. All public masks are independent uniform ring
elements; the complete primary/auxiliary error family is an explicit sampler parameter. -/
def sourceProblem
    {R Aux : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] [DecidableEq Aux] {rows : ℕ}
    (secretSampler : ProbComp (Secret R))
    (sourceErrorSampler : ProbComp (SourceOutput R rows Aux)) :
    LearningWithErrors.Problem
      (SourceChallenge R rows Aux) (Secret R) (SourceOutput R rows Aux) where
  sampleChallenge := do
    let primary ← $ᵗ (Challenge R rows)
    let auxiliary ← $ᵗ (AuxiliaryMask R rows Aux)
    return (primary, auxiliary)
  sampleSecret := secretSampler
  sampleError := sourceErrorSampler
  noiseless := sourceNoiseless
  sampleUniform := do
    let primary ← $ᵗ (Output R rows)
    let auxiliary ← $ᵗ (AuxiliaryBody R rows Aux)
    return (primary, auxiliary)

/-- Real ordinary source sampler. -/
def sourceRealSampler
    {R Aux : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] [DecidableEq Aux] {rows : ℕ}
    (secretSampler : ProbComp (Secret R))
    (sourceErrorSampler : ProbComp (SourceOutput R rows Aux)) :
    ProbComp (SourceTranscript R rows Aux) :=
  LearningWithErrors.distr (sourceProblem secretSampler sourceErrorSampler)

/-- Uniform ordinary source sampler. -/
def sourceUniformSampler
    {R Aux : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] [DecidableEq Aux] {rows : ℕ}
    (secretSampler : ProbComp (Secret R))
    (sourceErrorSampler : ProbComp (SourceOutput R rows Aux)) :
    ProbComp (SourceTranscript R rows Aux) :=
  LearningWithErrors.uniformDistr (sourceProblem secretSampler sourceErrorSampler)

/-! ## Exact real algebra -/

/-- Error induced by the primary error and the automorphed auxiliary errors. -/
def inducedError {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (auxiliaryMask : AuxiliaryMask R rows Aux)
    (sourceError : SourceOutput R rows Aux) : Output R rows :=
  sourceError.1 + fun row ↦ ∑ index,
    factorizer auxiliaryMask row index *
      spec.automorphism row (sourceError.2 row index)

/-- Pointwise source transcript with explicit ordinary errors. -/
def realSourceTranscript {R Aux : Type} [CommRing R] {rows : ℕ}
    (secret : Secret R) (sourceError : SourceOutput R rows Aux)
    (challenge : SourceChallenge R rows Aux) : SourceTranscript R rows Aux :=
  (challenge, sourceNoiseless secret challenge + sourceError)

/-- Expanding the ring-aware compiler gives the represented automorphism weight and precisely the
factorization-weighted auxiliary error. -/
theorem compile_realSourceTranscript
    {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (secret : Secret R) (sourceError : SourceOutput R rows Aux)
    (challenge : SourceChallenge R rows Aux) :
    compile spec factorizer (realSourceTranscript secret sourceError challenge) =
      MaskedGalois.targetTranscript
        (representedSpec spec factorizer challenge.2) secret
        (inducedError spec factorizer challenge.2 sourceError) challenge.1 := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [compile, realSourceTranscript, sourceNoiseless, correction,
      representedSpec, representedWeight, inducedError,
      MaskedGalois.targetTranscript, GaloisKDM.message,
      Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, map_mul]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hFactor :
        (∑ index, factorizer challenge.2 row index *
          (spec.automorphism row (challenge.2 row index) *
            spec.automorphism row (secret 0))) =
          (∑ index, factorizer challenge.2 row index *
            spec.automorphism row (challenge.2 row index)) *
              spec.automorphism row (secret 0) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro index _
      ring
    rw [hFactor]
    ring

/-- On successful public masks, the compiler produces exactly the requested Galois message. -/
theorem compile_realSourceTranscript_of_good
    {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (secret : Secret R) (sourceError : SourceOutput R rows Aux)
    (challenge : SourceChallenge R rows Aux)
    (hgood : Good spec factorizer challenge.2) :
    compile spec factorizer (realSourceTranscript secret sourceError challenge) =
      MaskedGalois.targetTranscript spec secret
        (inducedError spec factorizer challenge.2 sourceError) challenge.1 := by
  rw [compile_realSourceTranscript]
  apply Prod.ext
  · rfl
  · funext row
    simp [MaskedGalois.targetTranscript, GaloisKDM.message, representedSpec,
      hgood row]

/-! ## Exact uniform transport and ordinary-RLWE advantage -/

/-- Translating a primary uniform body by a fixed auxiliary correction is bijective. -/
theorem primaryBodyTranslation_bijective
    {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (auxiliaryMask : AuxiliaryMask R rows Aux)
    (auxiliaryBody : AuxiliaryBody R rows Aux) :
    Function.Bijective (fun primaryBody : Output R rows ↦
      primaryBody + correction spec factorizer auxiliaryMask auxiliaryBody) := by
  let inverse : Output R rows → Output R rows := fun output ↦
    output - correction spec factorizer auxiliaryMask auxiliaryBody
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro primaryBody
    simp [inverse]
  · intro output
    simp [inverse]

/-- For fixed primary/auxiliary masks and auxiliary bodies, compiling a uniform primary body
gives a uniform target body. -/
theorem fixedUniformPrimaryBody_evalDist
    {R Aux : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (primaryMask : Challenge R rows)
    (auxiliaryMask : AuxiliaryMask R rows Aux)
    (auxiliaryBody : AuxiliaryBody R rows Aux) :
    evalDist (($ᵗ (Output R rows)) >>= fun primaryBody ↦
        pure (compile spec factorizer
          ((primaryMask, auxiliaryMask), (primaryBody, auxiliaryBody)))) =
      evalDist (($ᵗ (Output R rows)) >>= fun body ↦ pure (primaryMask, body)) := by
  have hUniform :
      evalDist ((fun primaryBody : Output R rows ↦
          primaryBody + correction spec factorizer auxiliaryMask auxiliaryBody) <$>
        ($ᵗ (Output R rows))) = evalDist ($ᵗ (Output R rows)) :=
    evalDist_map_bijective_uniform_cross
      (α := Output R rows) (β := Output R rows) _
      (primaryBodyTranslation_bijective
        spec factorizer auxiliaryMask auxiliaryBody)
  simpa only [compile, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind] using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      hUniform (fun body ↦ pure (primaryMask, body)))

/-- Compiling the complete ordinary uniform source gives the canonical uniform Galois transcript.
The factorizer may be arbitrary and may fail on every mask. -/
theorem compiledSourceUniform_evalDist_eq_uniform
    {R Aux : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] [DecidableEq Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (secretSampler : ProbComp (Secret R))
    (sourceErrorSampler : ProbComp (SourceOutput R rows Aux)) :
    evalDist (sourceUniformSampler secretSampler sourceErrorSampler >>= fun source ↦
        pure (compile spec factorizer source)) =
      evalDist (GaloisKDM.uniformSampler rows spec secretSampler
        (pure 0 : ProbComp R)) := by
  unfold sourceUniformSampler LearningWithErrors.uniformDistr sourceProblem
  simp only [bind_assoc, pure_bind]
  calc
    evalDist (($ᵗ (Challenge R rows)) >>= fun primaryMask ↦
        ($ᵗ (AuxiliaryMask R rows Aux)) >>= fun auxiliaryMask ↦
          ($ᵗ (Output R rows)) >>= fun primaryBody ↦
            ($ᵗ (AuxiliaryBody R rows Aux)) >>= fun auxiliaryBody ↦
              pure (compile spec factorizer
                ((primaryMask, auxiliaryMask), (primaryBody, auxiliaryBody)))) =
      evalDist (($ᵗ (Challenge R rows)) >>= fun primaryMask ↦
        ($ᵗ (AuxiliaryMask R rows Aux)) >>= fun _auxiliaryMask ↦
          ($ᵗ (AuxiliaryBody R rows Aux)) >>= fun _auxiliaryBody ↦
            ($ᵗ (Output R rows)) >>= fun body ↦ pure (primaryMask, body)) := by
        refine evalDist_bind_congr' ($ᵗ (Challenge R rows)) fun primaryMask ↦ ?_
        refine evalDist_bind_congr'
          ($ᵗ (AuxiliaryMask R rows Aux)) fun auxiliaryMask ↦ ?_
        calc
          evalDist (($ᵗ (Output R rows)) >>= fun primaryBody ↦
              ($ᵗ (AuxiliaryBody R rows Aux)) >>= fun auxiliaryBody ↦
                pure (compile spec factorizer
                  ((primaryMask, auxiliaryMask), (primaryBody, auxiliaryBody)))) =
            evalDist (($ᵗ (AuxiliaryBody R rows Aux)) >>= fun auxiliaryBody ↦
              ($ᵗ (Output R rows)) >>= fun primaryBody ↦
                pure (compile spec factorizer
                  ((primaryMask, auxiliaryMask), (primaryBody, auxiliaryBody)))) :=
              evalDist_bind_bind_swap ($ᵗ (Output R rows))
                ($ᵗ (AuxiliaryBody R rows Aux)) _
          _ = _ := by
            refine evalDist_bind_congr'
              ($ᵗ (AuxiliaryBody R rows Aux)) fun auxiliaryBody ↦ ?_
            exact fixedUniformPrimaryBody_evalDist
              spec factorizer primaryMask auxiliaryMask auxiliaryBody
    _ = evalDist (($ᵗ (Challenge R rows)) >>= fun primaryMask ↦
        ($ᵗ (AuxiliaryMask R rows Aux)) >>= fun _auxiliaryMask ↦
          ($ᵗ (Output R rows)) >>= fun body ↦ pure (primaryMask, body)) := by
      refine evalDist_bind_congr' ($ᵗ (Challenge R rows)) fun _primaryMask ↦ ?_
      refine evalDist_bind_congr'
        ($ᵗ (AuxiliaryMask R rows Aux)) fun _auxiliaryMask ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ (AuxiliaryBody R rows Aux)) (by simp) _
    _ = evalDist (($ᵗ (Challenge R rows)) >>= fun primaryMask ↦
        ($ᵗ (Output R rows)) >>= fun body ↦ pure (primaryMask, body)) := by
      refine evalDist_bind_congr' ($ᵗ (Challenge R rows)) fun _primaryMask ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ (AuxiliaryMask R rows Aux)) (by simp) _
    _ = evalDist (GaloisKDM.uniformSampler rows spec secretSampler
        (pure 0 : ProbComp R)) := rfl

/-- Source adversary obtained from the public factorization compiler. -/
def sourceReduction
    {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (distinguisher : GaloisKDM.Distinguisher R rows) :
    SourceTranscript R rows Aux → ProbComp Bool :=
  fun source ↦ distinguisher (compile spec factorizer source)

/-- Advantage of the factorized real target against the canonical target uniform branch. -/
noncomputable def factorizedAdvantage
    {R Aux : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] [DecidableEq Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (secretSampler : ProbComp (Secret R))
    (sourceErrorSampler : ProbComp (SourceOutput R rows Aux))
    (distinguisher : GaloisKDM.Distinguisher R rows) : ℝ :=
  (sourceRealSampler secretSampler sourceErrorSampler >>=
      sourceReduction spec factorizer distinguisher).boolDistAdvantage
    (GaloisKDM.uniformSampler rows spec secretSampler (pure 0) >>= distinguisher)

/-- The complete factorized target advantage is exactly one ordinary common-secret rank-one LWE
advantage for all primary and auxiliary rows. -/
theorem factorizedAdvantage_eq_sourceAdvantage
    {R Aux : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] [DecidableEq Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (secretSampler : ProbComp (Secret R))
    (sourceErrorSampler : ProbComp (SourceOutput R rows Aux))
    (distinguisher : GaloisKDM.Distinguisher R rows) :
    factorizedAdvantage spec factorizer secretSampler sourceErrorSampler distinguisher =
      LearningWithErrors.advantage
        (sourceProblem secretSampler sourceErrorSampler)
        (sourceReduction spec factorizer distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold factorizedAdvantage LearningWithErrors.game0 LearningWithErrors.game1
    sourceRealSampler
  have hUniform := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (compiledSourceUniform_evalDist_eq_uniform
      spec factorizer secretSampler sourceErrorSampler) distinguisher
  unfold sourceReduction
  simp only [bind_assoc, pure_bind] at hUniform
  unfold sourceUniformSampler at hUniform
  unfold ProbComp.boolDistAdvantage
  have hUniformProbability := evalDist_ext_iff.mp hUniform true
  rw [hUniformProbability]

/-! ## Exact residual gap to the implementation target -/

/-- Distance, as seen by one distinguisher, between the desired narrow-error Galois batch and the
ordinary-RLWE-generated factorized batch. It contains exactly factorization failure and induced
error mismatch. -/
noncomputable def factorizationNoiseGap
    {R Aux : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] [DecidableEq Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (secretSampler : ProbComp (Secret R)) (targetErrorSampler : ProbComp R)
    (sourceErrorSampler : ProbComp (SourceOutput R rows Aux))
    (distinguisher : GaloisKDM.Distinguisher R rows) : ℝ :=
  (GaloisKDM.realSampler rows spec secretSampler targetErrorSampler >>=
      distinguisher).boolDistAdvantage
    (sourceRealSampler secretSampler sourceErrorSampler >>=
      sourceReduction spec factorizer distinguisher)

/-- Joint automorphism-KDM is bounded by one explicit factorization/noise gap plus ordinary
source RLWE. -/
theorem automorphismUniformAdvantage_le_gap_add_source
    {R Aux : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] [DecidableEq Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (secretSampler : ProbComp (Secret R)) (targetErrorSampler : ProbComp R)
    (sourceErrorSampler : ProbComp (SourceOutput R rows Aux))
    (distinguisher : GaloisKDM.Distinguisher R rows) :
    GaloisKDM.automorphismUniformAdvantage rows spec secretSampler targetErrorSampler
        distinguisher ≤
      factorizationNoiseGap spec factorizer secretSampler targetErrorSampler
          sourceErrorSampler distinguisher +
        LearningWithErrors.advantage
          (sourceProblem secretSampler sourceErrorSampler)
          (sourceReduction spec factorizer distinguisher) := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (GaloisKDM.realSampler rows spec secretSampler targetErrorSampler >>= distinguisher)
    (sourceRealSampler secretSampler sourceErrorSampler >>=
      sourceReduction spec factorizer distinguisher)
    (GaloisKDM.uniformSampler rows spec secretSampler (pure 0) >>= distinguisher)
  unfold GaloisKDM.automorphismUniformAdvantage factorizationNoiseGap
  rw [← factorizedAdvantage_eq_sourceAdvantage
    spec factorizer secretSampler sourceErrorSampler distinguisher]
  exact hTriangle

/-- Complete real-versus-zero Galois-key bound for the ring-aware path. -/
theorem kdmAdvantage_le_gap_add_source_add_zero
    {R Aux : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Aux] [DecidableEq Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (secretSampler : ProbComp (Secret R)) (targetErrorSampler : ProbComp R)
    (sourceErrorSampler : ProbComp (SourceOutput R rows Aux))
    (distinguisher : GaloisKDM.Distinguisher R rows) :
    GaloisKDM.kdmAdvantage rows spec secretSampler targetErrorSampler distinguisher ≤
      factorizationNoiseGap spec factorizer secretSampler targetErrorSampler
          sourceErrorSampler distinguisher +
        LearningWithErrors.advantage
          (sourceProblem secretSampler sourceErrorSampler)
          (sourceReduction spec factorizer distinguisher) +
        LearningWithErrors.advantage
          (GaloisKDM.ordinaryProblem rows secretSampler targetErrorSampler) distinguisher := by
  apply (GaloisKDM.kdmAdvantage_le_automorphismUniform_add_zeroUniform
    rows spec secretSampler targetErrorSampler distinguisher).trans
  rw [GaloisKDM.zeroUniformAdvantage_eq_ordinaryAdvantage]
  simpa only [add_assoc] using add_le_add
    (automorphismUniformAdvantage_le_gap_add_source
      spec factorizer secretSampler targetErrorSampler sourceErrorSampler distinguisher)
    (le_refl (LearningWithErrors.advantage
      (GaloisKDM.ordinaryProblem rows secretSampler targetErrorSampler) distinguisher))

/-! ## Why a short, almost-everywhere factorizer is essential -/

/-- All-zero auxiliary public masks. -/
def zeroAuxiliaryMask {R Aux : Type} [Zero R] {rows : ℕ} :
    AuxiliaryMask R rows Aux := 0

@[simp]
theorem representedWeight_zeroAuxiliaryMask
    {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux) (row : Fin rows) :
    representedWeight spec factorizer (zeroAuxiliaryMask (R := R) (Aux := Aux)) row = 0 := by
  simp [representedWeight, zeroAuxiliaryMask]

/-- No factorizer can succeed on every public mask when any requested gadget weight is nonzero.
Any ordinary-uniform-mask reduction must therefore account for a failure event. -/
theorem no_total_factorizer_of_weight_ne_zero
    {R Aux : Type} [CommRing R] [Fintype Aux] {rows : ℕ}
    (spec : Spec R rows) (factorizer : Factorizer R rows Aux)
    (row : Fin rows) (hweight : spec.weight row ≠ 0) :
    ¬ ∀ auxiliaryMask, Good spec factorizer auxiliaryMask := by
  intro hall
  have hgood := hall (zeroAuxiliaryMask (R := R) (Aux := Aux)) row
  rw [representedWeight_zeroAuxiliaryMask] at hgood
  exact hweight hgood.symm

/-! ## Literal flattening to the standard finite batch problem -/

/-- Split one parallel block's first sample from its `auxiliaries` remaining samples, across all
target rows. -/
def parallelChallengeEquiv (R : Type) (rows auxiliaries : ℕ) :
    FormalProof4FHE.LWE.ParallelBatch.Challenge R 1 rows (auxiliaries + 1) ≃
      SourceChallenge R rows (Fin auxiliaries) where
  toFun challenge :=
    (fun _ row ↦ challenge row 0 0,
      fun row index ↦ challenge row 0 index.succ)
  invFun challenge := fun row _ sampleIndex ↦
    Fin.cases (challenge.1 0 row) (challenge.2 row) sampleIndex
  left_inv challenge := by
    funext row coordinate sampleIndex
    fin_cases coordinate
    refine Fin.cases ?_ (fun index ↦ ?_) sampleIndex <;> rfl
  right_inv challenge := by
    apply Prod.ext
    · funext coordinate row
      fin_cases coordinate
      rfl
    · rfl

/-- Output counterpart of `parallelChallengeEquiv`. -/
def parallelOutputEquiv (R : Type) (rows auxiliaries : ℕ) :
    FormalProof4FHE.LWE.ParallelBatch.Output R rows (auxiliaries + 1) ≃
      SourceOutput R rows (Fin auxiliaries) where
  toFun output :=
    (fun row ↦ output row 0, fun row index ↦ output row index.succ)
  invFun output := fun row sampleIndex ↦
    Fin.cases (output.1 row) (output.2 row) sampleIndex
  left_inv output := by
    funext row sampleIndex
    refine Fin.cases ?_ (fun index ↦ ?_) sampleIndex <;> rfl
  right_inv output := by
    apply Prod.ext <;> rfl

/-- Complete public transcript reshaping from equal-size parallel blocks to the primary/auxiliary
source presentation. -/
def parallelTranscriptEquiv (R : Type) (rows auxiliaries : ℕ) :
    FormalProof4FHE.LWE.ParallelBatch.Transcript R 1 rows (auxiliaries + 1) ≃
      SourceTranscript R rows (Fin auxiliaries) :=
  (parallelChallengeEquiv R rows auxiliaries).prodCongr
    (parallelOutputEquiv R rows auxiliaries)

/-- IID source errors defined literally as the reshaping of IID errors in the standard parallel
batch. -/
def iidSourceErrorSampler
    {R : Type} (rows auxiliaries : ℕ) (errorSampler : ProbComp R) :
    ProbComp (SourceOutput R rows (Fin auxiliaries)) :=
  parallelOutputEquiv R rows auxiliaries <$>
    (Fin.mOfFn rows fun _ ↦ ProbComp.sampleIID (auxiliaries + 1) errorSampler)

/-- Reshaping commutes exactly with common-secret noiseless products and pointwise errors. -/
theorem parallelTranscriptEquiv_real
    {R : Type} [CommRing R] (rows auxiliaries : ℕ)
    (secret : Secret R)
    (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
      R 1 rows (auxiliaries + 1))
    (error : FormalProof4FHE.LWE.ParallelBatch.Output
      R rows (auxiliaries + 1)) :
    parallelTranscriptEquiv R rows auxiliaries
        (challenge, fun row ↦ vecMul secret (challenge row) + error row) =
      (parallelChallengeEquiv R rows auxiliaries challenge,
        sourceNoiseless secret (parallelChallengeEquiv R rows auxiliaries challenge) +
          parallelOutputEquiv R rows auxiliaries error) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext row
      simp [parallelTranscriptEquiv, parallelOutputEquiv, parallelChallengeEquiv,
        sourceNoiseless, Matrix.vecMul, dotProduct, mul_comm]
    · funext row index
      simp [parallelTranscriptEquiv, parallelOutputEquiv, parallelChallengeEquiv,
        sourceNoiseless, Matrix.vecMul, dotProduct, mul_comm]

/-- The parallel challenge sampler reshapes to the exact independent primary/auxiliary sampler
used by `sourceProblem`. -/
theorem parallelChallengeSampler_evalDist
    {R : Type} [Fintype R] [SampleableType R] (rows auxiliaries : ℕ) :
    evalDist (parallelChallengeEquiv R rows auxiliaries <$>
        (Fin.mOfFn rows fun _ ↦
          $ᵗ Matrix (Fin 1) (Fin (auxiliaries + 1)) R)) =
      evalDist (do
        let primary ← $ᵗ (Challenge R rows)
        let auxiliary ← $ᵗ (AuxiliaryMask R rows (Fin auxiliaries))
        return (primary, auxiliary)) := by
  let Parallel := FormalProof4FHE.LWE.ParallelBatch.Challenge
    R 1 rows (auxiliaries + 1)
  let Source := SourceChallenge R rows (Fin auxiliaries)
  have hParallel :
      evalDist (Fin.mOfFn rows fun _ ↦
          $ᵗ Matrix (Fin 1) (Fin (auxiliaries + 1)) R) =
        evalDist ($ᵗ Parallel) := by
    simpa [Parallel, ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Matrix (Fin 1) (Fin (auxiliaries + 1)) R) rows)
  have hMapped :
      evalDist (parallelChallengeEquiv R rows auxiliaries <$> ($ᵗ Parallel)) =
        evalDist ($ᵗ Source) :=
    evalDist_map_bijective_uniform_cross
      (α := Parallel) (β := Source)
      (parallelChallengeEquiv R rows auxiliaries)
      (parallelChallengeEquiv R rows auxiliaries).bijective
  have hSource :
      evalDist (do
        let primary ← $ᵗ (Challenge R rows)
        let auxiliary ← $ᵗ (AuxiliaryMask R rows (Fin auxiliaries))
        return (primary, auxiliary)) = evalDist ($ᵗ Source) :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  calc
    evalDist (parallelChallengeEquiv R rows auxiliaries <$>
        (Fin.mOfFn rows fun _ ↦
          $ᵗ Matrix (Fin 1) (Fin (auxiliaries + 1)) R)) =
      evalDist (parallelChallengeEquiv R rows auxiliaries <$> ($ᵗ Parallel)) := by
        simpa only [evalDist_map] using congrArg
          (fun distribution ↦
            parallelChallengeEquiv R rows auxiliaries <$> distribution) hParallel
    _ = evalDist ($ᵗ Source) := hMapped
    _ = _ := hSource.symm

/-- The parallel uniform-output sampler reshapes to the exact independent primary/auxiliary
uniform sampler used by `sourceProblem`. -/
theorem parallelUniformOutputSampler_evalDist
    {R : Type} [Fintype R] [SampleableType R] (rows auxiliaries : ℕ) :
    evalDist (parallelOutputEquiv R rows auxiliaries <$>
        (Fin.mOfFn rows fun _ ↦ $ᵗ (Fin (auxiliaries + 1) → R))) =
      evalDist (do
        let primary ← $ᵗ (Output R rows)
        let auxiliary ← $ᵗ (AuxiliaryBody R rows (Fin auxiliaries))
        return (primary, auxiliary)) := by
  let Parallel := FormalProof4FHE.LWE.ParallelBatch.Output
    R rows (auxiliaries + 1)
  let Source := SourceOutput R rows (Fin auxiliaries)
  have hParallel :
      evalDist (Fin.mOfFn rows fun _ ↦ $ᵗ (Fin (auxiliaries + 1) → R)) =
        evalDist ($ᵗ Parallel) := by
    simpa [Parallel, ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Fin (auxiliaries + 1) → R) rows)
  have hMapped :
      evalDist (parallelOutputEquiv R rows auxiliaries <$> ($ᵗ Parallel)) =
        evalDist ($ᵗ Source) :=
    evalDist_map_bijective_uniform_cross
      (α := Parallel) (β := Source)
      (parallelOutputEquiv R rows auxiliaries)
      (parallelOutputEquiv R rows auxiliaries).bijective
  have hSource :
      evalDist (do
        let primary ← $ᵗ (Output R rows)
        let auxiliary ← $ᵗ (AuxiliaryBody R rows (Fin auxiliaries))
        return (primary, auxiliary)) = evalDist ($ᵗ Source) :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  calc
    evalDist (parallelOutputEquiv R rows auxiliaries <$>
        (Fin.mOfFn rows fun _ ↦ $ᵗ (Fin (auxiliaries + 1) → R))) =
      evalDist (parallelOutputEquiv R rows auxiliaries <$> ($ᵗ Parallel)) := by
        simpa only [evalDist_map] using congrArg
          (fun distribution ↦ parallelOutputEquiv R rows auxiliaries <$> distribution)
          hParallel
    _ = evalDist ($ᵗ Source) := hMapped
    _ = _ := hSource.symm

/-- Equal-size parallel-batch presentation whose first local sample is primary and whose remaining
samples are auxiliary. -/
noncomputable def parallelSourceProblem
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (rows auxiliaries : ℕ) (secretSampler : ProbComp (Secret R))
    (errorSampler : ProbComp R) :=
  FormalProof4FHE.LWE.ParallelBatch.problem
    1 rows (auxiliaries + 1) secretSampler (fun secret ↦ secret) errorSampler

/-- Preprocess the parallel ordinary transcript for an adversary against the grouped source. -/
def parallelReduction
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    {rows auxiliaries : ℕ} {secretSampler : ProbComp (Secret R)}
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (sourceProblem secretSampler
        (iidSourceErrorSampler rows auxiliaries errorSampler))) :
    LearningWithErrors.Adversary
      (parallelSourceProblem rows auxiliaries secretSampler errorSampler) :=
  fun transcript ↦ adversary (parallelTranscriptEquiv R rows auxiliaries transcript)

/-- Mapping a parallel real transcript gives the exact grouped ordinary source distribution. -/
theorem parallelReal_evalDist_eq_source
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rows auxiliaries : ℕ) (secretSampler : ProbComp (Secret R))
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.distr
        (parallelSourceProblem rows auxiliaries secretSampler errorSampler) >>=
      fun transcript ↦ pure (parallelTranscriptEquiv R rows auxiliaries transcript)) =
      evalDist (LearningWithErrors.distr
        (sourceProblem secretSampler
          (iidSourceErrorSampler rows auxiliaries errorSampler))) := by
  let ParallelChallengeSampler :=
    Fin.mOfFn rows fun _ ↦ $ᵗ Matrix (Fin 1) (Fin (auxiliaries + 1)) R
  let MappedChallengeSampler :=
    parallelChallengeEquiv R rows auxiliaries <$> ParallelChallengeSampler
  let ParallelErrorSampler :=
    Fin.mOfFn rows fun _ ↦ ProbComp.sampleIID (auxiliaries + 1) errorSampler
  let MappedErrorSampler :=
    parallelOutputEquiv R rows auxiliaries <$> ParallelErrorSampler
  let Source := sourceProblem secretSampler
    (iidSourceErrorSampler rows auxiliaries errorSampler)
  let SourceChallengeSampler := Source.sampleChallenge
  have hChallenge : evalDist MappedChallengeSampler = evalDist SourceChallengeSampler := by
    simpa [MappedChallengeSampler, ParallelChallengeSampler, SourceChallengeSampler,
      Source, sourceProblem] using
      (parallelChallengeSampler_evalDist (R := R) rows auxiliaries)
  have left_eq :
      (LearningWithErrors.distr
          (parallelSourceProblem rows auxiliaries secretSampler errorSampler) >>=
        fun transcript ↦ pure (parallelTranscriptEquiv R rows auxiliaries transcript)) =
      (MappedChallengeSampler >>= fun challenge ↦
        secretSampler >>= fun secret ↦
          MappedErrorSampler >>= fun error ↦
            pure (challenge, sourceNoiseless secret challenge + error)) := by
    simp [LearningWithErrors.distr, parallelSourceProblem,
      FormalProof4FHE.LWE.ParallelBatch.problem, MappedChallengeSampler,
      ParallelChallengeSampler, MappedErrorSampler, ParallelErrorSampler,
      bind_assoc, monad_norm]
    apply bind_congr
    intro challenge
    apply bind_congr
    intro secret
    apply bind_congr
    intro error
    simp only [Function.comp_apply]
    rw [show (fun block ↦ vecMul secret (challenge block)) + error =
      (fun row ↦ vecMul secret (challenge row) + error row) by rfl]
    rw [parallelTranscriptEquiv_real]
  have right_eq :
      LearningWithErrors.distr Source =
      (SourceChallengeSampler >>= fun challenge ↦
        secretSampler >>= fun secret ↦
          MappedErrorSampler >>= fun error ↦
            pure (challenge, sourceNoiseless secret challenge + error)) := by
    simp [LearningWithErrors.distr, Source, sourceProblem, iidSourceErrorSampler,
      SourceChallengeSampler, MappedErrorSampler, ParallelErrorSampler, monad_norm]
  rw [left_eq, right_eq]
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _

/-- Mapping a parallel uniform transcript gives the exact grouped ordinary source uniform
distribution. -/
theorem parallelUniform_evalDist_eq_source
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rows auxiliaries : ℕ) (secretSampler : ProbComp (Secret R))
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.uniformDistr
        (parallelSourceProblem rows auxiliaries secretSampler errorSampler) >>=
      fun transcript ↦ pure (parallelTranscriptEquiv R rows auxiliaries transcript)) =
      evalDist (LearningWithErrors.uniformDistr
        (sourceProblem secretSampler
          (iidSourceErrorSampler rows auxiliaries errorSampler))) := by
  let ParallelChallengeSampler :=
    Fin.mOfFn rows fun _ ↦ $ᵗ Matrix (Fin 1) (Fin (auxiliaries + 1)) R
  let MappedChallengeSampler :=
    parallelChallengeEquiv R rows auxiliaries <$> ParallelChallengeSampler
  let ParallelOutputSampler :=
    Fin.mOfFn rows fun _ ↦ $ᵗ (Fin (auxiliaries + 1) → R)
  let MappedOutputSampler :=
    parallelOutputEquiv R rows auxiliaries <$> ParallelOutputSampler
  let Source := sourceProblem secretSampler
    (iidSourceErrorSampler rows auxiliaries errorSampler)
  let SourceChallengeSampler := Source.sampleChallenge
  let SourceOutputSampler := Source.sampleUniform
  have hChallenge : evalDist MappedChallengeSampler = evalDist SourceChallengeSampler := by
    simpa [MappedChallengeSampler, ParallelChallengeSampler, SourceChallengeSampler,
      Source, sourceProblem] using
      (parallelChallengeSampler_evalDist (R := R) rows auxiliaries)
  have hOutput : evalDist MappedOutputSampler = evalDist SourceOutputSampler := by
    simpa [MappedOutputSampler, ParallelOutputSampler, SourceOutputSampler,
      Source, sourceProblem] using
      (parallelUniformOutputSampler_evalDist (R := R) rows auxiliaries)
  have left_eq :
      (LearningWithErrors.uniformDistr
          (parallelSourceProblem rows auxiliaries secretSampler errorSampler) >>=
        fun transcript ↦ pure (parallelTranscriptEquiv R rows auxiliaries transcript)) =
      (MappedChallengeSampler >>= fun challenge ↦
        MappedOutputSampler >>= fun output ↦ pure (challenge, output)) := by
    simp [LearningWithErrors.uniformDistr, parallelSourceProblem,
      FormalProof4FHE.LWE.ParallelBatch.problem, MappedChallengeSampler,
      ParallelChallengeSampler, MappedOutputSampler, ParallelOutputSampler,
      bind_assoc, monad_norm]
    rfl
  have right_eq :
      LearningWithErrors.uniformDistr Source =
      (SourceChallengeSampler >>= fun challenge ↦
        SourceOutputSampler >>= fun output ↦ pure (challenge, output)) := by
    rfl
  rw [left_eq, right_eq]
  calc
    evalDist (MappedChallengeSampler >>= fun challenge ↦
        MappedOutputSampler >>= fun output ↦ pure (challenge, output)) =
      evalDist (SourceChallengeSampler >>= fun challenge ↦
        MappedOutputSampler >>= fun output ↦ pure (challenge, output)) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' SourceChallengeSampler fun _challenge ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hOutput _

/-- The grouped ordinary source advantage is exactly the parallel-batch advantage. -/
theorem sourceAdvantage_eq_parallel
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rows auxiliaries : ℕ) (secretSampler : ProbComp (Secret R))
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (sourceProblem secretSampler
        (iidSourceErrorSampler rows auxiliaries errorSampler))) :
    LearningWithErrors.advantage
        (sourceProblem secretSampler
          (iidSourceErrorSampler rows auxiliaries errorSampler)) adversary =
      LearningWithErrors.advantage
        (parallelSourceProblem rows auxiliaries secretSampler errorSampler)
        (parallelReduction adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold LearningWithErrors.game0 LearningWithErrors.game1 parallelReduction
    ProbComp.boolDistAdvantage
  have hReal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (parallelReal_evalDist_eq_source rows auxiliaries secretSampler errorSampler) adversary
  have hUniform := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (parallelUniform_evalDist_eq_source rows auxiliaries secretSampler errorSampler) adversary
  simp only [bind_assoc, pure_bind] at hReal hUniform
  rw [evalDist_ext_iff.mp hReal true, evalDist_ext_iff.mp hUniform true]

/-- Finally, the parallel source is exactly the repository's conventional combined batch with
`rows * (auxiliaries + 1)` samples. -/
theorem sourceAdvantage_eq_standardBatch
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rows auxiliaries : ℕ) (secretSampler : ProbComp (Secret R))
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (sourceProblem secretSampler
        (iidSourceErrorSampler rows auxiliaries errorSampler))) :
    LearningWithErrors.advantage
        (sourceProblem secretSampler
          (iidSourceErrorSampler rows auxiliaries errorSampler)) adversary =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.embeddedBatchProblem
          1 (rows * (auxiliaries + 1)) secretSampler (fun secret ↦ secret) errorSampler)
        (FormalProof4FHE.LWE.ParallelBatch.reduction
          (parallelReduction adversary)) := by
  rw [sourceAdvantage_eq_parallel]
  exact FormalProof4FHE.LWE.ParallelBatch.advantage_eq_batch
    1 rows (auxiliaries + 1) secretSampler (fun secret ↦ secret)
      errorSampler (parallelReduction adversary)

/-- End-to-end ring-aware bound with the source term literally replaced by the conventional
ordinary batch problem. The only nonstandard term left is `factorizationNoiseGap`. -/
theorem kdmAdvantage_le_gap_add_standardBatch_add_zero
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (auxiliaries : ℕ)
    (spec : Spec R rows) (factorizer : Factorizer R rows (Fin auxiliaries))
    (secretSampler : ProbComp (Secret R))
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (distinguisher : GaloisKDM.Distinguisher R rows) :
    GaloisKDM.kdmAdvantage rows spec secretSampler targetErrorSampler distinguisher ≤
      factorizationNoiseGap spec factorizer secretSampler targetErrorSampler
          (iidSourceErrorSampler rows auxiliaries sourceErrorSampler) distinguisher +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem
            1 (rows * (auxiliaries + 1)) secretSampler
              (fun secret ↦ secret) sourceErrorSampler)
          (FormalProof4FHE.LWE.ParallelBatch.reduction
            (parallelReduction
              (sourceReduction spec factorizer distinguisher))) +
        LearningWithErrors.advantage
          (GaloisKDM.ordinaryProblem rows secretSampler targetErrorSampler) distinguisher := by
  apply (kdmAdvantage_le_gap_add_source_add_zero
    spec factorizer secretSampler targetErrorSampler
      (iidSourceErrorSampler rows auxiliaries sourceErrorSampler) distinguisher).trans_eq
  rw [sourceAdvantage_eq_standardBatch rows auxiliaries secretSampler sourceErrorSampler
    (sourceReduction spec factorizer distinguisher)]

end

end FormalProof4FHE.RLWE.RingAwareGaloisFactorization
