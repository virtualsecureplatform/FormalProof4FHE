/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.GaloisKDM
import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.SharedRandomness.Reduction

/-!
# Exact masked compiler for joint Galois evaluation keys

This file checks the proposed proof-mask construction for a complete batch of Galois-key rows.
For a secret `S`, an independent proof mask `F`, and a public hint `H = S + F`, the source body
in row `j` is

`A_j * S + E_j - g_j * sigma_j(F)`.

Adding `g_j * sigma_j(H)` gives the desired target body exactly.  The same translation is a
bijection on uniform transcripts.

The compiler is also publicly invertible because the hint is part of the source transcript.
Consequently, the masked-source real-versus-uniform problem is *exactly equivalent* to joint
automorphism-KDM, up to independent sampling of the public hint.  Thus this mask construction is
a useful exact normal form, but by itself it does not prove Galois-key security from ordinary
rank-one RLWE.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.MaskedGalois

noncomputable section

open GaloisKDM

/-- The proof-only public hint together with a complete batch transcript. -/
abbrev SourceTranscript (R : Type) (rows : ℕ) :=
  R × GaloisKDM.Transcript R rows

/-- The row correction publicly determined by a hint. -/
def correction {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (hint : R) : Output R rows :=
  fun row ↦ spec.weight row * spec.automorphism row hint

/-- Translate target bodies by the public hint correction. -/
def translate {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (hint : R) (transcript : Transcript R rows) :
    Transcript R rows :=
  (transcript.1, transcript.2 + correction spec hint)

/-- Inverse translation for a fixed public hint. -/
def untranslate {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (hint : R) (transcript : Transcript R rows) :
    Transcript R rows :=
  (transcript.1, transcript.2 - correction spec hint)

/-- Drop the hint after applying its public correction. -/
def compile {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (source : SourceTranscript R rows) :
    Transcript R rows :=
  translate spec source.1 source.2

/-- Reattach a chosen hint and undo the public correction. -/
def decompile {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (hint : R) (target : Transcript R rows) :
    SourceTranscript R rows :=
  (hint, untranslate spec hint target)

@[simp]
theorem translate_untranslate {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (hint : R) (transcript : Transcript R rows) :
    translate spec hint (untranslate spec hint transcript) = transcript := by
  apply Prod.ext
  · rfl
  · simp [translate, untranslate]

@[simp]
theorem untranslate_translate {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (hint : R) (transcript : Transcript R rows) :
    untranslate spec hint (translate spec hint transcript) = transcript := by
  apply Prod.ext
  · rfl
  · simp [translate, untranslate]

/-- For every fixed hint, compilation is a permutation of the complete target transcript. -/
theorem translate_bijective {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (hint : R) :
    Function.Bijective (translate spec hint) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨untranslate spec hint, untranslate_translate spec hint,
      translate_untranslate spec hint⟩

@[simp]
theorem compile_decompile {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (hint : R) (target : Transcript R rows) :
    compile spec (decompile spec hint target) = target := by
  exact translate_untranslate spec hint target

@[simp]
theorem decompile_compile {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (source : SourceTranscript R rows) :
    decompile spec source.1 (compile spec source) = source := by
  apply Prod.ext
  · rfl
  · exact untranslate_translate spec source.1 source.2

/-! ## Pointwise real-source identity -/

/-- Exact source transcript before public compilation. -/
def realSourceTranscript {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (secret : Secret R) (proofMask : R)
    (finalError : Output R rows) (challenge : Challenge R rows) :
    SourceTranscript R rows :=
  (secret 0 + proofMask,
    (challenge,
      vecMul secret challenge + finalError - correction spec proofMask))

/-- The desired complete Galois-key transcript, written without probability syntax. -/
def targetTranscript {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (secret : Secret R)
    (finalError : Output R rows) (challenge : Challenge R rows) :
    Transcript R rows :=
  (challenge, vecMul secret challenge + message spec secret + finalError)

/-- The proof mask cancels in every row, leaving exactly the narrow final error. -/
theorem compile_realSourceTranscript {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (secret : Secret R) (proofMask : R)
    (finalError : Output R rows) (challenge : Challenge R rows) :
    compile spec
        (realSourceTranscript spec secret proofMask finalError challenge) =
      targetTranscript spec secret finalError challenge := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [compile, translate, realSourceTranscript, targetTranscript, correction,
      message, Pi.add_apply, Pi.sub_apply, map_add]
    ring

/-! ## Complete source games -/

/-- The complete masked real source, retaining the proof-only hint. -/
def realSourceSampler
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R] {rows : ℕ}
    (spec : Spec R rows) (secretSampler : ProbComp (Secret R))
    (proofMaskSampler errorSampler : ProbComp R) :
    ProbComp (SourceTranscript R rows) := do
  let challenge ← $ᵗ (Challenge R rows)
  let secret ← secretSampler
  let proofMask ← proofMaskSampler
  let finalError ← ProbComp.sampleIID rows errorSampler
  return realSourceTranscript spec secret proofMask finalError challenge

/-- The ideal branch retains the exact hint law, but its complete pair transcript is uniform and
independent of that hint. -/
def uniformSourceSampler
    {R : Type} {rows : ℕ} [CommRing R] [DecidableEq R] [SampleableType R]
    [SampleableType (Transcript R rows)]
    (secretSampler : ProbComp (Secret R)) (proofMaskSampler : ProbComp R) :
    ProbComp (SourceTranscript R rows) := do
  let secret ← secretSampler
  let proofMask ← proofMaskSampler
  let transcript ← $ᵗ (Transcript R rows)
  return (secret 0 + proofMask, transcript)

/-- The target real sampler in an order convenient for comparison with `realSourceSampler`. -/
def explicitTargetSampler
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R] {rows : ℕ}
    (spec : Spec R rows) (secretSampler : ProbComp (Secret R))
    (errorSampler : ProbComp R) : ProbComp (Transcript R rows) := do
  let challenge ← $ᵗ (Challenge R rows)
  let secret ← secretSampler
  let finalError ← ProbComp.sampleIID rows errorSampler
  return targetTranscript spec secret finalError challenge

/-- The explicit sampler is definitionally the generic Galois-KDM real sampler. -/
theorem explicitTargetSampler_eq_realSampler
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R] (rows : ℕ)
    (spec : Spec R rows) (secretSampler : ProbComp (Secret R))
    (errorSampler : ProbComp R) :
    explicitTargetSampler spec secretSampler errorSampler =
      GaloisKDM.realSampler rows spec secretSampler errorSampler := by
  rfl

/-! ## Exact probability transport -/

/-- Compiling the complete real masked source gives exactly the intended Galois-KDM sampler.
The proof-mask distribution is arbitrary and contributes no target error. -/
theorem compiledRealSource_evalDist_eq_realSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R))
    (proofMaskSampler errorSampler : ProbComp R) :
    evalDist (realSourceSampler spec secretSampler proofMaskSampler errorSampler >>=
        fun source ↦ pure (compile spec source)) =
      evalDist (GaloisKDM.realSampler rows spec secretSampler errorSampler) := by
  rw [← explicitTargetSampler_eq_realSampler]
  unfold realSourceSampler explicitTargetSampler
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' ($ᵗ (Challenge R rows)) fun challenge ↦ ?_
  refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
  calc
    evalDist (proofMaskSampler >>= fun proofMask ↦
        ProbComp.sampleIID rows errorSampler >>= fun finalError ↦
          pure (compile spec
            (realSourceTranscript spec secret proofMask finalError challenge))) =
      evalDist (proofMaskSampler >>= fun _proofMask ↦
        ProbComp.sampleIID rows errorSampler >>= fun finalError ↦
          pure (targetTranscript spec secret finalError challenge)) := by
        refine evalDist_bind_congr' proofMaskSampler fun proofMask ↦ ?_
        refine evalDist_bind_congr'
          (ProbComp.sampleIID rows errorSampler) fun finalError ↦ ?_
        rw [compile_realSourceTranscript]
    _ = evalDist (ProbComp.sampleIID rows errorSampler >>= fun finalError ↦
          pure (targetTranscript spec secret finalError challenge)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        proofMaskSampler (by simp) _

/-- A fixed public hint translates the canonical uniform complete transcript to itself. -/
theorem fixedUniformCompile_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows) (hint : R) :
    evalDist (($ᵗ (Transcript R rows)) >>= fun transcript ↦
        pure (translate spec hint transcript)) =
      evalDist ($ᵗ (Transcript R rows)) := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    (evalDist_map_bijective_uniform_cross
      (α := Transcript R rows) (β := Transcript R rows)
      (translate spec hint) (translate_bijective spec hint))

/-- Compiling the ideal masked source gives the canonical uniform complete transcript. -/
theorem compiledUniformSource_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (proofMaskSampler : ProbComp R) :
    evalDist (uniformSourceSampler (rows := rows) secretSampler proofMaskSampler >>=
      fun source ↦
        pure (compile spec source)) =
      evalDist ($ᵗ (Transcript R rows)) := by
  let Uniform : ProbComp (Transcript R rows) := $ᵗ (Transcript R rows)
  calc
    evalDist (uniformSourceSampler (rows := rows) secretSampler proofMaskSampler >>=
      fun source ↦
        pure (compile spec source)) =
      evalDist (secretSampler >>= fun secret ↦
        proofMaskSampler >>= fun proofMask ↦ Uniform) := by
        unfold uniformSourceSampler
        simp only [bind_assoc, pure_bind]
        refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
        refine evalDist_bind_congr' proofMaskSampler fun proofMask ↦ ?_
        exact fixedUniformCompile_evalDist spec (secret 0 + proofMask)
    _ = evalDist (secretSampler >>= fun _secret ↦ Uniform) := by
      refine evalDist_bind_congr' secretSampler fun _secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        proofMaskSampler (by simp) _
    _ = evalDist Uniform :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        secretSampler (by simp) _

/-- The generic Galois problem's uniform branch is the canonical uniform sampler on the product
transcript type. -/
theorem uniformSampler_evalDist_eq_uniformSample
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R) :
    evalDist (GaloisKDM.uniformSampler rows spec secretSampler errorSampler) =
      evalDist ($ᵗ (Transcript R rows)) := by
  unfold GaloisKDM.uniformSampler LearningWithErrors.uniformDistr GaloisKDM.problem
  exact FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product

/-- Therefore the ideal compiler endpoint is exactly the Galois problem's named uniform branch. -/
theorem compiledUniformSource_evalDist_eq_uniformSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R))
    (proofMaskSampler errorSampler : ProbComp R) :
    evalDist (uniformSourceSampler (rows := rows) secretSampler proofMaskSampler >>=
      fun source ↦
        pure (compile spec source)) =
      evalDist (GaloisKDM.uniformSampler rows spec secretSampler errorSampler) := by
  rw [compiledUniformSource_evalDist spec secretSampler proofMaskSampler,
    uniformSampler_evalDist_eq_uniformSample spec secretSampler errorSampler]

/-! ## The exact masked-source security endpoint -/

/-- A distinguisher for the complete source view, including its public hint. -/
abbrev SourceDistinguisher (R : Type) (rows : ℕ) :=
  SourceTranscript R rows → ProbComp Bool

/-- Real masked source versus the same-hint uniform-pair branch. -/
noncomputable def sourceAdvantage
    {R : Type} {rows : ℕ} [CommRing R] [DecidableEq R] [SampleableType R]
    [SampleableType (Transcript R rows)]
    (spec : Spec R rows) (secretSampler : ProbComp (Secret R))
    (proofMaskSampler errorSampler : ProbComp R)
    (distinguisher : SourceDistinguisher R rows) : ℝ :=
  (realSourceSampler spec secretSampler proofMaskSampler errorSampler >>=
      distinguisher).boolDistAdvantage
    (uniformSourceSampler (rows := rows) secretSampler proofMaskSampler >>=
      distinguisher)

/-- Any target Galois-key distinguisher becomes a source distinguisher by public compilation. -/
def sourceReduction {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (distinguisher : GaloisKDM.Distinguisher R rows) :
    SourceDistinguisher R rows :=
  fun source ↦ distinguisher (compile spec source)

/-- The named joint automorphism-KDM advantage is *exactly* the advantage of the reduced
masked-source distinguisher.  Hence a source-hardness theorem is sufficient with no statistical
loss and no per-row factor. -/
theorem automorphismUniformAdvantage_eq_sourceAdvantage
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R))
    (proofMaskSampler errorSampler : ProbComp R)
    (distinguisher : GaloisKDM.Distinguisher R rows) :
    GaloisKDM.automorphismUniformAdvantage rows spec secretSampler errorSampler
        distinguisher =
      sourceAdvantage (rows := rows) spec secretSampler proofMaskSampler errorSampler
        (sourceReduction spec distinguisher) := by
  have hReal :
      evalDist (realSourceSampler spec secretSampler proofMaskSampler errorSampler >>=
          sourceReduction spec distinguisher) =
        evalDist (GaloisKDM.realSampler rows spec secretSampler errorSampler >>=
          distinguisher) := by
    change evalDist (realSourceSampler spec secretSampler proofMaskSampler errorSampler >>=
        fun source ↦ distinguisher (compile spec source)) = _
    simpa only [bind_assoc, pure_bind] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (compiledRealSource_evalDist_eq_realSampler
          spec secretSampler proofMaskSampler errorSampler) distinguisher)
  have hUniform :
      evalDist (uniformSourceSampler (rows := rows) secretSampler proofMaskSampler >>=
          sourceReduction spec distinguisher) =
        evalDist (GaloisKDM.uniformSampler rows spec secretSampler errorSampler >>=
          distinguisher) := by
    change evalDist
        (uniformSourceSampler (rows := rows) secretSampler proofMaskSampler >>=
          fun source ↦ distinguisher (compile spec source)) = _
    simpa only [bind_assoc, pure_bind] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (compiledUniformSource_evalDist_eq_uniformSampler
          spec secretSampler proofMaskSampler errorSampler) distinguisher)
  unfold GaloisKDM.automorphismUniformAdvantage sourceAdvantage
    ProbComp.boolDistAdvantage
  have hRealProbability := evalDist_ext_iff.mp hReal true
  have hUniformProbability := evalDist_ext_iff.mp hUniform true
  rw [hRealProbability.symm, hUniformProbability.symm]

/-- Combining the proved masked compiler with the already checked ordinary zero-message endpoint
gives a complete conditional real-versus-zero Galois-key theorem. -/
theorem kdmAdvantage_le_source_add_rlwe
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R))
    (proofMaskSampler errorSampler : ProbComp R)
    (distinguisher : GaloisKDM.Distinguisher R rows)
    (sourceBound rlweBound : ℝ)
    (hSource : sourceAdvantage (rows := rows) spec secretSampler proofMaskSampler errorSampler
      (sourceReduction spec distinguisher) ≤ sourceBound)
    (hRLWE : LearningWithErrors.advantage
      (GaloisKDM.ordinaryProblem rows secretSampler errorSampler) distinguisher ≤
        rlweBound) :
    GaloisKDM.kdmAdvantage rows spec secretSampler errorSampler distinguisher ≤
      sourceBound + rlweBound := by
  apply GaloisKDM.kdmAdvantage_le_of_automorphismKDM_and_rlwe
    rows spec secretSampler errorSampler distinguisher sourceBound rlweBound
  · rw [← GaloisKDM.automorphismUniformAdvantage_eq_problemAdvantage,
      automorphismUniformAdvantage_eq_sourceAdvantage
        (rows := rows) spec secretSampler proofMaskSampler errorSampler]
    exact hSource
  · exact hRLWE

/-! ## Uniform proof masks do not weaken the hard problem -/

/-- For fixed secret, changing variables from the uniform proof mask `F` to `H = S + F` is a
permutation of the ring. -/
theorem proofMaskToHint_bijective {R : Type} [AddCommGroup R]
    (secret : R) : Function.Bijective (fun proofMask : R ↦ secret + proofMask) := by
  let inverse : R → R := fun hint ↦ hint - secret
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro proofMask
    simp [inverse]
  · intro hint
    simp [inverse]

/-- Decompiling a target transcript at `H = S + F` recovers the complete real source transcript,
not merely its compiled image. -/
theorem decompile_targetTranscript_add_proofMask
    {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (secret : Secret R) (proofMask : R)
    (finalError : Output R rows) (challenge : Challenge R rows) :
    decompile spec (secret 0 + proofMask)
        (targetTranscript spec secret finalError challenge) =
      realSourceTranscript spec secret proofMask finalError challenge := by
  rw [← compile_realSourceTranscript spec secret proofMask finalError challenge]
  simpa only [realSourceTranscript] using
    (decompile_compile spec
      (realSourceTranscript spec secret proofMask finalError challenge))

/-- Public reverse reduction: choose an independent uniform hint, undo its body translation, and
run a source distinguisher. -/
def targetReduction
    {R : Type} [CommRing R] [SampleableType R] {rows : ℕ}
    (spec : Spec R rows) (distinguisher : SourceDistinguisher R rows) :
    GaloisKDM.Distinguisher R rows :=
  fun target ↦ do
    let hint ← $ᵗ R
    distinguisher (decompile spec hint target)

/-- For fixed hidden target coins, independently sampling a uniform hint and decompiling is the
same distribution as sampling a uniform proof mask and constructing the real source directly. -/
theorem fixedRealDecompile_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows) (secret : Secret R)
    (challenge : Challenge R rows) (errorSampler : ProbComp (Output R rows))
    (distinguisher : SourceDistinguisher R rows) :
    evalDist (($ᵗ R) >>= fun hint ↦
        errorSampler >>= fun finalError ↦
          distinguisher
            (decompile spec hint
              (targetTranscript spec secret finalError challenge))) =
      evalDist (($ᵗ R) >>= fun proofMask ↦
        errorSampler >>= fun finalError ↦
          distinguisher
            (realSourceTranscript spec secret proofMask finalError challenge)) := by
  let shift : R → R := fun proofMask ↦ secret 0 + proofMask
  have hShift : evalDist (shift <$> ($ᵗ R)) = evalDist ($ᵗ R) :=
    evalDist_map_bijective_uniform_cross (α := R) (β := R) shift
      (proofMaskToHint_bijective (secret 0))
  symm
  calc
    evalDist (($ᵗ R) >>= fun proofMask ↦
        errorSampler >>= fun finalError ↦
          distinguisher
            (realSourceTranscript spec secret proofMask finalError challenge)) =
      evalDist ((shift <$> ($ᵗ R)) >>= fun hint ↦
        errorSampler >>= fun finalError ↦
          distinguisher
            (decompile spec hint
              (targetTranscript spec secret finalError challenge))) := by
        simp only [shift, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
          pure_bind]
        refine evalDist_bind_congr' ($ᵗ R) fun proofMask ↦ ?_
        refine evalDist_bind_congr' errorSampler fun finalError ↦ ?_
        rw [decompile_targetTranscript_add_proofMask]
    _ = evalDist (($ᵗ R) >>= fun hint ↦
        errorSampler >>= fun finalError ↦
          distinguisher
            (decompile spec hint
              (targetTranscript spec secret finalError challenge))) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hShift _

/-- Against any source distinguisher, the public reverse reduction maps the target real game to
the uniform-mask source real game exactly. -/
theorem targetReduction_real_evalDist_eq_source
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : SourceDistinguisher R rows) :
    evalDist (GaloisKDM.realSampler rows spec secretSampler errorSampler >>=
        targetReduction spec distinguisher) =
      evalDist (realSourceSampler spec secretSampler ($ᵗ R) errorSampler >>=
        distinguisher) := by
  rw [← explicitTargetSampler_eq_realSampler]
  unfold explicitTargetSampler realSourceSampler targetReduction
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' ($ᵗ (Challenge R rows)) fun challenge ↦ ?_
  refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
  calc
    evalDist (ProbComp.sampleIID rows errorSampler >>= fun finalError ↦
        ($ᵗ R) >>= fun hint ↦
          distinguisher
            (decompile spec hint
              (targetTranscript spec secret finalError challenge))) =
      evalDist (($ᵗ R) >>= fun hint ↦
        ProbComp.sampleIID rows errorSampler >>= fun finalError ↦
          distinguisher
            (decompile spec hint
              (targetTranscript spec secret finalError challenge))) :=
        evalDist_bind_bind_swap (ProbComp.sampleIID rows errorSampler) ($ᵗ R) _
    _ = evalDist (($ᵗ R) >>= fun proofMask ↦
        ProbComp.sampleIID rows errorSampler >>= fun finalError ↦
          distinguisher
            (realSourceTranscript spec secret proofMask finalError challenge)) :=
      fixedRealDecompile_evalDist spec secret challenge
        (ProbComp.sampleIID rows errorSampler) distinguisher

/-- Inverse translation is also a permutation of a complete transcript for every fixed hint. -/
theorem untranslate_bijective {R : Type} [CommRing R] {rows : ℕ}
    (spec : Spec R rows) (hint : R) :
    Function.Bijective (untranslate spec hint) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨translate spec hint, translate_untranslate spec hint,
      untranslate_translate spec hint⟩

/-- For fixed hint, decompiling a uniform target transcript leaves the pair component uniform. -/
theorem fixedUniformDecompile_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows) (hint : R)
    (distinguisher : SourceDistinguisher R rows) :
    evalDist (($ᵗ (Transcript R rows)) >>= fun target ↦
        distinguisher (decompile spec hint target)) =
      evalDist (($ᵗ (Transcript R rows)) >>= fun transcript ↦
        distinguisher (hint, transcript)) := by
  have hUniform :
      evalDist (untranslate spec hint <$> ($ᵗ (Transcript R rows))) =
        evalDist ($ᵗ (Transcript R rows)) :=
    evalDist_map_bijective_uniform_cross
      (α := Transcript R rows) (β := Transcript R rows)
      (untranslate spec hint) (untranslate_bijective spec hint)
  simpa only [decompile, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind] using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      hUniform (fun transcript ↦ distinguisher (hint, transcript)))

/-- With a uniform proof mask, the ideal source game is simply an independent uniform hint and
uniform complete pair transcript; the secret sampler disappears exactly. -/
theorem uniformMask_sourceUniform_evalDist_eq_independent
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (secretSampler : ProbComp (Secret R))
    (distinguisher : SourceDistinguisher R rows) :
    evalDist (uniformSourceSampler (rows := rows) secretSampler ($ᵗ R) >>=
        distinguisher) =
      evalDist (($ᵗ R) >>= fun hint ↦
        ($ᵗ (Transcript R rows)) >>= fun transcript ↦
          distinguisher (hint, transcript)) := by
  let Independent : ProbComp Bool := do
    let hint ← $ᵗ R
    let transcript ← $ᵗ (Transcript R rows)
    distinguisher (hint, transcript)
  calc
    evalDist (uniformSourceSampler (rows := rows) secretSampler ($ᵗ R) >>=
        distinguisher) =
      evalDist (secretSampler >>= fun _secret ↦ Independent) := by
        unfold uniformSourceSampler Independent
        simp only [bind_assoc, pure_bind]
        refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
        let shift : R → R := fun proofMask ↦ secret 0 + proofMask
        have hShift : evalDist (shift <$> ($ᵗ R)) = evalDist ($ᵗ R) :=
          evalDist_map_bijective_uniform_cross (α := R) (β := R) shift
            (proofMaskToHint_bijective (secret 0))
        simpa only [shift, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
            pure_bind] using
          (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
            hShift (fun hint ↦
              ($ᵗ (Transcript R rows)) >>= fun transcript ↦
                distinguisher (hint, transcript)))
    _ = evalDist Independent :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        secretSampler (by simp) _

/-- The public reverse reduction maps the target uniform game to the uniform-mask source ideal
game exactly. -/
theorem targetReduction_uniform_evalDist_eq_source
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : SourceDistinguisher R rows) :
    evalDist (GaloisKDM.uniformSampler rows spec secretSampler errorSampler >>=
        targetReduction spec distinguisher) =
      evalDist (uniformSourceSampler (rows := rows) secretSampler ($ᵗ R) >>=
        distinguisher) := by
  let Independent : ProbComp Bool := do
    let hint ← $ᵗ R
    let transcript ← $ᵗ (Transcript R rows)
    distinguisher (hint, transcript)
  calc
    evalDist (GaloisKDM.uniformSampler rows spec secretSampler errorSampler >>=
        targetReduction spec distinguisher) =
      evalDist (($ᵗ (Transcript R rows)) >>= targetReduction spec distinguisher) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (uniformSampler_evalDist_eq_uniformSample
            spec secretSampler errorSampler) _
    _ = evalDist (($ᵗ R) >>= fun hint ↦
        ($ᵗ (Transcript R rows)) >>= fun target ↦
          distinguisher (decompile spec hint target)) := by
      unfold targetReduction
      exact evalDist_bind_bind_swap ($ᵗ (Transcript R rows)) ($ᵗ R) _
    _ = evalDist Independent := by
      unfold Independent
      refine evalDist_bind_congr' ($ᵗ R) fun hint ↦ ?_
      exact fixedUniformDecompile_evalDist spec hint distinguisher
    _ = evalDist (uniformSourceSampler (rows := rows) secretSampler ($ᵗ R) >>=
        distinguisher) :=
      (uniformMask_sourceUniform_evalDist_eq_independent
        secretSampler distinguisher).symm

/-- **Exact equivalence for a uniform proof mask.**  Every masked-source distinguisher has a
public target distinguisher with exactly the same advantage.  Together with
`automorphismUniformAdvantage_eq_sourceAdvantage`, this proves reductions in both directions.
Therefore choosing `F` uniformly does not derive Galois-key security from ordinary RLWE; it
re-encodes the joint automorphism-KDM problem. -/
theorem uniformMask_sourceAdvantage_eq_automorphismUniformAdvantage
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {rows : ℕ} (spec : Spec R rows)
    (secretSampler : ProbComp (Secret R)) (errorSampler : ProbComp R)
    (distinguisher : SourceDistinguisher R rows) :
    sourceAdvantage (rows := rows) spec secretSampler ($ᵗ R) errorSampler
        distinguisher =
      GaloisKDM.automorphismUniformAdvantage rows spec secretSampler errorSampler
        (targetReduction spec distinguisher) := by
  unfold sourceAdvantage GaloisKDM.automorphismUniformAdvantage
    ProbComp.boolDistAdvantage
  have hRealProbability := evalDist_ext_iff.mp
    (targetReduction_real_evalDist_eq_source
      spec secretSampler errorSampler distinguisher) true
  have hUniformProbability := evalDist_ext_iff.mp
    (targetReduction_uniform_evalDist_eq_source
      spec secretSampler errorSampler distinguisher) true
  rw [hRealProbability, hUniformProbability]

end

end FormalProof4FHE.RLWE.MaskedGalois
