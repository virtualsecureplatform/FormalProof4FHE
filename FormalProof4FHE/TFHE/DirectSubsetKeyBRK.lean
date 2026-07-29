/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.ParallelBatch
import FormalProof4FHE.Probability.BinaryGuessCheck
import FormalProof4FHE.RLWE.RingRegev
import FormalProof4FHE.TFHE.BootstrappingSecurity

/-!
# Direct Subset-Key BRK Security from Suffix RLWE

This file formalizes the direct reduction for a master secret split as a known sampled prefix plus
an independent suffix.  The reduction samples the prefix itself, absorbs its public additive
embedding into a suffix-LWE transcript, and uses only public postprocessing to construct the real
or zero-message BRK view.

The abstract theorem permits an arbitrary retained auxiliary view.  Its constructor records three
explicit total-variation defects: simulation of the real-message target, simulation of the
zero-message target, and disagreement of the two constructed views on a uniform source
challenge.  The resulting target-view advantage is bounded by twice one ordinary source-problem
advantage plus those three defects.

The later algebraic section proves the exact known-offset identities and uniform preservation.
No candidate randomization, pointwise gap, coordinate prediction, search assumption, or
whole-prefix guessing loss is used.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.DirectSubsetKeyBRK

/-! ## Abstract public-view constructor -/

/-- A public distinguisher for the constructed BRK-plus-auxiliary view. -/
abbrev Distinguisher (View : Type) := View → ProbComp Bool

/-- Run one constructor branch after sampling a source challenge and an independent prefix. -/
def constructedView {Prefix Challenge View : Type}
    (prefixSampler : ProbComp Prefix) (challengeSampler : ProbComp Challenge)
    (build : Bool → Prefix → Challenge → ProbComp View) (branch : Bool) : ProbComp View := do
  let challenge ← challengeSampler
  let prefixValue ← prefixSampler
  build branch prefixValue challenge

/-- Boolean decision experiment obtained by postprocessing a constructed public view. -/
def constructedDecision {Prefix Challenge View : Type}
    (prefixSampler : ProbComp Prefix) (challengeSampler : ProbComp Challenge)
    (build : Bool → Prefix → Challenge → ProbComp View) (branch : Bool)
    (distinguisher : Distinguisher View) : ProbComp Bool :=
  constructedView prefixSampler challengeSampler build branch >>= distinguisher

/-- Real-versus-zero distinguishing advantage for two target public views. -/
noncomputable def targetAdvantage {View : Type} (targetView : Bool → ProbComp View)
    (distinguisher : Distinguisher View) : ℝ :=
  (targetView true >>= distinguisher).boolDistAdvantage
    (targetView false >>= distinguisher)

/-- An approximate public constructor from an ordinary source challenge to two target views.

`realError true` is the simulation defect for the real-message target and `realError false` is
the defect for the zero-message target.  `uniformError` only asks that the two constructed
branches be close when the source challenge is uniform; it does not require either complete view
to be uniform. -/
structure PublicViewConstructor {Sample Secret Output Prefix View : Type} [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (prefixSampler : ProbComp Prefix) (targetView : Bool → ProbComp View) where
  build : Bool → Prefix → (Sample × Output) → ProbComp View
  realError : Bool → ℝ
  uniformError : ℝ
  realError_nonneg : ∀ branch, 0 ≤ realError branch
  uniformError_nonneg : 0 ≤ uniformError
  realDistance : ∀ branch,
    tvDist
        (constructedView prefixSampler (LearningWithErrors.distr problem) build branch)
        (targetView branch) ≤ realError branch
  uniformDistance :
    tvDist
        (constructedView prefixSampler (LearningWithErrors.uniformDistr problem) build true)
        (constructedView prefixSampler (LearningWithErrors.uniformDistr problem) build false) ≤
      uniformError

namespace PublicViewConstructor

variable {Sample Secret Output Prefix View : Type} [Add Output]
  {problem : LearningWithErrors.Problem Sample Secret Output}
  {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}

/-- Constructor with exact real-branch laws and an exact common uniform branch. -/
def ofExact
    (build : Bool → Prefix → (Sample × Output) → ProbComp View)
    (realLaw : ∀ branch,
      evalDist
          (constructedView prefixSampler (LearningWithErrors.distr problem) build branch) =
        evalDist (targetView branch))
    (uniformLaw :
      evalDist
          (constructedView prefixSampler (LearningWithErrors.uniformDistr problem) build true) =
        evalDist
          (constructedView prefixSampler (LearningWithErrors.uniformDistr problem) build false)) :
    PublicViewConstructor problem prefixSampler targetView where
  build := build
  realError := fun _ ↦ 0
  uniformError := 0
  realError_nonneg := fun _ ↦ le_rfl
  uniformError_nonneg := le_rfl
  realDistance := by
    intro branch
    unfold tvDist
    rw [realLaw branch]
    simp
  uniformDistance := by
    unfold tvDist
    rw [uniformLaw]
    simp

/-- Canonical sign of the target real/zero distinguishing gap.  It is one bit of nonuniform
reduction advice. -/
noncomputable def orientation
    (_constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) : Bool :=
  if (Pr[= true | targetView false >>= distinguisher]).toReal ≤
      (Pr[= true | targetView true >>= distinguisher]).toReal then true else false

/-- The canonical orientation selects a nonnegative target gap. -/
theorem orientation_le
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) :
    if constructor.orientation distinguisher then
      (Pr[= true | targetView false >>= distinguisher]).toReal ≤
        (Pr[= true | targetView true >>= distinguisher]).toReal
    else
      (Pr[= true | targetView true >>= distinguisher]).toReal ≤
        (Pr[= true | targetView false >>= distinguisher]).toReal := by
  unfold orientation
  split
  · assumption
  · exact le_of_not_ge ‹_›

/-- Acceptance gap between two Boolean games, with a selected orientation. -/
noncomputable def orientedGap (selectedOrientation : Bool)
    (positive negative : ProbComp Bool) : ℝ :=
  if selectedOrientation then
    (Pr[= true | positive]).toReal - (Pr[= true | negative]).toReal
  else
    (Pr[= true | negative]).toReal - (Pr[= true | positive]).toReal

/-- Choose between the two branches and complement the negative branch's answer. -/
def orientedChoice (selectedOrientation : Bool)
    (positive negative : ProbComp Bool) : ProbComp Bool :=
  if selectedOrientation then
    FormalProof4FHE.BinaryGuessCheck.signedChoice positive negative
  else
    FormalProof4FHE.BinaryGuessCheck.signedChoice negative positive

/-- Exact real-valued acceptance formula for an oriented branch choice. -/
theorem probOutput_true_orientedChoice (selectedOrientation : Bool)
    (positive negative : ProbComp Bool) :
    (Pr[= true | orientedChoice selectedOrientation positive negative]).toReal =
      (1 + orientedGap selectedOrientation positive negative) / 2 := by
  cases selectedOrientation <;>
    simp only [orientedChoice, Bool.false_eq_true, if_false, if_true, orientedGap,
      FormalProof4FHE.BinaryGuessCheck.probOutput_true_signedChoice] <;>
    ring

/-- The oriented target gap is exactly the absolute real/zero target advantage. -/
theorem orientedGap_target_eq_advantage
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) :
    orientedGap (constructor.orientation distinguisher)
        (targetView true >>= distinguisher) (targetView false >>= distinguisher) =
      targetAdvantage targetView distinguisher := by
  unfold orientedGap targetAdvantage ProbComp.boolDistAdvantage
  by_cases horientation : constructor.orientation distinguisher = true
  · have hle := constructor.orientation_le distinguisher
    rw [if_pos horientation] at hle ⊢
    exact (abs_of_nonneg (sub_nonneg.mpr hle)).symm
  · have hle := constructor.orientation_le distinguisher
    rw [if_neg horientation] at hle ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    ring

/-- Pull a target-view distinguisher back to the ordinary source problem.  The reduction samples
the prefix and a uniform target branch, builds that branch from the supplied challenge, and
checks the oriented distinguisher answer. -/
noncomputable def reduction
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) : LearningWithErrors.Adversary problem :=
  fun challenge ↦
    orientedChoice (constructor.orientation distinguisher)
      (prefixSampler >>= fun prefixValue ↦
        constructor.build true prefixValue challenge >>= distinguisher)
      (prefixSampler >>= fun prefixValue ↦
        constructor.build false prefixValue challenge >>= distinguisher)

/-- Sampling the source before the reduction produces the oriented choice of the two complete
constructed decision games. -/
theorem source_bind_reduction_evalDist
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) (source : ProbComp (Sample × Output)) :
    evalDist (source >>= constructor.reduction distinguisher) =
      evalDist (orientedChoice (constructor.orientation distinguisher)
        (constructedDecision prefixSampler source constructor.build true distinguisher)
        (constructedDecision prefixSampler source constructor.build false distinguisher)) := by
  unfold reduction orientedChoice
  by_cases horientation : constructor.orientation distinguisher = true
  · simp only [horientation, if_true]
    have h := FormalProof4FHE.BinaryGuessCheck.evalDist_bind_signedChoice source
      (fun challenge ↦
        prefixSampler >>= fun prefixValue ↦
          constructor.build true prefixValue challenge >>= distinguisher)
      (fun challenge ↦
        prefixSampler >>= fun prefixValue ↦
          constructor.build false prefixValue challenge >>= distinguisher)
    simpa only [constructedDecision, constructedView, bind_assoc] using h
  · have horientationFalse : constructor.orientation distinguisher = false := by
      exact Bool.eq_false_iff.mpr horientation
    simp only [horientationFalse, Bool.false_eq_true, if_false]
    have h := FormalProof4FHE.BinaryGuessCheck.evalDist_bind_signedChoice source
      (fun challenge ↦
        prefixSampler >>= fun prefixValue ↦
          constructor.build false prefixValue challenge >>= distinguisher)
      (fun challenge ↦
        prefixSampler >>= fun prefixValue ↦
          constructor.build true prefixValue challenge >>= distinguisher)
    simpa only [constructedDecision, constructedView, bind_assoc] using h

/-- Real source-game acceptance probability of the reduction. -/
theorem game0_probability
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) :
    (Pr[= true | LearningWithErrors.game0 problem (constructor.reduction distinguisher)]).toReal =
      (1 + orientedGap (constructor.orientation distinguisher)
        (constructedDecision prefixSampler (LearningWithErrors.distr problem)
          constructor.build true distinguisher)
        (constructedDecision prefixSampler (LearningWithErrors.distr problem)
          constructor.build false distinguisher)) / 2 := by
  have hdist :
      evalDist (LearningWithErrors.game0 problem (constructor.reduction distinguisher)) =
        evalDist (orientedChoice (constructor.orientation distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.distr problem)
            constructor.build true distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.distr problem)
            constructor.build false distinguisher)) := by
    unfold LearningWithErrors.game0
    exact constructor.source_bind_reduction_evalDist distinguisher
      (LearningWithErrors.distr problem)
  rw [probOutput_congr rfl hdist]
  exact probOutput_true_orientedChoice _ _ _

/-- Uniform source-game acceptance probability of the reduction. -/
theorem game1_probability
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) :
    (Pr[= true | LearningWithErrors.game1 problem (constructor.reduction distinguisher)]).toReal =
      (1 + orientedGap (constructor.orientation distinguisher)
        (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
          constructor.build true distinguisher)
        (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
          constructor.build false distinguisher)) / 2 := by
  have hdist :
      evalDist (LearningWithErrors.game1 problem (constructor.reduction distinguisher)) =
        evalDist (orientedChoice (constructor.orientation distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
            constructor.build true distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
            constructor.build false distinguisher)) := by
    unfold LearningWithErrors.game1
    exact constructor.source_bind_reduction_evalDist distinguisher
      (LearningWithErrors.uniformDistr problem)
  rw [probOutput_congr rfl hdist]
  exact probOutput_true_orientedChoice _ _ _

/-- The ordinary source advantage is half the absolute difference of the constructed oriented
gaps in its real and uniform branches. -/
theorem reduction_advantage_eq
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) :
    LearningWithErrors.advantage problem (constructor.reduction distinguisher) =
      |orientedGap (constructor.orientation distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.distr problem)
            constructor.build true distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.distr problem)
            constructor.build false distinguisher) -
        orientedGap (constructor.orientation distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
            constructor.build true distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
            constructor.build false distinguisher)| / 2 := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [constructor.game0_probability distinguisher, constructor.game1_probability distinguisher]
  rw [show
      (1 + orientedGap (constructor.orientation distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.distr problem)
            constructor.build true distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.distr problem)
            constructor.build false distinguisher)) / 2 -
        (1 + orientedGap (constructor.orientation distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
            constructor.build true distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
            constructor.build false distinguisher)) / 2 =
        (orientedGap (constructor.orientation distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.distr problem)
            constructor.build true distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.distr problem)
            constructor.build false distinguisher) -
        orientedGap (constructor.orientation distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
            constructor.build true distinguisher)
          (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
            constructor.build false distinguisher)) / 2 by ring]
  rw [abs_div, abs_two]

/-- Postprocessing the two real-branch simulations by a distinguisher preserves their stated
total-variation bounds. -/
theorem decisionRealDistance
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) (branch : Bool) :
    tvDist
        (constructedDecision prefixSampler (LearningWithErrors.distr problem)
          constructor.build branch distinguisher)
        (targetView branch >>= distinguisher) ≤ constructor.realError branch := by
  exact (tvDist_bind_right_le distinguisher _ _).trans (constructor.realDistance branch)

/-- Postprocessing the common-uniform-branch condition preserves its defect. -/
theorem decisionUniformDistance
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) :
    tvDist
        (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
          constructor.build true distinguisher)
        (constructedDecision prefixSampler (LearningWithErrors.uniformDistr problem)
          constructor.build false distinguisher) ≤ constructor.uniformError := by
  exact (tvDist_bind_right_le distinguisher _ _).trans constructor.uniformDistance

/-- **Direct subset-key BRK reduction.**  Any target real/zero distinguisher yields one ordinary
source-problem distinguisher.  The only losses are the factor two from choosing a target branch
and the three constructor defects. -/
theorem targetAdvantage_le_two_source_add_errors
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        constructor.realError true + constructor.realError false + constructor.uniformError := by
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
  have hUniformAbs : |uniformGap| ≤ constructor.uniformError := by
    have hDecision := (abs_probOutput_toReal_sub_le_tvDist uniformOne uniformZero).trans
      (constructor.decisionUniformDistance distinguisher)
    unfold uniformGap orientedGap
    by_cases horientation : selectedOrientation = true
    · rw [if_pos horientation]
      exact hDecision
    · rw [if_neg horientation, abs_sub_comm]
      exact hDecision
  have hAdvantage :
      LearningWithErrors.advantage problem (constructor.reduction distinguisher) =
        |realGap - uniformGap| / 2 := by
    simpa only [realGap, uniformGap, selectedOrientation, realOne, realZero, uniformOne,
      uniformZero] using constructor.reduction_advantage_eq distinguisher
  have hRealGap : realGap ≤ |realGap - uniformGap| + |uniformGap| := by
    have hFirst : realGap - uniformGap ≤ |realGap - uniformGap| := le_abs_self _
    have hSecond : uniformGap ≤ |uniformGap| := le_abs_self _
    linarith
  linarith

/-- Exact constructors have only the factor-two reduction loss. -/
theorem targetAdvantage_le_two_source_of_exact
    (constructor : PublicViewConstructor problem prefixSampler targetView)
    (hRealError : ∀ branch, constructor.realError branch = 0)
    (hUniformError : constructor.uniformError = 0)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) := by
  have h := constructor.targetAdvantage_le_two_source_add_errors distinguisher
  rw [hRealError true, hRealError false, hUniformError] at h
  simpa using h

end PublicViewConstructor

/-! ## Exact known-offset algebra -/

/-- Add the known prefix contribution to every LWE output coordinate. -/
def addKnownOffsetOutput {R : Type} [Semiring R] {dimension samples : ℕ}
    (offset : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (output : Fin samples → R) : Fin samples → R :=
  output + vecMul offset challenge

/-- Public known-offset conversion of a complete batch transcript. -/
def addKnownOffsetTranscript {R : Type} [Semiring R] {dimension samples : ℕ}
    (offset : Fin dimension → R)
    (transcript : LWE.BatchTranscript R dimension samples) :
    LWE.BatchTranscript R dimension samples :=
  (transcript.1, addKnownOffsetOutput offset transcript.1 transcript.2)

/-- Remove a previously added known offset. -/
def removeKnownOffsetTranscript {R : Type} [Ring R] {dimension samples : ℕ}
    (offset : Fin dimension → R)
    (transcript : LWE.BatchTranscript R dimension samples) :
    LWE.BatchTranscript R dimension samples :=
  (transcript.1, transcript.2 - vecMul offset transcript.1)

/-- Known-offset conversion changes the LWE secret from `secret` to `secret + offset` while
preserving the error vector exactly. -/
theorem addKnownOffsetTranscript_real {R : Type} [CommSemiring R]
    {dimension samples : ℕ}
    (secret offset : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) :
    addKnownOffsetTranscript offset (challenge, vecMul secret challenge + error) =
      (challenge, vecMul (secret + offset) challenge + error) := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [addKnownOffsetTranscript, addKnownOffsetOutput, Pi.add_apply, Matrix.vecMul,
      dotProduct]
    simp_rw [add_mul, Finset.sum_add_distrib]
    abel

@[simp]
theorem removeKnownOffsetTranscript_addKnownOffsetTranscript {R : Type} [Ring R]
    {dimension samples : ℕ} (offset : Fin dimension → R)
    (transcript : LWE.BatchTranscript R dimension samples) :
    removeKnownOffsetTranscript offset (addKnownOffsetTranscript offset transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [removeKnownOffsetTranscript, addKnownOffsetTranscript, addKnownOffsetOutput]

@[simp]
theorem addKnownOffsetTranscript_removeKnownOffsetTranscript {R : Type} [Ring R]
    {dimension samples : ℕ} (offset : Fin dimension → R)
    (transcript : LWE.BatchTranscript R dimension samples) :
    addKnownOffsetTranscript offset (removeKnownOffsetTranscript offset transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [removeKnownOffsetTranscript, addKnownOffsetTranscript, addKnownOffsetOutput]

/-- For every fixed public offset, known-offset conversion is a permutation of the complete
transcript carrier. -/
theorem addKnownOffsetTranscript_bijective {R : Type} [Ring R]
    {dimension samples : ℕ} (offset : Fin dimension → R) :
    Function.Bijective
      (addKnownOffsetTranscript (samples := samples) offset) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨removeKnownOffsetTranscript offset,
      removeKnownOffsetTranscript_addKnownOffsetTranscript offset,
      addKnownOffsetTranscript_removeKnownOffsetTranscript offset⟩

/-- A fixed known-offset conversion preserves the uniform transcript distribution exactly. -/
theorem addKnownOffsetTranscript_uniform_evalDist {R : Type}
    [Ring R] [Fintype R] [SampleableType R]
    (dimension samples : ℕ) (offset : Fin dimension → R) :
    evalDist (addKnownOffsetTranscript offset <$>
      ($ᵗ (LWE.BatchTranscript R dimension samples))) =
      evalDist ($ᵗ (LWE.BatchTranscript R dimension samples)) :=
  evalDist_map_bijective_uniform_cross
    (α := LWE.BatchTranscript R dimension samples)
    (β := LWE.BatchTranscript R dimension samples)
    (addKnownOffsetTranscript offset)
    (addKnownOffsetTranscript_bijective offset)

/-! ## Exact native rank-one RGSW/BRK constructor -/

namespace Native

/-- A rank-one native RGSW ciphertext for each encrypted subset-key coordinate. -/
abbrev BootstrappingKey (R : Type) (levels entries : ℕ) :=
  Fin entries → TGSW.Ciphertext R 1 levels

/-- Parallel suffix-RLWE blocks, one complete rank-one RGSW row set per BRK entry. -/
noncomputable def suffixProblem {R : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels entries : ℕ) (suffixSampler : ProbComp (Fin 1 → R))
    (errorSampler : ProbComp R) :=
  LWE.ParallelBatch.problem 1 entries (TGSW.rowCount 1 levels)
    suffixSampler id errorSampler

/-- Select the known BRK plaintext in the real branch and zero in the reference branch. -/
def branchMessage {R Prefix : Type} [Zero R]
    {entries : ℕ} (messages : Prefix → Fin entries → R)
    (branch : Bool) (prefixValue : Prefix) (entry : Fin entries) : R :=
  if branch then messages prefixValue entry else 0

/-- Assemble the complete native BRK from explicit masks, a suffix secret, explicit errors, and
the independently sampled known prefix. -/
def assembleNative {R Prefix : Type} [CommRing R]
    {levels entries : ℕ}
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) (prefixValue : Prefix)
    (suffixSecret : Fin 1 → R)
    (challenge : LWE.ParallelBatch.Challenge R 1 entries (TGSW.rowCount 1 levels))
    (error : LWE.ParallelBatch.Output R entries (TGSW.rowCount 1 levels)) :
    BootstrappingKey R levels entries :=
  fun entry ↦
    TGSW.addGadget gadget (branchMessage messages branch prefixValue entry)
      (challenge entry,
        vecMul (suffixSecret + offset prefixValue) (challenge entry) + error entry)

/-- Native real/zero BRK view under the full secret `suffixSecret + offset prefixValue`.

The sampling order is chosen to expose its exact relation to the parallel suffix-RLWE problem;
all public masks and row errors have the standard independent native laws. -/
noncomputable def view {R Prefix : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels entries : ℕ) (prefixSampler : ProbComp Prefix)
    (suffixSampler : ProbComp (Fin 1 → R)) (errorSampler : ProbComp R)
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) :
    ProbComp (BootstrappingKey R levels entries) := do
  let challenge ← Fin.mOfFn entries fun _ ↦
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R
  let suffixSecret ← suffixSampler
  let error ← Fin.mOfFn entries fun _ ↦
    ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler
  let prefixValue ← prefixSampler
  return assembleNative offset messages gadget branch prefixValue suffixSecret challenge error

/-- Deterministically build a native BRK from a parallel suffix-RLWE transcript by adding the
known prefix offset and then the public RGSW gadget message. -/
def buildKey {R Prefix : Type} [CommRing R]
    {levels entries : ℕ}
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) (prefixValue : Prefix)
    (transcript : LWE.ParallelBatch.Transcript R 1 entries (TGSW.rowCount 1 levels)) :
    BootstrappingKey R levels entries :=
  fun entry ↦
    TGSW.addGadget gadget (branchMessage messages branch prefixValue entry)
      (addKnownOffsetTranscript (offset prefixValue)
        (transcript.1 entry, transcript.2 entry))

/-- Probabilistic constructor interface obtained by returning the deterministic native BRK. -/
def build {R Prefix : Type} [CommRing R]
    {levels entries : ℕ}
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) :
    Bool → Prefix →
      LWE.ParallelBatch.Transcript R 1 entries (TGSW.rowCount 1 levels) →
        ProbComp (BootstrappingKey R levels entries) :=
  fun branch prefixValue transcript ↦
    pure (buildKey offset messages gadget branch prefixValue transcript)

/-- Pointwise known-offset identity for a complete native BRK. -/
theorem buildKey_realTranscript {R Prefix : Type} [CommRing R]
    {levels entries : ℕ}
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) (prefixValue : Prefix)
    (suffixSecret : Fin 1 → R)
    (challenge : LWE.ParallelBatch.Challenge R 1 entries (TGSW.rowCount 1 levels))
    (error : LWE.ParallelBatch.Output R entries (TGSW.rowCount 1 levels)) :
    buildKey offset messages gadget branch prefixValue
        (challenge, fun entry ↦ vecMul suffixSecret (challenge entry) + error entry) =
      assembleNative offset messages gadget branch prefixValue suffixSecret challenge error := by
  funext entry
  unfold buildKey assembleNative
  rw [addKnownOffsetTranscript_real]

/-- The constructed real suffix-RLWE branch is exactly the native full-secret BRK view. -/
theorem constructed_real_evalDist_eq_view {R Prefix : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels entries : ℕ) (prefixSampler : ProbComp Prefix)
    (suffixSampler : ProbComp (Fin 1 → R)) (errorSampler : ProbComp R)
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) :
    evalDist (constructedView prefixSampler
        (LearningWithErrors.distr
          (suffixProblem levels entries suffixSampler errorSampler))
        (build offset messages gadget) branch) =
      evalDist (view levels entries prefixSampler suffixSampler errorSampler
        offset messages gadget branch) := by
  simp only [constructedView, LearningWithErrors.distr, suffixProblem,
    LWE.ParallelBatch.problem, build, bind_assoc, pure_bind]
  refine evalDist_bind_congr'
    (Fin.mOfFn entries fun _ ↦
      $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) fun challenge ↦ ?_
  refine evalDist_bind_congr' suffixSampler fun suffixSecret ↦ ?_
  refine evalDist_bind_congr'
    (Fin.mOfFn entries fun _ ↦
      ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler) fun error ↦ ?_
  refine evalDist_bind_congr' prefixSampler fun prefixValue ↦ ?_
  exact congrArg
    (fun key : BootstrappingKey R levels entries ↦
      evalDist (pure key : ProbComp (BootstrappingKey R levels entries)))
    (buildKey_realTranscript offset messages gadget branch prefixValue suffixSecret challenge error)

/-- Remove a public RGSW gadget translation. -/
def removeGadget {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R 1 levels) : TGSW.Ciphertext R 1 levels :=
  (ciphertext.1 - TGSW.gadgetMaskShift gadget message,
    ciphertext.2 - TGSW.gadgetBodyShift gadget message)

@[simp]
theorem removeGadget_addGadget {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R 1 levels) :
    removeGadget gadget message (TGSW.addGadget gadget message ciphertext) = ciphertext := by
  apply Prod.ext
  · simp [removeGadget, TGSW.addGadget]
  · simp [removeGadget, TGSW.addGadget]

@[simp]
theorem addGadget_removeGadget {R : Type} [Ring R] {levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R 1 levels) :
    TGSW.addGadget gadget message (removeGadget gadget message ciphertext) = ciphertext := by
  apply Prod.ext
  · simp [removeGadget, TGSW.addGadget]
  · simp [removeGadget, TGSW.addGadget]

/-- Inverse of `buildKey` on the complete family of parallel transcript blocks. -/
def unbuildKey {R Prefix : Type} [CommRing R]
    {levels entries : ℕ}
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) (prefixValue : Prefix)
    (key : BootstrappingKey R levels entries) :
    LWE.ParallelBatch.Transcript R 1 entries (TGSW.rowCount 1 levels) :=
  let blocks := fun entry ↦
    removeKnownOffsetTranscript (offset prefixValue)
      (removeGadget gadget (branchMessage messages branch prefixValue entry) (key entry))
  (fun entry ↦ (blocks entry).1, fun entry ↦ (blocks entry).2)

@[simp]
theorem unbuildKey_buildKey {R Prefix : Type} [CommRing R]
    {levels entries : ℕ}
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) (prefixValue : Prefix)
    (transcript : LWE.ParallelBatch.Transcript R 1 entries (TGSW.rowCount 1 levels)) :
    unbuildKey offset messages gadget branch prefixValue
        (buildKey offset messages gadget branch prefixValue transcript) = transcript := by
  apply Prod.ext
  · funext entry row sample
    simp [unbuildKey, buildKey]
  · funext entry sample
    simp [unbuildKey, buildKey]

@[simp]
theorem buildKey_unbuildKey {R Prefix : Type} [CommRing R]
    {levels entries : ℕ}
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) (prefixValue : Prefix)
    (key : BootstrappingKey R levels entries) :
    buildKey offset messages gadget branch prefixValue
        (unbuildKey offset messages gadget branch prefixValue key) = key := by
  funext entry
  simp [unbuildKey, buildKey]

/-- For every fixed prefix and branch, public offset and gadget translations are a permutation
from parallel suffix-RLWE transcripts to native BRKs. -/
theorem buildKey_bijective {R Prefix : Type} [CommRing R]
    {levels entries : ℕ}
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) (prefixValue : Prefix) :
    Function.Bijective (buildKey offset messages gadget branch prefixValue) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unbuildKey offset messages gadget branch prefixValue,
      unbuildKey_buildKey offset messages gadget branch prefixValue,
      buildKey_unbuildKey offset messages gadget branch prefixValue⟩

/-- For a fixed sampled prefix, either constructed message branch maps a uniform parallel
transcript to an exactly uniform native BRK. -/
theorem fixedPrefix_uniform_evalDist {R Prefix : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels entries : ℕ) (suffixSampler : ProbComp (Fin 1 → R))
    (errorSampler : ProbComp R)
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) (branch : Bool) (prefixValue : Prefix) :
    evalDist (LearningWithErrors.uniformDistr
          (suffixProblem levels entries suffixSampler errorSampler) >>= fun transcript ↦
        pure (buildKey offset messages gadget branch prefixValue transcript)) =
      evalDist ($ᵗ (BootstrappingKey R levels entries)) := by
  have hUniform := LWE.ParallelBatch.uniformDistr_evalDist_eq_uniformSample
    1 entries (TGSW.rowCount 1 levels) suffixSampler id errorSampler
  calc
    _ = evalDist (($ᵗ
          (LWE.ParallelBatch.Transcript R 1 entries (TGSW.rowCount 1 levels))) >>= fun transcript ↦
        pure (buildKey offset messages gadget branch prefixValue transcript)) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hUniform _
    _ = evalDist (buildKey offset messages gadget branch prefixValue <$>
          ($ᵗ (LWE.ParallelBatch.Transcript R 1 entries (TGSW.rowCount 1 levels)))) := by
      simp [map_eq_bind_pure_comp]
    _ = _ := evalDist_map_bijective_uniform_cross
      (α := LWE.ParallelBatch.Transcript R 1 entries (TGSW.rowCount 1 levels))
      (β := BootstrappingKey R levels entries)
      (buildKey offset messages gadget branch prefixValue)
      (buildKey_bijective offset messages gadget branch prefixValue)

/-- The real-message and zero-message constructors have exactly the same law on a uniform
suffix-RLWE challenge. -/
theorem constructed_uniform_branches_evalDist_eq {R Prefix : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels entries : ℕ) (prefixSampler : ProbComp Prefix)
    (suffixSampler : ProbComp (Fin 1 → R)) (errorSampler : ProbComp R)
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) :
    evalDist (constructedView prefixSampler
        (LearningWithErrors.uniformDistr
          (suffixProblem levels entries suffixSampler errorSampler))
        (build offset messages gadget) true) =
      evalDist (constructedView prefixSampler
        (LearningWithErrors.uniformDistr
          (suffixProblem levels entries suffixSampler errorSampler))
        (build offset messages gadget) false) := by
  let source := LearningWithErrors.uniformDistr
    (suffixProblem levels entries suffixSampler errorSampler)
  let finish := fun (branch : Bool) (prefixValue : Prefix)
      (transcript : LWE.ParallelBatch.Transcript R 1 entries (TGSW.rowCount 1 levels)) ↦
    (pure (buildKey offset messages gadget branch prefixValue transcript) :
      ProbComp (BootstrappingKey R levels entries))
  have hSwap (branch : Bool) :
      evalDist (constructedView prefixSampler source (build offset messages gadget) branch) =
        evalDist (prefixSampler >>= fun prefixValue ↦
          source >>= fun transcript ↦ finish branch prefixValue transcript) := by
    unfold constructedView build finish
    exact OracleComp.DeferredSampling.evalDist_bind_comm source prefixSampler _
  rw [hSwap true, hSwap false]
  refine evalDist_bind_congr' prefixSampler fun prefixValue ↦ ?_
  have hTrue := fixedPrefix_uniform_evalDist levels entries suffixSampler errorSampler
    offset messages gadget true prefixValue
  have hFalse := fixedPrefix_uniform_evalDist levels entries suffixSampler errorSampler
    offset messages gadget false prefixValue
  exact hTrue.trans hFalse.symm

/-- Exact constructor for the native rank-one subset-key BRK views. -/
noncomputable def exactConstructor {R Prefix : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels entries : ℕ) (prefixSampler : ProbComp Prefix)
    (suffixSampler : ProbComp (Fin 1 → R)) (errorSampler : ProbComp R)
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R) :
    PublicViewConstructor
      (suffixProblem levels entries suffixSampler errorSampler) prefixSampler
      (view levels entries prefixSampler suffixSampler errorSampler offset messages gadget) :=
  PublicViewConstructor.ofExact (build offset messages gadget)
    (constructed_real_evalDist_eq_view levels entries prefixSampler suffixSampler errorSampler
      offset messages gadget)
    (constructed_uniform_branches_evalDist_eq levels entries prefixSampler suffixSampler
      errorSampler offset messages gadget)

/-- Exact native subset-key BRK security from the parallel suffix-RLWE problem. -/
theorem targetAdvantage_le_two_parallelSuffix
    {R Prefix : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels entries : ℕ) (prefixSampler : ProbComp Prefix)
    (suffixSampler : ProbComp (Fin 1 → R)) (errorSampler : ProbComp R)
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R)
    (distinguisher : Distinguisher (BootstrappingKey R levels entries)) :
    targetAdvantage
        (view levels entries prefixSampler suffixSampler errorSampler offset messages gadget)
        distinguisher ≤
      2 * LearningWithErrors.advantage
        (suffixProblem levels entries suffixSampler errorSampler)
        ((exactConstructor levels entries prefixSampler suffixSampler errorSampler
          offset messages gadget).reduction distinguisher) := by
  let constructor := exactConstructor levels entries prefixSampler suffixSampler errorSampler
    offset messages gadget
  exact constructor.targetAdvantage_le_two_source_of_exact
    (fun branch ↦ by cases branch <;> rfl) rfl distinguisher

/-- Flatten the parallel native reduction into one conventional batch of
`entries * rowCount` suffix-RLWE samples. -/
noncomputable def flattenedReduction
    {R Prefix : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels entries : ℕ) (prefixSampler : ProbComp Prefix)
    (suffixSampler : ProbComp (Fin 1 → R)) (errorSampler : ProbComp R)
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R)
    (distinguisher : Distinguisher (BootstrappingKey R levels entries)) :=
  LWE.ParallelBatch.reduction
    ((exactConstructor levels entries prefixSampler suffixSampler errorSampler
      offset messages gadget).reduction distinguisher)

/-- Final exact native theorem over the conventional combined suffix-RLWE batch. -/
theorem targetAdvantage_le_two_flatSuffix
    {R Prefix : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels entries : ℕ) (prefixSampler : ProbComp Prefix)
    (suffixSampler : ProbComp (Fin 1 → R)) (errorSampler : ProbComp R)
    (offset : Prefix → Fin 1 → R) (messages : Prefix → Fin entries → R)
    (gadget : Fin levels → R)
    (distinguisher : Distinguisher (BootstrappingKey R levels entries)) :
    targetAdvantage
        (view levels entries prefixSampler suffixSampler errorSampler offset messages gadget)
        distinguisher ≤
      2 * LearningWithErrors.advantage
        (LWE.embeddedBatchProblem 1 (entries * TGSW.rowCount 1 levels)
          suffixSampler id errorSampler)
        (flattenedReduction levels entries prefixSampler suffixSampler errorSampler
          offset messages gadget distinguisher) := by
  unfold flattenedReduction
  rw [← LWE.ParallelBatch.advantage_eq_batch 1 entries (TGSW.rowCount 1 levels)
    suffixSampler id errorSampler]
  exact targetAdvantage_le_two_parallelSuffix levels entries prefixSampler suffixSampler
    errorSampler offset messages gadget distinguisher

/-- The native rank-one BRK consumes exactly two gadget rows per level and entry. -/
theorem flatSampleCount_eq (levels entries : ℕ) :
    entries * TGSW.rowCount 1 levels = 2 * levels * entries := by
  simp only [TGSW.rowCount]
  ring

/-- Specialization of the flat native theorem to the repository's negacyclic suffix-RLWE
problem with an explicit suffix-secret sampler. -/
theorem targetAdvantage_le_two_rlwe
    {Prefix : Type} {q degree : ℕ} [NeZero q]
    (levels entries : ℕ) (prefixSampler : ProbComp Prefix)
    (suffixSampler : ProbComp (RLWE.Secret q degree))
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (offset : Prefix → RLWE.Secret q degree)
    (messages : Prefix → Fin entries → RLWE.Rq q degree)
    (gadget : Fin levels → RLWE.Rq q degree)
    (distinguisher : Distinguisher
      (BootstrappingKey (RLWE.Rq q degree) levels entries)) :
    targetAdvantage
        (view levels entries prefixSampler suffixSampler errorSampler offset messages gadget)
        distinguisher ≤
      2 * LearningWithErrors.advantage
        (RLWE.problem q degree (entries * TGSW.rowCount 1 levels)
          suffixSampler errorSampler)
        (flattenedReduction levels entries prefixSampler suffixSampler errorSampler
          offset messages gadget distinguisher) := by
  have h := targetAdvantage_le_two_flatSuffix levels entries prefixSampler suffixSampler
    errorSampler offset messages gadget distinguisher
  change _ ≤ 2 * @LearningWithErrors.advantage
      (RLWE.Sample q degree (entries * TGSW.rowCount 1 levels))
      (RLWE.Secret q degree)
      (RLWE.Output q degree (entries * TGSW.rowCount 1 levels))
      (RLWE.RingRegev.semiringOutputAdd q degree
        (entries * TGSW.rowCount 1 levels))
      (RLWE.problem q degree (entries * TGSW.rowCount 1 levels)
        suffixSampler errorSampler)
      (flattenedReduction levels entries prefixSampler suffixSampler errorSampler
        offset messages gadget distinguisher) at h
  rw [RLWE.RingRegev.semiringOutputAdd_eq] at h
  exact h

end Native

/-! ## Module-coordinate offset identity -/

/-- Extend a suffix-only module-LWE row by an independently chosen public prefix mask and add the
known prefix contribution to its body. -/
def moduleOffsetBody {R : Type} [Semiring R]
    {prefixDimension samples : ℕ}
    (prefixSecret : Fin prefixDimension → R)
    (prefixChallenge : Matrix (Fin prefixDimension) (Fin samples) R)
    (suffixOutput : Fin samples → R) : Fin samples → R :=
  suffixOutput + vecMul prefixSecret prefixChallenge

/-- The module-coordinate construction has exactly the full concatenated-secret noiseless term
and preserves the suffix error. -/
theorem moduleOffsetBody_real {R : Type} [CommSemiring R]
    {prefixDimension suffixDimension samples : ℕ}
    (prefixSecret : Fin prefixDimension → R)
    (suffixSecret : Fin suffixDimension → R)
    (prefixChallenge : Matrix (Fin prefixDimension) (Fin samples) R)
    (suffixChallenge : Matrix (Fin suffixDimension) (Fin samples) R)
    (error : Fin samples → R) :
    moduleOffsetBody prefixSecret prefixChallenge
        (vecMul suffixSecret suffixChallenge + error) =
      vecMul (Fin.append prefixSecret suffixSecret)
        (FormalProof4FHE.SharedRandomness.appendRows prefixChallenge suffixChallenge) + error := by
  funext sample
  simp [moduleOffsetBody, FormalProof4FHE.SharedRandomness.vecMul_appendRows]
  abel

end FormalProof4FHE.TFHE.DirectSubsetKeyBRK
