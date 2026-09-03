/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CompactCoverBGVScalarSecurity
import FormalProof4FHE.SubspaceLWE.Security
import FormalProof4FHE.TFHE.EncryptionSecurity

/-!
# Adaptive symmetric encryption for scalar compact-cover BGV

This module generalizes the existing TFHE eager-query-tape proof from `ZMod q`
to an arbitrary finite commutative ring. An adaptive adversary chooses each
left/right message pair after seeing the public evaluation directory and all
previous ciphertexts. A public query bound makes a pre-generated row table
exactly equivalent to the online oracle. On the uniform endpoint, translating
the body by an adaptively chosen message preserves uniformity query by query.
-/

open OracleComp OracleSpec

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVAdaptiveSecurity

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev Interface (Message Ciphertext : Type) :=
  unifSpec + ((Message × Message) →ₒ Ciphertext)

abbrev Adversary (Message Cloud Ciphertext : Type) :=
  Cloud → OracleComp (Interface Message Ciphertext) Bool

def isEncryptionQuery {Message Ciphertext : Type} :
    (Interface Message Ciphertext).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance instDecidablePredIsEncryptionQuery {Message Ciphertext : Type} :
    DecidablePred (isEncryptionQuery (Message := Message) (Ciphertext := Ciphertext))
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

def IsQueryBound {Message Cloud Ciphertext : Type}
    (adversary : Adversary Message Cloud Ciphertext) (queryCount : ℕ) : Prop :=
  ∀ cloud, IsQueryBoundP (adversary cloud)
    (isEncryptionQuery (Message := Message) (Ciphertext := Ciphertext)) queryCount

abbrev SourceSample (R : Type) :=
  GeneralizedSubspaceLWE.Adaptive.LWESample R 1

/-- Translate one online source row into the selected left/right ciphertext. -/
noncomputable def sourceReduction {Message R : Type} [Add R]
    (bit : Bool) (encode : Message → R) :
    QueryImpl (Interface Message (R × R))
      (OracleComp (GeneralizedSubspaceLWE.Adaptive.SourceInterface R 1)) := by
  intro query
  rcases query with uniformIndex | messages
  · exact liftM ((GeneralizedSubspaceLWE.Adaptive.SourceInterface R 1).query
      (Sum.inl uniformIndex))
  · exact do
      let sample ← liftM
        ((GeneralizedSubspaceLWE.Adaptive.SourceInterface R 1).query (Sum.inr ()))
      return (sample.1 0, sample.2 + encode (if bit then messages.1 else messages.2))

theorem sourceReduction_isQueryBoundP {Message R Cloud : Type}
    [Add R] [Inhabited R] [Fintype R] [SampleableType R]
    (bit : Bool) (encode : Message → R)
    (adversary : Adversary Message Cloud (R × R)) (cloud : Cloud)
    (queryCount : ℕ)
    (hbound : IsQueryBoundP (adversary cloud)
      (isEncryptionQuery (Message := Message) (Ciphertext := R × R)) queryCount) :
    IsQueryBoundP
      (simulateQ (sourceReduction bit encode) (adversary cloud))
      (GeneralizedSubspaceLWE.Adaptive.isSourceSample (F := R) (dimension := 1))
      queryCount := by
  letI : IsUniformSpec (Unit →ₒ SourceSample R) :=
    IsUniformSpec.ofFintypeInhabited _
  apply IsQueryBoundP.simulateQ_of_step hbound
  · intro query hcharged
    rcases query with uniformIndex | messages
    · simp [isEncryptionQuery] at hcharged
    · simp only [sourceReduction]
      let sourceQuery : OracleComp
          (GeneralizedSubspaceLWE.Adaptive.SourceInterface R 1) (SourceSample R) :=
        liftM ((GeneralizedSubspaceLWE.Adaptive.SourceInterface R 1).query (Sum.inr ()))
      let continuation := fun sample : SourceSample R =>
        (pure (sample.1 0,
          sample.2 + encode (if bit then messages.1 else messages.2)) :
          OracleComp (GeneralizedSubspaceLWE.Adaptive.SourceInterface R 1) (R × R))
      change IsQueryBoundP (sourceQuery >>= continuation)
        (GeneralizedSubspaceLWE.Adaptive.isSourceSample (F := R) (dimension := 1)) 1
      have hsource : IsQueryBoundP sourceQuery
          (GeneralizedSubspaceLWE.Adaptive.isSourceSample (F := R) (dimension := 1)) 1 := by
        dsimp [sourceQuery]
        change (¬ GeneralizedSubspaceLWE.Adaptive.isSourceSample
            (F := R) (dimension := 1) (Sum.inr ()) ∨ 0 < 1) ∧
          ∀ _ : SourceSample R, True
        simp [GeneralizedSubspaceLWE.Adaptive.isSourceSample]
      have hcontinuation : ∀ sample ∈ support sourceQuery,
          IsQueryBoundP (continuation sample)
            (GeneralizedSubspaceLWE.Adaptive.isSourceSample (F := R) (dimension := 1)) 0 := by
        simp [continuation]
      simpa [sourceQuery, continuation] using
        isQueryBoundP_bind (n := 1) (m := 0) hsource hcontinuation
  · intro query hfree
    rcases query with uniformIndex | messages
    · exact GeneralizedSubspaceLWE.Adaptive.isQueryBoundP_liftProbComp_left
        (F := R) (dimension := 1)
        (liftM (unifSpec.query uniformIndex) : ProbComp (unifSpec.Range uniformIndex))
    · simp [isEncryptionQuery] at hfree

def rowToSourceSample {R : Type} (row : R × R) : SourceSample R :=
  (fun _ => row.1, row.2)

def sourceSampleToRow {R : Type} (sample : SourceSample R) : R × R :=
  (sample.1 0, sample.2)

@[simp] theorem sourceSampleToRow_rowToSourceSample {R : Type} (row : R × R) :
    sourceSampleToRow (rowToSourceSample row) = row := by
  rcases row with ⟨mask, body⟩
  rfl

@[simp] theorem rowToSourceSample_sourceSampleToRow {R : Type}
    (sample : SourceSample R) : rowToSourceSample (sourceSampleToRow sample) = sample := by
  rcases sample with ⟨mask, body⟩
  apply Prod.ext
  · funext index
    exact Fin.eq_zero index ▸ rfl
  · rfl

def rowSourceEquiv (R : Type) : (R × R) ≃ SourceSample R where
  toFun := rowToSourceSample
  invFun := sourceSampleToRow
  left_inv := sourceSampleToRow_rowToSourceSample
  right_inv := rowToSourceSample_sourceSampleToRow

def rowsToSourceTable {R : Type} {queryCount : ℕ}
    (rows : Fin queryCount → R × R) : Fin queryCount → SourceSample R :=
  fun index => rowToSourceSample (rows index)

theorem rowsToSourceTable_bijective (R : Type) (queryCount : ℕ) :
    Function.Bijective (rowsToSourceTable :
      (Fin queryCount → R × R) → (Fin queryCount → SourceSample R)) := by
  exact Equiv.piCongrRight (fun _ => rowSourceEquiv R) |>.bijective

/-- Execute the adaptive adversary from an eager table of zero-message rows. -/
noncomputable def runFromTable {Message Cloud R : Type}
    [Add R] [Fintype R] [SampleableType R]
    (bit : Bool) (encode : Message → R)
    (adversary : Adversary Message Cloud (R × R)) (cloud : Cloud)
    {queryCount : ℕ} (rows : Fin queryCount → R × R) : ProbComp Bool :=
  (simulateQ
      (GeneralizedSubspaceLWE.Adaptive.sourceImpl ($ᵗ SourceSample R)).withPregen
      (simulateQ (sourceReduction bit encode) (adversary cloud))).run'
    (GeneralizedSubspaceLWE.Adaptive.sourceSampleSeed
      (List.ofFn (rowsToSourceTable rows)))

/-- Uniform row functions become a uniform source-sample function by a
pointwise equivalence. -/
theorem evalDist_uniform_rowsToSourceTable {R : Type}
    [Fintype R] [SampleableType R] (queryCount : ℕ) :
    evalDist (rowsToSourceTable <$> ($ᵗ (Fin queryCount → R × R))) =
      evalDist ($ᵗ (Fin queryCount → SourceSample R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Fin queryCount → R × R) (β := Fin queryCount → SourceSample R)
    rowsToSourceTable (rowsToSourceTable_bijective R queryCount)

/-- Installing a uniform table is exactly the online uniform source oracle for
every bounded adaptive adversary. -/
theorem evalDist_uniformTable_runFromTable_eq_online
    {Message Cloud R : Type}
    [Add R] [Inhabited R] [Fintype R] [SampleableType R]
    (queryCount : ℕ) (bit : Bool) (encode : Message → R)
    (adversary : Adversary Message Cloud (R × R)) (cloud : Cloud)
    (hbound : IsQueryBoundP (adversary cloud)
      (isEncryptionQuery (Message := Message) (Ciphertext := R × R)) queryCount) :
    evalDist (do
        let rows ← $ᵗ (Fin queryCount → R × R)
        runFromTable bit encode adversary cloud rows) =
      evalDist (simulateQ
        (GeneralizedSubspaceLWE.Adaptive.sourceImpl ($ᵗ SourceSample R))
        (simulateQ (sourceReduction bit encode) (adversary cloud))) := by
  let sampleSampler : ProbComp (SourceSample R) := $ᵗ SourceSample R
  let computation := simulateQ (sourceReduction bit encode) (adversary cloud)
  let finish := fun samples : List (SourceSample R) =>
    (simulateQ
      (GeneralizedSubspaceLWE.Adaptive.sourceImpl sampleSampler).withPregen
      computation).run'
      (GeneralizedSubspaceLWE.Adaptive.sourceSampleSeed samples)
  have hsource : IsQueryBoundP computation
      (GeneralizedSubspaceLWE.Adaptive.isSourceSample (F := R) (dimension := 1))
      queryCount := sourceReduction_isQueryBoundP bit encode adversary cloud queryCount hbound
  have hiid := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
    (alpha := SourceSample R) queryCount
  have hrows := evalDist_uniform_rowsToSourceTable (R := R) queryCount
  have hlists :
      evalDist (List.ofFn <$> (rowsToSourceTable <$>
        ($ᵗ (Fin queryCount → R × R)))) =
      evalDist (OracleComp.replicate queryCount sampleSampler) := by
    calc
      _ = evalDist (List.ofFn <$> ($ᵗ (Fin queryCount → SourceSample R))) :=
        evalDist_map_eq_of_evalDist_eq hrows List.ofFn
      _ = evalDist (List.ofFn <$> ProbComp.sampleIID queryCount sampleSampler) :=
        evalDist_map_eq_of_evalDist_eq hiid.symm List.ofFn
      _ = _ := by
        rw [show ProbComp.sampleIID queryCount sampleSampler =
            Fin.mOfFn queryCount (fun _ => sampleSampler) by rfl,
          GeneralizedSubspaceLWE.Adaptive.mOfFn_toList_eq_replicate]
  have hbatched := GeneralizedSubspaceLWE.Adaptive.evalDist_sourceImpl_eq_batched
    sampleSampler sampleSampler computation queryCount hsource
  calc
    evalDist (do
        let rows ← $ᵗ (Fin queryCount → R × R)
        runFromTable bit encode adversary cloud rows) =
      evalDist ((List.ofFn <$> (rowsToSourceTable <$>
        ($ᵗ (Fin queryCount → R × R)))) >>= finish) := by
          simp [runFromTable, finish, computation, sampleSampler,
            map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (OracleComp.replicate queryCount sampleSampler >>= finish) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hlists finish
    _ = _ := hbatched.symm

def shiftSourceSample {R : Type} [Add R] (offset : R)
    (sample : SourceSample R) : SourceSample R :=
  (sample.1, sample.2 + offset)

def unshiftSourceSample {R : Type} [AddGroup R] (offset : R)
    (sample : SourceSample R) : SourceSample R :=
  (sample.1, sample.2 - offset)

@[simp] theorem unshift_shift {R : Type} [AddGroup R] (offset : R)
    (sample : SourceSample R) :
    unshiftSourceSample offset (shiftSourceSample offset sample) = sample := by
  rcases sample with ⟨mask, body⟩
  simp [unshiftSourceSample, shiftSourceSample]

@[simp] theorem shift_unshift {R : Type} [AddGroup R] (offset : R)
    (sample : SourceSample R) :
    shiftSourceSample offset (unshiftSourceSample offset sample) = sample := by
  rcases sample with ⟨mask, body⟩
  simp [unshiftSourceSample, shiftSourceSample]

theorem shiftSourceSample_bijective {R : Type} [AddGroup R] (offset : R) :
    Function.Bijective (shiftSourceSample (R := R) offset) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unshiftSourceSample offset, unshift_shift offset, shift_unshift offset⟩

noncomputable def plainUniformImpl {Message R : Type}
    [Fintype R] [SampleableType R] :
    QueryImpl (Interface Message (R × R)) ProbComp :=
  (QueryImpl.ofLift unifSpec ProbComp) +
    (fun _ : Message × Message => $ᵗ (R × R) :
      QueryImpl ((Message × Message) →ₒ (R × R)) ProbComp)

theorem evalDist_uniformSource_compose_sourceReduction
    {Message R : Type} [AddCommGroup R] [Fintype R] [SampleableType R]
    (bit : Bool) (encode : Message → R)
    (query : (Interface Message (R × R)).Domain) :
    evalDist ((GeneralizedSubspaceLWE.Adaptive.sourceImpl ($ᵗ SourceSample R) ∘ₛ
      sourceReduction bit encode) query) =
      evalDist (plainUniformImpl (Message := Message) (R := R) query) := by
  rcases query with uniformIndex | messages
  · rfl
  · let offset := encode (if bit then messages.1 else messages.2)
    let sampleSampler : ProbComp (SourceSample R) := $ᵗ SourceSample R
    have hsource :
        GeneralizedSubspaceLWE.Adaptive.sourceImpl sampleSampler (Sum.inr ()) =
          sampleSampler := by rfl
    have hplain :
        plainUniformImpl (Message := Message) (R := R) (Sum.inr messages) =
          ($ᵗ (R × R)) := by rfl
    have htranslated :
        evalDist ((fun sample : SourceSample R =>
          sourceSampleToRow (shiftSourceSample offset sample)) <$>
            ($ᵗ SourceSample R)) = evalDist ($ᵗ (R × R)) := by
      apply evalDist_map_bijective_uniform_cross
      exact (rowSourceEquiv R).symm.bijective.comp
        (shiftSourceSample_bijective offset)
    simpa [QueryImpl.apply_compose, sourceReduction, hsource, hplain,
      sampleSampler, offset, shiftSourceSample, sourceSampleToRow,
      map_eq_bind_pure_comp, bind_assoc] using htranslated

theorem evalDist_onlineUniform_eq_plain
    {Message Cloud R : Type}
    [AddCommGroup R] [Fintype R] [SampleableType R]
    (bit : Bool) (encode : Message → R)
    (adversary : Adversary Message Cloud (R × R)) (cloud : Cloud) :
    evalDist (simulateQ
        (GeneralizedSubspaceLWE.Adaptive.sourceImpl ($ᵗ SourceSample R))
        (simulateQ (sourceReduction bit encode) (adversary cloud))) =
      evalDist (simulateQ (plainUniformImpl (Message := Message) (R := R))
        (adversary cloud)) := by
  rw [← QueryImpl.simulateQ_compose]
  exact GeneralizedSubspaceLWE.Adaptive.evalDist_simulateQ_congr _ _
    (evalDist_uniformSource_compose_sourceReduction bit encode)
    (adversary cloud)

/-- A bounded adaptive adversary has success exactly one half against a
uniform eager query table, for every fixed public evaluation directory. -/
theorem uniformAdaptive_probOutput_true
    {Message Cloud R : Type}
    [AddCommGroup R] [Inhabited R] [Fintype R] [SampleableType R]
    (queryCount : ℕ) (encode : Message → R)
    (adversary : Adversary Message Cloud (R × R)) (cloud : Cloud)
    (hbound : IsQueryBoundP (adversary cloud)
      (isEncryptionQuery (Message := Message) (Ciphertext := R × R)) queryCount) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let rows ← $ᵗ (Fin queryCount → R × R)
      let guess ← runFromTable bit encode adversary cloud rows
      return bit == guess] = 1 / 2 := by
  let plainGuess := simulateQ (plainUniformImpl (Message := Message) (R := R))
    (adversary cloud)
  have hgame :
      evalDist (do
        let bit ← $ᵗ Bool
        let rows ← $ᵗ (Fin queryCount → R × R)
        let guess ← runFromTable bit encode adversary cloud rows
        return bit == guess) =
      evalDist (do
        let bit ← $ᵗ Bool
        let guess ← plainGuess
        return bit == guess) := by
    refine evalDist_bind_congr' ($ᵗ Bool) fun bit => ?_
    have htape := evalDist_uniformTable_runFromTable_eq_online
      queryCount bit encode adversary cloud hbound
    have honline := evalDist_onlineUniform_eq_plain bit encode adversary cloud
    simpa [plainGuess, bind_assoc] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (htape.trans honline) (fun guess => pure (bit == guess)))
  rw [evalDist_ext_iff.mp hgame true]
  exact FormalProof4FHE.TFHE.Encryption.Security.fairBit_eq_independentGuess plainGuess

/-! ## Application to the scalar compact-cover transcript -/

namespace Scalar

open CompactCoverBGVScalarSecurity CompactCoverCyclicCompiler

abbrev EvaluationDirectory (R : Type) := EvaluationRow → R × R
abbrev Cloud (R : Type) [CommRing R] := CompilerContext R × EvaluationDirectory R

def splitTranscript (queryCount : ℕ) (R : Type) :
    Transcript queryCount R ≃
      EvaluationDirectory R × (Fin queryCount → R × R) where
  toFun transcript :=
    (fun row => transcript (.evaluation row),
      fun query => transcript (.encryption query))
  invFun tables
    | .evaluation row => tables.1 row
    | .encryption query => tables.2 query
  left_inv transcript := by
    funext row
    cases row <;> rfl
  right_inv tables := by
    rcases tables with ⟨evaluation, queries⟩
    rfl

def cloudOf {queryCount : ℕ} {R : Type} [CommRing R]
    (view : ContextualView queryCount R) : Cloud R :=
  (view.1, fun row => view.2 (.evaluation row))

def queryRowsOf {queryCount : ℕ} {R : Type} [CommRing R]
    (view : ContextualView queryCount R) : Fin queryCount → R × R :=
  fun query => view.2 (.encryption query)

noncomputable def adaptiveDistinguisher
    {Message R : Type} [CommRing R] [Fintype R] [SampleableType R]
    (queryCount : ℕ) (encode : Message → R)
    (adversary : Adversary Message (Cloud R) (R × R)) :
    Distinguisher (ContextualView queryCount R) :=
  fun view => do
    let bit ← $ᵗ Bool
    let guess ← runFromTable bit encode adversary (cloudOf view) (queryRowsOf view)
    return bit == guess

noncomputable def uniformTranscriptGame
    {Message R : Type} [CommRing R] [Fintype R] [SampleableType R]
    (queryCount : ℕ) (encode : Message → R)
    (adversary : Adversary Message (Cloud R) (R × R))
    (context : CompilerContext R) : ProbComp Bool := do
  let transcript ← $ᵗ (Transcript queryCount R)
  adaptiveDistinguisher queryCount encode adversary (context, transcript)

theorem uniformTranscript_adaptive_probOutput_true
    {Message R : Type}
    [CommRing R] [Inhabited R] [Fintype R] [SampleableType R]
    (queryCount : ℕ) (encode : Message → R)
    (adversary : Adversary Message (Cloud R) (R × R))
    (hbound : IsQueryBound adversary queryCount)
    (context : CompilerContext R) :
    Pr[= true | uniformTranscriptGame queryCount encode adversary context] = 1 / 2 := by
  let Split := EvaluationDirectory R × (Fin queryCount → R × R)
  let split := splitTranscript queryCount R
  let finish := fun tables : Split => do
    let bit ← $ᵗ Bool
    let guess ← runFromTable bit encode adversary (context, tables.1) tables.2
    return bit == guess
  have hsplit :
      evalDist (split <$> ($ᵗ (Transcript queryCount R))) =
        evalDist ($ᵗ Split) :=
    evalDist_map_bijective_uniform_cross
      (α := Transcript queryCount R) (β := Split) split split.bijective
  have hproduct :
      evalDist (do
        let evaluation ← $ᵗ (EvaluationDirectory R)
        let queries ← $ᵗ (Fin queryCount → R × R)
        return (evaluation, queries)) = evalDist ($ᵗ Split) :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  have hgame :
      evalDist (uniformTranscriptGame queryCount encode adversary context) =
      evalDist (do
        let evaluation ← $ᵗ (EvaluationDirectory R)
        let queries ← $ᵗ (Fin queryCount → R × R)
        finish (evaluation, queries)) := by
    have hpoint (transcript : Transcript queryCount R) :
        adaptiveDistinguisher queryCount encode adversary (context, transcript) =
          finish (split transcript) := by rfl
    calc
      _ = evalDist (($ᵗ (Transcript queryCount R)) >>=
          fun transcript => finish (split transcript)) := by
        unfold uniformTranscriptGame
        exact evalDist_bind_congr' ($ᵗ (Transcript queryCount R)) fun transcript =>
          congrArg evalDist (hpoint transcript)
      _ = evalDist ((split <$> ($ᵗ (Transcript queryCount R))) >>= finish) := by
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
      _ = evalDist (($ᵗ Split) >>= finish) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hsplit finish
      _ = evalDist ((do
          let evaluation ← $ᵗ (EvaluationDirectory R)
          let queries ← $ᵗ (Fin queryCount → R × R)
          return (evaluation, queries)) >>= finish) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          hproduct.symm finish
      _ = _ := by simp only [bind_assoc, pure_bind]
  rw [evalDist_ext_iff.mp hgame true]
  have hevaluation (evaluation : EvaluationDirectory R) :
      Pr[= true | do
        let queries ← $ᵗ (Fin queryCount → R × R)
        finish (evaluation, queries)] = 1 / 2 := by
    let continuation := fun (queries : Fin queryCount → R × R) (bit : Bool) => do
      let guess ← runFromTable bit encode adversary (context, evaluation) queries
      return bit == guess
    have hcommute := OracleComp.DeferredSampling.evalDist_bind_comm
      ($ᵗ (Fin queryCount → R × R)) ($ᵗ Bool) continuation
    rw [evalDist_ext_iff.mp hcommute true]
    simpa [finish, continuation, bind_assoc] using
      uniformAdaptive_probOutput_true queryCount encode adversary
        (context, evaluation) (hbound (context, evaluation))
  rw [probOutput_bind_eq_tsum]
  simp_rw [hevaluation]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

/-- Averaging the fixed-context result over a total sampler of public contexts
preserves the exact one-half uniform-endpoint success probability. -/
theorem sampledContexts_adaptive_probOutput_true
    {Message R : Type} (queryCount : ℕ)
    [CommRing R] [Inhabited R] [Fintype R] [SampleableType R]
    [SampleableType (Transcript queryCount R)]
    (encode : Message → R)
    (adversary : Adversary Message (Cloud R) (R × R))
    (hbound : IsQueryBound adversary queryCount)
    (contextSampler : ProbComp (CompilerContext R))
    (contextTotal : NeverFail contextSampler) :
    Pr[= true | contextSampler >>= fun context =>
      uniformTranscriptGame queryCount encode adversary context] = 1 / 2 := by
  rw [probOutput_bind_eq_tsum]
  calc
    (∑' context, Pr[= context | contextSampler] *
        Pr[= true | uniformTranscriptGame queryCount encode adversary context]) =
      ∑' context, Pr[= context | contextSampler] * (1 / 2) := by
        apply tsum_congr
        intro context
        rw [uniformTranscript_adaptive_probOutput_true queryCount encode
          adversary hbound context]
    _ = 1 / 2 := by
      rw [ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' contextTotal.probFailure_eq_zero, one_mul]

def adaptivePublicConstants {queryCount : ℕ} {R : Type} [CommRing R]
    (evaluationConstants : CompilerContext R → EvaluationRow → R) :
    CompilerContext R → ScalarRow queryCount → R :=
  fun context row => match row with
    | .evaluation evaluation => evaluationConstants context evaluation
    | .encryption _ => 0

def adaptiveCompiledProblem
    (queryCount : ℕ) (R : Type)
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (Transcript queryCount R)]
    (message : CompilerContext R → ScalarRow queryCount → WitnessAffine R)
    (evaluationConstants : CompilerContext R → EvaluationRow → R)
    (realSource : ProbComp (ContextualView queryCount R)) :
    DecisionProblem (ContextualView queryCount R) :=
  contextualCompiledProblem queryCount R message
    (adaptivePublicConstants evaluationConstants) realSource

noncomputable def adaptiveGame
    {Message R : Type} (queryCount : ℕ)
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (Transcript queryCount R)]
    (encode : Message → R)
    (adversary : Adversary Message (Cloud R) (R × R))
    (problem : DecisionProblem (ContextualView queryCount R)) : ProbComp Bool :=
  problem.real >>= adaptiveDistinguisher queryCount encode adversary

/-- Generic final composition used after an adaptive uniform endpoint has been
shown to win with probability one half. -/
theorem adaptive_advantage_eq_source_of_exactReduction
    {SourceView TargetView : Type}
    {sourceProblem : DecisionProblem SourceView}
    {targetProblem : DecisionProblem TargetView}
    (reduction : ExactMapReduction sourceProblem targetProblem)
    (distinguisher : Distinguisher TargetView)
    (uniformHalf : Pr[= true | targetProblem.random >>= distinguisher] = 1 / 2) :
    |Pr[= true | targetProblem.real >>= distinguisher].toReal - 1 / 2| =
      advantage sourceProblem (reduction.pullback distinguisher) := by
  rw [reduction.advantage_pullback]
  unfold advantage ProbComp.boolDistAdvantage
  rw [uniformHalf]
  norm_num

end Scalar

end FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverBGVAdaptiveSecurity
