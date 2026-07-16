/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SubspaceLWE.Simulator
import FormalProof4FHE.LWE.Security
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-!
# Concrete Security of Adaptive Subspace LWE from Ordinary LWE

This module closes the concrete affine-fiber simulator, adaptive rank-loss,
and bounded online-to-batch compilation arguments. Its final theorem reduces
adaptive subspace-LWE security to ordinary matrix batch LWE with an explicit
Pietrzak rank-loss term.
-/

open Matrix OracleComp OracleSpec
open ENNReal
open scoped ENNReal
open OracleComp.ProgramLogic.Relational
namespace FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive

universe u

/-- A bad-flagged stateless handler is coupled to the same handler with an
input log; the flag is exactly the disjunction of the logged bad inputs. -/
theorem relTriple_badFlag_appendInputLog
    {iota : Type} {spec : OracleSpec iota} {alpha : Type}
    (base : QueryImpl spec ProbComp) (bad : spec.Domain → Bool)
    (computation : OracleComp spec alpha) :
    RelTriple
      ((simulateQ
        ((QueryImpl.Stateful.ofStateless base).withBadUpdate
          (fun t _ _ ↦ bad t)) computation).run (PUnit.unit, false))
      ((simulateQ (QueryImpl.appendInputLog base) computation).run [])
      (fun left right ↦ left.1 = right.1 ∧
        left.2.2 = right.2.any bad) := by
  let relation : PUnit × Bool → List spec.Domain → Prop :=
    fun left log ↦ left.2 = log.any bad
  apply relTriple_simulateQ_run
    ((QueryImpl.Stateful.ofStateless base).withBadUpdate
      (fun t _ _ ↦ bad t))
    (QueryImpl.appendInputLog base) relation computation
  · intro index left log hrelation
    rcases left with ⟨trivialState, fired⟩
    change fired = log.any bad at hrelation
    have hstep : RelTriple
        (base index >>= fun response ↦
          pure (response, (trivialState, fired || bad index)))
        (base index >>= fun response ↦
          pure (response, log ++ [index]))
        (fun (left : spec.Range index × (PUnit × Bool))
          (right : spec.Range index × List spec.Domain) ↦
          left.1 = right.1 ∧ relation left.2 right.2) :=
      relTriple_bind (relTriple_refl (base index))
        (fun response response' hresponse ↦ by
          subst response'
          exact relTriple_pure_pure ⟨rfl, by
            simp [relation, hrelation]⟩)
    simpa [QueryImpl.Stateful.ofStateless, QueryImpl.appendInputLog,
      QueryImpl.preInsert, QueryImpl.withBadUpdate, monad_norm] using hstep
  · simp [relation]

/-- Discarding the input log recovers the underlying stateless simulation. -/
theorem run'_simulateQ_appendInputLog_eq
    {iota : Type} {spec : OracleSpec iota} {alpha : Type}
    (base : QueryImpl spec ProbComp) (computation : OracleComp spec alpha)
    (initial : List spec.Domain) :
    (simulateQ (QueryImpl.appendInputLog base) computation).run' initial =
      simulateQ base computation := by
  induction computation using OracleComp.inductionOn generalizing initial with
  | pure output => simp
  | query_bind index continuation ih =>
      simp only [StateT.run'_eq] at ih ⊢
      simp [QueryImpl.appendInputLog, QueryImpl.preInsert, monad_norm]
      apply bind_congr
      intro response
      simpa [QueryImpl.appendInputLog_eq_preInsert,
        map_eq_bind_pure_comp] using ih response (initial ++ [index])

/-- Discarding the bad flag recovers the underlying stateless simulation. -/
theorem evalDist_run'_simulateQ_badFlag_eq
    {iota : Type} {spec : OracleSpec iota} {alpha : Type}
    (base : QueryImpl spec ProbComp) (bad : spec.Domain → Bool)
    (computation : OracleComp spec alpha) :
    evalDist ((simulateQ
      ((QueryImpl.Stateful.ofStateless base).withBadUpdate
        (fun index _ _ ↦ bad index)) computation).run' (PUnit.unit, false)) =
      evalDist (simulateQ base computation) := by
  calc
    evalDist ((simulateQ
        ((QueryImpl.Stateful.ofStateless base).withBadUpdate
          (fun index _ _ ↦ bad index)) computation).run' (PUnit.unit, false)) =
      evalDist ((simulateQ (QueryImpl.appendInputLog base) computation).run' []) := by
        simp only [StateT.run'_eq]
        apply evalDist_map_eq_of_relTriple
        exact relTriple_post_mono
          (relTriple_badFlag_appendInputLog base bad computation)
          (fun _ _ h ↦ h.1)
    _ = evalDist (simulateQ base computation) := by
      rw [run'_simulateQ_appendInputLog_eq]

/-- Identical-until-bad for two stateless handlers with a response-independent
per-input bad predicate. -/
theorem tvDist_simulateQ_le_probEvent_badFlag
    {iota : Type} {spec : OracleSpec iota} {alpha : Type}
    (first second : QueryImpl spec ProbComp) (bad : spec.Domain → Bool)
    (computation : OracleComp spec alpha)
    (hgood : ∀ index, bad index = false →
      evalDist (first index) = evalDist (second index)) :
    tvDist (simulateQ first computation) (simulateQ second computation) ≤
      Pr[(fun result : alpha × (PUnit × Bool) ↦ result.2.2 = true) |
        (simulateQ
          ((QueryImpl.Stateful.ofStateless first).withBadUpdate
            (fun index _ _ ↦ bad index)) computation).run
          (PUnit.unit, false)].toReal := by
  let firstFlagged :=
    (QueryImpl.Stateful.ofStateless first).withBadUpdate
      (fun index _ _ ↦ bad index)
  let secondFlagged :=
    (QueryImpl.Stateful.ofStateless second).withBadUpdate
      (fun index _ _ ↦ bad index)
  have hagree : ∀ (index : spec.Domain) (state : PUnit)
      (response : spec.Range index) (state' : PUnit),
      Pr[= (response, (state', false)) |
        (firstFlagged index).run (state, false)] =
      Pr[= (response, (state', false)) |
        (secondFlagged index).run (state, false)] := by
    intro index state response state'
    cases Subsingleton.elim state PUnit.unit
    cases Subsingleton.elim state' PUnit.unit
    cases hbad : bad index with
    | true =>
        simp [firstFlagged, secondFlagged, QueryImpl.Stateful.ofStateless,
          QueryImpl.withBadUpdate, hbad]
    | false =>
        apply probOutput_congr rfl
        simp only [firstFlagged, secondFlagged,
          QueryImpl.withBadUpdate_apply_run]
        apply evalDist_map_eq_of_evalDist_eq
        simpa [QueryImpl.Stateful.ofStateless, QueryImpl.liftTarget_apply,
          StateT.run_monadLift, monadLift_self,
          map_eq_bind_pure_comp] using
            (evalDist_map_eq_of_evalDist_eq (hgood index hbad)
              (fun response ↦ (response, PUnit.unit)))
  have hmonoFirst : ∀ (index : spec.Domain) (state : PUnit × Bool),
      state.2 = true → ∀ result ∈ support ((firstFlagged index).run state),
        result.2.2 = true := by
    intro index state hstate result hresult
    change result ∈ support
      ((fun source ↦ (source.1, source.2,
        state.2 || bad index)) <$>
        ((QueryImpl.Stateful.ofStateless first index).run state.1)) at hresult
    obtain ⟨source, _, rfl⟩ :=
      OracleComp.mem_support_map_peel _ _ hresult
    simp [hstate]
  have hmonoSecond : ∀ (index : spec.Domain) (state : PUnit × Bool),
      state.2 = true → ∀ result ∈ support ((secondFlagged index).run state),
        result.2.2 = true := by
    intro index state hstate result hresult
    change result ∈ support
      ((fun source ↦ (source.1, source.2,
        state.2 || bad index)) <$>
        ((QueryImpl.Stateful.ofStateless second index).run state.1)) at hresult
    obtain ⟨source, _, rfl⟩ :=
      OracleComp.mem_support_map_peel _ _ hresult
    simp [hstate]
  calc
    tvDist (simulateQ first computation) (simulateQ second computation) =
        tvDist ((simulateQ firstFlagged computation).run' (PUnit.unit, false))
          ((simulateQ secondFlagged computation).run' (PUnit.unit, false)) := by
            simp only [tvDist]
            rw [evalDist_run'_simulateQ_badFlag_eq first bad computation,
              evalDist_run'_simulateQ_badFlag_eq second bad computation]
    _ ≤ tvDist ((simulateQ firstFlagged computation).run (PUnit.unit, false))
          ((simulateQ secondFlagged computation).run (PUnit.unit, false)) := by
            simp only [StateT.run'_eq]
            exact tvDist_map_le Prod.fst _ _
    _ ≤ Pr[(fun result : alpha × (PUnit × Bool) ↦ result.2.2 = true) |
          (simulateQ firstFlagged computation).run (PUnit.unit, false)].toReal :=
      tvDist_simulateQ_run_le_probEvent_output_bad
        firstFlagged secondFlagged computation PUnit.unit
          hagree hmonoFirst hmonoSecond

/-- Averaging pointwise TV bounds expressed by continuation bad events gives
the bad probability of the combined run. -/
theorem tvDist_bind_left_le_probEvent_cont
    {Prefix Output BadOutput : Type} (prefixSampler : ProbComp Prefix)
    (first second : Prefix → ProbComp Output)
    (badRun : Prefix → ProbComp BadOutput) (badEvent : BadOutput → Prop)
    (hpoint : ∀ prefixValue,
      tvDist (first prefixValue) (second prefixValue) ≤
        Pr[badEvent | badRun prefixValue].toReal) :
    tvDist (prefixSampler >>= first) (prefixSampler >>= second) ≤
      Pr[badEvent | prefixSampler >>= badRun].toReal := by
  have hprobSummable : Summable
      (fun value : Prefix ↦ Pr[= value | prefixSampler].toReal) :=
    ENNReal.summable_toReal
      (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
  have hlhsSummable : Summable (fun value : Prefix ↦
      Pr[= value | prefixSampler].toReal *
        tvDist (first value) (second value)) :=
    hprobSummable.of_nonneg_of_le
      (fun _ ↦ mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
      (fun _ ↦ mul_le_of_le_one_right ENNReal.toReal_nonneg
        (tvDist_le_one _ _))
  have hrhsSummable : Summable (fun value : Prefix ↦
      Pr[= value | prefixSampler].toReal * Pr[badEvent | badRun value].toReal) :=
    hprobSummable.of_nonneg_of_le
      (fun _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun _ ↦ mul_le_of_le_one_right ENNReal.toReal_nonneg
        (ENNReal.toReal_mono one_ne_top probEvent_le_one))
  calc
    tvDist (prefixSampler >>= first) (prefixSampler >>= second) ≤
        ∑' value, Pr[= value | prefixSampler].toReal *
          tvDist (first value) (second value) :=
      tvDist_bind_left_le prefixSampler first second
    _ ≤ ∑' value, Pr[= value | prefixSampler].toReal *
          Pr[badEvent | badRun value].toReal :=
      Summable.tsum_le_tsum
        (fun value ↦ mul_le_mul_of_nonneg_left (hpoint value)
          ENNReal.toReal_nonneg) hlhsSummable hrhsSummable
    _ = Pr[badEvent | prefixSampler >>= badRun].toReal := by
      rw [probEvent_bind_eq_tsum, ENNReal.tsum_toReal_eq]
      · exact tsum_congr fun value ↦ ENNReal.toReal_mul.symm
      · intro value
        exact ENNReal.mul_ne_top
          (ne_top_of_le_ne_top one_ne_top probOutput_le_one)
          probEvent_ne_top

/-- Pointwise equality of stateless handler distributions lifts through a
free-monad simulation. -/
theorem evalDist_simulateQ_congr
    {Index : Type} {spec : OracleSpec Index} {alpha : Type}
    (first second : QueryImpl spec ProbComp)
    (hstep : ∀ index, evalDist (first index) = evalDist (second index))
    (computation : OracleComp spec alpha) :
    evalDist (simulateQ first computation) =
      evalDist (simulateQ second computation) := by
  induction computation using OracleComp.inductionOn with
  | pure output => rfl
  | query_bind index continuation ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      rw [evalDist_bind, hstep index, ← evalDist_bind]
      exact evalDist_bind_congr'
        (second index) (fun response ↦ ih response)

/-- A predicate query bound controls the number of charged inputs in every
support trace produced by `appendInputLog`. -/
theorem countP_le_of_mem_support_run_appendInputLog
    {iota : Type} {spec : OracleSpec iota} {alpha : Type}
    (base : QueryImpl spec ProbComp) (charged : spec.Domain → Prop)
    [DecidablePred charged] (computation : OracleComp spec alpha)
    (budget : ℕ) (hbound : IsQueryBoundP computation charged budget)
    (initial : List spec.Domain) {result : alpha × List spec.Domain}
    (hresult : result ∈ support
      ((simulateQ (QueryImpl.appendInputLog base) computation).run initial)) :
    result.2.countP charged ≤ initial.countP charged + budget := by
  induction computation using OracleComp.inductionOn generalizing budget initial result with
  | pure output =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact Nat.le_add_right _ _
  | query_bind index continuation ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind,
        QueryImpl.run_appendInputLog_apply, support_bind,
        Set.mem_iUnion, exists_prop] at hresult
      obtain ⟨⟨response, middle⟩, hhead, htail⟩ := hresult
      obtain ⟨actualResponse, _, hpure⟩ := hhead
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      cases hpure
      have hrec := ih response (if charged index then budget - 1 else budget)
        (hbound.2 response) (initial ++ [index]) htail
      simp only [List.countP_append, List.countP_singleton] at hrec
      by_cases hcharged : charged index
      · simp [hcharged] at hrec
        have hpositive : 0 < budget := by
          rcases hbound.1 with hfalse | hpos
          · exact absurd hcharged hfalse
          · exact hpos
        omega
      · simp [hcharged] at hrec
        exact hrec

/-- Union bound over a fixed log, charging only inputs selected by `charged`. -/
theorem probEvent_list_any_bad_le_countP {Hidden Index : Type}
    (hiddenSampler : ProbComp Hidden) (bad : Hidden → Index → Bool)
    (charged : Index → Prop) [DecidablePred charged] (ε : ℝ≥0∞)
    (hfixed : ∀ index, charged index →
      Pr[(fun hidden ↦ bad hidden index = true) | hiddenSampler] ≤ ε)
    (hfree : ∀ hidden index, ¬ charged index → bad hidden index = false)
    (log : List Index) :
    Pr[(fun hidden ↦ log.any (bad hidden) = true) | hiddenSampler] ≤
      (log.countP charged : ℝ≥0∞) * ε := by
  induction log with
  | nil => simp
  | cons head tail ih =>
      by_cases hcharged : charged head
      · calc
          Pr[(fun hidden ↦ (head :: tail).any (bad hidden) = true) | hiddenSampler] ≤
              Pr[(fun hidden ↦ bad hidden head = true) | hiddenSampler] +
                Pr[(fun hidden ↦ tail.any (bad hidden) = true) | hiddenSampler] := by
                simpa [Bool.or_eq_true] using probEvent_or_le hiddenSampler
                  (fun hidden ↦ bad hidden head = true)
                  (fun hidden ↦ tail.any (bad hidden) = true)
          _ ≤ ε + (tail.countP charged : ℝ≥0∞) * ε :=
            add_le_add (hfixed head hcharged) ih
          _ = ((head :: tail).countP charged : ℝ≥0∞) * ε := by
            simp [hcharged, add_mul, add_comm]
      · have hhead : ∀ hidden, bad hidden head = false :=
          fun hidden ↦ hfree hidden head hcharged
        simpa [hhead, hcharged] using ih

/-- A hidden-input, query-bounded bad flag obeys the adaptive union bound
whenever the base handler is independent of the hidden input. -/
theorem probEvent_hidden_badFlag_le {Hidden Index : Type}
    {spec : OracleSpec Index} {alpha : Type}
    (hiddenSampler : ProbComp Hidden) (base : QueryImpl spec ProbComp)
    (bad : Hidden → spec.Domain → Bool)
    (charged : spec.Domain → Prop) [DecidablePred charged]
    (computation : OracleComp spec alpha) (budget : ℕ)
    (hbound : IsQueryBoundP computation charged budget) (ε : ℝ≥0∞)
    (hfixed : ∀ index, charged index →
      Pr[(fun hidden ↦ bad hidden index = true) | hiddenSampler] ≤ ε)
    (hfree : ∀ hidden index, ¬charged index → bad hidden index = false) :
    Pr[(fun fired : Bool ↦ fired = true) |
      do
        let hidden ← hiddenSampler
        (fun result : alpha × (PUnit × Bool) ↦ result.2.2) <$>
          (simulateQ
            ((QueryImpl.Stateful.ofStateless base).withBadUpdate
              (fun index _ _ ↦ bad hidden index)) computation).run
            (PUnit.unit, false)] ≤ (budget : ℝ≥0∞) * ε := by
  let loggedRun : ProbComp (alpha × List spec.Domain) :=
    (simulateQ (QueryImpl.appendInputLog base) computation).run []
  let flaggedRun (hidden : Hidden) : ProbComp Bool :=
    (fun result : alpha × (PUnit × Bool) ↦ result.2.2) <$>
      (simulateQ
        ((QueryImpl.Stateful.ofStateless base).withBadUpdate
          (fun index _ _ ↦ bad hidden index)) computation).run
        (PUnit.unit, false)
  let loggedBad (hidden : Hidden) : ProbComp Bool :=
    (fun result ↦ result.2.any (bad hidden)) <$> loggedRun
  have hstep : ∀ hidden, evalDist (flaggedRun hidden) = evalDist (loggedBad hidden) := by
    intro hidden
    dsimp [flaggedRun, loggedBad, loggedRun]
    apply evalDist_map_eq_of_relTriple
    exact relTriple_post_mono
      (relTriple_badFlag_appendInputLog base (bad hidden) computation)
      (fun _ _ h ↦ h.2)
  calc
    Pr[(fun fired : Bool ↦ fired = true) |
        do
          let hidden ← hiddenSampler
          (fun result : alpha × (PUnit × Bool) ↦ result.2.2) <$>
            (simulateQ
              ((QueryImpl.Stateful.ofStateless base).withBadUpdate
                (fun index _ _ ↦ bad hidden index)) computation).run
              (PUnit.unit, false)] =
      Pr[(fun fired : Bool ↦ fired = true) |
        hiddenSampler >>= loggedBad] := by
          exact probEvent_congr' (fun _ _ ↦ Iff.rfl)
            (evalDist_bind_congr' hiddenSampler hstep)
    _ = Pr[(fun fired : Bool ↦ fired = true) |
        loggedRun >>= fun result ↦
          hiddenSampler >>= fun hidden ↦
            pure (result.2.any (bad hidden))] := by
          exact probEvent_congr' (fun _ _ ↦ Iff.rfl)
            (by
              simpa [loggedBad, map_eq_bind_pure_comp] using
                (OracleComp.DeferredSampling.evalDist_bind_comm
                  hiddenSampler loggedRun
                    (fun hidden result ↦ pure (result.2.any (bad hidden)))))
    _ ≤ (budget : ℝ≥0∞) * ε := by
      apply probEvent_bind_le_of_forall_le
      intro result hresult
      calc
        Pr[(fun fired : Bool ↦ fired = true) |
            hiddenSampler >>= fun hidden ↦
              pure (result.2.any (bad hidden))] =
            Pr[(fun hidden ↦ result.2.any (bad hidden) = true) |
              hiddenSampler] := by
                change Pr[(fun fired : Bool ↦ fired = true) |
                  hiddenSampler >>= pure ∘
                    (fun hidden ↦ result.2.any (bad hidden))] = _
                rw [probEvent_bind_pure_comp]
                rfl
        _ ≤ (result.2.countP charged : ℝ≥0∞) * ε :=
          probEvent_list_any_bad_le_countP hiddenSampler bad charged ε
            hfixed hfree result.2
        _ ≤ (budget : ℝ≥0∞) * ε := by
          gcongr
          have hcount : result.2.countP charged ≤ budget := by
            simpa using countP_le_of_mem_support_run_appendInputLog
              base charged computation budget hbound [] hresult
          exact_mod_cast hcount

/-! ## Concrete adaptive-SLWE handlers -/

/-- One online real-LWE value for a public challenge. -/
def realLWEValue {F : Type} [Semiring F] {dimension : ℕ}
    (secret : Fin dimension → F) (errorSampler : ProbComp F)
    (challenge : Fin dimension → F) : ProbComp F := do
  let error ← errorSampler
  pure (dotProduct challenge secret + error)

/-- Stateless affine-fiber simulator, with rank loss represented by `none`. -/
noncomputable def simulatedQueryImpl {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (valueSampler : (Fin dimension → F) → ProbComp F) :
    QueryImpl (Query F ambient →ₒ Response F ambient) ProbComp := by
  classical
  intro query
  exact if hadmissible : query.IsAdmissible threshold then
    if hfull : (query.overlap * hidden).rank = dimension then
      goodSimulator query hidden blinding hfull valueSampler
    else pure none
  else pure none

/-- Add the adversary's internal uniform oracle to the concrete simulator. -/
noncomputable def simulatedFullImpl {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (valueSampler : (Fin dimension → F) → ProbComp F) :
    QueryImpl (OracleInterface F ambient) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    simulatedQueryImpl threshold hidden blinding valueSampler

/-- Composing the concrete source-oracle reduction with an online LWE sample
handler has exactly the direct stateless simulator semantics. -/
theorem evalDist_source_compose_simulatorReduction {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (valueSampler : (Fin dimension → F) → ProbComp F)
    (index : (OracleInterface F ambient).Domain) :
    evalDist ((sourceImpl (pairSamplerFromValue valueSampler) ∘ₛ
      simulatorReduction threshold hidden blinding) index) =
      evalDist (simulatedFullImpl threshold hidden blinding valueSampler index) := by
  classical
  rcases index with uniformIndex | query
  · simp [QueryImpl.apply_compose, simulatorReduction, sourceImpl,
      simulatedFullImpl]
    intro response
    change Pr[= response | (QueryImpl.id' unifSpec) uniformIndex] = _
    simp
  · by_cases hadmissible : query.IsAdmissible threshold
    · by_cases hfull : (query.overlap * hidden).rank = dimension
      · change evalDist (simulateQ (sourceImpl (pairSamplerFromValue valueSampler))
            (simulatorReduction threshold hidden blinding (Sum.inr query))) =
          evalDist (simulatedQueryImpl threshold hidden blinding valueSampler query)
        calc
          evalDist (simulateQ (sourceImpl (pairSamplerFromValue valueSampler))
              (simulatorReduction threshold hidden blinding (Sum.inr query))) =
            evalDist (pairedGoodSimulator query hidden blinding hfull
              (pairSamplerFromValue valueSampler)) :=
                evalDist_sourceImpl_simulatorReduction_of_admissible_full
                  threshold hidden blinding query hadmissible hfull
                    (pairSamplerFromValue valueSampler)
          _ = evalDist (goodSimulator query hidden blinding hfull valueSampler) :=
            evalDist_pairedGoodSimulator_eq_goodSimulator
              query hidden blinding hfull valueSampler
          _ = evalDist (simulatedQueryImpl threshold hidden blinding
              valueSampler query) := by
                simp [simulatedQueryImpl, hadmissible, hfull]
      · simp [QueryImpl.apply_compose, simulatorReduction, sourceImpl,
          simulatedFullImpl, simulatedQueryImpl, hadmissible, hfull]
    · simp [QueryImpl.apply_compose, simulatorReduction, sourceImpl,
        simulatedFullImpl, simulatedQueryImpl, hadmissible]

/-- Whole-program form of the concrete source-composition equality. -/
theorem evalDist_source_simulator_eq_direct {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (valueSampler : (Fin dimension → F) → ProbComp F)
    (adversary : Adversary F ambient) :
    evalDist (simulateQ (sourceImpl (pairSamplerFromValue valueSampler))
      (simulateQ (simulatorReduction threshold hidden blinding) adversary)) =
      evalDist (simulateQ
        (simulatedFullImpl threshold hidden blinding valueSampler) adversary) := by
  rw [← QueryImpl.simulateQ_compose]
  exact evalDist_simulateQ_congr
    (sourceImpl (pairSamplerFromValue valueSampler) ∘ₛ
      simulatorReduction threshold hidden blinding)
    (simulatedFullImpl threshold hidden blinding valueSampler)
    (evalDist_source_compose_simulatorReduction threshold hidden blinding valueSampler)
    adversary

/-- The distinguished right source query consumes one pre-generated LWE sample. -/
def isSourceSample {F : Type} {dimension : ℕ} :
    (SourceInterface F dimension).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance instDecidablePredIsSourceSample {F : Type} {dimension : ℕ} :
    DecidablePred (isSourceSample (F := F) (dimension := dimension))
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Lifting an internal probabilistic computation into the left source summand
does not consume a source-sample query. -/
theorem isQueryBoundP_liftProbComp_left {F : Type} {dimension : ℕ}
    {alpha : Type} (computation : ProbComp alpha) :
    IsQueryBoundP
      (liftM computation : OracleComp (SourceInterface F dimension) alpha)
      (isSourceSample (F := F) (dimension := dimension)) 0 := by
  rw [← OracleComp.liftComp_eq_liftM]
  induction computation using OracleComp.inductionOn with
  | pure output => simp
  | query_bind index continuation ih =>
      rw [OracleComp.liftComp_bind]
      have hhead : IsQueryBoundP
          (OracleComp.liftComp
            (liftM (unifSpec.query index) : ProbComp (unifSpec.Range index))
            (SourceInterface F dimension))
          (isSourceSample (F := F) (dimension := dimension)) 0 := by
        rw [OracleComp.liftComp_query, isQueryBoundP_map_iff]
        change (¬ isSourceSample (F := F) (dimension := dimension) (Sum.inl index) ∨
          0 < 0) ∧ ∀ _ : unifSpec.Range index, True
        simp [isSourceSample]
      simpa using isQueryBoundP_bind (n := 0) (m := 0) hhead
        (fun response _ ↦ ih response)

/-- Rank loss as a predicate on the sum-interface input. -/
noncomputable def rankLossInput {F : Type} [Field F] [DecidableEq F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F) :
    (OracleInterface F ambient).Domain → Bool
  | .inl _ => false
  | .inr query => rankLoss dimension threshold hidden query

/-- Only adaptive SLWE calls, not internal random-bit calls, consume the public query budget. -/
def isSLWEQuery {F : Type} {ambient : ℕ} :
    (OracleInterface F ambient).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance instDecidablePredIsSLWEQuery {F : Type} {ambient : ℕ} :
    DecidablePred (isSLWEQuery (F := F) (ambient := ambient))
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- The concrete reduction makes at most one source-sample query per adaptive
SLWE query and none per internal uniform query. -/
theorem simulatorReduction_isQueryBoundP {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold queryCount : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F) (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) queryCount) :
    IsQueryBoundP
      (simulateQ (simulatorReduction threshold hidden blinding) adversary)
      (isSourceSample (F := F) (dimension := dimension)) queryCount := by
  letI : Inhabited F := ⟨0⟩
  letI : IsUniformSpec (Unit →ₒ LWESample F dimension) :=
    IsUniformSpec.ofFintypeInhabited _
  apply IsQueryBoundP.simulateQ_of_step hbound
  · intro index hcharged
    rcases index with uniformIndex | query
    · simp [isSLWEQuery] at hcharged
    · by_cases hadmissible : query.IsAdmissible threshold
      · by_cases hfull : (query.overlap * hidden).rank = dimension
        · simp only [simulatorReduction, hadmissible, hfull, dif_pos]
          let sourceQuery : OracleComp (SourceInterface F dimension)
              (LWESample F dimension) :=
            liftM ((SourceInterface F dimension).query (Sum.inr ()))
          let continuation (sample : LWESample F dimension) :
              OracleComp (SourceInterface F dimension) (Response F ambient) := do
            let randomness ← liftM
              (samplePreimage (query.overlap * hidden).vecMulLinear
                (vecMul_surjective_of_rank_eq_width ambient dimension
                  (query.overlap * hidden) hfull)
                (simulatorTarget query hidden sample.1))
            pure (some (randomness,
              sample.2 + simulatorCorrection query blinding randomness))
          change IsQueryBoundP (sourceQuery >>= continuation)
            (isSourceSample (F := F) (dimension := dimension)) 1
          have hsource : IsQueryBoundP sourceQuery
              (isSourceSample (F := F) (dimension := dimension)) 1 := by
            dsimp [sourceQuery]
            change (¬ isSourceSample (F := F) (dimension := dimension) (Sum.inr ()) ∨
              0 < 1) ∧ ∀ _ : LWESample F dimension, True
            simp [isSourceSample]
          have hcontinuation : ∀ sample ∈ support sourceQuery,
              IsQueryBoundP (continuation sample)
                (isSourceSample (F := F) (dimension := dimension)) 0 := by
            intro sample _
            have hpreimage := isQueryBoundP_liftProbComp_left
              (F := F) (dimension := dimension)
              (samplePreimage (query.overlap * hidden).vecMulLinear
                (vecMul_surjective_of_rank_eq_width ambient dimension
                  (query.overlap * hidden) hfull)
                (simulatorTarget query hidden sample.1))
            dsimp [continuation]
            simpa using hpreimage
          simpa using isQueryBoundP_bind (n := 1) (m := 0)
            hsource hcontinuation
        · simp [simulatorReduction, hadmissible, hfull]
      · simp [simulatorReduction, hadmissible]
  · intro index hfree
    rcases index with uniformIndex | query
    · exact isQueryBoundP_liftProbComp_left
        (liftM (unifSpec.query uniformIndex) : ProbComp (unifSpec.Range uniformIndex))
    · simp [isSLWEQuery] at hfree

/-- Before rank loss, the real online-LWE simulator has exactly the honest
adaptive-SLWE one-step distribution. -/
theorem evalDist_simulatedFullImpl_real_of_not_rankLoss {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F) (secret : Fin dimension → F)
    (errorSampler : ProbComp F) (index : (OracleInterface F ambient).Domain)
    (hgood : rankLossInput threshold hidden index = false) :
    evalDist (simulatedFullImpl threshold hidden blinding
      (realLWEValue secret errorSampler) index) =
      evalDist (fullImpl threshold (hidden *ᵥ secret + blinding)
        errorSampler index) := by
  classical
  rcases index with uniformIndex | query
  · rfl
  · by_cases hadmissible : query.IsAdmissible threshold
    · have hnotlt : ¬ (query.overlap * hidden).rank < dimension := by
        simpa [rankLossInput, rankLoss, hadmissible] using hgood
      have hrankle : (query.overlap * hidden).rank ≤ dimension :=
        Matrix.rank_le_width _
      have hfull : (query.overlap * hidden).rank = dimension :=
        Nat.le_antisymm hrankle (Nat.le_of_not_gt hnotlt)
      simp only [simulatedFullImpl, fullImpl, QueryImpl.add_apply_inr]
      simp [simulatedQueryImpl, hadmissible, hfull,
        queryImpl_of_admissible]
      have hvalue : realLWEValue secret errorSampler =
          (fun challenge ↦ do
            let error ← errorSampler
            pure (dotProduct challenge secret + error)) := by
        funext challenge
        rfl
      rw [hvalue]
      simpa [map_eq_bind_pure_comp, monad_norm] using
        (evalDist_goodSimulator_real query hidden blinding hfull secret errorSampler)
    · simp [simulatedFullImpl, fullImpl, simulatedQueryImpl,
        hadmissible, queryImpl_of_not_admissible]

/-- Before rank loss, the uniform-value simulator has exactly the honest
uniform-error adaptive-SLWE one-step distribution. -/
theorem evalDist_simulatedFullImpl_uniform_of_not_rankLoss {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding secret : Fin ambient → F)
    (index : (OracleInterface F ambient).Domain)
    (hgood : rankLossInput threshold hidden index = false) :
    evalDist (simulatedFullImpl threshold hidden blinding
      (fun _ ↦ $ᵗ F) index) =
      evalDist (fullImpl threshold secret ($ᵗ F) index) := by
  classical
  rcases index with uniformIndex | query
  · rfl
  · by_cases hadmissible : query.IsAdmissible threshold
    · have hnotlt : ¬ (query.overlap * hidden).rank < dimension := by
        simpa [rankLossInput, rankLoss, hadmissible] using hgood
      have hrankle : (query.overlap * hidden).rank ≤ dimension :=
        Matrix.rank_le_width _
      have hfull : (query.overlap * hidden).rank = dimension :=
        Nat.le_antisymm hrankle (Nat.le_of_not_gt hnotlt)
      simp only [simulatedFullImpl, fullImpl, QueryImpl.add_apply_inr]
      calc
        evalDist (simulatedQueryImpl threshold hidden blinding
            (fun _ ↦ $ᵗ F) query) =
            evalDist (goodSimulator query hidden blinding hfull
              (fun _ ↦ $ᵗ F)) := by
                simp [simulatedQueryImpl, hadmissible, hfull]
        _ = evalDist (uniformResponse (R := F) ambient) :=
          evalDist_goodSimulator_uniform query hidden blinding hfull
        _ = evalDist (queryImpl threshold secret ($ᵗ F) query) :=
          (evalDist_queryImpl_uniform_of_admissible
            threshold secret query hadmissible).symm
    · simp [simulatedFullImpl, fullImpl, simulatedQueryImpl,
        hadmissible, queryImpl_of_not_admissible]

/-- Honest execution with a monotone flag for rank loss, projected to the flag. -/
noncomputable def honestRankLossRun {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (secret : Fin ambient → F) (errorSampler : ProbComp F)
    (adversary : Adversary F ambient) : ProbComp Bool :=
  (fun result : Bool × (PUnit × Bool) ↦ result.2.2) <$>
    (simulateQ
      ((QueryImpl.Stateful.ofStateless
        (fullImpl threshold secret errorSampler)).withBadUpdate
          (fun index _ _ ↦ rankLossInput threshold hidden index))
      adversary).run (PUnit.unit, false)

/-- Honest adaptive responses reveal no information about the independent hidden
matrix, so the direct logged-transcript union bound applies. -/
theorem probEvent_honestRankLoss_le_pietrzak {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (slack queryCount : ℕ)
    (secret : Fin ambient → F) (errorSampler : ProbComp F)
    (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) queryCount) :
    Pr[(fun fired : Bool ↦ fired = true) |
      do
        let hidden ← $ᵗ HiddenMatrix F ambient dimension
        (fun result : Bool × (PUnit × Bool) ↦ result.2.2) <$>
          (simulateQ
            ((QueryImpl.Stateful.ofStateless
              (fullImpl (dimension + slack) secret errorSampler)).withBadUpdate
                (fun index _ _ ↦
                  rankLossInput (dimension + slack) hidden index))
            adversary).run (PUnit.unit, false)] ≤
      (queryCount : ℝ≥0∞) * pietrzakRankError F slack := by
  apply probEvent_hidden_badFlag_le
    ($ᵗ HiddenMatrix F ambient dimension)
    (fullImpl (dimension + slack) secret errorSampler)
    (fun hidden index ↦ rankLossInput (dimension + slack) hidden index)
    (isSLWEQuery (F := F)) adversary queryCount hbound
    (pietrzakRankError F slack)
  · intro index hcharged
    rcases index with uniformIndex | query
    · simp [isSLWEQuery] at hcharged
    · simpa [rankLossInput] using
        (fixedRankLossBound_pietrzak ambient dimension slack query)
  · intro hidden index hfree
    rcases index with uniformIndex | query
    · rfl
    · simp [isSLWEQuery] at hfree

/-- Replacing the uniform affine blinding by the resulting secret makes the
hidden matrix independent of the honest transcript; hence the same adaptive
rank bound applies to the affine simulator coupling. -/
theorem probEvent_affineHonestRankLoss_le_pietrzak {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (slack queryCount : ℕ)
    (sourceSecret : Fin dimension → F) (errorSampler : ProbComp F)
    (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) queryCount) :
    Pr[(fun fired : Bool ↦ fired = true) |
      do
        let hidden ← $ᵗ HiddenMatrix F ambient dimension
        let blinding ← $ᵗ (Fin ambient → F)
        honestRankLossRun (dimension + slack) hidden
          (hidden *ᵥ sourceSecret + blinding) errorSampler adversary] ≤
      (queryCount : ℝ≥0∞) * pietrzakRankError F slack := by
  let hiddenSampler : ProbComp (HiddenMatrix F ambient dimension) :=
    $ᵗ HiddenMatrix F ambient dimension
  let secretSampler : ProbComp (Fin ambient → F) := $ᵗ (Fin ambient → F)
  let badRun (hidden : HiddenMatrix F ambient dimension)
      (secret : Fin ambient → F) : ProbComp Bool :=
    honestRankLossRun (dimension + slack) hidden secret errorSampler adversary
  have hshift : ∀ hidden,
      evalDist (do
        let blinding ← secretSampler
        badRun hidden (hidden *ᵥ sourceSecret + blinding)) =
      evalDist (do
        let secret ← secretSampler
        badRun hidden secret) := by
    intro hidden
    simpa [secretSampler, badRun, add_comm] using
      (evalDist_bind_bijective_add_right_uniform
        (α := Fin ambient → F) (β := Fin ambient → F)
        (γ := Bool) id Function.bijective_id (hidden *ᵥ sourceSecret)
        (badRun hidden))
  calc
    Pr[(fun fired : Bool ↦ fired = true) |
        do
          let hidden ← $ᵗ HiddenMatrix F ambient dimension
          let blinding ← $ᵗ (Fin ambient → F)
          honestRankLossRun (dimension + slack) hidden
            (hidden *ᵥ sourceSecret + blinding) errorSampler adversary] =
      Pr[(fun fired : Bool ↦ fired = true) |
        do
          let hidden ← hiddenSampler
          let secret ← secretSampler
          badRun hidden secret] := by
            exact probEvent_congr' (fun _ _ ↦ Iff.rfl)
              (evalDist_bind_congr' hiddenSampler hshift)
    _ = Pr[(fun fired : Bool ↦ fired = true) |
        do
          let secret ← secretSampler
          let hidden ← hiddenSampler
          badRun hidden secret] := by
            exact probEvent_congr' (fun _ _ ↦ Iff.rfl)
              (OracleComp.DeferredSampling.evalDist_bind_comm
                hiddenSampler secretSampler badRun)
    _ ≤ (queryCount : ℝ≥0∞) * pietrzakRankError F slack := by
      apply probEvent_bind_le_of_forall_le
      intro secret _
      simpa [hiddenSampler, badRun, honestRankLossRun] using
        (probEvent_honestRankLoss_le_pietrzak slack queryCount secret
          errorSampler adversary hbound)

/-- Independent simulator matrix and affine blinding coins. -/
noncomputable def simulatorCoins {F : Type} [SampleableType F]
    (ambient dimension : ℕ) :
    ProbComp (HiddenMatrix F ambient dimension × (Fin ambient → F)) := do
  let hidden ← $ᵗ HiddenMatrix F ambient dimension
  let blinding ← $ᵗ (Fin ambient → F)
  pure (hidden, blinding)

/-- Honest affine-secret branch used in the simulator coupling. -/
noncomputable def affineHonestGame {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (sourceSecret : Fin dimension → F) (errorSampler : ProbComp F)
    (adversary : Adversary F ambient) : ProbComp Bool :=
  simulatorCoins (F := F) ambient dimension >>= fun coins ↦
    simulateQ (fullImpl threshold
      (coins.1 *ᵥ sourceSecret + coins.2) errorSampler) adversary

/-- Online real-LWE simulator branch. -/
noncomputable def onlineRealSimulatorGame {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (sourceSecret : Fin dimension → F) (errorSampler : ProbComp F)
    (adversary : Adversary F ambient) : ProbComp Bool :=
  simulatorCoins (F := F) ambient dimension >>= fun coins ↦
    simulateQ (simulatedFullImpl threshold coins.1 coins.2
      (realLWEValue sourceSecret errorSampler)) adversary

/-- Online uniform-value simulator branch. -/
noncomputable def onlineUniformSimulatorGame {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (adversary : Adversary F ambient) : ProbComp Bool :=
  simulatorCoins (F := F) ambient dimension >>= fun coins ↦
    simulateQ (simulatedFullImpl threshold coins.1 coins.2
      (fun _ ↦ $ᵗ F)) adversary

/-- The online real simulator differs from its honest affine-secret branch only
on the rank-loss event. -/
theorem tvDist_affineHonest_onlineReal_le_pietrzak {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (slack queryCount : ℕ)
    (sourceSecret : Fin dimension → F) (errorSampler : ProbComp F)
    (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) queryCount) :
    tvDist
      (affineHonestGame (dimension + slack) sourceSecret errorSampler adversary)
      (onlineRealSimulatorGame (dimension + slack) sourceSecret errorSampler adversary) ≤
      ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal := by
  let coinsSampler := simulatorCoins (F := F) ambient dimension
  let honest (coins : HiddenMatrix F ambient dimension × (Fin ambient → F)) :=
    simulateQ (fullImpl (dimension + slack)
      (coins.1 *ᵥ sourceSecret + coins.2) errorSampler) adversary
  let simulated (coins : HiddenMatrix F ambient dimension × (Fin ambient → F)) :=
    simulateQ (simulatedFullImpl (dimension + slack) coins.1 coins.2
      (realLWEValue sourceSecret errorSampler)) adversary
  let badRun (coins : HiddenMatrix F ambient dimension × (Fin ambient → F)) :=
    honestRankLossRun (dimension + slack) coins.1
      (coins.1 *ᵥ sourceSecret + coins.2) errorSampler adversary
  calc
    tvDist
        (affineHonestGame (dimension + slack) sourceSecret errorSampler adversary)
        (onlineRealSimulatorGame (dimension + slack) sourceSecret errorSampler adversary) =
      tvDist (coinsSampler >>= honest) (coinsSampler >>= simulated) := rfl
    _ ≤ Pr[(fun fired : Bool ↦ fired = true) |
        coinsSampler >>= badRun].toReal := by
      apply tvDist_bind_left_le_probEvent_cont coinsSampler honest simulated
        badRun (fun fired ↦ fired = true)
      intro coins
      dsimp [honest, simulated, badRun, honestRankLossRun]
      let flaggedRun :=
        (simulateQ
          ((QueryImpl.Stateful.ofStateless
            (fullImpl (dimension + slack)
              (coins.1 *ᵥ sourceSecret + coins.2) errorSampler)).withBadUpdate
                (fun index _ _ ↦
                  rankLossInput (dimension + slack) coins.1 index))
          adversary).run (PUnit.unit, false)
      calc
        tvDist
            (simulateQ (fullImpl (dimension + slack)
              (coins.1 *ᵥ sourceSecret + coins.2) errorSampler) adversary)
            (simulateQ (simulatedFullImpl (dimension + slack) coins.1 coins.2
              (realLWEValue sourceSecret errorSampler)) adversary) ≤
            Pr[(fun result : Bool × (PUnit × Bool) ↦ result.2.2 = true) |
              flaggedRun].toReal :=
          tvDist_simulateQ_le_probEvent_badFlag
            (fullImpl (dimension + slack)
              (coins.1 *ᵥ sourceSecret + coins.2) errorSampler)
            (simulatedFullImpl (dimension + slack) coins.1 coins.2
              (realLWEValue sourceSecret errorSampler))
            (rankLossInput (dimension + slack) coins.1) adversary
            (fun index hgood ↦
              (evalDist_simulatedFullImpl_real_of_not_rankLoss
                (dimension + slack) coins.1 coins.2 sourceSecret errorSampler
                index hgood).symm)
        _ = Pr[(fun fired : Bool ↦ fired = true) |
              (fun result : Bool × (PUnit × Bool) ↦ result.2.2) <$>
                flaggedRun].toReal := by
          rw [probEvent_map]
          rfl
    _ ≤ ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal := by
      apply ENNReal.toReal_mono
      · apply ENNReal.mul_ne_top (by simp)
        apply ENNReal.div_ne_top (by simp)
        exact pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
      · simpa [coinsSampler, badRun, simulatorCoins, bind_assoc] using
          (probEvent_affineHonestRankLoss_le_pietrzak slack queryCount
            sourceSecret errorSampler adversary hbound)

/-- Affine blinding makes the honest affine branch exactly the standard real
adaptive-SLWE game, for every fixed source-LWE secret. -/
theorem evalDist_affineHonestGame_eq_realGame {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ)
    (sourceSecret : Fin dimension → F) (errorSampler : ProbComp F)
    (adversary : Adversary F ambient) :
    evalDist (affineHonestGame threshold sourceSecret errorSampler adversary) =
      evalDist (realGame threshold errorSampler adversary) := by
  let hiddenSampler : ProbComp (HiddenMatrix F ambient dimension) :=
    $ᵗ HiddenMatrix F ambient dimension
  let secretSampler : ProbComp (Fin ambient → F) := $ᵗ (Fin ambient → F)
  let honest (secret : Fin ambient → F) : ProbComp Bool :=
    simulateQ (fullImpl threshold secret errorSampler) adversary
  have hshift : ∀ hidden,
      evalDist (do
        let blinding ← secretSampler
        honest (hidden *ᵥ sourceSecret + blinding)) =
      evalDist (secretSampler >>= honest) := by
    intro hidden
    simpa [secretSampler, add_comm] using
      (evalDist_bind_bijective_add_right_uniform
        (α := Fin ambient → F) (β := Fin ambient → F)
        (γ := Bool) id Function.bijective_id (hidden *ᵥ sourceSecret) honest)
  calc
    evalDist (affineHonestGame threshold sourceSecret errorSampler adversary) =
        evalDist (hiddenSampler >>= fun hidden ↦ secretSampler >>= honest) := by
      simpa [affineHonestGame, simulatorCoins, hiddenSampler,
        secretSampler, honest, bind_assoc] using
        (evalDist_bind_congr' hiddenSampler hshift)
    _ = evalDist (secretSampler >>= honest) :=
      OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        hiddenSampler (by simp [hiddenSampler]) (secretSampler >>= honest)
    _ = evalDist (realGame threshold errorSampler adversary) := by
      rfl

/-- The online uniform simulator differs from its honest affine-secret branch
only on the same rank-loss event. -/
theorem tvDist_affineHonest_onlineUniform_le_pietrzak {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (slack queryCount : ℕ)
    (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) queryCount) :
    tvDist
      (affineHonestGame (dimension + slack) (0 : Fin dimension → F) ($ᵗ F) adversary)
      (onlineUniformSimulatorGame (dimension := dimension)
        (dimension + slack) adversary) ≤
      ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal := by
  let coinsSampler := simulatorCoins (F := F) ambient dimension
  let honest (coins : HiddenMatrix F ambient dimension × (Fin ambient → F)) :=
    simulateQ (fullImpl (dimension + slack)
      (coins.1 *ᵥ (0 : Fin dimension → F) + coins.2) ($ᵗ F)) adversary
  let simulated (coins : HiddenMatrix F ambient dimension × (Fin ambient → F)) :=
    simulateQ (simulatedFullImpl (dimension + slack) coins.1 coins.2
      (fun _ ↦ $ᵗ F)) adversary
  let badRun (coins : HiddenMatrix F ambient dimension × (Fin ambient → F)) :=
    honestRankLossRun (dimension + slack) coins.1
      (coins.1 *ᵥ (0 : Fin dimension → F) + coins.2) ($ᵗ F) adversary
  calc
    tvDist
        (affineHonestGame (dimension + slack) (0 : Fin dimension → F) ($ᵗ F) adversary)
        (onlineUniformSimulatorGame (dimension := dimension)
          (dimension + slack) adversary) =
      tvDist (coinsSampler >>= honest) (coinsSampler >>= simulated) := rfl
    _ ≤ Pr[(fun fired : Bool ↦ fired = true) |
        coinsSampler >>= badRun].toReal := by
      apply tvDist_bind_left_le_probEvent_cont coinsSampler honest simulated
        badRun (fun fired ↦ fired = true)
      intro coins
      dsimp [honest, simulated, badRun, honestRankLossRun]
      let flaggedRun :=
        (simulateQ
          ((QueryImpl.Stateful.ofStateless
            (fullImpl (dimension + slack)
              (coins.1 *ᵥ (0 : Fin dimension → F) + coins.2) ($ᵗ F))).withBadUpdate
                (fun index _ _ ↦
                  rankLossInput (dimension + slack) coins.1 index))
          adversary).run (PUnit.unit, false)
      calc
        tvDist
            (simulateQ (fullImpl (dimension + slack)
              (coins.1 *ᵥ (0 : Fin dimension → F) + coins.2) ($ᵗ F)) adversary)
            (simulateQ (simulatedFullImpl (dimension + slack) coins.1 coins.2
              (fun _ ↦ $ᵗ F)) adversary) ≤
            Pr[(fun result : Bool × (PUnit × Bool) ↦ result.2.2 = true) |
              flaggedRun].toReal :=
          tvDist_simulateQ_le_probEvent_badFlag
            (fullImpl (dimension + slack)
              (coins.1 *ᵥ (0 : Fin dimension → F) + coins.2) ($ᵗ F))
            (simulatedFullImpl (dimension + slack) coins.1 coins.2
              (fun _ ↦ $ᵗ F))
            (rankLossInput (dimension + slack) coins.1) adversary
            (fun index hgood ↦
              (evalDist_simulatedFullImpl_uniform_of_not_rankLoss
                (dimension + slack) coins.1 coins.2
                (coins.1 *ᵥ (0 : Fin dimension → F) + coins.2)
                index hgood).symm)
        _ = Pr[(fun fired : Bool ↦ fired = true) |
              (fun result : Bool × (PUnit × Bool) ↦ result.2.2) <$>
                flaggedRun].toReal := by
          rw [probEvent_map]
          rfl
    _ ≤ ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal := by
      apply ENNReal.toReal_mono
      · apply ENNReal.mul_ne_top (by simp)
        apply ENNReal.div_ne_top (by simp)
        exact pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
      · simpa [coinsSampler, badRun, simulatorCoins, bind_assoc] using
          (probEvent_affineHonestRankLoss_le_pietrzak slack queryCount
            (0 : Fin dimension → F) ($ᵗ F) adversary hbound)

/-- Real online reduction with the ordinary uniform LWE secret sampler. -/
noncomputable def onlineRealGame {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ) (errorSampler : ProbComp F)
    (adversary : Adversary F ambient) : ProbComp Bool := do
  let sourceSecret ← $ᵗ (Fin dimension → F)
  onlineRealSimulatorGame threshold sourceSecret errorSampler adversary

/-- Premise-free online-source adaptive-SLWE reduction. The only hypothesis is
the adversary's public query bound; the two rank-loss branches contribute the
explicit factor `2`. -/
theorem advantage_le_onlineLWE_add_rankLoss {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (slack queryCount : ℕ)
    (errorSampler : ProbComp F) (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) queryCount) :
    advantage (dimension + slack) errorSampler adversary ≤
      (onlineRealGame (dimension := dimension) (dimension + slack)
        errorSampler adversary).boolDistAdvantage
      (onlineUniformSimulatorGame (dimension := dimension)
        (dimension + slack) adversary) +
      2 * ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal := by
  let sourceSecretSampler : ProbComp (Fin dimension → F) :=
    $ᵗ (Fin dimension → F)
  let averagedAffineReal : ProbComp Bool :=
    sourceSecretSampler >>= fun sourceSecret ↦
      affineHonestGame (dimension + slack) sourceSecret errorSampler adversary
  let rankError : ℝ :=
    ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal
  have hAveragedReal : evalDist averagedAffineReal =
      evalDist (realGame (dimension + slack) errorSampler adversary) := by
    calc
      evalDist averagedAffineReal =
          evalDist (sourceSecretSampler >>= fun _ ↦
            realGame (dimension + slack) errorSampler adversary) := by
        apply evalDist_bind_congr' sourceSecretSampler
        intro sourceSecret
        exact evalDist_affineHonestGame_eq_realGame
          (dimension + slack) sourceSecret errorSampler adversary
      _ = evalDist (realGame (dimension + slack) errorSampler adversary) :=
        OracleComp.DeferredSampling.evalDist_bind_const_neverFails
          sourceSecretSampler (by simp [sourceSecretSampler]) _
  have hRealTV : tvDist averagedAffineReal
      (onlineRealGame (dimension := dimension) (dimension + slack)
        errorSampler adversary) ≤ rankError := by
    change tvDist
      (sourceSecretSampler >>= fun sourceSecret ↦
        affineHonestGame (dimension + slack) sourceSecret errorSampler adversary)
      (sourceSecretSampler >>= fun sourceSecret ↦
        onlineRealSimulatorGame (dimension + slack) sourceSecret errorSampler adversary) ≤
      rankError
    apply tvDist_bind_left_le_const
    intro sourceSecret _
    exact tvDist_affineHonest_onlineReal_le_pietrzak
      slack queryCount sourceSecret errorSampler adversary hbound
  have hUniformAffine : evalDist
      (affineHonestGame (dimension + slack) (0 : Fin dimension → F) ($ᵗ F) adversary) =
      evalDist (uniformGame (dimension + slack) adversary) :=
    evalDist_affineHonestGame_eq_realGame
      (dimension + slack) (0 : Fin dimension → F) ($ᵗ F) adversary
  have hRealGap :
      |(Pr[= true | realGame (dimension + slack) errorSampler adversary]).toReal -
        (Pr[= true | onlineRealGame (dimension := dimension)
          (dimension + slack) errorSampler adversary]).toReal| ≤ rankError := by
    rw [← probOutput_congr rfl hAveragedReal]
    exact (abs_probOutput_toReal_sub_le_tvDist _ _).trans hRealTV
  have hUniformGap :
      |(Pr[= true | onlineUniformSimulatorGame (dimension := dimension)
          (dimension + slack) adversary]).toReal -
        (Pr[= true | uniformGame (dimension + slack) adversary]).toReal| ≤ rankError := by
    rw [← probOutput_congr rfl hUniformAffine]
    exact (abs_probOutput_toReal_sub_le_tvDist _ _).trans
      (by
        rw [tvDist_comm]
        exact tvDist_affineHonest_onlineUniform_le_pietrzak
          slack queryCount adversary hbound)
  unfold advantage
  calc
    (realGame (dimension + slack) errorSampler adversary).boolDistAdvantage
        (uniformGame (dimension + slack) adversary) ≤
      (onlineRealGame (dimension := dimension) (dimension + slack)
        errorSampler adversary).boolDistAdvantage
        (onlineUniformSimulatorGame (dimension := dimension)
          (dimension + slack) adversary) + rankError + rankError :=
      advantage_le_reduction_add_gaps
        (realGame (dimension + slack) errorSampler adversary)
        (uniformGame (dimension + slack) adversary)
        (onlineRealGame (dimension := dimension) (dimension + slack)
          errorSampler adversary)
        (onlineUniformSimulatorGame (dimension := dimension)
          (dimension + slack) adversary)
        rankError rankError hRealGap hUniformGap
    _ = _ := by ring

/-! ## Compilation of the bounded online source into ordinary batch LWE -/

/-- An empty eager tape is observationally the original stateless implementation. -/
theorem run'_simulateQ_withPregen_empty_eq {iota : Type} {spec : OracleSpec iota}
    [DecidableEq iota] {alpha : Type} (implementation : QueryImpl spec ProbComp)
    (computation : OracleComp spec alpha) :
    (simulateQ implementation.withPregen computation).run' (∅ : QuerySeed spec) =
      simulateQ implementation computation := by
  induction computation using OracleComp.inductionOn with
  | pure output => simp
  | query_bind index continuation ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      rw [withPregen_run'_bind_query_eq_pop]
      have hpop : (∅ : QuerySeed spec).pop index = none :=
        (QuerySeed.pop_eq_none_iff _ _).mpr (QuerySeed.empty_apply index)
      rw [hpop]
      apply bind_congr
      intro response
      exact ih response

/-- Output probabilities of a finite independent product multiply coordinatewise. -/
theorem probOutput_fin_mOfFn {alpha : Type} [Finite alpha] (count : ℕ)
    (samplers : Fin count → ProbComp alpha) (values : Fin count → alpha) :
    Pr[= values | Fin.mOfFn count samplers] =
      ∏ index, Pr[= values index | samplers index] := by
  letI : Fintype alpha := Fintype.ofFinite alpha
  letI : DecidableEq alpha := Classical.decEq alpha
  induction count with
  | zero =>
      have hvalues : values = Fin.elim0 := funext fun index => index.elim0
      subst hvalues
      simp [Fin.mOfFn, probOutput_pure]
  | succ count ih =>
      simp only [Fin.mOfFn]
      rw [probOutput_bind_eq_sum_fintype]
      have hinner : ∀ value : alpha,
          Pr[= values | Fin.mOfFn count (fun index => samplers index.succ) >>=
              fun rest => pure (Fin.cons value rest)] =
            if value = values 0 then
              Pr[= Fin.tail values |
                Fin.mOfFn count fun index => samplers index.succ]
            else 0 := by
        intro value
        rw [probOutput_bind_eq_sum_fintype]
        have hiff : ∀ rest : Fin count → alpha,
            values = Fin.cons value rest ↔
              value = values 0 ∧ rest = Fin.tail values := by
          intro rest
          constructor
          · intro heq
            refine ⟨by rw [heq, Fin.cons_zero], funext fun index => ?_⟩
            have hcomponent := congrFun heq index.succ
            rw [Fin.cons_succ] at hcomponent
            exact hcomponent.symm
          · rintro ⟨rfl, rfl⟩
            exact (Fin.cons_self_tail values).symm
        by_cases hvalue : value = values 0
        · rw [if_pos hvalue]
          subst value
          simp only [probOutput_pure, hiff, true_and]
          simp [mul_ite]
        · rw [if_neg hvalue]
          refine Finset.sum_eq_zero fun rest _ => ?_
          rw [probOutput_pure,
            if_neg (fun heq => hvalue ((hiff rest).mp heq).1), mul_zero]
      simp only [hinner, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ (values 0)
        (fun value => Pr[= value | samplers 0] *
          Pr[= Fin.tail values |
            Fin.mOfFn count fun index => samplers index.succ]),
        if_pos (Finset.mem_univ _), ih, Fin.prod_univ_succ]
      rfl

/-- Independent uniform coordinates are the uniform distribution on a finite function space. -/
theorem evalDist_sampleIID_uniform {alpha : Type} [Fintype alpha]
    [SampleableType alpha] (count : ℕ) :
    evalDist (ProbComp.sampleIID count ($ᵗ alpha)) =
      evalDist ($ᵗ (Fin count → alpha)) := by
  apply evalDist_ext
  intro values
  simp only [ProbComp.sampleIID, probOutput_fin_mOfFn,
    probOutput_uniformSample]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fun, Nat.cast_pow]
  exact ENNReal.inv_pow.symm

/-- Mapping an independent function-valued product to a list is `replicate`. -/
theorem mOfFn_toList_eq_replicate {alpha : Type} (count : ℕ)
    (sampler : ProbComp alpha) :
    List.ofFn <$> Fin.mOfFn count (fun _ => sampler) =
      OracleComp.replicate count sampler := by
  induction count with
  | zero => simp [Fin.mOfFn, OracleComp.replicate]
  | succ count ih =>
      simp only [Fin.mOfFn, OracleComp.replicate_succ_bind, map_eq_bind_pure_comp,
        bind_assoc, pure_bind]
      apply bind_congr
      intro head
      rw [← ih]
      simp [map_eq_bind_pure_comp, bind_assoc]

/-- Sampling two finite products separately and then zipping them agrees with
sampling the coordinate pairs independently. -/
theorem evalDist_fin_mOfFn_zip {left right : Type}
    [Finite left] [Finite right] (count : ℕ)
    (leftSampler : Fin count → ProbComp left)
    (rightSampler : Fin count → ProbComp right) :
    evalDist
      ((Equiv.arrowProdEquivProdArrow (Fin count) (fun _ => left)
          (fun _ => right)).symm <$>
        (do
          let leftValues ← Fin.mOfFn count leftSampler
          let rightValues ← Fin.mOfFn count rightSampler
          pure (leftValues, rightValues))) =
      evalDist (Fin.mOfFn count fun index => do
        let leftValue ← leftSampler index
        let rightValue ← rightSampler index
        pure (leftValue, rightValue)) := by
  classical
  apply evalDist_ext
  intro values
  rw [probOutput_map_equiv]
  simp only [probOutput_fin_mOfFn]
  simp [Finset.prod_mul_distrib]
  rw [probOutput_fin_mOfFn, probOutput_fin_mOfFn]

/-- A matrix viewed columnwise. -/
def matrixColumns {F : Type} {dimension count : ℕ}
    (matrix : Matrix (Fin dimension) (Fin count) F) :
    Fin count → (Fin dimension → F) :=
  fun column row => matrix row column

theorem matrixColumns_bijective {F : Type} [Add F] (dimension count : ℕ) :
    Function.Bijective
      (matrixColumns : Matrix (Fin dimension) (Fin count) F →
        Fin count → (Fin dimension → F)) := by
  constructor
  · intro first second heq
    funext row column
    exact congrFun (congrFun heq column) row
  · intro columns
    exact ⟨fun row column => columns column row, rfl⟩

/-- Uniform matrix columns are independent uniform vectors. -/
theorem evalDist_uniform_matrixColumns {F : Type} [AddCommMonoid F]
    [Fintype F] [SampleableType F] (dimension count : ℕ) :
    evalDist (matrixColumns <$> ($ᵗ Matrix (Fin dimension) (Fin count) F)) =
      evalDist (ProbComp.sampleIID count ($ᵗ (Fin dimension → F))) := by
  calc
    evalDist (matrixColumns <$> ($ᵗ Matrix (Fin dimension) (Fin count) F)) =
        evalDist ($ᵗ (Fin count → (Fin dimension → F))) :=
      evalDist_map_bijective_uniform_cross
        (α := Matrix (Fin dimension) (Fin count) F)
        (β := Fin count → (Fin dimension → F)) matrixColumns
        (matrixColumns_bijective dimension count)
    _ = evalDist (ProbComp.sampleIID count ($ᵗ (Fin dimension → F))) :=
      (evalDist_sampleIID_uniform count).symm

/-- A uniform challenge matrix and an IID error vector, viewed coordinatewise,
are IID challenge/error pairs. -/
theorem evalDist_uniformMatrix_sampleIID_zip {F : Type} [AddCommMonoid F]
    [Fintype F] [SampleableType F] (dimension count : ℕ)
    (errorSampler : ProbComp F) :
    evalDist
      ((Equiv.arrowProdEquivProdArrow (Fin count)
          (fun _ => Fin dimension → F) (fun _ => F)).symm <$>
        (do
          let matrix ← $ᵗ Matrix (Fin dimension) (Fin count) F
          let errors ← ProbComp.sampleIID count errorSampler
          pure (matrixColumns matrix, errors))) =
      evalDist (Fin.mOfFn count fun _ => do
        let challenge ← $ᵗ (Fin dimension → F)
        let error ← errorSampler
        pure (challenge, error)) := by
  let columnSampler : ProbComp (Fin count → (Fin dimension → F)) :=
    matrixColumns <$> ($ᵗ Matrix (Fin dimension) (Fin count) F)
  let independentColumns : ProbComp (Fin count → (Fin dimension → F)) :=
    ProbComp.sampleIID count ($ᵗ (Fin dimension → F))
  let errors : ProbComp (Fin count → F) :=
    ProbComp.sampleIID count errorSampler
  have hcolumns : evalDist columnSampler = evalDist independentColumns := by
    exact evalDist_uniform_matrixColumns dimension count
  have hproduct :
      evalDist (do
        let columns ← columnSampler
        let errorValues ← errors
        pure (columns, errorValues)) =
      evalDist (do
        let columns ← independentColumns
        let errorValues ← errors
        pure (columns, errorValues)) := by
    rw [evalDist_bind, hcolumns, ← evalDist_bind]
  calc
    evalDist
        ((Equiv.arrowProdEquivProdArrow (Fin count)
            (fun _ => Fin dimension → F) (fun _ => F)).symm <$>
          (do
            let matrix ← $ᵗ Matrix (Fin dimension) (Fin count) F
            let errorValues ← ProbComp.sampleIID count errorSampler
            pure (matrixColumns matrix, errorValues))) =
      evalDist
        ((Equiv.arrowProdEquivProdArrow (Fin count)
            (fun _ => Fin dimension → F) (fun _ => F)).symm <$>
          (do
            let columns ← independentColumns
            let errorValues ← errors
            pure (columns, errorValues))) := by
        apply evalDist_map_eq_of_evalDist_eq
        simpa [columnSampler, errors, bind_assoc] using hproduct
    _ = evalDist (Fin.mOfFn count fun _ => do
          let challenge ← $ᵗ (Fin dimension → F)
          let error ← errorSampler
          pure (challenge, error)) := by
      simpa [independentColumns, errors, ProbComp.sampleIID] using
        (evalDist_fin_mOfFn_zip count
          (fun _ => ($ᵗ (Fin dimension → F) : ProbComp (Fin dimension → F)))
          (fun _ => errorSampler))

/-- Coordinatewise mapping commutes with an IID finite product. -/
theorem map_fin_mOfFn_const {alpha beta : Type} (count : ℕ)
    (sampler : ProbComp alpha) (transform : alpha → beta) :
    (fun values index => transform (values index)) <$>
        Fin.mOfFn count (fun _ => sampler) =
      Fin.mOfFn count (fun _ => transform <$> sampler) := by
  induction count with
  | zero =>
      simp only [Fin.mOfFn, map_pure]
      congr 1
      funext index
      exact index.elim0
  | succ count ih =>
      simp only [Fin.mOfFn, map_eq_bind_pure_comp, bind_assoc, pure_bind]
      apply bind_congr
      intro head
      simp only [Function.comp_apply, pure_bind]
      let tailTransform : (Fin count → alpha) → (Fin count → beta) :=
        fun rest index => transform (rest index)
      let addHead : (Fin count → beta) → (Fin (count + 1) → beta) :=
        fun rest => @Fin.cons count (fun _ : Fin (count + 1) => beta)
          (transform head) rest
      have hcons (rest : Fin count → alpha) :
          (fun index => transform
            (@Fin.cons count (fun _ : Fin (count + 1) => alpha) head rest index)) =
            addHead (tailTransform rest) := by
        funext index
        refine Fin.cases ?_ (fun tailIndex => ?_) index
        · simp [addHead]
        · simp [addHead, tailTransform]
      calc
        (do
          let rest ← Fin.mOfFn count (fun _ => sampler)
          pure (fun index => transform
            (@Fin.cons count (fun _ : Fin (count + 1) => alpha)
              head rest index))) =
            (do
              let rest ← Fin.mOfFn count (fun _ => sampler)
              pure (addHead (tailTransform rest))) := by
                apply bind_congr
                intro rest
                rw [hcons]
        _ = addHead <$> (tailTransform <$>
              Fin.mOfFn count (fun _ => sampler)) := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = addHead <$>
              Fin.mOfFn count (fun _ => transform <$> sampler) := by
            rw [ih]
        _ = (do
              let rest ← Fin.mOfFn count
                (fun _ => sampler >>= pure ∘ transform)
              pure (Fin.cons (transform head) rest)) := by
            simp [addHead, map_eq_bind_pure_comp]

/-- Convert a matrix-form batch transcript to the ordered online sample tape. -/
def batchSamples {F : Type} {dimension count : ℕ}
    (transcript : Matrix (Fin dimension) (Fin count) F × (Fin count → F)) :
    List (LWESample F dimension) :=
  List.ofFn fun index => (matrixColumns transcript.1 index, transcript.2 index)

/-- Add the fixed-secret LWE signal to one challenge/error pair. -/
def realPairTransform {F : Type} [Semiring F] {dimension : ℕ}
    (secret : Fin dimension → F)
    (sample : (Fin dimension → F) × F) : LWESample F dimension :=
  (sample.1, dotProduct secret sample.1 + sample.2)

/-- Matrix LWE with a fixed secret, before averaging over the usual secret sampler. -/
def fixedSecretBatchReal {F : Type} [Semiring F] [DecidableEq F]
    [SampleableType F] (dimension count : ℕ)
    (secret : Fin dimension → F) (errorSampler : ProbComp F) :
    ProbComp (Matrix (Fin dimension) (Fin count) F × (Fin count → F)) := do
  let matrix ← $ᵗ Matrix (Fin dimension) (Fin count) F
  let errors ← ProbComp.sampleIID count errorSampler
  pure (matrix, secret ᵥ* matrix + errors)

/-- For a fixed secret, ordinary matrix LWE is exactly a list of independent
online LWE samples. -/
theorem evalDist_batchSamples_fixedSecretBatchReal {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (dimension count : ℕ) (secret : Fin dimension → F)
    (errorSampler : ProbComp F) :
    evalDist (batchSamples <$> fixedSecretBatchReal dimension count secret errorSampler) =
      evalDist (OracleComp.replicate count
        (pairSamplerFromValue (realLWEValue secret errorSampler))) := by
  let rawPairs : ProbComp (Fin count → ((Fin dimension → F) × F)) :=
    (Equiv.arrowProdEquivProdArrow (Fin count)
      (fun _ => Fin dimension → F) (fun _ => F)).symm <$>
      (do
        let matrix ← $ᵗ Matrix (Fin dimension) (Fin count) F
        let errors ← ProbComp.sampleIID count errorSampler
        pure (matrixColumns matrix, errors))
  let independentPairs : ProbComp (Fin count → ((Fin dimension → F) × F)) :=
    Fin.mOfFn count fun _ => do
      let challenge ← $ᵗ (Fin dimension → F)
      let error ← errorSampler
      pure (challenge, error)
  let transform : ((Fin dimension → F) × F) → LWESample F dimension :=
    realPairTransform secret
  let mapCoordinates :
      (Fin count → ((Fin dimension → F) × F)) →
        (Fin count → LWESample F dimension) :=
    fun samples index => transform (samples index)
  have hraw : evalDist rawPairs = evalDist independentPairs := by
    exact evalDist_uniformMatrix_sampleIID_zip dimension count errorSampler
  have hcolumn (matrix : Matrix (Fin dimension) (Fin count) F)
      (index : Fin count) : matrix.col index = matrixColumns matrix index := by
    rfl
  have hbatch :
      batchSamples <$> fixedSecretBatchReal dimension count secret errorSampler =
        List.ofFn <$> (mapCoordinates <$> rawPairs) := by
    simp [fixedSecretBatchReal, batchSamples, rawPairs, mapCoordinates,
      transform, realPairTransform, Matrix.vecMul_apply, hcolumn,
      map_eq_bind_pure_comp, bind_assoc]
  have hcoordinate :
      transform <$> (do
        let challenge ← $ᵗ (Fin dimension → F)
        let error ← errorSampler
        pure (challenge, error)) =
      pairSamplerFromValue (realLWEValue secret errorSampler) := by
    simp [transform, realPairTransform, pairSamplerFromValue, realLWEValue,
      map_eq_bind_pure_comp, bind_assoc, dotProduct_comm]
  calc
    evalDist (batchSamples <$>
        fixedSecretBatchReal dimension count secret errorSampler) =
      evalDist (List.ofFn <$> (mapCoordinates <$> rawPairs)) := by
        rw [hbatch]
    _ = evalDist (List.ofFn <$> (mapCoordinates <$> independentPairs)) := by
      apply evalDist_map_eq_of_evalDist_eq
      exact evalDist_map_eq_of_evalDist_eq hraw mapCoordinates
    _ = evalDist (List.ofFn <$> Fin.mOfFn count (fun _ =>
          transform <$> (do
            let challenge ← $ᵗ (Fin dimension → F)
            let error ← errorSampler
            pure (challenge, error)))) := by
      rw [← map_fin_mOfFn_const]
    _ = evalDist (OracleComp.replicate count
          (transform <$> (do
            let challenge ← $ᵗ (Fin dimension → F)
            let error ← errorSampler
            pure (challenge, error)))) := by
      rw [mOfFn_toList_eq_replicate]
    _ = evalDist (OracleComp.replicate count
          (pairSamplerFromValue (realLWEValue secret errorSampler))) := by
      rw [hcoordinate]

/-- The real distribution of ordinary batch LWE maps to a finite online-sample tape. -/
theorem evalDist_batchSamples_batchDistr {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (dimension count : ℕ) (errorSampler : ProbComp F) :
    evalDist (batchSamples <$>
      LearningWithErrors.distr
        (FormalProof4FHE.LWE.batchProblem dimension count
          ($ᵗ (Fin dimension → F)) errorSampler)) =
      evalDist (do
        let secret ← $ᵗ (Fin dimension → F)
        OracleComp.replicate count
          (pairSamplerFromValue (realLWEValue secret errorSampler))) := by
  let challengeSampler : ProbComp (Matrix (Fin dimension) (Fin count) F) :=
    $ᵗ Matrix (Fin dimension) (Fin count) F
  let continuation (matrix : Matrix (Fin dimension) (Fin count) F)
      (secret : Fin dimension → F) : ProbComp (List (LWESample F dimension)) := do
    let errors ← ProbComp.sampleIID count errorSampler
    pure (batchSamples (matrix, secret ᵥ* matrix + errors))
  calc
    evalDist (batchSamples <$>
        LearningWithErrors.distr
          (FormalProof4FHE.LWE.batchProblem dimension count
            ($ᵗ (Fin dimension → F)) errorSampler)) =
      evalDist (challengeSampler >>= fun matrix =>
        ($ᵗ (Fin dimension → F)) >>= fun secret =>
          continuation matrix secret) := by
          simp [LearningWithErrors.distr, FormalProof4FHE.LWE.batchProblem,
            challengeSampler, continuation,
            map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ (Fin dimension → F)) >>= fun secret =>
          challengeSampler >>= fun matrix => continuation matrix secret) :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        challengeSampler ($ᵗ (Fin dimension → F)) continuation
    _ = evalDist (($ᵗ (Fin dimension → F)) >>= fun secret =>
          batchSamples <$>
            fixedSecretBatchReal dimension count secret errorSampler) := by
      simp [challengeSampler, continuation, fixedSecretBatchReal,
        map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ (Fin dimension → F)) >>= fun secret =>
          OracleComp.replicate count
            (pairSamplerFromValue (realLWEValue secret errorSampler))) := by
      apply evalDist_bind_congr' ($ᵗ (Fin dimension → F))
      intro secret
      exact evalDist_batchSamples_fixedSecretBatchReal
        dimension count secret errorSampler

/-- The uniform distribution of ordinary batch LWE maps to independent
uniform challenge/value online samples. -/
theorem evalDist_batchSamples_batchUniformDistr {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (dimension count : ℕ) (secretSampler : ProbComp (Fin dimension → F))
    (errorSampler : ProbComp F) :
    evalDist (batchSamples <$>
      LearningWithErrors.uniformDistr
        (FormalProof4FHE.LWE.batchProblem dimension count
          secretSampler errorSampler)) =
      evalDist (OracleComp.replicate count
        (pairSamplerFromValue (fun _ => $ᵗ F))) := by
  let fixedUniform : ProbComp
      (Matrix (Fin dimension) (Fin count) F × (Fin count → F)) := do
    let matrix ← $ᵗ Matrix (Fin dimension) (Fin count) F
    let values ← $ᵗ (Fin count → F)
    pure (matrix, values)
  let zeroReal := fixedSecretBatchReal dimension count
    (0 : Fin dimension → F) ($ᵗ F)
  have hzero : evalDist zeroReal = evalDist fixedUniform := by
    let challengeSampler : ProbComp (Matrix (Fin dimension) (Fin count) F) :=
      $ᵗ Matrix (Fin dimension) (Fin count) F
    have hvalues := evalDist_sampleIID_uniform (alpha := F) count
    calc
      evalDist zeroReal = evalDist (challengeSampler >>= fun matrix =>
          ProbComp.sampleIID count ($ᵗ F) >>= fun values =>
            pure (matrix, values)) := by
        simp [zeroReal, fixedSecretBatchReal, challengeSampler]
      _ = evalDist (challengeSampler >>= fun matrix =>
          ($ᵗ (Fin count → F)) >>= fun values =>
            pure (matrix, values)) := by
        apply evalDist_bind_congr' challengeSampler
        intro matrix
        rw [evalDist_bind, hvalues, ← evalDist_bind]
      _ = evalDist fixedUniform := by rfl
  have hmapped : evalDist (batchSamples <$> zeroReal) =
      evalDist (batchSamples <$> fixedUniform) :=
    evalDist_map_eq_of_evalDist_eq hzero batchSamples
  have hcoordinate :
      pairSamplerFromValue
          (realLWEValue (0 : Fin dimension → F) ($ᵗ F)) =
        pairSamplerFromValue (fun _ => $ᵗ F) := by
    simp [pairSamplerFromValue, realLWEValue]
  calc
    evalDist (batchSamples <$>
        LearningWithErrors.uniformDistr
          (FormalProof4FHE.LWE.batchProblem dimension count
            secretSampler errorSampler)) =
      evalDist (batchSamples <$> fixedUniform) := by rfl
    _ = evalDist (batchSamples <$> zeroReal) := hmapped.symm
    _ = evalDist (OracleComp.replicate count
          (pairSamplerFromValue
            (realLWEValue (0 : Fin dimension → F) ($ᵗ F)))) :=
      evalDist_batchSamples_fixedSecretBatchReal dimension count
        (0 : Fin dimension → F) ($ᵗ F)
    _ = evalDist (OracleComp.replicate count
          (pairSamplerFromValue (fun _ => $ᵗ F))) := by
      rw [hcoordinate]

/-- Seed the distinguished source query with an ordered list of LWE samples. -/
def sourceSampleSeed {F : Type} {dimension : ℕ}
    (samples : List (LWESample F dimension)) :
    QuerySeed (SourceInterface F dimension) :=
  (∅ : QuerySeed (SourceInterface F dimension)).addValues
    (i := Sum.inr ()) samples

/-- A bounded source computation can consume a finite sample list eagerly;
after the list is installed, the fallback sample distribution is unobservable. -/
theorem evalDist_sourceImpl_eq_batched {F : Type} [SampleableType F]
    {dimension : ℕ} {alpha : Type}
    (sampleSampler fallbackSampler : ProbComp (LWESample F dimension))
    (computation : OracleComp (SourceInterface F dimension) alpha) (count : ℕ)
    (hbound : IsQueryBoundP computation
      (isSourceSample (F := F) (dimension := dimension)) count) :
    evalDist (simulateQ (sourceImpl sampleSampler) computation) =
      evalDist (do
        let samples ← OracleComp.replicate count sampleSampler
        (simulateQ (sourceImpl fallbackSampler).withPregen computation).run'
          (sourceSampleSeed samples)) := by
  let actual := sourceImpl sampleSampler
  let fallback := sourceImpl fallbackSampler
  have hsame : ∀ index,
      ¬ isSourceSample (F := F) (dimension := dimension) index →
        actual index = fallback index := by
    intro index hfree
    rcases index with uniformIndex | sampleIndex
    · rfl
    · simp [isSourceSample] at hfree
  have hreplace :
      evalDist (do
        let samples ← OracleComp.replicate count (actual (Sum.inr ()))
        (simulateQ actual.withPregen computation).run'
          (sourceSampleSeed samples)) =
      evalDist (do
        let samples ← OracleComp.replicate count (actual (Sum.inr ()))
        (simulateQ fallback.withPregen computation).run'
          (sourceSampleSeed samples)) := by
    apply evalDist_bind_congr
    intro samples hsamples
    have hlength : samples.length = count := by
      rw [OracleComp.support_replicate] at hsamples
      exact hsamples.1
    rw [run_withPregen_eq_of_queryBound actual fallback
      (isSourceSample (F := F) (dimension := dimension)) hsame
      computation count hbound (sourceSampleSeed samples)]
    intro index hcharged
    rcases index with uniformIndex | sampleIndex
    · simp [isSourceSample] at hcharged
    · cases sampleIndex
      change count ≤ samples.length
      omega
  have heager := evalDist_replicate_bind_withPregen_addValues
    actual (Sum.inr ()) computation count
    (∅ : QuerySeed (SourceInterface F dimension))
  calc
    evalDist (simulateQ (sourceImpl sampleSampler) computation) =
      evalDist ((simulateQ actual.withPregen computation).run'
        (∅ : QuerySeed (SourceInterface F dimension))) := by
          rw [run'_simulateQ_withPregen_empty_eq]
    _ = evalDist (do
          let samples ← OracleComp.replicate count (actual (Sum.inr ()))
          (simulateQ actual.withPregen computation).run'
            (sourceSampleSeed samples)) := by
      simpa [sourceSampleSeed] using heager.symm
    _ = evalDist (do
          let samples ← OracleComp.replicate count (actual (Sum.inr ()))
          (simulateQ fallback.withPregen computation).run'
            (sourceSampleSeed samples)) := hreplace
    _ = _ := by
      rw [show actual (Sum.inr ()) = sampleSampler by rfl,
        show fallback = sourceImpl fallbackSampler by rfl]
      apply evalDist_ext
      intro output
      rfl

/-- Execute the concrete simulator from an eager LWE sample tape. The uniform
fallback cannot be reached by a query-bounded adversary when the tape has the
advertised length. -/
noncomputable def batchReductionFromSamples {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold : ℕ) (adversary : Adversary F ambient)
    (samples : List (LWESample F dimension)) : ProbComp Bool := do
  let coins ← simulatorCoins (F := F) ambient dimension
  (simulateQ (sourceImpl ($ᵗ LWESample F dimension)).withPregen
    (simulateQ (simulatorReduction threshold coins.1 coins.2) adversary)).run'
      (sourceSampleSeed samples)

/-- The ordinary batch-LWE adversary obtained by installing the matrix
transcript columnwise as the simulator's eager source tape. -/
noncomputable def batchReduction {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold count : ℕ)
    (adversary : Adversary F ambient) :
    Matrix (Fin dimension) (Fin count) F × (Fin count → F) → ProbComp Bool :=
  fun transcript =>
    batchReductionFromSamples threshold adversary (batchSamples transcript)

/-- Direct affine-fiber simulation equals execution from an eager bounded
sample tape for an arbitrary online LWE value sampler. -/
theorem evalDist_simulatedFull_eq_batched {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold count : ℕ)
    (hidden : Matrix (Fin ambient) (Fin dimension) F)
    (blinding : Fin ambient → F)
    (valueSampler : (Fin dimension → F) → ProbComp F)
    (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) count) :
    evalDist (simulateQ
      (simulatedFullImpl threshold hidden blinding valueSampler) adversary) =
      evalDist (do
        let samples ← OracleComp.replicate count
          (pairSamplerFromValue valueSampler)
        (simulateQ (sourceImpl ($ᵗ LWESample F dimension)).withPregen
          (simulateQ (simulatorReduction threshold hidden blinding) adversary)).run'
            (sourceSampleSeed samples)) := by
  let computation :=
    simulateQ (simulatorReduction threshold hidden blinding) adversary
  have hsourceBound : IsQueryBoundP computation
      (isSourceSample (F := F) (dimension := dimension)) count :=
    simulatorReduction_isQueryBoundP threshold count hidden blinding adversary hbound
  calc
    evalDist (simulateQ
        (simulatedFullImpl threshold hidden blinding valueSampler) adversary) =
      evalDist (simulateQ (sourceImpl (pairSamplerFromValue valueSampler))
        computation) :=
      (evalDist_source_simulator_eq_direct threshold hidden blinding
        valueSampler adversary).symm
    _ = _ := evalDist_sourceImpl_eq_batched
      (pairSamplerFromValue valueSampler) ($ᵗ LWESample F dimension)
      computation count hsourceBound

/-- After averaging the independent simulator coins, the online source can be
front-loaded before those coins and supplied to the batch reduction. -/
theorem evalDist_onlineSimulator_eq_sampleBatch {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold count : ℕ)
    (valueSampler : (Fin dimension → F) → ProbComp F)
    (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) count) :
    evalDist (simulatorCoins (F := F) ambient dimension >>= fun coins =>
      simulateQ (simulatedFullImpl threshold coins.1 coins.2 valueSampler)
        adversary) =
      evalDist (OracleComp.replicate count
        (pairSamplerFromValue valueSampler) >>= fun samples =>
          batchReductionFromSamples threshold adversary samples) := by
  let coinsSampler := simulatorCoins (F := F) ambient dimension
  let samplesSampler := OracleComp.replicate count
    (pairSamplerFromValue valueSampler)
  let continuation
      (coins : HiddenMatrix F ambient dimension × (Fin ambient → F))
      (samples : List (LWESample F dimension)) : ProbComp Bool :=
    (simulateQ (sourceImpl ($ᵗ LWESample F dimension)).withPregen
      (simulateQ (simulatorReduction threshold coins.1 coins.2) adversary)).run'
        (sourceSampleSeed samples)
  have hcoins : ∀ coins ∈ support coinsSampler,
      evalDist (simulateQ
        (simulatedFullImpl threshold coins.1 coins.2 valueSampler) adversary) =
      evalDist (samplesSampler >>= continuation coins) := by
    intro coins _
    exact evalDist_simulatedFull_eq_batched threshold count coins.1 coins.2
      valueSampler adversary hbound
  calc
    evalDist (simulatorCoins (F := F) ambient dimension >>= fun coins =>
        simulateQ (simulatedFullImpl threshold coins.1 coins.2 valueSampler)
          adversary) =
      evalDist (coinsSampler >>= fun coins =>
        samplesSampler >>= continuation coins) := by
      apply evalDist_bind_congr
      exact hcoins
    _ = evalDist (samplesSampler >>= fun samples =>
          coinsSampler >>= fun coins => continuation coins samples) :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        coinsSampler samplesSampler continuation
    _ = _ := by
      simp [coinsSampler, samplesSampler, continuation,
        batchReductionFromSamples]

/-- Fixed-secret real online simulation is exactly the batch reduction fed
independent real LWE samples. -/
theorem evalDist_onlineRealSimulatorGame_eq_sampleBatch {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold count : ℕ)
    (secret : Fin dimension → F) (errorSampler : ProbComp F)
    (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) count) :
    evalDist (onlineRealSimulatorGame threshold secret errorSampler adversary) =
      evalDist (OracleComp.replicate count
        (pairSamplerFromValue (realLWEValue secret errorSampler)) >>= fun samples =>
          batchReductionFromSamples threshold adversary samples) := by
  exact evalDist_onlineSimulator_eq_sampleBatch threshold count
    (realLWEValue secret errorSampler) adversary hbound

/-- Uniform-value online simulation is exactly the same batch reduction fed
independent uniform challenge/value samples. -/
theorem evalDist_onlineUniformSimulatorGame_eq_sampleBatch {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold count : ℕ)
    (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) count) :
    evalDist (onlineUniformSimulatorGame (dimension := dimension)
      threshold adversary) =
      evalDist (OracleComp.replicate count
        (pairSamplerFromValue (dimension := dimension)
          (fun _ : Fin dimension → F => $ᵗ F)) >>= fun samples =>
          batchReductionFromSamples (dimension := dimension)
            threshold adversary samples) := by
  exact evalDist_onlineSimulator_eq_sampleBatch threshold count
    (fun _ : Fin dimension → F => $ᵗ F) adversary hbound

/-- The real online simulator is exactly game 0 of ordinary matrix batch LWE
against `batchReduction`. -/
theorem evalDist_onlineRealGame_eq_batch_game0 {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold count : ℕ)
    (errorSampler : ProbComp F) (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) count) :
    evalDist (onlineRealGame (dimension := dimension)
      threshold errorSampler adversary) =
      evalDist (LearningWithErrors.game0
        (FormalProof4FHE.LWE.batchProblem dimension count
          ($ᵗ (Fin dimension → F)) errorSampler)
        (batchReduction threshold count adversary)) := by
  let problem := FormalProof4FHE.LWE.batchProblem dimension count
    ($ᵗ (Fin dimension → F)) errorSampler
  let tapeDistr : ProbComp (List (LWESample F dimension)) := do
    let secret ← $ᵗ (Fin dimension → F)
    OracleComp.replicate count
      (pairSamplerFromValue (realLWEValue secret errorSampler))
  let mappedDistr : ProbComp (List (LWESample F dimension)) :=
    batchSamples <$> LearningWithErrors.distr problem
  let continuation (samples : List (LWESample F dimension)) : ProbComp Bool :=
    batchReductionFromSamples threshold adversary samples
  have hdist : evalDist mappedDistr = evalDist tapeDistr := by
    exact evalDist_batchSamples_batchDistr dimension count errorSampler
  have honline :
      evalDist (onlineRealGame (dimension := dimension)
        threshold errorSampler adversary) =
      evalDist (tapeDistr >>= continuation) := by
    rw [show tapeDistr >>= continuation =
        (($ᵗ (Fin dimension → F)) >>= fun secret =>
          OracleComp.replicate count
            (pairSamplerFromValue (realLWEValue secret errorSampler)) >>=
              continuation) by
      simp [tapeDistr, bind_assoc]]
    unfold onlineRealGame
    apply evalDist_bind_congr' ($ᵗ (Fin dimension → F))
    intro secret
    exact evalDist_onlineRealSimulatorGame_eq_sampleBatch
      threshold count secret errorSampler adversary hbound
  have hgame :
      evalDist (LearningWithErrors.game0 problem
        (batchReduction threshold count adversary)) =
      evalDist (mappedDistr >>= continuation) := by
    simp [LearningWithErrors.game0, mappedDistr, continuation,
      batchReduction, map_eq_bind_pure_comp, bind_assoc]
  calc
    evalDist (onlineRealGame (dimension := dimension)
        threshold errorSampler adversary) =
      evalDist (tapeDistr >>= continuation) := honline
    _ = evalDist (mappedDistr >>= continuation) := by
      rw [evalDist_bind tapeDistr continuation,
        evalDist_bind mappedDistr continuation, hdist]
    _ = _ := hgame.symm

/-- The uniform-value online simulator is exactly game 1 of the same ordinary
matrix batch-LWE problem and reduction. -/
theorem evalDist_onlineUniformGame_eq_batch_game1 {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (threshold count : ℕ)
    (errorSampler : ProbComp F) (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) count) :
    evalDist (onlineUniformSimulatorGame (dimension := dimension)
      threshold adversary) =
      evalDist (LearningWithErrors.game1
        (FormalProof4FHE.LWE.batchProblem dimension count
          ($ᵗ (Fin dimension → F)) errorSampler)
        (batchReduction threshold count adversary)) := by
  let problem := FormalProof4FHE.LWE.batchProblem dimension count
    ($ᵗ (Fin dimension → F)) errorSampler
  let tapeDistr : ProbComp (List (LWESample F dimension)) :=
    OracleComp.replicate count
      (pairSamplerFromValue (dimension := dimension)
        (fun _ : Fin dimension → F => $ᵗ F))
  let mappedDistr : ProbComp (List (LWESample F dimension)) :=
    batchSamples <$> LearningWithErrors.uniformDistr problem
  let continuation (samples : List (LWESample F dimension)) : ProbComp Bool :=
    batchReductionFromSamples threshold adversary samples
  have hdist : evalDist mappedDistr = evalDist tapeDistr := by
    exact evalDist_batchSamples_batchUniformDistr dimension count
      ($ᵗ (Fin dimension → F)) errorSampler
  have honline :
      evalDist (onlineUniformSimulatorGame (dimension := dimension)
        threshold adversary) =
      evalDist (tapeDistr >>= continuation) := by
    exact evalDist_onlineUniformSimulatorGame_eq_sampleBatch
      threshold count adversary hbound
  have hgame :
      evalDist (LearningWithErrors.game1 problem
        (batchReduction threshold count adversary)) =
      evalDist (mappedDistr >>= continuation) := by
    simp [LearningWithErrors.game1, mappedDistr, continuation,
      batchReduction, map_eq_bind_pure_comp, bind_assoc]
  calc
    evalDist (onlineUniformSimulatorGame (dimension := dimension)
        threshold adversary) =
      evalDist (tapeDistr >>= continuation) := honline
    _ = evalDist (mappedDistr >>= continuation) := by
      rw [evalDist_bind tapeDistr continuation,
        evalDist_bind mappedDistr continuation, hdist]
    _ = _ := hgame.symm

/-- Concrete adaptive subspace-LWE security from ordinary matrix batch LWE.

This is the premise-closing theorem: apart from the adversary's public query
bound, every simulator-correctness, eager-tape, and adaptive-rank premise has
been discharged by the constructions above. The factor `2` accounts for the
real and uniform hybrid endpoints. -/
theorem advantage_le_batchLWE_add_rankLoss {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (slack queryCount : ℕ)
    (errorSampler : ProbComp F) (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) queryCount) :
    advantage (dimension + slack) errorSampler adversary ≤
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem dimension queryCount
          ($ᵗ (Fin dimension → F)) errorSampler)
        (batchReduction (dimension := dimension)
          (dimension + slack) queryCount adversary) +
      2 * ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal := by
  let problem := FormalProof4FHE.LWE.batchProblem dimension queryCount
    ($ᵗ (Fin dimension → F)) errorSampler
  let reduction := batchReduction (dimension := dimension)
    (dimension + slack) queryCount adversary
  have hreal :
      evalDist (onlineRealGame (dimension := dimension)
        (dimension + slack) errorSampler adversary) =
      evalDist (LearningWithErrors.game0 problem reduction) :=
    evalDist_onlineRealGame_eq_batch_game0
      (dimension + slack) queryCount errorSampler adversary hbound
  have huniform :
      evalDist (onlineUniformSimulatorGame (dimension := dimension)
        (dimension + slack) adversary) =
      evalDist (LearningWithErrors.game1 problem reduction) :=
    evalDist_onlineUniformGame_eq_batch_game1
      (dimension + slack) queryCount errorSampler adversary hbound
  have honlineAdvantage :
      (onlineRealGame (dimension := dimension)
        (dimension + slack) errorSampler adversary).boolDistAdvantage
        (onlineUniformSimulatorGame (dimension := dimension)
          (dimension + slack) adversary) =
      LearningWithErrors.advantage problem reduction := by
    rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
    simp only [ProbComp.boolDistAdvantage,
      probOutput_congr rfl hreal, probOutput_congr rfl huniform]
  calc
    advantage (dimension + slack) errorSampler adversary ≤
        (onlineRealGame (dimension := dimension)
          (dimension + slack) errorSampler adversary).boolDistAdvantage
          (onlineUniformSimulatorGame (dimension := dimension)
            (dimension + slack) adversary) +
        2 * ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal :=
      advantage_le_onlineLWE_add_rankLoss
        slack queryCount errorSampler adversary hbound
    _ = LearningWithErrors.advantage problem reduction +
        2 * ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal := by
      rw [honlineAdvantage]
    _ = _ := by rfl

/-- Security corollary stated against any supplied concrete batch-LWE bound. -/
theorem advantage_le_of_batchLWE {F : Type}
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (slack queryCount : ℕ)
    (errorSampler : ProbComp F) (adversary : Adversary F ambient)
    (hbound : IsQueryBoundP adversary (isSLWEQuery (F := F)) queryCount)
    (lweBound : ℝ)
    (hLWE : LearningWithErrors.advantage
      (FormalProof4FHE.LWE.batchProblem dimension queryCount
        ($ᵗ (Fin dimension → F)) errorSampler)
      (batchReduction (dimension := dimension)
        (dimension + slack) queryCount adversary) ≤ lweBound) :
    advantage (dimension + slack) errorSampler adversary ≤
      lweBound +
        2 * ((queryCount : ℝ≥0∞) * pietrzakRankError F slack).toReal :=
  (advantage_le_batchLWE_add_rankLoss
    slack queryCount errorSampler adversary hbound).trans
      (add_le_add hLWE (le_refl _))

end FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive
