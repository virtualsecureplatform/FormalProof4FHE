/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BinaryGuessCheck

/-!
# Shared-Context Majority Amplification

This module formalizes an executable majority-of-three amplifier for a Boolean guess.  Three
fresh runs are conditionally independent after the public context is fixed.  Iterating the
amplifier therefore remains sound even when every run shares an arbitrarily correlated hidden
bit and public context, provided the base error bound holds pointwise on the source support.

The exact error update is

`majorityError e = e² * (1 + 2 * (1 - e))`.

No cryptographic or independence assumption about the source itself is used.  In particular, the
pointwise hypothesis below is deliberately stronger than an average distinguishing-gap bound.
-/

open OracleComp

namespace FormalProof4FHE.MajorityAmplification

/-- Run one Boolean computation three times independently and return its strict majority. -/
def majority3 (trial : ProbComp Bool) : ProbComp Bool := do
  let first ← trial
  let second ← trial
  let third ← trial
  return (first && second) || (first && third) || (second && third)

/-- Exact failure probability of majority-of-three, expressed using the base failure and success
probabilities. -/
theorem failureProbability_majority3 (trial : ProbComp Bool) :
    Pr[= false | majority3 trial] =
      Pr[= false | trial] ^ 2 * (1 + 2 * Pr[= true | trial]) := by
  simp [majority3, probOutput_bind_eq_tsum]
  ring

/-- A convenient quadratic upper bound on one majority-of-three step. -/
theorem failureProbability_majority3_le_three_mul_sq (trial : ProbComp Bool) :
    Pr[= false | majority3 trial] ≤ 3 * Pr[= false | trial] ^ 2 := by
  rw [failureProbability_majority3]
  calc
    _ ≤ Pr[= false | trial] ^ 2 * (1 + 2 * 1) := by
      gcongr
      exact probOutput_le_one
    _ = _ := by ring

/-- Turn a candidate bit into the Boolean event that it equals the fixed hidden bit. -/
def correctness (hidden : Bool) (guess : ProbComp Bool) : ProbComp Bool := do
  let candidate ← guess
  return decide (candidate = hidden)

/-- Majority voting on candidate bits is majority voting on their correctness bits. -/
theorem failureProbability_correctness_majority3 (hidden : Bool) (guess : ProbComp Bool) :
    Pr[= false | correctness hidden (majority3 guess)] =
      Pr[= false | correctness hidden guess] ^ 2 *
        (1 + 2 * Pr[= true | correctness hidden guess]) := by
  cases hidden <;>
    simp [correctness, majority3, probOutput_bind_eq_tsum] <;>
    ring

/-- Exact error update for one majority-of-three step. -/
noncomputable def majorityError (error : ENNReal) : ENNReal :=
  error ^ 2 * (1 + 2 * (1 - error))

private theorem majorityErrorReal_mono {left right : ℝ}
    (hleft : 0 ≤ left) (hle : left ≤ right) (hright : right ≤ 1) :
    left ^ 2 * (1 + 2 * (1 - left)) ≤
      right ^ 2 * (1 + 2 * (1 - right)) := by
  have hright_nonneg : 0 ≤ right := hleft.trans hle
  have hleft_one : left ≤ 1 := hle.trans hright
  have hleft_sq : left ^ 2 ≤ left := by
    nlinarith [mul_nonneg hleft (sub_nonneg.mpr hleft_one)]
  have hright_sq : right ^ 2 ≤ right := by
    nlinarith [mul_nonneg hright_nonneg (sub_nonneg.mpr hright)]
  have hcross : 2 * left * right ≤ left ^ 2 + right ^ 2 := by
    nlinarith [sq_nonneg (left - right)]
  have hfactor : 0 ≤
      3 * (left + right) - 2 * (left ^ 2 + left * right + right ^ 2) := by
    nlinarith
  have hproduct := mul_nonneg (sub_nonneg.mpr hle) hfactor
  nlinarith

/-- `majorityError` is monotone throughout the probability interval `[0,1]`. -/
theorem majorityError_mono {left right : ENNReal} (hle : left ≤ right)
    (hright : right ≤ 1) : majorityError left ≤ majorityError right := by
  have hleft : left ≤ 1 := hle.trans hright
  have hleft_ne : left ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hleft
  have hright_ne : right ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hright
  have majorityError_le_three (error : ENNReal) (herror : error ≤ 1) :
      majorityError error ≤ 3 := by
    unfold majorityError
    calc
      error ^ 2 * (1 + 2 * (1 - error)) ≤ 1 ^ 2 * (1 + 2 * 1) := by
        gcongr
        exact tsub_le_self
      _ = 3 := by norm_num
  have hleft_error_ne : majorityError left ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) (majorityError_le_three left hleft)
  have hright_error_ne : majorityError right ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) (majorityError_le_three right hright)
  have majorityError_toReal (error : ENNReal) (herror : error ≤ 1) :
      (majorityError error).toReal =
        error.toReal ^ 2 * (1 + 2 * (1 - error.toReal)) := by
    have hsub_ne : 1 - error ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hmul_ne : 2 * (1 - error) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hsub_ne
    unfold majorityError
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_add ENNReal.one_ne_top hmul_ne,
      ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le herror ENNReal.one_ne_top]
    norm_num
  apply (ENNReal.toReal_le_toReal hleft_error_ne hright_error_ne).mp
  rw [majorityError_toReal left hleft, majorityError_toReal right hright]
  exact majorityErrorReal_mono ENNReal.toReal_nonneg
    ((ENNReal.toReal_le_toReal hleft_ne hright_ne).mpr hle)
    ((ENNReal.toReal_le_toReal hright_ne ENNReal.one_ne_top).mpr hright)

/-- The exact majority error specializes to the failure probability of candidate recovery. -/
theorem failureProbability_correctness_majority3_eq_majorityError
    (hidden : Bool) (guess : ProbComp Bool) :
    Pr[= false | correctness hidden (majority3 guess)] =
      majorityError Pr[= false | correctness hidden guess] := by
  rw [failureProbability_correctness_majority3]
  simp [majorityError, probOutput_true_eq_sub]

/-- Iterate majority-of-three for `rounds` levels.  Level `r` executes `3^r` fresh base guesses. -/
def amplify : ℕ → {Context : Type} → (Context → ProbComp Bool) → Context → ProbComp Bool
  | 0, _, guess => guess
  | rounds + 1, _, guess => fun context => majority3 (amplify rounds guess context)

/-- Amplification depends only on the base trial at the selected context. -/
theorem amplify_eq_of_base_eq {LeftContext RightContext : Type} (rounds : ℕ)
    (left : LeftContext → ProbComp Bool) (right : RightContext → ProbComp Bool)
    (leftContext : LeftContext) (rightContext : RightContext)
    (hbase : left leftContext = right rightContext) :
    amplify rounds left leftContext = amplify rounds right rightContext := by
  induction rounds with
  | zero => exact hbase
  | succ rounds ih =>
      simpa only [amplify] using congrArg majority3 ih

/-! ## Explicit finite tapes for majority amplification -/

/-- Strict majority of a three-entry Boolean vector. -/
def strictMajority (votes : Fin 3 → Bool) : Bool :=
  (votes 0 && votes 1) || (votes 0 && votes 2) || (votes 1 && votes 2)

/-- A depth-indexed ternary tree holding one explicit input at every majority leaf. -/
def MajorityBatch (Input : Type) : ℕ → Type
  | 0 => Input
  | rounds + 1 => Fin 3 → MajorityBatch Input rounds

/-- Finite inputs give finite majority batches at every depth. -/
instance instFiniteMajorityBatch {Input : Type} [Finite Input] (rounds : ℕ) :
    Finite (MajorityBatch Input rounds) := by
  induction rounds with
  | zero => simpa only [MajorityBatch] using (inferInstance : Finite Input)
  | succ rounds ih =>
      simpa only [MajorityBatch] using
        (inferInstance : Finite (Fin 3 → MajorityBatch Input rounds))

/-- Independently fill every leaf of a ternary majority batch from one input sampler. -/
def sampleMajorityBatch {Input : Type} :
    (rounds : ℕ) → ProbComp Input → ProbComp (MajorityBatch Input rounds)
  | 0, sampler => sampler
  | rounds + 1, sampler =>
      Fin.mOfFn 3 fun _ => sampleMajorityBatch rounds sampler

/-- Run the base randomized procedure once on every stored leaf and combine the results through
the same ternary majority tree. -/
def runMajorityBatch {Input : Type} :
    (rounds : ℕ) → (Input → ProbComp Bool) →
      MajorityBatch Input rounds → ProbComp Bool
  | 0, trial, input => trial input
  | rounds + 1, trial, inputs =>
      strictMajority <$> Fin.mOfFn 3 fun branch =>
        runMajorityBatch rounds trial (inputs branch)

/-- Number of stored inputs in a depth-indexed majority batch. -/
def majorityBatchViewCount : ℕ → ℕ
  | 0 => 1
  | rounds + 1 => 3 * majorityBatchViewCount rounds

/-- A depth-`rounds` majority batch stores exactly `3 ^ rounds` inputs. -/
theorem majorityBatchViewCount_eq_pow (rounds : ℕ) :
    majorityBatchViewCount rounds = 3 ^ rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      simp only [majorityBatchViewCount, ih, pow_succ]
      omega

/-- The vector presentation of three independent trials is exactly `majority3`. -/
theorem strictMajority_fin_mOfFn_three (trial : ProbComp Bool) :
    strictMajority <$> Fin.mOfFn 3 (fun _ => trial) = majority3 trial := by
  simp only [Fin.mOfFn, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply bind_congr
  intro first
  apply bind_congr
  intro second
  apply bind_congr
  intro third
  let votes : Fin 3 → Bool :=
    Fin.cons first (Fin.cons second (Fin.cons third Fin.elim0))
  change (pure ∘ strictMajority) votes =
    pure (first && second || first && third || second && third)
  simp only [Function.comp_apply, strictMajority, votes, Fin.cons_zero]
  rw [show (2 : Fin 3) = (0 : Fin 1).succ.succ by rfl]
  rfl

/-- Sampling all majority inputs up front and then consuming the finite batch has exactly the
same output distribution as recursive fresh-sample amplification. -/
theorem evalDist_sampleMajorityBatch_run {Input : Type} [Finite Input]
    (rounds : ℕ) (sampler : ProbComp Input) (trial : Input → ProbComp Bool) :
    evalDist (do
      let inputs ← sampleMajorityBatch rounds sampler
      runMajorityBatch rounds trial inputs) =
      evalDist (amplify rounds (fun _ : Unit => sampler >>= trial) ()) := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      let childSampler := sampleMajorityBatch rounds sampler
      let childTrial := runMajorityBatch rounds trial
      let amplifiedTrial := amplify rounds (fun _ : Unit => sampler >>= trial) ()
      have hfront :=
        FormalProof4FHE.FiniteProduct.evalDist_presample_fin_mOfFn
          3 (fun _ => childSampler) (fun _ => childTrial)
      have hchildren :
          evalDist (Fin.mOfFn 3 fun _ => childSampler >>= childTrial) =
            evalDist (Fin.mOfFn 3 fun _ => amplifiedTrial) :=
        FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr 3
          (fun _ => childSampler >>= childTrial)
          (fun _ => amplifiedTrial) (fun _ => ih)
      calc
        evalDist (do
            let inputs ← sampleMajorityBatch (rounds + 1) sampler
            runMajorityBatch (rounds + 1) trial inputs) =
          evalDist (strictMajority <$> (do
            let inputs ← Fin.mOfFn 3 fun _ => childSampler
            Fin.mOfFn 3 fun branch => childTrial (inputs branch))) := by
              simp only [sampleMajorityBatch, runMajorityBatch, childSampler,
                childTrial, map_eq_bind_pure_comp, bind_assoc]
              rfl
        _ = evalDist
            (strictMajority <$> Fin.mOfFn 3
              (fun _ => childSampler >>= childTrial)) := by
              simpa only [evalDist_map] using
                congrArg (fun distribution => strictMajority <$> distribution) hfront
        _ = evalDist
            (strictMajority <$> Fin.mOfFn 3 (fun _ => amplifiedTrial)) := by
              simpa only [evalDist_map] using
                congrArg (fun distribution => strictMajority <$> distribution) hchildren
        _ = evalDist
            (amplify (rounds + 1) (fun _ : Unit => sampler >>= trial) ()) := by
              rw [strictMajority_fin_mOfFn_three]
              rfl

/-- Iterate the exact majority error update. -/
noncomputable def amplifiedError : ℕ → ENNReal → ENNReal
  | 0, error => error
  | rounds + 1, error => majorityError (amplifiedError rounds error)

/-- One majority update preserves the probability interval. -/
theorem majorityError_le_one {error : ENNReal} (herror : error ≤ 1) :
    majorityError error ≤ 1 := by
  have h := majorityError_mono herror (right := 1) le_rfl
  simpa [majorityError] using h

/-- Every iterated error bound remains at most one. -/
theorem amplifiedError_le_one (rounds : ℕ) {error : ENNReal}
    (herror : error ≤ 1) : amplifiedError rounds error ≤ 1 := by
  induction rounds with
  | zero => exact herror
  | succ rounds ih => exact majorityError_le_one ih

/-- Pointwise amplification for one fixed hidden bit and context. -/
theorem failureProbability_correctness_amplify_le {Context : Type} (rounds : ℕ)
    (guess : Context → ProbComp Bool) (hidden : Bool) (context : Context) (error : ENNReal)
    (herror_one : error ≤ 1)
    (herror : Pr[= false | correctness hidden (guess context)] ≤ error) :
    Pr[= false | correctness hidden (amplify rounds guess context)] ≤
      amplifiedError rounds error := by
  induction rounds with
  | zero => exact herror
  | succ rounds ih =>
      change Pr[= false |
          correctness hidden (majority3 (amplify rounds guess context))] ≤ _
      rw [failureProbability_correctness_majority3_eq_majorityError]
      simp only [amplifiedError]
      exact majorityError_mono ih (amplifiedError_le_one rounds herror_one)

/-- Recovery experiment for a hidden bit correlated with an arbitrary public context. -/
def recoveryGame {Context : Type} (source : ProbComp (Bool × Context))
    (guess : Context → ProbComp Bool) : ProbComp Bool := do
  let hiddenAndContext ← source
  correctness hiddenAndContext.1 (guess hiddenAndContext.2)

/-- Shared-context amplification theorem.

The source is sampled only once.  All repeated guesses see the same context, so soundness is based
on a pointwise conditional error bound for every source-support element, not on independence of
unconditional trials. -/
theorem recoveryGame_amplify_failure_le {Context : Type}
    (source : ProbComp (Bool × Context)) (guess : Context → ProbComp Bool)
    (rounds : ℕ) (error : ENNReal) (herror_one : error ≤ 1)
    (herror : ∀ hiddenAndContext ∈ support source,
      Pr[= false | correctness hiddenAndContext.1 (guess hiddenAndContext.2)] ≤ error) :
    Pr[= false | recoveryGame source (amplify rounds guess)] ≤
      amplifiedError rounds error := by
  rw [← probEvent_not_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro hiddenAndContext hsupport
  rw [probEvent_not_eq_probOutput]
  exact failureProbability_correctness_amplify_le rounds guess hiddenAndContext.1
    hiddenAndContext.2 error herror_one (herror hiddenAndContext hsupport)

/-- Shared-context amplification from an **averaged** base error, with an explicit threshold
loss.  This is the finite-probability analogue of splitting contexts into good fibers, whose
conditional base error is at most `threshold`, and bad fibers controlled by Markov's inequality.

Unlike `recoveryGame_amplify_failure_le`, this theorem does not require a uniform pointwise bound.
It pays

`amplifiedError rounds threshold + averageBaseError / threshold`.

The second term is essential: repeating guesses against one fixed public context cannot in
general amplify an averaged distinguishing gap for free. -/
theorem recoveryGame_amplify_failure_le_threshold {Context : Type}
    (source : ProbComp (Bool × Context)) (guess : Context → ProbComp Bool)
    (rounds : ℕ) (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1) :
    Pr[= false | recoveryGame source (amplify rounds guess)] ≤
      amplifiedError rounds threshold +
        Pr[= false | recoveryGame source guess] / threshold := by
  have hthreshold_ne_zero : threshold ≠ 0 := ne_of_gt hthreshold_pos
  have hthreshold_ne_top : threshold ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hthreshold_one
  have hpointwise (hiddenAndContext : Bool × Context) :
      Pr[= false |
          correctness hiddenAndContext.1
            (amplify rounds guess hiddenAndContext.2)] ≤
        amplifiedError rounds threshold +
          Pr[= false |
            correctness hiddenAndContext.1 (guess hiddenAndContext.2)] / threshold := by
    let baseError := Pr[= false |
      correctness hiddenAndContext.1 (guess hiddenAndContext.2)]
    by_cases hgood : baseError ≤ threshold
    · exact (failureProbability_correctness_amplify_le rounds guess
          hiddenAndContext.1 hiddenAndContext.2 threshold hthreshold_one hgood).trans
        (le_add_right le_rfl)
    · have hthreshold_lt : threshold < baseError := lt_of_not_ge hgood
      have hone_le : (1 : ENNReal) ≤ baseError / threshold := by
        apply (ENNReal.le_div_iff_mul_le
          (Or.inl hthreshold_ne_zero) (Or.inl hthreshold_ne_top)).2
        simpa only [one_mul] using hthreshold_lt.le
      exact probOutput_le_one.trans
        (hone_le.trans (le_add_left le_rfl))
  change Pr[= false |
      source >>= fun hiddenAndContext ↦
        correctness hiddenAndContext.1
          (amplify rounds guess hiddenAndContext.2)] ≤ _
  rw [probOutput_bind_eq_tsum]
  change _ ≤ amplifiedError rounds threshold +
    Pr[= false |
      source >>= fun hiddenAndContext ↦
        correctness hiddenAndContext.1 (guess hiddenAndContext.2)] / threshold
  rw [probOutput_bind_eq_tsum]
  calc
    (∑' hiddenAndContext,
        Pr[= hiddenAndContext | source] *
          Pr[= false |
            correctness hiddenAndContext.1
              (amplify rounds guess hiddenAndContext.2)]) ≤
      ∑' hiddenAndContext,
        Pr[= hiddenAndContext | source] *
          (amplifiedError rounds threshold +
            Pr[= false |
              correctness hiddenAndContext.1 (guess hiddenAndContext.2)] / threshold) := by
      apply ENNReal.tsum_le_tsum
      intro hiddenAndContext
      exact mul_le_mul_right (hpointwise hiddenAndContext) _
    _ = (∑' hiddenAndContext,
          Pr[= hiddenAndContext | source] * amplifiedError rounds threshold) +
        ∑' hiddenAndContext,
          Pr[= hiddenAndContext | source] *
            (Pr[= false |
              correctness hiddenAndContext.1 (guess hiddenAndContext.2)] / threshold) := by
      simp_rw [mul_add]
      exact ENNReal.tsum_add
    _ = amplifiedError rounds threshold +
        (∑' hiddenAndContext,
          Pr[= hiddenAndContext | source] *
            Pr[= false |
              correctness hiddenAndContext.1 (guess hiddenAndContext.2)]) / threshold := by
      rw [FormalProof4FHE.FiniteProduct.tsum_probOutput_mul_const]
      congr 1
      simp_rw [ENNReal.div_eq_inv_mul]
      calc
        (∑' hiddenAndContext,
          Pr[= hiddenAndContext | source] *
            (threshold⁻¹ * Pr[= false |
              correctness hiddenAndContext.1 (guess hiddenAndContext.2)])) =
            ∑' hiddenAndContext,
              threshold⁻¹ *
                (Pr[= hiddenAndContext | source] *
                  Pr[= false |
                    correctness hiddenAndContext.1 (guess hiddenAndContext.2)]) := by
          apply tsum_congr
          intro hiddenAndContext
          ac_rfl
        _ = threshold⁻¹ *
            ∑' hiddenAndContext,
              Pr[= hiddenAndContext | source] *
                Pr[= false |
                  correctness hiddenAndContext.1 (guess hiddenAndContext.2)] :=
          ENNReal.tsum_mul_left
    _ = _ := rfl

/-- Convenient consequence when the averaged one-shot failure is bounded by a supplied value. -/
theorem recoveryGame_amplify_failure_le_of_average
    {Context : Type}
    (source : ProbComp (Bool × Context)) (guess : Context → ProbComp Bool)
    (rounds : ℕ) (threshold averageError : ENNReal)
    (hthreshold_pos : 0 < threshold) (hthreshold_one : threshold ≤ 1)
    (haverage : Pr[= false | recoveryGame source guess] ≤ averageError) :
    Pr[= false | recoveryGame source (amplify rounds guess)] ≤
      amplifiedError rounds threshold + averageError / threshold := by
  exact (recoveryGame_amplify_failure_le_threshold source guess rounds threshold
    hthreshold_pos hthreshold_one).trans
      (add_le_add le_rfl (ENNReal.div_le_div_right haverage threshold))

/-! ## Whole-vector amplification with one bad-fiber charge -/

/-- Correctness of a candidate vector against a fixed hidden Boolean vector. -/
def vectorCorrectness {count : ℕ} (hidden : Fin count → Bool)
    (guess : ProbComp (Fin count → Bool)) : ProbComp Bool := do
  let candidate ← guess
  return decide (candidate = hidden)

/-- Independently run the amplified coordinate guess for every coordinate.  Each base invocation
may itself query a fresh public view through the supplied context. -/
def amplifyVector {count : ℕ} {Context : Type}
    (rounds : Fin count → ℕ)
    (guess : Fin count → Context → ProbComp Bool)
    (context : Context) : ProbComp (Fin count → Bool) :=
  Fin.mOfFn count fun coordinate ↦
    amplify (rounds coordinate) (guess coordinate) context

/-- Sample one hidden-vector/context fiber and test the complete amplified candidate. -/
def vectorRecoveryGame {count : ℕ} {Context : Type}
    (source : ProbComp ((Fin count → Bool) × Context))
    (rounds : Fin count → ℕ)
    (guess : Fin count → Context → ProbComp Bool) : ProbComp Bool := do
  let hiddenAndContext ← source
  vectorCorrectness hiddenAndContext.1
    (amplifyVector rounds guess hiddenAndContext.2)

/-- Failure of independently sampled coordinate guesses is bounded by the sum of their
coordinate failure probabilities. -/
theorem failureProbability_vectorCorrectness_fin_mOfFn_le_sum
    {count : ℕ} (hidden : Fin count → Bool)
    (samplers : Fin count → ProbComp Bool) :
    Pr[= false |
      vectorCorrectness hidden (Fin.mOfFn count samplers)] ≤
      ∑ coordinate,
        Pr[= false | correctness (hidden coordinate) (samplers coordinate)] := by
  classical
  have hevent :
      (fun candidate : Fin count → Bool ↦ candidate ≠ hidden) =
      (fun candidate ↦ ∃ coordinate ∈ (Finset.univ : Finset (Fin count)),
        candidate coordinate ≠ hidden coordinate) := by
    funext candidate
    apply propext
    constructor
    · intro hne
      by_contra hnone
      apply hne
      funext coordinate
      by_contra hcoordinate
      exact hnone ⟨coordinate, Finset.mem_univ coordinate, hcoordinate⟩
    · rintro ⟨coordinate, _hcoordinate, hne⟩ heq
      exact hne (congrFun heq coordinate)
  have hcoordinate (coordinate : Fin count) :
      Pr[(fun candidate : Fin count → Bool ↦
          candidate coordinate ≠ hidden coordinate) |
        Fin.mOfFn count samplers] =
      Pr[= false | correctness (hidden coordinate) (samplers coordinate)] := by
    calc
      _ = Pr[(fun candidate : Bool ↦ candidate ≠ hidden coordinate) |
          samplers coordinate] :=
        FormalProof4FHE.FiniteProduct.probEvent_fin_mOfFn_apply
          count samplers coordinate
            (fun candidate ↦ candidate ≠ hidden coordinate)
      _ = _ := by
        rw [show correctness (hidden coordinate) (samplers coordinate) =
            (fun candidate ↦ decide (candidate = hidden coordinate)) <$>
              samplers coordinate by simp [correctness, map_eq_bind_pure_comp]]
        rw [probOutput_map]
        simp
  rw [show vectorCorrectness hidden (Fin.mOfFn count samplers) =
      (fun candidate ↦ decide (candidate = hidden)) <$>
        Fin.mOfFn count samplers by
      simp [vectorCorrectness, map_eq_bind_pure_comp],
    probOutput_map]
  simp only [decide_eq_false_iff_not]
  rw [hevent]
  simpa only [hcoordinate] using
    (probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin count))
      (Fin.mOfFn count samplers)
      (fun coordinate candidate ↦ candidate coordinate ≠ hidden coordinate))

/-- **Whole-vector averaged amplification.**

Every coordinate may have a different guess algorithm and amplification depth, but all
coordinates share one hidden-vector/context fiber.  If their conditional base errors are bounded
by one common fiber error, the bad-fiber Markov term is paid only once for the complete vector:

`failure ≤ ∑ᵢ amplifiedError (rounds i) threshold + averageFiberError / threshold`.

This is stronger than applying the scalar averaged theorem coordinatewise, which would charge the
same bad fiber once per coordinate. -/
theorem vectorRecoveryGame_amplify_failure_le_of_common_average
    {count : ℕ} {Context : Type}
    (source : ProbComp ((Fin count → Bool) × Context))
    (rounds : Fin count → ℕ)
    (guess : Fin count → Context → ProbComp Bool)
    (fiberError : ((Fin count → Bool) × Context) → ENNReal)
    (threshold averageError : ENNReal)
    (hthreshold_pos : 0 < threshold) (hthreshold_one : threshold ≤ 1)
    (hcoordinate : ∀ hiddenAndContext ∈ support source, ∀ coordinate,
      Pr[= false |
        correctness (hiddenAndContext.1 coordinate)
          (guess coordinate hiddenAndContext.2)] ≤
        fiberError hiddenAndContext)
    (haverage :
      (∑' hiddenAndContext,
        Pr[= hiddenAndContext | source] * fiberError hiddenAndContext) ≤
          averageError) :
    Pr[= false | vectorRecoveryGame source rounds guess] ≤
      (∑ coordinate, amplifiedError (rounds coordinate) threshold) +
        averageError / threshold := by
  have hthreshold_ne_zero : threshold ≠ 0 := ne_of_gt hthreshold_pos
  have hthreshold_ne_top : threshold ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hthreshold_one
  let amplifiedSum := ∑ coordinate, amplifiedError (rounds coordinate) threshold
  have hpointwise (hiddenAndContext : (Fin count → Bool) × Context)
      (hsupport : hiddenAndContext ∈ support source) :
      Pr[= false |
        vectorCorrectness hiddenAndContext.1
          (amplifyVector rounds guess hiddenAndContext.2)] ≤
        amplifiedSum + fiberError hiddenAndContext / threshold := by
    by_cases hgood : fiberError hiddenAndContext ≤ threshold
    · have hcoordinateAmplified (coordinate : Fin count) :
          Pr[= false |
            correctness (hiddenAndContext.1 coordinate)
              (amplify (rounds coordinate) (guess coordinate)
                hiddenAndContext.2)] ≤
            amplifiedError (rounds coordinate) threshold :=
        failureProbability_correctness_amplify_le
          (rounds coordinate) (guess coordinate)
          (hiddenAndContext.1 coordinate) hiddenAndContext.2 threshold
          hthreshold_one
          ((hcoordinate hiddenAndContext hsupport coordinate).trans hgood)
      exact (failureProbability_vectorCorrectness_fin_mOfFn_le_sum
          hiddenAndContext.1
          (fun coordinate ↦ amplify (rounds coordinate) (guess coordinate)
            hiddenAndContext.2)).trans
        ((Finset.sum_le_sum fun coordinate _ ↦ hcoordinateAmplified coordinate).trans
          (le_add_right le_rfl))
    · have hthreshold_lt : threshold < fiberError hiddenAndContext :=
        lt_of_not_ge hgood
      have hone_le : (1 : ENNReal) ≤ fiberError hiddenAndContext / threshold := by
        apply (ENNReal.le_div_iff_mul_le
          (Or.inl hthreshold_ne_zero) (Or.inl hthreshold_ne_top)).2
        simpa only [one_mul] using hthreshold_lt.le
      exact probOutput_le_one.trans (hone_le.trans (le_add_left le_rfl))
  change Pr[= false |
      source >>= fun hiddenAndContext ↦
        vectorCorrectness hiddenAndContext.1
          (amplifyVector rounds guess hiddenAndContext.2)] ≤ _
  rw [probOutput_bind_eq_tsum]
  calc
    (∑' hiddenAndContext,
        Pr[= hiddenAndContext | source] *
          Pr[= false |
            vectorCorrectness hiddenAndContext.1
              (amplifyVector rounds guess hiddenAndContext.2)]) ≤
      ∑' hiddenAndContext,
        Pr[= hiddenAndContext | source] *
          (amplifiedSum + fiberError hiddenAndContext / threshold) := by
      apply ENNReal.tsum_le_tsum
      intro hiddenAndContext
      by_cases hsupport : hiddenAndContext ∈ support source
      · exact mul_le_mul_right (hpointwise hiddenAndContext hsupport) _
      · rw [probOutput_eq_zero_of_not_mem_support hsupport, zero_mul, zero_mul]
    _ = (∑' hiddenAndContext,
          Pr[= hiddenAndContext | source] * amplifiedSum) +
        ∑' hiddenAndContext,
          Pr[= hiddenAndContext | source] *
            (fiberError hiddenAndContext / threshold) := by
      simp_rw [mul_add]
      exact ENNReal.tsum_add
    _ = amplifiedSum +
        (∑' hiddenAndContext,
          Pr[= hiddenAndContext | source] * fiberError hiddenAndContext) /
            threshold := by
      rw [FormalProof4FHE.FiniteProduct.tsum_probOutput_mul_const]
      congr 1
      simp_rw [ENNReal.div_eq_inv_mul]
      calc
        (∑' hiddenAndContext,
          Pr[= hiddenAndContext | source] *
            (threshold⁻¹ * fiberError hiddenAndContext)) =
            ∑' hiddenAndContext,
              threshold⁻¹ *
                (Pr[= hiddenAndContext | source] *
                  fiberError hiddenAndContext) := by
          apply tsum_congr
          intro hiddenAndContext
          ac_rfl
        _ = threshold⁻¹ *
            ∑' hiddenAndContext,
              Pr[= hiddenAndContext | source] *
                fiberError hiddenAndContext := ENNReal.tsum_mul_left
    _ ≤ amplifiedSum + averageError / threshold :=
      add_le_add le_rfl (ENNReal.div_le_div_right haverage threshold)
    _ = _ := rfl

end FormalProof4FHE.MajorityAmplification
