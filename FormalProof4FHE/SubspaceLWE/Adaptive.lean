/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.RankBound
import Mathlib.LinearAlgebra.Matrix.Rank
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.Append

/-!
# Adaptive Affine-Projection Subspace LWE

This file formalizes the adaptive oracle from Pietrzak's Subspace-LWE definition.  A query is a
pair of affine projections.  Queries whose linear overlap has rank below the public threshold
return `none` (the paper's `⊥`); admissible queries return an ambient random vector together with
the noisy inner product of the two projected vectors.

The second half isolates the probabilistic argument used by the LWE-to-SLWE simulator.  A hidden
matrix is sampled once, and adaptively selected admissible queries may trigger a rank-loss event.
The theorem `adaptiveRankLoss_le` proves the complete first-bad union bound: a pointwise
fixed-query estimate `ε` lifts to `Q * ε` for `Q` adaptive queries, provided the query strategy's
pre-failure view is independent of the hidden matrix.  This is exactly the independence supplied
by the affine blinding vector in Pietrzak's simulator.

The rectangular finite-field rank estimate is proved in `Probability.RankBound`.  The remaining
bridge from a high-rank query overlap to that rectangular experiment, and the construction and
correctness proof of the LWE simulator, are deliberately exposed as separate premises.  Thus the
adaptive theorem below does not hide either ingredient as an axiom.
-/

open Matrix OracleComp OracleSpec
open scoped ENNReal

namespace FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive

/-! ## The adaptive affine-projection oracle -/

/-- An affine endomorphism `v ↦ linear * v + offset` of the ambient secret space. -/
structure AffineProjection (R : Type) (ambientDimension : ℕ) where
  linear : Matrix (Fin ambientDimension) (Fin ambientDimension) R
  offset : Fin ambientDimension → R

namespace AffineProjection

/-- Evaluate an affine projection. -/
def apply {R : Type} [Semiring R] {ambientDimension : ℕ}
    (projection : AffineProjection R ambientDimension)
    (vector : Fin ambientDimension → R) : Fin ambientDimension → R :=
  projection.linear *ᵥ vector + projection.offset

@[simp]
theorem apply_zeroOffset {R : Type} [Semiring R] {ambientDimension : ℕ}
    (linear : Matrix (Fin ambientDimension) (Fin ambientDimension) R)
    (vector : Fin ambientDimension → R) :
    (AffineProjection.mk linear 0).apply vector = linear *ᵥ vector := by
  simp [apply]

end AffineProjection

/-- A Subspace-LWE oracle query contains affine projections of both the fresh randomness and the
fixed secret. -/
structure Query (R : Type) (ambientDimension : ℕ) where
  randomness : AffineProjection R ambientDimension
  secret : AffineProjection R ambientDimension

namespace Query

/-- The linear overlap whose rank controls whether a query is answered. -/
def overlap {R : Type} [Semiring R] {ambientDimension : ℕ}
    (query : Query R ambientDimension) :
    Matrix (Fin ambientDimension) (Fin ambientDimension) R :=
  query.randomness.linearᵀ * query.secret.linear

/-- The public rank guard in the Subspace-LWE oracle. -/
def IsAdmissible {R : Type} [CommSemiring R] {ambientDimension : ℕ}
    (threshold : ℕ) (query : Query R ambientDimension) : Prop :=
  threshold ≤ query.overlap.rank

end Query

/-- An oracle answer.  `none` represents `⊥`; `some (r, z)` represents the ambient random
vector and its noisy projected inner product. -/
abbrev Response (R : Type) (ambientDimension : ℕ) :=
  Option ((Fin ambientDimension → R) × R)

/-- The adversary-facing oracle interface: internal uniform sampling plus adaptive
affine-projection queries. -/
abbrev OracleInterface (R : Type) (ambientDimension : ℕ) :=
  unifSpec + (Query R ambientDimension →ₒ Response R ambientDimension)

/-- An adaptive Subspace-LWE distinguisher. -/
abbrev Adversary (R : Type) (ambientDimension : ℕ) :=
  OracleComp (OracleInterface R ambientDimension) Bool

/-- The scalar returned by an admissible query before it is paired with the fresh randomness. -/
def noisyInnerProduct {R : Type} [CommSemiring R] {ambientDimension : ℕ}
    (secret randomness : Fin ambientDimension → R)
    (query : Query R ambientDimension) (error : R) : R :=
  dotProduct (query.randomness.apply randomness) (query.secret.apply secret) + error

/-- The adaptive `Γ_{χ,ℓ,d}` query implementation from Pietrzak's definition. -/
noncomputable def queryImpl {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (threshold : ℕ) (secret : Fin ambientDimension → R) (errorSampler : ProbComp R) :
    QueryImpl (Query R ambientDimension →ₒ Response R ambientDimension) ProbComp :=
  fun query ↦
    if threshold ≤ query.overlap.rank then do
      let randomness ← $ᵗ (Fin ambientDimension → R)
      let error ← errorSampler
      return some (randomness, noisyInnerProduct secret randomness query error)
    else
      return none

/-- Combine the Subspace-LWE oracle with the adversary's internal uniform-sampling oracle. -/
noncomputable def fullImpl {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (threshold : ℕ) (secret : Fin ambientDimension → R) (errorSampler : ProbComp R) :
    QueryImpl (OracleInterface R ambientDimension) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + queryImpl threshold secret errorSampler

/-- The real adaptive Subspace-LWE game. -/
noncomputable def realGame {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (threshold : ℕ) (errorSampler : ProbComp R)
    (adversary : Adversary R ambientDimension) : ProbComp Bool := do
  let secret ← $ᵗ (Fin ambientDimension → R)
  simulateQ (fullImpl threshold secret errorSampler) adversary

/-- The uniform-error adaptive Subspace-LWE game `Γ_{U, ℓ, d}`. -/
noncomputable def uniformGame {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (threshold : ℕ) (adversary : Adversary R ambientDimension) : ProbComp Bool :=
  realGame threshold ($ᵗ R) adversary

/-- Adaptive Subspace-LWE distinguishing advantage. -/
noncomputable def advantage {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (threshold : ℕ) (errorSampler : ProbComp R)
    (adversary : Adversary R ambientDimension) : ℝ :=
  (realGame threshold errorSampler adversary).boolDistAdvantage
    (uniformGame threshold adversary)

@[simp]
theorem queryImpl_of_not_admissible {R : Type}
    [CommSemiring R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (threshold : ℕ) (secret : Fin ambientDimension → R) (errorSampler : ProbComp R)
    (query : Query R ambientDimension) (hquery : ¬ query.IsAdmissible threshold) :
    queryImpl threshold secret errorSampler query = pure none := by
  change ¬threshold ≤ query.overlap.rank at hquery
  simp [queryImpl, hquery]

@[simp]
theorem queryImpl_of_admissible {R : Type}
    [CommSemiring R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (threshold : ℕ) (secret : Fin ambientDimension → R) (errorSampler : ProbComp R)
    (query : Query R ambientDimension) (hquery : query.IsAdmissible threshold) :
    queryImpl threshold secret errorSampler query = do
      let randomness ← $ᵗ (Fin ambientDimension → R)
      let error ← errorSampler
      return some (randomness, noisyInnerProduct secret randomness query error) := by
  change threshold ≤ query.overlap.rank at hquery
  simp [queryImpl, hquery]

/-- The ideal answer to an admissible uniform-error query, written without the secret. -/
def uniformResponse {R : Type} [SampleableType R] (ambientDimension : ℕ) :
    ProbComp (Response R ambientDimension) := do
  let randomness ← $ᵗ (Fin ambientDimension → R)
  let value ← $ᵗ R
  return some (randomness, value)

/-- Adding the fixed projected inner product to a uniform error makes the returned scalar
uniform.  Hence an admissible `Γ_U` answer is independent of both the query and the secret. -/
theorem evalDist_queryImpl_uniform_of_admissible {R : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (threshold : ℕ) (secret : Fin ambientDimension → R)
    (query : Query R ambientDimension) (hquery : query.IsAdmissible threshold) :
    evalDist (queryImpl threshold secret ($ᵗ R) query) =
      evalDist (uniformResponse (R := R) ambientDimension) := by
  rw [queryImpl_of_admissible threshold secret ($ᵗ R) query hquery]
  unfold uniformResponse
  refine evalDist_bind_congr' ($ᵗ (Fin ambientDimension → R)) ?_
  intro randomness
  apply evalDist_ext
  intro output
  simpa [noisyInnerProduct] using
    (probOutput_bind_add_left_uniform R
      (dotProduct (query.randomness.apply randomness) (query.secret.apply secret))
      (fun value ↦ (pure (some (randomness, value)) :
        ProbComp (Response R ambientDimension))) output)

/-! ## Adaptive rank-loss accounting -/

/-- Run `queryCount` adaptive tests against one hidden value and fire at the first bad query.
Only the bad/good history is exposed here.  Any additional pre-failure transcript that is
independent of the hidden value can be fixed as an extra argument to `strategy`. -/
def firstBad {Hidden QueryType : Type} (bad : Hidden → QueryType → Bool)
    (hidden : Hidden) : ℕ → (List Bool → QueryType) → Bool
  | 0, _ => false
  | queryCount + 1, strategy =>
      let fired := bad hidden (strategy [])
      fired || firstBad bad hidden queryCount (fun history ↦ strategy (fired :: history))

/-- Before the first bad query, every reply is `false`, so the queries that can cause the first
failure are fixed by the all-good transcript. -/
theorem firstBad_eq_true_iff {Hidden QueryType : Type}
    (bad : Hidden → QueryType → Bool) (hidden : Hidden)
    (queryCount : ℕ) (strategy : List Bool → QueryType) :
    firstBad bad hidden queryCount strategy = true ↔
      ∃ index < queryCount,
        bad hidden (strategy (List.replicate index false)) = true := by
  induction queryCount generalizing strategy with
  | zero => simp [firstBad]
  | succ queryCount ih =>
      rw [firstBad]
      simp only [Bool.or_eq_true]
      constructor
      · intro hfired
        rcases hfired with hfired | htail
        · exact ⟨0, Nat.succ_pos queryCount, by simpa using hfired⟩
        · by_cases hhead : bad hidden (strategy []) = true
          · exact ⟨0, Nat.succ_pos queryCount, by simpa using hhead⟩
          · have hfalse : bad hidden (strategy []) = false := Bool.eq_false_of_not_eq_true hhead
            rw [hfalse] at htail
            obtain ⟨index, hindex, hbad⟩ :=
              (ih (fun history ↦ strategy (false :: history))).1 htail
            exact ⟨index + 1, Nat.succ_lt_succ hindex,
              by simpa [List.replicate_succ] using hbad⟩
      · rintro ⟨index, hindex, hbad⟩
        cases index with
        | zero => exact Or.inl (by simpa using hbad)
        | succ index =>
            by_cases hhead : bad hidden (strategy []) = true
            · exact Or.inl hhead
            · refine Or.inr ?_
              have hfalse : bad hidden (strategy []) = false :=
                Bool.eq_false_of_not_eq_true hhead
              rw [hfalse]
              exact (ih (fun history ↦ strategy (false :: history))).2
                ⟨index, Nat.lt_of_succ_lt_succ hindex,
                  by simpa [List.replicate_succ] using hbad⟩

/-- Sample one hidden value and run the adaptive first-bad test. -/
def adaptiveBadGame {Hidden QueryType : Type} (hiddenSampler : ProbComp Hidden)
    (bad : Hidden → QueryType → Bool) (queryCount : ℕ)
    (strategy : List Bool → QueryType) : ProbComp Bool :=
  hiddenSampler >>= pure ∘ fun hidden ↦ firstBad bad hidden queryCount strategy

/-- A fixed-query bad-event estimate lifts to `queryCount * ε` adaptive queries.  The theorem
is information-theoretic: `strategy` may depend arbitrarily on all previous bad/good replies.
An independent public/random transcript can be included in the query type or fixed before
applying the theorem. -/
theorem probEvent_adaptiveBadGame_le {Hidden QueryType : Type}
    (hiddenSampler : ProbComp Hidden) (bad : Hidden → QueryType → Bool)
    (queryCount : ℕ) (strategy : List Bool → QueryType) (ε : ℝ≥0∞)
    (hFixed : ∀ query,
      Pr[(fun hidden ↦ bad hidden query = true) | hiddenSampler] ≤ ε) :
    Pr[(fun fired : Bool ↦ fired = true) |
      adaptiveBadGame hiddenSampler bad queryCount strategy] ≤
        (queryCount : ℝ≥0∞) * ε := by
  rw [adaptiveBadGame, probEvent_bind_pure_comp]
  calc
    Pr[(fun hidden ↦ firstBad bad hidden queryCount strategy = true) | hiddenSampler]
        ≤ Pr[(fun hidden ↦ ∃ index ∈ Finset.range queryCount,
            bad hidden (strategy (List.replicate index false)) = true) | hiddenSampler] := by
          apply probEvent_mono
          intro hidden _ hfired
          obtain ⟨index, hindex, hbad⟩ :=
            (firstBad_eq_true_iff bad hidden queryCount strategy).1 hfired
          exact ⟨index, Finset.mem_range.2 hindex, hbad⟩
    _ ≤ ∑ index ∈ Finset.range queryCount,
          Pr[(fun hidden ↦
            bad hidden (strategy (List.replicate index false)) = true) | hiddenSampler] :=
      probEvent_exists_finset_le_sum (Finset.range queryCount) hiddenSampler
        (fun index hidden ↦
          bad hidden (strategy (List.replicate index false)) = true)
    _ ≤ ∑ _index ∈ Finset.range queryCount, ε := by
      exact Finset.sum_le_sum fun index _ ↦ hFixed (strategy (List.replicate index false))
    _ = (queryCount : ℝ≥0∞) * ε := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Version of `adaptiveBadGame` with an arbitrary random tape sampled independently of the
hidden value.  The tape models all public coins and simulated pre-failure oracle answers that an
adaptive distinguisher may use when selecting its next query. -/
def adaptiveBadGameWithTape {Hidden Tape QueryType : Type}
    (hiddenSampler : ProbComp Hidden) (tapeSampler : ProbComp Tape)
    (bad : Hidden → QueryType → Bool) (queryCount : ℕ)
    (strategy : Tape → List Bool → QueryType) : ProbComp Bool := do
  let tape ← tapeSampler
  adaptiveBadGame hiddenSampler bad queryCount (strategy tape)

/-- Independent transcript randomness does not change the adaptive first-bad bound. -/
theorem probEvent_adaptiveBadGameWithTape_le {Hidden Tape QueryType : Type}
    (hiddenSampler : ProbComp Hidden) (tapeSampler : ProbComp Tape)
    (bad : Hidden → QueryType → Bool) (queryCount : ℕ)
    (strategy : Tape → List Bool → QueryType) (ε : ℝ≥0∞)
    (hFixed : ∀ query,
      Pr[(fun hidden ↦ bad hidden query = true) | hiddenSampler] ≤ ε) :
    Pr[(fun fired : Bool ↦ fired = true) |
      adaptiveBadGameWithTape hiddenSampler tapeSampler bad queryCount strategy] ≤
        (queryCount : ℝ≥0∞) * ε := by
  unfold adaptiveBadGameWithTape
  apply probEvent_bind_le_of_forall_le
  intro tape _
  exact probEvent_adaptiveBadGame_le hiddenSampler bad queryCount (strategy tape) ε hFixed

/-! ## The rank event in Pietrzak's simulator -/

/-- The simulator's hidden linear map `R : R^{ℓ × d}`. -/
abbrev HiddenMatrix (R : Type) (ambientDimension lweDimension : ℕ) :=
  Matrix (Fin ambientDimension) (Fin lweDimension) R

/-- The simulator fails on a publicly admissible query precisely when multiplication by its
hidden matrix drops the overlap rank below the source LWE dimension. -/
noncomputable def rankLoss {R : Type} [Field R] [DecidableEq R]
    {ambientDimension : ℕ}
    (lweDimension threshold : ℕ)
    (hidden : HiddenMatrix R ambientDimension lweDimension)
    (query : Query R ambientDimension) : Bool :=
  by
    classical
    exact decide (query.IsAdmissible threshold ∧
      (query.overlap * hidden).rank < lweDimension)

/-- The fixed-query linear-algebra estimate needed by the adaptive argument.  It is named as a
property so later files can discharge it using an exact finite-field rank count without changing
the oracle or reduction statements. -/
def FixedRankLossBound {R : Type} [Field R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (lweDimension threshold : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ query : Query R ambientDimension,
    Pr[(fun hidden ↦ rankLoss lweDimension threshold hidden query = true) |
      ($ᵗ HiddenMatrix R ambientDimension lweDimension)] ≤ ε

/-- Rank loss against `queryCount` adaptive affine-projection queries. -/
noncomputable def adaptiveRankLossGame {R : Type}
    [Field R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (lweDimension threshold queryCount : ℕ)
    (strategy : List Bool → Query R ambientDimension) : ProbComp Bool :=
  adaptiveBadGame ($ᵗ HiddenMatrix R ambientDimension lweDimension)
    (rankLoss lweDimension threshold) queryCount strategy

/-- Rank loss with an independent tape containing the entire simulated good transcript. -/
noncomputable def adaptiveRankLossGameWithTape {R Tape : Type}
    [Field R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (tapeSampler : ProbComp Tape) (lweDimension threshold queryCount : ℕ)
    (strategy : Tape → List Bool → Query R ambientDimension) : ProbComp Bool :=
  adaptiveBadGameWithTape ($ᵗ HiddenMatrix R ambientDimension lweDimension) tapeSampler
    (rankLoss lweDimension threshold) queryCount strategy

/-- Complete adaptive union bound for the Pietrzak rank-loss event. -/
theorem adaptiveRankLoss_le {R : Type} [Field R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (lweDimension threshold queryCount : ℕ) (ε : ℝ≥0∞)
    (strategy : List Bool → Query R ambientDimension)
    (hFixed : FixedRankLossBound (R := R) (ambientDimension := ambientDimension)
      lweDimension threshold ε) :
    Pr[(fun fired : Bool ↦ fired = true) |
      adaptiveRankLossGame lweDimension threshold queryCount strategy] ≤
        (queryCount : ℝ≥0∞) * ε :=
  probEvent_adaptiveBadGame_le
    ($ᵗ HiddenMatrix R ambientDimension lweDimension)
    (rankLoss lweDimension threshold) queryCount strategy ε hFixed

/-- Adaptive rank-loss bound in the presence of an independent simulated transcript tape. -/
theorem adaptiveRankLossWithTape_le {R Tape : Type}
    [Field R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (tapeSampler : ProbComp Tape) (lweDimension threshold queryCount : ℕ) (ε : ℝ≥0∞)
    (strategy : Tape → List Bool → Query R ambientDimension)
    (hFixed : FixedRankLossBound (R := R) (ambientDimension := ambientDimension)
      lweDimension threshold ε) :
    Pr[(fun fired : Bool ↦ fired = true) |
      adaptiveRankLossGameWithTape tapeSampler lweDimension threshold queryCount strategy] ≤
        (queryCount : ℝ≥0∞) * ε :=
  probEvent_adaptiveBadGameWithTape_le
    ($ᵗ HiddenMatrix R ambientDimension lweDimension) tapeSampler
    (rankLoss lweDimension threshold) queryCount strategy ε hFixed

/-- The explicit per-query error appearing in Pietrzak's rank lemma. -/
noncomputable def pietrzakRankError (R : Type) [Fintype R] (slack : ℕ) : ℝ≥0∞ :=
  2 / (Fintype.card R : ℝ≥0∞) ^ (slack + 1)

/-- The independent rectangular matrix experiment satisfies Pietrzak's per-query error bound.
This is the finite-field counting lemma to which the fixed-query overlap argument reduces. -/
theorem rectangularRankFailure_le_pietrzak {R : Type}
    [Field R] [Fintype R] [SampleableType R] (lweDimension slack : ℕ) :
    Pr[(fun matrix : Matrix (Fin (lweDimension + slack)) (Fin lweDimension) R ↦
      matrix.rank < lweDimension) |
      ($ᵗ Matrix (Fin (lweDimension + slack)) (Fin lweDimension) R)] ≤
      pietrzakRankError R slack :=
  FormalProof4FHE.FiniteFieldRank.rankFailure_le lweDimension slack

/-- Once the fixed-query rank lemma is supplied with Pietrzak's explicit estimate, the complete
adaptive loss is `Q · 2 / |R|^(δ+1)`. -/
theorem adaptiveRankLossWithTape_le_pietrzak {R Tape : Type}
    [Field R] [DecidableEq R] [Fintype R] [SampleableType R]
    (tapeSampler : ProbComp Tape) (ambientDimension lweDimension slack queryCount : ℕ)
    (strategy : Tape → List Bool → Query R ambientDimension)
    (hFixed : FixedRankLossBound (R := R) (ambientDimension := ambientDimension)
      lweDimension (lweDimension + slack) (pietrzakRankError R slack)) :
    Pr[(fun fired : Bool ↦ fired = true) |
      adaptiveRankLossGameWithTape tapeSampler lweDimension (lweDimension + slack)
        queryCount strategy] ≤
      (queryCount : ℝ≥0∞) * pietrzakRankError R slack :=
  adaptiveRankLossWithTape_le tapeSampler lweDimension (lweDimension + slack)
    queryCount (pietrzakRankError R slack) strategy hFixed

/-! ## Security accounting -/

/-- A generic reduction inequality: if the real and uniform SLWE branches are simulated with
gaps `realGap` and `uniformGap`, their distinguishing advantage is at most the reduced LWE
advantage plus those gaps. -/
theorem advantage_le_reduction_add_gaps
    (slweReal slweUniform lweReal lweUniform : ProbComp Bool)
    (realGap uniformGap : ℝ)
    (hReal : |(Pr[= true | slweReal]).toReal - (Pr[= true | lweReal]).toReal| ≤ realGap)
    (hUniform : |(Pr[= true | lweUniform]).toReal -
      (Pr[= true | slweUniform]).toReal| ≤ uniformGap) :
    slweReal.boolDistAdvantage slweUniform ≤
      lweReal.boolDistAdvantage lweUniform + realGap + uniformGap := by
  unfold ProbComp.boolDistAdvantage
  let a := (Pr[= true | slweReal]).toReal
  let b := (Pr[= true | lweReal]).toReal
  let c := (Pr[= true | lweUniform]).toReal
  let d := (Pr[= true | slweUniform]).toReal
  calc
    |a - d| ≤ |a - b| + |b - d| := abs_sub_le a b d
    _ ≤ |a - b| + (|b - c| + |c - d|) := by
      gcongr
      exact abs_sub_le b c d
    _ = |a - b| + |b - c| + |c - d| := by ring
    _ ≤ |b - c| + realGap + uniformGap := by
      dsimp [a, b, c, d] at *
      linarith

/-- Correctness condition for an LWE-to-SLWE simulator: the sum of its two branch gaps is bounded
by the probability that its hidden matrix suffers rank loss. -/
def SimulationCorrect
    (slweReal slweUniform lweReal lweUniform rankLossGame : ProbComp Bool) : Prop :=
  |(Pr[= true | slweReal]).toReal - (Pr[= true | lweReal]).toReal| +
    |(Pr[= true | lweUniform]).toReal - (Pr[= true | slweUniform]).toReal| ≤
      (Pr[= true | rankLossGame]).toReal

/-- A correct simulator reduces adaptive SLWE advantage to its LWE advantage plus its rank-loss
probability. -/
theorem advantage_le_lwe_add_rankLoss
    (slweReal slweUniform lweReal lweUniform rankLossGame : ProbComp Bool)
    (hSimulation : SimulationCorrect slweReal slweUniform lweReal lweUniform rankLossGame) :
    slweReal.boolDistAdvantage slweUniform ≤
      lweReal.boolDistAdvantage lweUniform + (Pr[= true | rankLossGame]).toReal := by
  let realGap :=
    |(Pr[= true | slweReal]).toReal - (Pr[= true | lweReal]).toReal|
  let uniformGap :=
    |(Pr[= true | lweUniform]).toReal - (Pr[= true | slweUniform]).toReal|
  calc
    slweReal.boolDistAdvantage slweUniform ≤
        lweReal.boolDistAdvantage lweUniform + realGap + uniformGap :=
      advantage_le_reduction_add_gaps slweReal slweUniform lweReal lweUniform
        realGap uniformGap le_rfl le_rfl
    _ ≤ lweReal.boolDistAdvantage lweUniform + (Pr[= true | rankLossGame]).toReal := by
      unfold SimulationCorrect at hSimulation
      dsimp [realGap, uniformGap]
      linarith

/-- End-to-end security accounting after the fixed-query rank estimate and simulator correctness
have been discharged: adaptive SLWE advantage is at most LWE advantage plus `(Q * ε).toReal`. -/
theorem advantage_le_lwe_add_adaptiveRankLoss {R Tape : Type}
    [Field R] [DecidableEq R] [SampleableType R]
    {ambientDimension : ℕ}
    (slweReal slweUniform lweReal lweUniform : ProbComp Bool)
    (tapeSampler : ProbComp Tape) (lweDimension threshold queryCount : ℕ) (ε : ℝ≥0∞)
    (strategy : Tape → List Bool → Query R ambientDimension)
    (hε : ε ≠ ⊤)
    (hFixed : FixedRankLossBound (R := R) (ambientDimension := ambientDimension)
      lweDimension threshold ε)
    (hSimulation : SimulationCorrect slweReal slweUniform lweReal lweUniform
      (adaptiveRankLossGameWithTape tapeSampler lweDimension threshold queryCount strategy)) :
    slweReal.boolDistAdvantage slweUniform ≤
      lweReal.boolDistAdvantage lweUniform + ((queryCount : ℝ≥0∞) * ε).toReal := by
  calc
    slweReal.boolDistAdvantage slweUniform ≤
        lweReal.boolDistAdvantage lweUniform +
          (Pr[= true | adaptiveRankLossGameWithTape tapeSampler
            lweDimension threshold queryCount strategy]).toReal :=
      advantage_le_lwe_add_rankLoss slweReal slweUniform lweReal lweUniform _ hSimulation
    _ ≤ lweReal.boolDistAdvantage lweUniform + ((queryCount : ℝ≥0∞) * ε).toReal := by
      have hRank :
          Pr[= true | adaptiveRankLossGameWithTape tapeSampler
            lweDimension threshold queryCount strategy] ≤ (queryCount : ℝ≥0∞) * ε := by
        rw [← probEvent_eq_eq_probOutput]
        exact adaptiveRankLossWithTape_le tapeSampler lweDimension threshold queryCount ε
          strategy hFixed
      exact add_le_add le_rfl
        (ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hε)
          hRank)

end FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive
