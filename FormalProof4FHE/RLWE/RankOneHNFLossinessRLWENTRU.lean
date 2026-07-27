/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputSearch
import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.RLWE.RNSSplitSearchToDecisionCorrelated

/-!
# Rank-One HNF Lossiness from Ring-LWE and NTRU-Style Ratios

This module formalizes the finite algebraic and game-based content of
`sketch/rank_one_hnf_lossiness_rlwe_ntru.tex`.

The central exact fact is that the rank-one HNF transcript

`b₀ = X - S`, `d j = a j * X + E j`

is publicly equivalent to an independent uniform anchor together with the entropic Ring-LWE
view

`y j = d j - a j * b₀ = a j * S + E j`.

The module then gives an operational finite definition of conditional guessing probability and
proves the exact average-lossiness reduction: recovery with uniform coefficients is bounded by
the public-coefficient distinguishing advantage plus optimal recovery in the lossy branch.  The
bound permits arbitrary correlations between the secret, all terminal errors, and public side
information.

The Gaussian smoothing, singular-value tail, DSPR, Hermite-RLWE, and statistical wide-ratio
statements cited by the TeX note are external cryptographic or analytic results.  They are not
silently introduced as axioms here.  Instead, explicit certificate structures record their
numeric hypotheses and their precise finite-game conclusions.  Lean proves the masked-ratio
algebra, all game transformations and hybrid compositions, and the NTRU/DSPR, RLWE-only, and
coherent-RNS consequences of those certificates.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessRLWENTRU

noncomputable section

/-! ## Rank-one HNF and entropic Ring-LWE views -/

/-- Secret, arbitrarily correlated terminal errors, and arbitrary public leakage. -/
structure SourceState (R Row Leakage : Type) where
  secret : R
  error : Row → R
  leakage : Leakage

/-- Public rank-one HNF transcript `(Lambda,b0,{(a_j,d_j)}_j)`. -/
structure HNFView (R Row Leakage : Type) where
  leakage : Leakage
  anchor : R
  coefficient : Row → R
  body : Row → R

/-- Public entropic Ring-LWE transcript `(Lambda,{(a_j,y_j)}_j)`. -/
structure EntropicRLWEView (R Row Leakage : Type) where
  leakage : Leakage
  coefficient : Row → R
  body : Row → R

@[ext]
theorem HNFView.ext
    {R Row Leakage : Type} {left right : HNFView R Row Leakage}
    (hLeakage : left.leakage = right.leakage)
    (hAnchor : left.anchor = right.anchor)
    (hCoefficient : left.coefficient = right.coefficient)
    (hBody : left.body = right.body) :
    left = right := by
  cases left
  cases right
  simp_all

@[ext]
theorem EntropicRLWEView.ext
    {R Row Leakage : Type} {left right : EntropicRLWEView R Row Leakage}
    (hLeakage : left.leakage = right.leakage)
    (hCoefficient : left.coefficient = right.coefficient)
    (hBody : left.body = right.body) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Assemble the original HNF transcript from its auxiliary secret. -/
def realHNFView {R Row Leakage : Type} [CommRing R]
    (auxiliarySecret : R) (state : SourceState R Row Leakage)
    (coefficient : Row → R) : HNFView R Row Leakage where
  leakage := state.leakage
  anchor := auxiliarySecret - state.secret
  coefficient := coefficient
  body := fun row ↦ coefficient row * auxiliarySecret + state.error row

/-- Assemble the entropic Ring-LWE view for fixed source state and coefficients. -/
def entropicRLWEView {R Row Leakage : Type} [CommRing R]
    (state : SourceState R Row Leakage) (coefficient : Row → R) :
    EntropicRLWEView R Row Leakage where
  leakage := state.leakage
  coefficient := coefficient
  body := fun row ↦ coefficient row * state.secret + state.error row

/-- Eliminate the HNF anchor, retaining it as an independent public component. -/
def eliminateHNF {R Row Leakage : Type} [Ring R]
    (view : HNFView R Row Leakage) : R × EntropicRLWEView R Row Leakage :=
  (view.anchor,
    { leakage := view.leakage
      coefficient := view.coefficient
      body := fun row ↦ view.body row - view.coefficient row * view.anchor })

/-- Reassemble an HNF transcript from an anchor and an entropic Ring-LWE transcript. -/
def assembleHNF {R Row Leakage : Type} [Ring R]
    (input : R × EntropicRLWEView R Row Leakage) : HNFView R Row Leakage where
  leakage := input.2.leakage
  anchor := input.1
  coefficient := input.2.coefficient
  body := fun row ↦ input.2.body row + input.2.coefficient row * input.1

@[simp]
theorem assembleHNF_eliminateHNF
    {R Row Leakage : Type} [Ring R] (view : HNFView R Row Leakage) :
    assembleHNF (eliminateHNF view) = view := by
  apply HNFView.ext <;> try rfl
  funext row
  simp [assembleHNF, eliminateHNF]

@[simp]
theorem eliminateHNF_assembleHNF
    {R Row Leakage : Type} [Ring R]
    (input : R × EntropicRLWEView R Row Leakage) :
    eliminateHNF (assembleHNF input) = input := by
  apply Prod.ext
  · rfl
  · apply EntropicRLWEView.ext <;> try rfl
    funext row
    simp [assembleHNF, eliminateHNF]

/-- HNF elimination is an explicit bijection, rather than merely a one-way reduction. -/
theorem eliminateHNF_bijective
    {R Row Leakage : Type} [Ring R] :
    Function.Bijective
      (eliminateHNF : HNFView R Row Leakage → R × EntropicRLWEView R Row Leakage) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨assembleHNF, assembleHNF_eliminateHNF, eliminateHNF_assembleHNF⟩

/-- Exact elimination identity `d_j-a_j b_0=a_j S+E_j`. -/
theorem eliminateHNF_realHNFView
    {R Row Leakage : Type} [CommRing R]
    (auxiliarySecret : R) (state : SourceState R Row Leakage)
    (coefficient : Row → R) :
    eliminateHNF (realHNFView auxiliarySecret state coefficient) =
      (auxiliarySecret - state.secret, entropicRLWEView state coefficient) := by
  apply Prod.ext
  · rfl
  · apply EntropicRLWEView.ext <;> try rfl
    funext row
    simp [eliminateHNF, realHNFView, entropicRLWEView]
    ring

/-- Assemble the same real transcript using its already-eliminated, uniformly distributed
anchor.  The corresponding auxiliary secret is `anchor + S`. -/
def anchoredHNFView {R Row Leakage : Type} [CommRing R]
    (anchor : R) (state : SourceState R Row Leakage)
    (coefficient : Row → R) : HNFView R Row Leakage :=
  assembleHNF (anchor, entropicRLWEView state coefficient)

theorem anchoredHNFView_eq_realHNFView
    {R Row Leakage : Type} [CommRing R]
    (anchor : R) (state : SourceState R Row Leakage)
    (coefficient : Row → R) :
    anchoredHNFView anchor state coefficient =
      realHNFView (anchor + state.secret) state coefficient := by
  apply HNFView.ext <;> try rfl
  · simp [anchoredHNFView, assembleHNF, realHNFView]
  · funext row
    simp [anchoredHNFView, assembleHNF, entropicRLWEView, realHNFView]
    ring

/-- Recover the HNF auxiliary secret from its anchor and the entropic secret. -/
def recoverAuxiliary {R : Type} [Add R] (anchor secret : R) : R :=
  anchor + secret

/-- Recover the entropic secret from the anchor and the auxiliary secret. -/
def recoverEntropic {R : Type} [AddGroup R] (anchor auxiliarySecret : R) : R :=
  auxiliarySecret - anchor

@[simp]
theorem recoverEntropic_recoverAuxiliary
    {R : Type} [AddCommGroup R] (anchor secret : R) :
    recoverEntropic anchor (recoverAuxiliary anchor secret) = secret := by
  simp [recoverEntropic, recoverAuxiliary]

@[simp]
theorem recoverAuxiliary_recoverEntropic
    {R : Type} [AddCommGroup R] (anchor auxiliarySecret : R) :
    recoverAuxiliary anchor (recoverEntropic anchor auxiliarySecret) = auxiliarySecret := by
  simp [recoverEntropic, recoverAuxiliary]

/-! ## Exact distributional independence of the HNF anchor -/

/-- Original-source sampler with a caller-supplied coefficient distribution.  Sampling the
complete state first makes all secret/error/leakage correlations explicit. -/
def realHNFSampler
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (coefficientSampler : ProbComp (Row → R)) :
    ProbComp (HNFView R Row Leakage) := do
  let state ← stateSampler
  let auxiliarySecret ← $ᵗ R
  let coefficient ← coefficientSampler
  return realHNFView auxiliarySecret state coefficient

/-- Canonical equivalent sampler: sample the public anchor independently and reconstruct the
auxiliary secret as `anchor+S`. -/
def anchoredHNFSampler
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (coefficientSampler : ProbComp (Row → R)) :
    ProbComp (HNFView R Row Leakage) := do
  let state ← stateSampler
  let anchor ← $ᵗ R
  let coefficient ← coefficientSampler
  return anchoredHNFView anchor state coefficient

/-- The original and independently anchored source samplers are exactly equal in distribution.
This is the finite probability statement behind independence of `b₀`. -/
theorem realHNFSampler_evalDist_eq_anchoredHNFSampler
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (coefficientSampler : ProbComp (Row → R)) :
    evalDist (realHNFSampler stateSampler coefficientSampler) =
      evalDist (anchoredHNFSampler stateSampler coefficientSampler) := by
  refine evalDist_bind_congr' stateSampler fun state ↦ ?_
  calc
    evalDist (do
        let auxiliarySecret ← $ᵗ R
        let coefficient ← coefficientSampler
        return realHNFView auxiliarySecret state coefficient) =
      evalDist (do
        let coefficient ← coefficientSampler
        let auxiliarySecret ← $ᵗ R
        return realHNFView auxiliarySecret state coefficient) :=
      evalDist_bind_bind_swap ($ᵗ R) coefficientSampler
        (fun auxiliarySecret coefficient ↦
          pure (realHNFView auxiliarySecret state coefficient))
    _ = evalDist (do
        let coefficient ← coefficientSampler
        let anchor ← $ᵗ R
        return anchoredHNFView anchor state coefficient) := by
      refine evalDist_bind_congr' coefficientSampler fun coefficient ↦ ?_
      let translation : R ≃ R :=
        { toFun := fun auxiliarySecret ↦ auxiliarySecret - state.secret
          invFun := fun anchor ↦ anchor + state.secret
          left_inv := by intro auxiliarySecret; simp
          right_inv := by intro anchor; simp }
      have hUniform := evalDist_map_bijective_uniform_cross
        (α := R) (β := R)
        (fun auxiliarySecret : R ↦ auxiliarySecret - state.secret) translation.bijective
      have hMapped := evalDist_map_eq_of_evalDist_eq hUniform
        (fun anchor ↦ anchoredHNFView anchor state coefficient)
      rw [Functor.map_map] at hMapped
      simpa only [Functor.map, bind_pure_comp, Function.comp_apply,
        anchoredHNFView_eq_realHNFView, sub_add_cancel] using hMapped
    _ = evalDist (do
        let anchor ← $ᵗ R
        let coefficient ← coefficientSampler
        return anchoredHNFView anchor state coefficient) := by
      exact evalDist_bind_bind_swap coefficientSampler ($ᵗ R)
        (fun coefficient anchor ↦
          pure (anchoredHNFView anchor state coefficient))

/-! ## Operational conditional guessing probability -/

/-- A randomized estimator sees the complete public side information and returns a secret. -/
abbrev Estimator (Secret Side : Type) := Side → ProbComp Secret

/-- Exact success game for a joint `(secret,side)` distribution. -/
def guessingGame {Secret Side : Type} [DecidableEq Secret]
    (joint : ProbComp (Secret × Side)) (estimator : Estimator Secret Side) : ProbComp Bool := do
  let value ← joint
  let guess ← estimator value.2
  return decide (guess = value.1)

/-- Exact success probability of one estimator. -/
noncomputable def guessingSuccess {Secret Side : Type} [DecidableEq Secret]
    (joint : ProbComp (Secret × Side)) (estimator : Estimator Secret Side) : ENNReal :=
  Pr[= true | guessingGame joint estimator]

/-- Operational finite conditional guessing probability: the supremum over every randomized
estimator that receives the side information.  On finite total distributions this is the usual
`sum_side max_secret Pr[secret,side]` definition.  The operational form avoids choosing a
particular maximizing estimator and is the exact interface needed by reductions. -/
noncomputable def conditionalGuessingProbability
    {Secret Side : Type} [DecidableEq Secret]
    (joint : ProbComp (Secret × Side)) : ENNReal :=
  ⨆ estimator : Estimator Secret Side, guessingSuccess joint estimator

theorem guessingSuccess_le_conditionalGuessingProbability
    {Secret Side : Type} [DecidableEq Secret]
    (joint : ProbComp (Secret × Side)) (estimator : Estimator Secret Side) :
    guessingSuccess joint estimator ≤ conditionalGuessingProbability joint := by
  exact le_iSup (fun candidate : Estimator Secret Side ↦ guessingSuccess joint candidate) estimator

theorem conditionalGuessingProbability_le_one
    {Secret Side : Type} [DecidableEq Secret]
    (joint : ProbComp (Secret × Side)) :
    conditionalGuessingProbability joint ≤ 1 := by
  apply iSup_le
  intro estimator
  exact probOutput_le_one

/-- Average conditional min-entropy in bits, defined from operational guessing probability. -/
noncomputable def averageConditionalMinEntropy
    {Secret Side : Type} [DecidableEq Secret]
    (joint : ProbComp (Secret × Side)) : ℝ :=
  -Real.logb 2 (conditionalGuessingProbability joint).toReal

/-! ## Exact average-lossiness reduction -/

/-- A public solver for the rank-one HNF search problem. -/
abbrev HNFSolver (R Row Leakage : Type) :=
  HNFView R Row Leakage → ProbComp R

/-- Run a solver on the canonical independently anchored source.  Coefficients are sampled first
so the same computation is directly a coefficient distinguisher. -/
def anchoredHNFSearchGame
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (coefficientSampler : ProbComp (Row → R))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) : ProbComp Bool := do
  let coefficient ← coefficientSampler
  let state ← stateSampler
  let anchor ← $ᵗ R
  let recovered ← solver (anchoredHNFView anchor state coefficient)
  return decide (recovered = recoverAuxiliary anchor state.secret)

/-- Exact auxiliary-secret recovery probability for a coefficient distribution. -/
noncomputable def anchoredHNFSearchSuccess
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (coefficientSampler : ProbComp (Row → R))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) : ENNReal :=
  Pr[= true | anchoredHNFSearchGame coefficientSampler stateSampler solver]

/-- The original source game samples `X` and checks recovery of that value. -/
def realHNFSearchGame
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (coefficientSampler : ProbComp (Row → R))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) : ProbComp Bool := do
  let coefficient ← coefficientSampler
  let state ← stateSampler
  let auxiliarySecret ← $ᵗ R
  let recovered ← solver (realHNFView auxiliarySecret state coefficient)
  return decide (recovered = auxiliarySecret)

/-- Exact-search games using a uniform auxiliary secret or an independent anchor have identical
output distributions, including the solver's randomized behavior. -/
theorem realHNFSearchGame_evalDist_eq_anchoredHNFSearchGame
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (coefficientSampler : ProbComp (Row → R))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    evalDist (realHNFSearchGame coefficientSampler stateSampler solver) =
      evalDist (anchoredHNFSearchGame coefficientSampler stateSampler solver) := by
  refine evalDist_bind_congr' coefficientSampler fun coefficient ↦ ?_
  refine evalDist_bind_congr' stateSampler fun state ↦ ?_
  let realInput : R → HNFView R Row Leakage × R := fun auxiliarySecret ↦
    (realHNFView auxiliarySecret state coefficient, auxiliarySecret)
  let anchoredInput : R → HNFView R Row Leakage × R := fun anchor ↦
    (anchoredHNFView anchor state coefficient, recoverAuxiliary anchor state.secret)
  let finish : HNFView R Row Leakage × R → ProbComp Bool := fun input ↦ do
    let recovered ← solver input.1
    return decide (recovered = input.2)
  let translation : R ≃ R :=
    { toFun := fun auxiliarySecret ↦ auxiliarySecret - state.secret
      invFun := fun anchor ↦ anchor + state.secret
      left_inv := by intro auxiliarySecret; simp
      right_inv := by intro anchor; simp }
  have hUniform := evalDist_map_bijective_uniform_cross
    (α := R) (β := R)
    (fun auxiliarySecret : R ↦ auxiliarySecret - state.secret) translation.bijective
  have hInput := evalDist_map_eq_of_evalDist_eq hUniform anchoredInput
  rw [Functor.map_map] at hInput
  have hInput' :
      evalDist (realInput <$> ($ᵗ R)) = evalDist (anchoredInput <$> ($ᵗ R)) := by
    simpa only [realInput, anchoredInput, Function.comp_apply,
      anchoredHNFView_eq_realHNFView, recoverAuxiliary, sub_add_cancel] using hInput
  change
    evalDist (($ᵗ R) >>= fun auxiliarySecret ↦ finish (realInput auxiliarySecret)) =
      evalDist (($ᵗ R) >>= fun anchor ↦ finish (anchoredInput anchor))
  calc
    evalDist (($ᵗ R) >>= fun auxiliarySecret ↦ finish (realInput auxiliarySecret)) =
      evalDist ((realInput <$> ($ᵗ R)) >>= finish) := by
        simp [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
    _ = evalDist ((anchoredInput <$> ($ᵗ R)) >>= finish) := by
      rw [evalDist_bind, hInput', ← evalDist_bind]
    _ = evalDist (($ᵗ R) >>= fun anchor ↦ finish (anchoredInput anchor)) := by
      simp [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]

theorem realHNFSearchSuccess_eq_anchoredHNFSearchSuccess
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (coefficientSampler : ProbComp (Row → R))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    Pr[= true | realHNFSearchGame coefficientSampler stateSampler solver] =
      anchoredHNFSearchSuccess coefficientSampler stateSampler solver := by
  unfold anchoredHNFSearchSuccess
  exact probOutput_congr rfl
    (realHNFSearchGame_evalDist_eq_anchoredHNFSearchGame
      coefficientSampler stateSampler solver)

/-- A coefficient family may retain a hidden descriptor.  Only its second projection is public. -/
abbrev CoefficientFamily (Descriptor R Row : Type) :=
  ProbComp (Descriptor × (Row → R))

def publicCoefficientSampler
    {Descriptor R Row : Type} (family : CoefficientFamily Descriptor R Row) :
    ProbComp (Row → R) :=
  Prod.snd <$> family

/-- Complete side information revealed in the definition of conditional lossiness. -/
structure LossySide (R Row Leakage Descriptor : Type) where
  leakage : Leakage
  descriptor : Descriptor
  coefficient : Row → R
  sample : Row → R

/-- Convert lossy side information back to its entropic Ring-LWE public view. -/
def LossySide.toEntropicRLWEView
    {R Row Leakage Descriptor : Type}
    (side : LossySide R Row Leakage Descriptor) : EntropicRLWEView R Row Leakage where
  leakage := side.leakage
  coefficient := side.coefficient
  body := side.sample

/-- The joint `(S,Lambda,tau,a,aS+E)` law used by average conditional min-entropy. -/
def lossyObservationSampler
    {R Row Leakage Descriptor : Type} [CommRing R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage)) :
    ProbComp (R × LossySide R Row Leakage Descriptor) := do
  let descriptorAndCoefficient ← family
  let state ← stateSampler
  return (state.secret,
    { leakage := state.leakage
      descriptor := descriptorAndCoefficient.1
      coefficient := descriptorAndCoefficient.2
      sample := fun row ↦
        descriptorAndCoefficient.2 row * state.secret + state.error row })

/-- The exact average-lossiness quantity for a coefficient family and source. -/
noncomputable def averageLossiness
    {R Row Leakage Descriptor : Type} [CommRing R] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage)) : ENNReal :=
  conditionalGuessingProbability (lossyObservationSampler family stateSampler)

/-- Reveal the descriptor and use an HNF solver as an entropic-secret estimator.  The estimator
samples the independent anchor itself and converts `X̂` to `Ŝ=X̂-b₀`. -/
def estimatorOfHNFSolver
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R]
    (solver : HNFSolver R Row Leakage) :
    Estimator R (LossySide R Row Leakage Descriptor) :=
  fun side ↦ do
    let anchor ← $ᵗ R
    let recovered ← solver (assembleHNF (anchor, side.toEntropicRLWEView))
    return recoverEntropic anchor recovered

@[simp]
theorem recoverEntropic_eq_iff
    {R : Type} [AddCommGroup R] (anchor recovered secret : R) :
    recoverEntropic anchor recovered = secret ↔
      recovered = recoverAuxiliary anchor secret := by
  simpa [recoverEntropic, recoverAuxiliary, add_comm] using
    (sub_eq_iff_eq_add : recovered - anchor = secret ↔ recovered = secret + anchor)

/-- A recovery solver, closed over the source distribution, is a Boolean coefficient
distinguisher. -/
def coefficientRecoveryDistinguisher
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    (Row → R) → ProbComp Bool :=
  fun coefficient ↦ do
    let state ← stateSampler
    let anchor ← $ᵗ R
    let recovered ← solver (anchoredHNFView anchor state coefficient)
    return decide (recovered = recoverAuxiliary anchor state.secret)

/-- Public-coefficient distinguishing advantage induced by a selected HNF solver. -/
noncomputable def coefficientRecoveryAdvantage
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) : ℝ :=
  ((($ᵗ (Row → R)) >>= coefficientRecoveryDistinguisher stateSampler solver).boolDistAdvantage
    (publicCoefficientSampler family >>=
      coefficientRecoveryDistinguisher stateSampler solver))

/-- Sampling the public projection of the lossy family and running the recovery distinguisher is
exactly an estimator in the lossy observation experiment with the descriptor additionally
revealed. -/
theorem lossyCoefficientRecovery_evalDist_eq_guessingGame
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    evalDist (publicCoefficientSampler family >>=
        coefficientRecoveryDistinguisher stateSampler solver) =
      evalDist (guessingGame (lossyObservationSampler family stateSampler)
        (estimatorOfHNFSolver solver)) := by
  simp [publicCoefficientSampler, coefficientRecoveryDistinguisher,
    lossyObservationSampler, estimatorOfHNFSolver, guessingGame,
    LossySide.toEntropicRLWEView, anchoredHNFView, entropicRLWEView,
    map_eq_bind_pure_comp, bind_assoc,
    recoverEntropic_eq_iff]

/-- Lossy-branch recovery is bounded by operational conditional guessing probability. -/
theorem lossyCoefficientRecovery_le_averageLossiness
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    Pr[= true | publicCoefficientSampler family >>=
        coefficientRecoveryDistinguisher stateSampler solver] ≤
      averageLossiness family stateSampler := by
  rw [show
      Pr[= true | publicCoefficientSampler family >>=
          coefficientRecoveryDistinguisher stateSampler solver] =
        guessingSuccess (lossyObservationSampler family stateSampler)
          (estimatorOfHNFSolver solver) by
    unfold guessingSuccess
    exact probOutput_congr rfl
      (lossyCoefficientRecovery_evalDist_eq_guessingGame family stateSampler solver)]
  exact guessingSuccess_le_conditionalGuessingProbability _ _

/-- Exact rank-one average-lossiness reduction.  No independence is imposed inside
`SourceState`: terminal errors and leakage may be arbitrarily correlated with the secret. -/
theorem uniformHNFRecovery_le_coefficientAdvantage_add_averageLossiness
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    anchoredHNFSearchSuccess ($ᵗ (Row → R)) stateSampler solver ≤
      ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler solver) +
        averageLossiness family stateSampler := by
  have h := ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
    (($ᵗ (Row → R)) >>= coefficientRecoveryDistinguisher stateSampler solver)
    (publicCoefficientSampler family >>=
      coefficientRecoveryDistinguisher stateSampler solver)
  change
    Pr[= true | ($ᵗ (Row → R)) >>=
        coefficientRecoveryDistinguisher stateSampler solver] ≤
      ENNReal.ofReal
          ((($ᵗ (Row → R)) >>=
              coefficientRecoveryDistinguisher stateSampler solver).boolDistAdvantage
            (publicCoefficientSampler family >>=
              coefficientRecoveryDistinguisher stateSampler solver)) +
        averageLossiness family stateSampler
  calc
    _ ≤ Pr[= true | publicCoefficientSampler family >>=
          coefficientRecoveryDistinguisher stateSampler solver] +
        ENNReal.ofReal
          ((($ᵗ (Row → R)) >>=
              coefficientRecoveryDistinguisher stateSampler solver).boolDistAdvantage
            (publicCoefficientSampler family >>=
              coefficientRecoveryDistinguisher stateSampler solver)) := h
    _ ≤ averageLossiness family stateSampler +
        ENNReal.ofReal
          ((($ᵗ (Row → R)) >>=
              coefficientRecoveryDistinguisher stateSampler solver).boolDistAdvantage
            (publicCoefficientSampler family >>=
              coefficientRecoveryDistinguisher stateSampler solver)) :=
      add_le_add
        (lossyCoefficientRecovery_le_averageLossiness family stateSampler solver) le_rfl
    _ = _ := add_comm _ _

/-- Original-`X` presentation of the same reduction. -/
theorem realUniformHNFRecovery_le_coefficientAdvantage_add_averageLossiness
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    Pr[= true | realHNFSearchGame ($ᵗ (Row → R)) stateSampler solver] ≤
      ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler solver) +
        averageLossiness family stateSampler := by
  rw [realHNFSearchSuccess_eq_anchoredHNFSearchSuccess]
  exact uniformHNFRecovery_le_coefficientAdvantage_add_averageLossiness
    family stateSampler solver

/-! ## Hardness interfaces and sometimes lossiness -/

/-- A coefficient family is pseudorandom for a selected class of Boolean distinguishers. -/
def CoefficientPseudorandomAgainst
    {R Row Descriptor : Type} [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)]
    (family : CoefficientFamily Descriptor R Row)
    (allowed : ((Row → R) → ProbComp Bool) → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    ((($ᵗ (Row → R)) >>= distinguisher).boolDistAdvantage
      (publicCoefficientSampler family >>= distinguisher)) ≤ bound

/-- Search hardness for the original rank-one HNF presentation. -/
def HNFHardAgainst
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (allowed : HNFSolver R Row Leakage → Prop) (bound : ENNReal) : Prop :=
  ∀ solver, allowed solver →
    Pr[= true | realHNFSearchGame ($ᵗ (Row → R)) stateSampler solver] ≤ bound

/-- Uniform coefficient pseudorandomness and an average guessing bound imply ordinary rank-one
HNF search hardness with their exact additive loss. -/
theorem hnfHardAgainst_of_coefficientPseudorandom_and_averageLossiness
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (allowedSolver : HNFSolver R Row Leakage → Prop)
    (allowedDistinguisher : ((Row → R) → ProbComp Bool) → Prop)
    (coefficientBound : ℝ) (lossinessBound : ENNReal)
    (hCoefficient : CoefficientPseudorandomAgainst family allowedDistinguisher coefficientBound)
    (hClosure : ∀ solver, allowedSolver solver →
      allowedDistinguisher (coefficientRecoveryDistinguisher stateSampler solver))
    (hLossiness : averageLossiness family stateSampler ≤ lossinessBound) :
    HNFHardAgainst stateSampler allowedSolver
      (ENNReal.ofReal coefficientBound + lossinessBound) := by
  intro solver hSolver
  calc
    Pr[= true | realHNFSearchGame ($ᵗ (Row → R)) stateSampler solver] ≤
        ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler solver) +
          averageLossiness family stateSampler :=
      realUniformHNFRecovery_le_coefficientAdvantage_add_averageLossiness
        family stateSampler solver
    _ ≤ ENNReal.ofReal coefficientBound + lossinessBound := by
      apply add_le_add
      · exact ENNReal.ofReal_le_ofReal
          (hCoefficient _ (hClosure solver hSolver))
      · exact hLossiness

/-- Finite operational form of an `(epsilon,kappa,delta)` sometimes-lossy statement.  The field
`lossiness_le` is exactly the Gaussian-decomposition/smooth-min-entropy conclusion supplied by
Brakerski--Döttling; all bad-event, smoothing, and good-event guessing masses remain visible. -/
structure SometimesLossyCertificate
    {R Row Leakage Descriptor : Type} [CommRing R] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage)) where
  smoothingError : ENNReal
  goodProbability : ENNReal
  goodGuessBound : ENNReal
  smoothingError_le_one : smoothingError ≤ 1
  goodProbability_le_one : goodProbability ≤ 1
  goodGuessBound_le_one : goodGuessBound ≤ 1
  lossiness_le :
    averageLossiness family stateSampler ≤
      smoothingError + (1 - goodProbability) + goodProbability * goodGuessBound

/-- The explicit total one-shot loss attached to a sometimes-lossy certificate. -/
def SometimesLossyCertificate.bound
    {R Row Leakage Descriptor : Type} [CommRing R] [DecidableEq R]
    {family : CoefficientFamily Descriptor R Row}
    {stateSampler : ProbComp (SourceState R Row Leakage)}
    (certificate : SometimesLossyCertificate family stateSampler) : ENNReal :=
  certificate.smoothingError + (1 - certificate.goodProbability) +
    certificate.goodProbability * certificate.goodGuessBound

theorem SometimesLossyCertificate.averageLossiness_le_bound
    {R Row Leakage Descriptor : Type} [CommRing R] [DecidableEq R]
    {family : CoefficientFamily Descriptor R Row}
    {stateSampler : ProbComp (SourceState R Row Leakage)}
    (certificate : SometimesLossyCertificate family stateSampler) :
    averageLossiness family stateSampler ≤ certificate.bound :=
  certificate.lossiness_le

/-- Sometimes lossiness gives the exact mild-HNF bound before any sample rerandomization or
asymptotic amplification is invoked. -/
theorem realUniformHNFRecovery_le_coefficientAdvantage_add_sometimesLossy
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    {family : CoefficientFamily Descriptor R Row}
    {stateSampler : ProbComp (SourceState R Row Leakage)}
    (certificate : SometimesLossyCertificate family stateSampler)
    (solver : HNFSolver R Row Leakage) :
    Pr[= true | realHNFSearchGame ($ᵗ (Row → R)) stateSampler solver] ≤
      ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler solver) +
        certificate.bound := by
  exact (realUniformHNFRecovery_le_coefficientAdvantage_add_averageLossiness
    family stateSampler solver).trans
      (add_le_add le_rfl certificate.averageLossiness_le_bound)

/-- A proof-carrying statistical rerandomization/amplification interface.  The TeX note imports
this step from the usual subset-sum rerandomization theorem; the interface prevents that imported
sample and entropy condition from being hidden in the rank-one algebra. -/
structure RerandomizationCertificate
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (sourceAllowed targetAllowed : HNFSolver R Row Leakage → Prop)
    (sourceBound targetBound : ENNReal) where
  overhead : ENNReal
  transform : HNFSolver R Row Leakage → HNFSolver R Row Leakage
  allowed : ∀ solver, targetAllowed solver → sourceAllowed (transform solver)
  success_le : ∀ solver, targetAllowed solver →
    Pr[= true | realHNFSearchGame ($ᵗ (Row → R)) stateSampler solver] ≤
      Pr[= true |
        realHNFSearchGame ($ᵗ (Row → R)) stateSampler (transform solver)] + overhead
  closes : sourceBound + overhead ≤ targetBound

/-- Apply a checked rerandomization reduction to a mild source-hardness theorem. -/
theorem hnfHardAgainst_of_rerandomization
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (sourceAllowed targetAllowed : HNFSolver R Row Leakage → Prop)
    (sourceBound targetBound : ENNReal)
    (hSource : HNFHardAgainst stateSampler sourceAllowed sourceBound)
    (certificate : RerandomizationCertificate stateSampler sourceAllowed targetAllowed
      sourceBound targetBound) :
    HNFHardAgainst stateSampler targetAllowed targetBound := by
  intro solver hSolver
  exact (certificate.success_le solver hSolver).trans
    ((add_le_add (hSource _ (certificate.allowed solver hSolver)) le_rfl).trans
      certificate.closes)

/-! ## Small polynomial ratios -/

/-- Algebraic witness for coefficients `a_j = z₀⁻¹ z_j`.  Analytic norm information about
the same witness belongs in `SmallRatioGaussianCertificate` below. -/
structure SmallRatioWitness (R Row : Type) [CommRing R] where
  denominator : R
  inverse : R
  numerator : Row → R
  inverse_mul_denominator : inverse * denominator = 1

/-- Public coefficients associated with a small-ratio witness. -/
def SmallRatioWitness.coefficient
    {R Row : Type} [CommRing R] (witness : SmallRatioWitness R Row) : Row → R :=
  fun row ↦ witness.inverse * witness.numerator row

/-- A hidden-witness small-ratio coefficient family. -/
def smallRatioFamily
    {R Row : Type} [CommRing R]
    (witnessSampler : ProbComp (SmallRatioWitness R Row)) :
    CoefficientFamily (SmallRatioWitness R Row) R Row :=
  show ProbComp (SmallRatioWitness R Row × (Row → R)) from
    witnessSampler >>= fun witness ↦
      pure (witness, SmallRatioWitness.coefficient witness)

/-- Masked numerator `z_j=g*u_j+f*v_j`. -/
def maskedNumerator {R : Type} [CommRing R] (f g u v : R) : R :=
  g * u + f * v

/-- Exact Brakerski--Döttling masked-ratio identity
`f⁻¹(gu+fv)=(f⁻¹g)u+v`. -/
theorem inverse_mul_maskedNumerator
    {R : Type} [CommRing R] (f g inverse u v : R)
    (hInverse : inverse * f = 1) :
    inverse * maskedNumerator f g u v = (inverse * g) * u + v := by
  unfold maskedNumerator
  rw [mul_add]
  exact congrArg₂ (fun left right ↦ left + right)
    (mul_assoc inverse g u).symm
    ((mul_assoc inverse f v).symm.trans (by rw [hInverse, one_mul]))

/-- Build the whole vector of masked small-ratio numerators. -/
def maskedSmallRatioWitness
    {R Row : Type} [CommRing R]
    (f g inverse : R) (first second : Row → R)
    (hInverse : inverse * f = 1) : SmallRatioWitness R Row where
  denominator := f
  inverse := inverse
  numerator := fun row ↦ maskedNumerator f g (first row) (second row)
  inverse_mul_denominator := hInverse

/-- Public Hermite-RLWE-masked coefficient vector `r*u_j+v_j`. -/
def maskedRatioVector
    {R Row : Type} [CommRing R]
    (ratio : R) (masks : Row → R × R) : Row → R :=
  fun row ↦ ratio * (masks row).1 + (masks row).2

/-- The coefficients of the explicit small-ratio witness equal the masked-ratio vector. -/
theorem maskedSmallRatioWitness_coefficient
    {R Row : Type} [CommRing R]
    (f g inverse : R) (first second : Row → R)
    (hInverse : inverse * f = 1) :
    (maskedSmallRatioWitness f g inverse first second hInverse).coefficient =
      maskedRatioVector (inverse * g) (fun row ↦ (first row, second row)) := by
  funext row
  exact inverse_mul_maskedNumerator f g inverse (first row) (second row) hInverse

/-- Sample masked public coefficients from a ratio and independent Hermite masks. -/
def maskedRatioPublicSampler
    {R Row : Type} [CommRing R]
    (ratioSampler : ProbComp R) (maskSampler : ProbComp (Row → R × R)) :
    ProbComp (Row → R) := do
  let ratio ← ratioSampler
  let masks ← maskSampler
  return maskedRatioVector ratio masks

/-- Preserve a hidden ratio descriptor for the later Gaussian lossiness analysis. -/
def maskedRatioFamily
    {R Row RatioDescriptor : Type} [CommRing R]
    (ratioFamily : ProbComp (RatioDescriptor × R))
    (maskSampler : ProbComp (Row → R × R)) :
    CoefficientFamily (RatioDescriptor × (Row → R × R)) R Row :=
  show ProbComp ((RatioDescriptor × (Row → R × R)) × (Row → R)) from
    ratioFamily >>= fun descriptorAndRatio ↦
      maskSampler >>= fun masks ↦
        pure ((descriptorAndRatio.1, masks),
          maskedRatioVector descriptorAndRatio.2 masks)

theorem publicCoefficientSampler_maskedRatioFamily_evalDist
    {R Row RatioDescriptor : Type} [CommRing R]
    (ratioFamily : ProbComp (RatioDescriptor × R))
    (maskSampler : ProbComp (Row → R × R)) :
    evalDist (publicCoefficientSampler (maskedRatioFamily ratioFamily maskSampler)) =
      evalDist (maskedRatioPublicSampler (Prod.snd <$> ratioFamily) maskSampler) := by
  simp [publicCoefficientSampler, maskedRatioFamily, maskedRatioPublicSampler,
    map_eq_bind_pure_comp, bind_assoc]

/-- Distinguisher induced on the hidden common ratio. -/
def maskedRatioReduction
    {R Row : Type} [CommRing R]
    (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool) : R → ProbComp Bool :=
  fun ratio ↦ do
    let masks ← maskSampler
    distinguisher (maskedRatioVector ratio masks)

/-- DSPR (or statistical ratio) replacement loss after applying the Hermite masks. -/
noncomputable def ratioReplacementAdvantage
    {R Row : Type} [CommRing R] [Fintype R] [SampleableType R]
    (ratioSampler referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool) : ℝ :=
  (ratioSampler >>= maskedRatioReduction maskSampler distinguisher).boolDistAdvantage
    (referenceRatioSampler >>= maskedRatioReduction maskSampler distinguisher)

/-- Hermite Ring-LWE hybrid loss once the common ratio has been made uniform. -/
noncomputable def hermiteMaskedAdvantage
    {R Row : Type} [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)]
    (referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool) : ℝ :=
  (referenceRatioSampler >>= maskedRatioReduction maskSampler distinguisher).boolDistAdvantage
    (($ᵗ (Row → R)) >>= distinguisher)

/-- Complete public masked-coefficient advantage. -/
noncomputable def maskedCoefficientAdvantage
    {R Row : Type} [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)]
    (ratioSampler : ProbComp R) (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool) : ℝ :=
  (ratioSampler >>= maskedRatioReduction maskSampler distinguisher).boolDistAdvantage
    (($ᵗ (Row → R)) >>= distinguisher)

/-- Masked-ratio pseudorandomness is one ratio-replacement hop plus one Hermite-RLWE hop. -/
theorem maskedCoefficientAdvantage_le_ratio_add_hermite
    {R Row : Type} [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)]
    (ratioSampler referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool) :
    maskedCoefficientAdvantage ratioSampler maskSampler distinguisher ≤
      ratioReplacementAdvantage ratioSampler referenceRatioSampler maskSampler distinguisher +
        hermiteMaskedAdvantage referenceRatioSampler maskSampler distinguisher := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (ratioSampler >>= maskedRatioReduction maskSampler distinguisher)
    (referenceRatioSampler >>= maskedRatioReduction maskSampler distinguisher)
    (($ᵗ (Row → R)) >>= distinguisher)
  simpa [maskedCoefficientAdvantage, ratioReplacementAdvantage,
    hermiteMaskedAdvantage] using hTriangle

/-- The computational ratio-replacement term is bounded by statistical distance of the ratio
itself.  This is the data-processing step used by the RLWE-only wide-ratio version. -/
theorem ratioReplacementAdvantage_le_tvDist
    {R Row : Type} [CommRing R] [Fintype R] [SampleableType R]
    (ratioSampler referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool) :
    ratioReplacementAdvantage ratioSampler referenceRatioSampler maskSampler distinguisher ≤
      tvDist ratioSampler referenceRatioSampler := by
  unfold ratioReplacementAdvantage ProbComp.boolDistAdvantage
  exact (abs_probOutput_toReal_sub_le_tvDist _ _).trans
    (tvDist_bind_right_le (maskedRatioReduction maskSampler distinguisher)
      ratioSampler referenceRatioSampler)

/-- Public sampler of a descriptor-carrying ratio family. -/
def publicRatioSampler
    {R RatioDescriptor : Type} (ratioFamily : ProbComp (RatioDescriptor × R)) :
    ProbComp R :=
  Prod.snd <$> ratioFamily

/-- Running a distinguisher after materializing the masked vector is distributionally identical
to running the induced ratio distinguisher directly. -/
theorem maskedRatioPublicSampler_bind_evalDist
    {R Row : Type} [CommRing R]
    (ratioSampler : ProbComp R) (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool) :
    evalDist (maskedRatioPublicSampler ratioSampler maskSampler >>= distinguisher) =
      evalDist (ratioSampler >>= maskedRatioReduction maskSampler distinguisher) := by
  simp [maskedRatioPublicSampler, maskedRatioReduction, bind_assoc]

/-- The public projection of a descriptor-carrying masked family induces exactly the common-ratio
game.  The hidden descriptor and the masks remain available to the lossiness proof. -/
theorem publicMaskedRatioFamily_bind_evalDist
    {R Row RatioDescriptor : Type} [CommRing R]
    (ratioFamily : ProbComp (RatioDescriptor × R))
    (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool) :
    evalDist (publicCoefficientSampler (maskedRatioFamily ratioFamily maskSampler) >>=
        distinguisher) =
      evalDist (publicRatioSampler ratioFamily >>=
        maskedRatioReduction maskSampler distinguisher) := by
  calc
    evalDist (publicCoefficientSampler (maskedRatioFamily ratioFamily maskSampler) >>=
        distinguisher) =
        evalDist (maskedRatioPublicSampler (publicRatioSampler ratioFamily) maskSampler >>=
          distinguisher) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (by simpa [publicRatioSampler] using
          publicCoefficientSampler_maskedRatioFamily_evalDist ratioFamily maskSampler)
        distinguisher
    _ = _ := maskedRatioPublicSampler_bind_evalDist _ _ _

/-- The coefficient advantage used by the HNF reduction is exactly the masked-ratio hybrid
advantage.  Its arguments appear in the opposite order, which disappears under absolute value. -/
theorem uniformToMaskedRatioFamilyAdvantage_eq
    {R Row RatioDescriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    (ratioFamily : ProbComp (RatioDescriptor × R))
    (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool) :
    ((($ᵗ (Row → R)) >>= distinguisher).boolDistAdvantage
        (publicCoefficientSampler (maskedRatioFamily ratioFamily maskSampler) >>=
          distinguisher)) =
      maskedCoefficientAdvantage (publicRatioSampler ratioFamily) maskSampler distinguisher := by
  unfold maskedCoefficientAdvantage ProbComp.boolDistAdvantage
  rw [show
      Pr[= true |
        publicCoefficientSampler (maskedRatioFamily ratioFamily maskSampler) >>= distinguisher] =
        Pr[= true |
          publicRatioSampler ratioFamily >>= maskedRatioReduction maskSampler distinguisher] from
    probOutput_congr rfl
      (publicMaskedRatioFamily_bind_evalDist ratioFamily maskSampler distinguisher)]
  exact abs_sub_comm _ _

/-- A proof-carrying DSPR/statistical-ratio plus Hermite-RLWE hybrid.  Conditioning losses and
bad-event probabilities, when a concrete sampler needs them, are included in the two displayed
bounds rather than hidden in the finite games. -/
structure MaskedRatioHybridCertificate
    {R Row : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    (ratioSampler referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (allowed : ((Row → R) → ProbComp Bool) → Prop) where
  ratioBound : ℝ
  hermiteBound : ℝ
  ratioReplacement_le : ∀ distinguisher, allowed distinguisher →
    ratioReplacementAdvantage ratioSampler referenceRatioSampler maskSampler distinguisher ≤
      ratioBound
  hermiteReplacement_le : ∀ distinguisher, allowed distinguisher →
    hermiteMaskedAdvantage referenceRatioSampler maskSampler distinguisher ≤ hermiteBound

/-- A masked-ratio hybrid proves pseudorandomness of the public vector while preserving the
hidden Gaussian descriptor needed by the lossiness branch. -/
theorem maskedRatio_coefficientPseudorandomAgainst
    {R Row RatioDescriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    (ratioFamily : ProbComp (RatioDescriptor × R))
    (referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (allowed : ((Row → R) → ProbComp Bool) → Prop)
    (certificate : MaskedRatioHybridCertificate (publicRatioSampler ratioFamily)
      referenceRatioSampler maskSampler allowed) :
    CoefficientPseudorandomAgainst (maskedRatioFamily ratioFamily maskSampler) allowed
      (certificate.ratioBound + certificate.hermiteBound) := by
  intro distinguisher hAllowed
  rw [uniformToMaskedRatioFamilyAdvantage_eq]
  exact (maskedCoefficientAdvantage_le_ratio_add_hermite
      (publicRatioSampler ratioFamily) referenceRatioSampler maskSampler distinguisher).trans
    (add_le_add (certificate.ratioReplacement_le distinguisher hAllowed)
      (certificate.hermiteReplacement_le distinguisher hAllowed))

/-! ## Proof-carrying Gaussian and singular-value conditions -/

/-- Explicit analytic certificate for the Brakerski--Döttling small-ratio theorem.  The final
field is the imported Gaussian decomposition/convolution conclusion.  All inequalities from the
paper are retained as data so a concrete instantiation cannot bypass them. -/
structure SmallRatioGaussianCertificate
    {R Row Leakage Descriptor : Type} [CommRing R] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage)) where
  ringRank : ℕ
  tauOneBound : ℝ
  tauTwoBound : ℝ
  smoothingParameter : ℝ
  commonNoise : ℝ
  terminalNoise : ℝ
  conditionalNoiseEntropy : ℝ
  entropySlack : ℝ
  tauOneBound_nonneg : 0 ≤ tauOneBound
  tauTwoBound_pos : 0 < tauTwoBound
  smoothingParameter_nonneg : 0 ≤ smoothingParameter
  commonNoise_gt_smoothing :
    tauTwoBound * smoothingParameter < commonNoise
  terminalNoise_gt_decomposition :
    (2 : ℝ) * Real.sqrt 2 * tauOneBound * commonNoise < terminalNoise
  entropy_ge_cosets_add_slack :
    (ringRank : ℝ) * Real.logb 2 tauTwoBound + entropySlack ≤
      conditionalNoiseEntropy
  entropySlack_pos : 0 < entropySlack
  sometimesLossy : SometimesLossyCertificate family stateSampler

/-- Ring small-ratio lossiness with leakage, in exact finite-game form. -/
theorem smallRatioHNFRecovery_le
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    {family : CoefficientFamily Descriptor R Row}
    {stateSampler : ProbComp (SourceState R Row Leakage)}
    (certificate : SmallRatioGaussianCertificate family stateSampler)
    (solver : HNFSolver R Row Leakage) :
    Pr[= true | realHNFSearchGame ($ᵗ (Row → R)) stateSampler solver] ≤
      ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler solver) +
        certificate.sometimesLossy.bound :=
  realUniformHNFRecovery_le_coefficientAdvantage_add_sometimesLossy
    certificate.sometimesLossy solver

/-! ## Joint NTRU/DSPR and masked-ratio theorems -/

/-- Direct joint NTRU/DSPR-ratio corollary.  The pseudorandomness premise is joint across every
row sharing the sampled denominator; no invalid conversion from a one-ratio assumption is made. -/
theorem jointNTRURatio_hnfHardAgainst
    {R Row Leakage : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (witnessSampler : ProbComp (SmallRatioWitness R Row))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (allowedSolver : HNFSolver R Row Leakage → Prop)
    (allowedDistinguisher : ((Row → R) → ProbComp Bool) → Prop)
    (coefficientBound : ℝ)
    (gaussian : SmallRatioGaussianCertificate (smallRatioFamily witnessSampler) stateSampler)
    (hJointRatio : CoefficientPseudorandomAgainst (smallRatioFamily witnessSampler)
      allowedDistinguisher coefficientBound)
    (hClosure : ∀ solver, allowedSolver solver →
      allowedDistinguisher (coefficientRecoveryDistinguisher stateSampler solver)) :
    HNFHardAgainst stateSampler allowedSolver
      (ENNReal.ofReal coefficientBound + gaussian.sometimesLossy.bound) := by
  exact hnfHardAgainst_of_coefficientPseudorandom_and_averageLossiness
    (smallRatioFamily witnessSampler) stateSampler allowedSolver allowedDistinguisher
    coefficientBound gaussian.sometimesLossy.bound hJointRatio hClosure
    gaussian.sometimesLossy.averageLossiness_le_bound

/-- Brakerski--Döttling DSPR/NTRU-style theorem: one common-ratio replacement, one
Hermite-RLWE masked-vector hybrid, and the certified Gaussian lossiness term. -/
theorem dsprNTRUStyle_hnfHardAgainst
    {R Row Leakage RatioDescriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (ratioFamily : ProbComp (RatioDescriptor × R))
    (referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (allowedSolver : HNFSolver R Row Leakage → Prop)
    (allowedDistinguisher : ((Row → R) → ProbComp Bool) → Prop)
    (gaussian : SmallRatioGaussianCertificate
      (maskedRatioFamily ratioFamily maskSampler) stateSampler)
    (hybrid : MaskedRatioHybridCertificate (publicRatioSampler ratioFamily)
      referenceRatioSampler maskSampler allowedDistinguisher)
    (hClosure : ∀ solver, allowedSolver solver →
      allowedDistinguisher (coefficientRecoveryDistinguisher stateSampler solver)) :
    HNFHardAgainst stateSampler allowedSolver
      (ENNReal.ofReal (hybrid.ratioBound + hybrid.hermiteBound) +
        gaussian.sometimesLossy.bound) := by
  exact hnfHardAgainst_of_coefficientPseudorandom_and_averageLossiness
    (maskedRatioFamily ratioFamily maskSampler) stateSampler allowedSolver
    allowedDistinguisher (hybrid.ratioBound + hybrid.hermiteBound)
    gaussian.sometimesLossy.bound
    (maskedRatio_coefficientPseudorandomAgainst ratioFamily referenceRatioSampler
      maskSampler allowedDistinguisher hybrid)
    hClosure gaussian.sometimesLossy.averageLossiness_le_bound

/-! ## RLWE-only wide-ratio theorem -/

/-- The explicit Stehlé--Steinfeld statistical term `2^(10n) q^(-alpha*n)`. -/
noncomputable def wideGaussianRatioDistanceBound
    (ringRank modulus : ℕ) (alpha : ℝ) : ℝ :=
  (2 : ℝ) ^ (10 * ringRank) *
    Real.rpow (modulus : ℝ) (-alpha * (ringRank : ℝ))

/-- The width threshold `n*sqrt(log(8*n*q))*q^(1/2+alpha)`. -/
noncomputable def wideGaussianRatioWidth
    (ringRank modulus : ℕ) (alpha : ℝ) : ℝ :=
  (ringRank : ℝ) * Real.sqrt (Real.log (8 * (ringRank : ℝ) * (modulus : ℝ))) *
    Real.rpow (modulus : ℝ) ((1 : ℝ) / 2 + alpha)

/-- Proof-carrying interface to wide Gaussian ratio uniformity.  `referenceRatioSampler` may be
uniform on the unit group rather than on the whole ring, matching the precise analytic theorem;
the subsequent Hermite premise must use that same reference law. -/
structure WideGaussianRatioUniformityCertificate
    {R : Type} (ratioSampler referenceRatioSampler : ProbComp R) where
  ringRank : ℕ
  modulus : ℕ
  alpha : ℝ
  gamma : ℝ
  ringRank_pos : 0 < ringRank
  modulus_pos : 0 < modulus
  alpha_pos : 0 < alpha
  alpha_lt_one_third : alpha < (1 : ℝ) / 3
  gamma_ge_width : wideGaussianRatioWidth ringRank modulus alpha ≤ gamma
  statisticalDistance_le :
    tvDist ratioSampler referenceRatioSampler ≤
      wideGaussianRatioDistanceBound ringRank modulus alpha

/-- Wide ratio uniformity replaces the computational DSPR hop by statistical data processing. -/
theorem wideRatioReplacementAdvantage_le
    {R Row : Type} [CommRing R] [Fintype R] [SampleableType R]
    (ratioSampler referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (distinguisher : (Row → R) → ProbComp Bool)
    (certificate : WideGaussianRatioUniformityCertificate ratioSampler
      referenceRatioSampler) :
    ratioReplacementAdvantage ratioSampler referenceRatioSampler maskSampler distinguisher ≤
      wideGaussianRatioDistanceBound certificate.ringRank certificate.modulus
        certificate.alpha := by
  exact (ratioReplacementAdvantage_le_tvDist ratioSampler referenceRatioSampler
    maskSampler distinguisher).trans certificate.statisticalDistance_le

/-- RLWE-only rank-one HNF theorem.  The only coefficient-computational premise is the
Hermite-RLWE masked hybrid; the common-ratio hop is the certified statistical bound. -/
theorem rlweOnly_hnfHardAgainst
    {R Row Leakage RatioDescriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (ratioFamily : ProbComp (RatioDescriptor × R))
    (referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (allowedSolver : HNFSolver R Row Leakage → Prop)
    (allowedDistinguisher : ((Row → R) → ProbComp Bool) → Prop)
    (gaussian : SmallRatioGaussianCertificate
      (maskedRatioFamily ratioFamily maskSampler) stateSampler)
    (wide : WideGaussianRatioUniformityCertificate (publicRatioSampler ratioFamily)
      referenceRatioSampler)
    (hermiteBound : ℝ)
    (hHermite : ∀ distinguisher, allowedDistinguisher distinguisher →
      hermiteMaskedAdvantage referenceRatioSampler maskSampler distinguisher ≤ hermiteBound)
    (hClosure : ∀ solver, allowedSolver solver →
      allowedDistinguisher (coefficientRecoveryDistinguisher stateSampler solver)) :
    HNFHardAgainst stateSampler allowedSolver
      (ENNReal.ofReal
          (wideGaussianRatioDistanceBound wide.ringRank wide.modulus wide.alpha + hermiteBound) +
        gaussian.sometimesLossy.bound) := by
  let hybrid : MaskedRatioHybridCertificate (publicRatioSampler ratioFamily)
      referenceRatioSampler maskSampler allowedDistinguisher :=
    { ratioBound := wideGaussianRatioDistanceBound wide.ringRank wide.modulus wide.alpha
      hermiteBound := hermiteBound
      ratioReplacement_le := fun distinguisher _hAllowed ↦
        wideRatioReplacementAdvantage_le _ _ _ distinguisher wide
      hermiteReplacement_le := hHermite }
  exact dsprNTRUStyle_hnfHardAgainst ratioFamily referenceRatioSampler maskSampler
    stateSampler allowedSolver allowedDistinguisher gaussian hybrid hClosure

/-! ## RNS composition with coherent errors -/

/-- The abstract RNS proposition as a finite, proof-carrying certificate.  `stateSampler` is one
joint sampler over the complete heterogeneous RNS product, so all residues of one coherent
integer error and all other limbs may be correlated with the secret and the leakage. -/
structure RNSCompositionCertificate
    {Limb Slot Row Leakage Descriptor : Type} {K : Limb → Type}
    [CommRing (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    [Fintype (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    [SampleableType (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    [Fintype Row]
    [SampleableType
      (Row → RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    [DecidableEq (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    (family : CoefficientFamily Descriptor
      (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K) Row)
    (stateSampler : ProbComp (SourceState
      (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K) Row Leakage))
    (allowedSolver : HNFSolver
      (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K) Row Leakage → Prop)
    (allowedDistinguisher :
      ((Row → RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K) → ProbComp Bool) →
        Prop) where
  limbHybridBound : ℝ
  coefficientPseudorandom :
    CoefficientPseudorandomAgainst family allowedDistinguisher limbHybridBound
  jointLossiness : SometimesLossyCertificate family stateSampler
  recoveryReductionClosed : ∀ solver, allowedSolver solver →
    allowedDistinguisher (coefficientRecoveryDistinguisher stateSampler solver)

/-- Abstract RNS composition.  The coefficient term may be obtained by a hybrid over limbs, but
the lossiness term is deliberately joint and makes no independence assumption on coherent error
residues. -/
theorem rnsComposition_hnfHardAgainst
    {Limb Slot Row Leakage Descriptor : Type} {K : Limb → Type}
    [CommRing (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    [Fintype (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    [SampleableType (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    [Fintype Row]
    [SampleableType
      (Row → RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    [DecidableEq (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K)]
    (family : CoefficientFamily Descriptor
      (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K) Row)
    (stateSampler : ProbComp (SourceState
      (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K) Row Leakage))
    (allowedSolver : HNFSolver
      (RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K) Row Leakage → Prop)
    (allowedDistinguisher :
      ((Row → RNSSplitSearchToDecisionCorrelated.RNS Limb Slot K) → ProbComp Bool) →
        Prop)
    (certificate : RNSCompositionCertificate family stateSampler allowedSolver
      allowedDistinguisher) :
    HNFHardAgainst stateSampler allowedSolver
      (ENNReal.ofReal certificate.limbHybridBound + certificate.jointLossiness.bound) := by
  exact hnfHardAgainst_of_coefficientPseudorandom_and_averageLossiness
    family stateSampler allowedSolver allowedDistinguisher certificate.limbHybridBound
    certificate.jointLossiness.bound certificate.coefficientPseudorandom
    certificate.recoveryReductionClosed
    certificate.jointLossiness.averageLossiness_le_bound

/-! ## Exact product-cancellation interface for quadratic KDM -/

/-- Interpret the correlated quadratic-KDM latent source as the exact rank-one lossiness state.
The public leakage contains every `alpha*S+F` and `beta*S+G`, while the terminal error is
`sum F*G+H`. -/
def productCancellationSourceState
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (latent : QuadraticKDM.Latent R Row Factor) :
    SourceState R Row (QuadraticKDM.Leakage R Row Factor) where
  secret := latent.secret
  error := QuadraticKDM.terminalError latent
  leakage := QuadraticKDM.publicLeakage gadget latent

@[simp]
theorem productCancellationSourceState_secret
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (latent : QuadraticKDM.Latent R Row Factor) :
    (productCancellationSourceState gadget latent).secret = latent.secret := rfl

/-- Exact terminal channel occurring after rank-one HNF elimination. -/
theorem productCancellation_entropic_body
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (latent : QuadraticKDM.Latent R Row Factor)
    (coefficient : Row → R) (row : Row) :
    (entropicRLWEView (productCancellationSourceState gadget latent) coefficient).body row =
      coefficient row * latent.secret +
        (∑ factor, latent.firstError row factor * latent.secondError row factor) +
          latent.finalError row := by
  simp [entropicRLWEView, productCancellationSourceState,
    QuadraticKDM.terminalError, add_assoc]

/-- Joint sampler for the actual product-cancellation source.  In particular, mapping the latent
sampler does not manufacture independence between leakage, secret, and terminal errors. -/
def productCancellationStateSampler
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (latentSampler : ProbComp (QuadraticKDM.Latent R Row Factor)) :
    ProbComp (SourceState R Row (QuadraticKDM.Leakage R Row Factor)) :=
  productCancellationSourceState gadget <$> latentSampler

/-- The exact remaining `P_guess` condition identified in the TeX note. -/
noncomputable def productCancellationGuessingProbability
    {R Row Factor Descriptor : Type} [CommRing R] [Fintype Factor] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (latentSampler : ProbComp (QuadraticKDM.Latent R Row Factor)) : ENNReal :=
  averageLossiness family (productCancellationStateSampler gadget latentSampler)

/-- The product-cancellation source is secure exactly when its actual joint guessing channel is
lossy and its chosen coefficient family is pseudorandom.  Gaussian small-ratio estimates are not
incorrectly applied to the non-Gaussian, leakage-conditioned `sum F*G+H` channel. -/
theorem productCancellation_hnfHardAgainst
    {R Row Factor Descriptor : Type} [CommRing R] [Fintype Factor]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (latentSampler : ProbComp (QuadraticKDM.Latent R Row Factor))
    (allowedSolver : HNFSolver R Row (QuadraticKDM.Leakage R Row Factor) → Prop)
    (allowedDistinguisher : ((Row → R) → ProbComp Bool) → Prop)
    (coefficientBound : ℝ) (guessingBound : ENNReal)
    (hCoefficient : CoefficientPseudorandomAgainst family allowedDistinguisher coefficientBound)
    (hClosure : ∀ solver, allowedSolver solver →
      allowedDistinguisher (coefficientRecoveryDistinguisher
        (productCancellationStateSampler gadget latentSampler) solver))
    (hGuessing : productCancellationGuessingProbability family gadget latentSampler ≤
      guessingBound) :
    HNFHardAgainst (productCancellationStateSampler gadget latentSampler) allowedSolver
      (ENNReal.ofReal coefficientBound + guessingBound) := by
  exact hnfHardAgainst_of_coefficientPseudorandom_and_averageLossiness
    family (productCancellationStateSampler gadget latentSampler) allowedSolver
    allowedDistinguisher coefficientBound guessingBound hCoefficient hClosure hGuessing

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessRLWENTRU
