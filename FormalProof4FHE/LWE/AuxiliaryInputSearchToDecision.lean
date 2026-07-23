/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputSearch

/-!
# Search-to-Decision Interface for Auxiliary-Input Circular LWE

This module isolates the two logically different ingredients in a CircLWE search-to-decision
proof.

* `ViewRandomization` records the paper's secret randomization, homomorphic shifted-function
  evaluation, and optional noise smudging.  It permits the transformed view to use a different
  (typically wider) error distribution and charges an explicit total-variation error.
* `Reduction` is the quantitative certificate produced by the subsequent guess-and-check
  argument: it turns a public decision distinguisher into a search solver and bounds decision
  advantage by recovery probability plus an explicit loss.

The generic composition theorems are unconditional.  An application still has to construct both
objects for its concrete ciphertext distribution.  In particular, merely filling the fields with
unproved cryptographic assumptions is not a proof that ordinary LWE or RLWE implies circular
security.
-/

open OracleComp

namespace FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision

/-! ## Public decision distinguishers -/

/-- A genuine decision distinguisher sees the challenge and correlated auxiliary input, but not
the hidden secret retained by the experiment. -/
abbrev PublicDistinguisher (Challenge Auxiliary : Type) :=
  Challenge → Auxiliary → ProbComp Bool

/-- Embed a public distinguisher into the secret-aware continuation interface used by the generic
auxiliary-input games. -/
def publicContinuation {Secret Challenge Auxiliary : Type}
    (distinguisher : PublicDistinguisher Challenge Auxiliary) :
    FormalProof4FHE.LWE.AuxiliaryInput.Continuation Secret Challenge Auxiliary :=
  fun _secret challenge auxiliary ↦ distinguisher challenge auxiliary

/-- Real-versus-uniform auxiliary-input CircLWE advantage of a public distinguisher. -/
noncomputable def publicAdvantage {Secret Challenge Auxiliary : Type}
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem Secret Challenge Auxiliary)
    (distinguisher : PublicDistinguisher Challenge Auxiliary) : ℝ :=
  FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage problem
    (publicContinuation distinguisher)

/-- A public auxiliary-input distinguishing advantage is nonnegative. -/
theorem publicAdvantage_nonneg {Secret Challenge Auxiliary : Type}
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem Secret Challenge Auxiliary)
    (distinguisher : PublicDistinguisher Challenge Auxiliary) :
    0 ≤ publicAdvantage problem distinguisher := by
  unfold publicAdvantage FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
  exact abs_nonneg _

/-- A public auxiliary-input distinguishing advantage is at most one. -/
theorem publicAdvantage_le_one {Secret Challenge Auxiliary : Type}
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem Secret Challenge Auxiliary)
    (distinguisher : PublicDistinguisher Challenge Auxiliary) :
    publicAdvantage problem distinguisher ≤ 1 := by
  unfold publicAdvantage FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
  unfold ProbComp.boolDistAdvantage
  have hreal :
      (Pr[= true |
        FormalProof4FHE.LWE.AuxiliaryInput.realGame problem
          (publicContinuation distinguisher)]).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one
  have huniform :
      (Pr[= true |
        FormalProof4FHE.LWE.AuxiliaryInput.uniformGame problem
          (publicContinuation distinguisher)]).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one
  have hreal_nonneg :
      0 ≤ (Pr[= true |
        FormalProof4FHE.LWE.AuxiliaryInput.realGame problem
          (publicContinuation distinguisher)]).toReal := ENNReal.toReal_nonneg
  have huniform_nonneg :
      0 ≤ (Pr[= true |
        FormalProof4FHE.LWE.AuxiliaryInput.uniformGame problem
          (publicContinuation distinguisher)]).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- Concrete public-decision hardness for a selected distinguisher class. -/
def PublicHardAgainst {Secret Challenge Auxiliary : Type}
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem Secret Challenge Auxiliary)
    (allowed : PublicDistinguisher Challenge Auxiliary → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher → publicAdvantage problem distinguisher ≤ bound

/-! ## Shifted evaluation and smudging -/

/-- A paper-aligned randomization compiler for secret-dependent public views.

`evaluateAndSmudge mask` may be probabilistic.  It represents homomorphic evaluation of the
shifted secret function followed by any noise-flooding step.  `sampleNarrowView` is the input
search distribution and `sampleWideView` is the distribution expected by the decision oracle.
The latter may therefore use a wider error law. -/
structure ViewRandomization (Secret Mask View : Type) where
  sampleMask : ProbComp Mask
  act : Secret → Mask → Secret
  sampleFreshSecret : ProbComp Secret
  sampleNarrowView : Secret → ProbComp View
  sampleWideView : Secret → ProbComp View
  evaluateAndSmudge : Mask → View → ProbComp View
  error : ℝ
  error_nonneg : 0 ≤ error
  secretLaw : ∀ secret,
    evalDist (act secret <$> sampleMask) = evalDist sampleFreshSecret
  viewDistance_le : ∀ secret mask,
    tvDist
        (sampleNarrowView secret >>= evaluateAndSmudge mask)
        (sampleWideView (act secret mask)) ≤ error

namespace ViewRandomization

variable {Secret Mask View : Type}

/-- Randomize a fixed hidden secret and transform its narrow-error public view. -/
def randomizedView (compiler : ViewRandomization Secret Mask View) (secret : Secret) :
    ProbComp (Secret × View) := do
  let mask ← compiler.sampleMask
  let view ← compiler.sampleNarrowView secret
  let transformed ← compiler.evaluateAndSmudge mask view
  return (compiler.act secret mask, transformed)

/-- The target experiment: a fresh secret together with its wide-error public view. -/
def freshWideView (compiler : ViewRandomization Secret Mask View) :
    ProbComp (Secret × View) := do
  let freshSecret ← compiler.sampleFreshSecret
  let view ← compiler.sampleWideView freshSecret
  return (freshSecret, view)

/-- Intermediate target indexed by the sampled mask. -/
private def transportedWideView
    (compiler : ViewRandomization Secret Mask View) (secret : Secret) :
    ProbComp (Secret × View) := do
  let mask ← compiler.sampleMask
  let freshSecret := compiler.act secret mask
  let view ← compiler.sampleWideView freshSecret
  return (freshSecret, view)

/-- The per-mask evaluator/smudger error remains a single total-variation loss after sampling the
mask and attaching the transformed secret. -/
private theorem randomizedView_tvDist_transportedWideView_le
    (compiler : ViewRandomization Secret Mask View) (secret : Secret) :
    tvDist (compiler.randomizedView secret) (compiler.transportedWideView secret) ≤
      compiler.error := by
  unfold randomizedView transportedWideView
  refine tvDist_bind_left_le_const' (m := ProbComp) compiler.sampleMask _ _
    compiler.error fun mask ↦ ?_
  let finish := fun view : View ↦
    (pure (compiler.act secret mask, view) : ProbComp (Secret × View))
  have hpost := tvDist_bind_right_le finish
    (compiler.sampleNarrowView secret >>= compiler.evaluateAndSmudge mask)
    (compiler.sampleWideView (compiler.act secret mask))
  have hpost' :
      tvDist
          (compiler.sampleNarrowView secret >>= fun view ↦
            compiler.evaluateAndSmudge mask view >>= finish)
          (compiler.sampleWideView (compiler.act secret mask) >>= finish) ≤
        tvDist
          (compiler.sampleNarrowView secret >>= compiler.evaluateAndSmudge mask)
          (compiler.sampleWideView (compiler.act secret mask)) := by
    simpa only [bind_assoc] using hpost
  exact hpost'.trans (compiler.viewDistance_le secret mask)

/-- Exact secret randomization identifies the mask-indexed wide view with the fresh-secret wide
view. -/
private theorem evalDist_transportedWideView_eq_freshWideView
    (compiler : ViewRandomization Secret Mask View) (secret : Secret) :
    evalDist (compiler.transportedWideView secret) =
      evalDist compiler.freshWideView := by
  let finish := fun (freshSecret : Secret) (view : View) ↦
    (pure (freshSecret, view) : ProbComp (Secret × View))
  calc
    _ = evalDist ((compiler.act secret <$> compiler.sampleMask) >>= fun freshSecret ↦
        compiler.sampleWideView freshSecret >>= fun view ↦ finish freshSecret view) := by
      simp [transportedWideView, finish, map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (compiler.sampleFreshSecret >>= fun freshSecret ↦
        compiler.sampleWideView freshSecret >>= fun view ↦ finish freshSecret view) := by
      rw [evalDist_bind, compiler.secretLaw secret, ← evalDist_bind]
    _ = _ := by simp [freshWideView, finish, monad_norm]

/-- A shifted evaluator and smudger with pointwise loss `error` produces the fresh wide-error
joint distribution with at most the same loss. -/
theorem randomizedView_tvDist_freshWideView_le
    (compiler : ViewRandomization Secret Mask View) (secret : Secret) :
    tvDist (compiler.randomizedView secret) compiler.freshWideView ≤ compiler.error := by
  have heq := compiler.evalDist_transportedWideView_eq_freshWideView secret
  have hzero : tvDist (compiler.transportedWideView secret) compiler.freshWideView = 0 := by
    unfold tvDist
    rw [heq]
    exact SPMF.tvDist_self _
  calc
    tvDist (compiler.randomizedView secret) compiler.freshWideView ≤
        tvDist (compiler.randomizedView secret) (compiler.transportedWideView secret) +
          tvDist (compiler.transportedWideView secret) compiler.freshWideView :=
      tvDist_triangle _ _ _
    _ ≤ compiler.error + 0 := add_le_add
      (compiler.randomizedView_tvDist_transportedWideView_le secret) (le_of_eq hzero)
    _ = compiler.error := add_zero _

/-- Build a zero-loss view randomizer from exact secret and view distribution identities. -/
def ofExact
    (sampleMask : ProbComp Mask)
    (act : Secret → Mask → Secret)
    (sampleFreshSecret : ProbComp Secret)
    (sampleView : Secret → ProbComp View)
    (transformView : Mask → View → ProbComp View)
    (secretLaw : ∀ secret,
      evalDist (act secret <$> sampleMask) = evalDist sampleFreshSecret)
    (viewLaw : ∀ secret mask,
      evalDist (sampleView secret >>= transformView mask) =
        evalDist (sampleView (act secret mask))) :
    ViewRandomization Secret Mask View where
  sampleMask := sampleMask
  act := act
  sampleFreshSecret := sampleFreshSecret
  sampleNarrowView := sampleView
  sampleWideView := sampleView
  evaluateAndSmudge := transformView
  error := 0
  error_nonneg := le_rfl
  secretLaw := secretLaw
  viewDistance_le := by
    intro secret mask
    unfold tvDist
    rw [viewLaw secret mask]
    simp

end ViewRandomization

/-! ## Quantitative decision-to-search certificates -/

/-- Search hardness stated on the real probability scale used by decision advantages. -/
def RealSearchHardAgainst {Secret Challenge Auxiliary : Type}
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      Secret Challenge Auxiliary)
    (allowed : FormalProof4FHE.LWE.AuxiliaryInput.Search.Solver
      Secret Challenge Auxiliary → Prop)
    (bound : ℝ) : Prop :=
  ∀ solver, allowed solver →
    (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability problem solver).toReal ≤ bound

/-- A checked quantitative search-to-decision reduction.

The essential nontrivial field is `advantage_le`: constructing it requires the guess-and-check
analysis for the concrete secret space and the correctness/error bounds of the view randomizer.
The `loss` field records smudging, finite guessing, amplification, and any other reduction loss. -/
structure Reduction {Secret Challenge Auxiliary : Type} [DecidableEq Secret]
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      Secret Challenge Auxiliary) where
  toSolver : PublicDistinguisher Challenge Auxiliary →
    FormalProof4FHE.LWE.AuxiliaryInput.Search.Solver Secret Challenge Auxiliary
  loss : PublicDistinguisher Challenge Auxiliary → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le : ∀ distinguisher,
    publicAdvantage problem distinguisher ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (FormalProof4FHE.LWE.AuxiliaryInput.Search.exactRecoveryProblem problem)
        (toSolver distinguisher)).toReal + loss distinguisher

/-- A checked search-to-decision reduction whose decision and search distributions may differ.

This is the form required by error smudging: the public distinguisher runs on a widened-error
auxiliary-input problem, while the produced solver is measured against a separately supplied
narrow-error search problem. -/
structure CrossReduction {SearchSecret DecisionSecret Challenge Auxiliary : Type}
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      SearchSecret Challenge Auxiliary) where
  toSolver : PublicDistinguisher Challenge Auxiliary →
    FormalProof4FHE.LWE.AuxiliaryInput.Search.Solver SearchSecret Challenge Auxiliary
  loss : PublicDistinguisher Challenge Auxiliary → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le : ∀ distinguisher,
    publicAdvantage decisionProblem distinguisher ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        searchProblem (toSolver distinguisher)).toReal + loss distinguisher

/-- Search hardness transfers to public decision hardness through a checked reduction, with the
search and reduction losses added once. -/
theorem publicHardAgainst_of_reduction
    {Secret Challenge Auxiliary : Type} [DecidableEq Secret]
    (problem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      Secret Challenge Auxiliary)
    (reduction : Reduction problem)
    (decisionAllowed : PublicDistinguisher Challenge Auxiliary → Prop)
    (solverAllowed : FormalProof4FHE.LWE.AuxiliaryInput.Search.Solver
      Secret Challenge Auxiliary → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : RealSearchHardAgainst
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.exactRecoveryProblem problem)
      solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed (reduction.toSolver distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      reduction.loss distinguisher ≤ lossBound) :
    PublicHardAgainst problem decisionAllowed (searchBound + lossBound) := by
  intro distinguisher hallowed
  exact (reduction.advantage_le distinguisher).trans
    (add_le_add
      (hSearch (reduction.toSolver distinguisher) (hClosed distinguisher hallowed))
      (hLoss distinguisher hallowed))

/-- Search hardness for a narrow problem transfers to public decision hardness for a separately
specified widened problem through a checked cross-distribution reduction. -/
theorem publicHardAgainst_of_crossReduction
    {SearchSecret DecisionSecret Challenge Auxiliary : Type}
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary)
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      SearchSecret Challenge Auxiliary)
    (reduction : CrossReduction decisionProblem searchProblem)
    (decisionAllowed : PublicDistinguisher Challenge Auxiliary → Prop)
    (solverAllowed : FormalProof4FHE.LWE.AuxiliaryInput.Search.Solver
      SearchSecret Challenge Auxiliary → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : RealSearchHardAgainst searchProblem solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed (reduction.toSolver distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      reduction.loss distinguisher ≤ lossBound) :
    PublicHardAgainst decisionProblem decisionAllowed (searchBound + lossBound) := by
  intro distinguisher hallowed
  exact (reduction.advantage_le distinguisher).trans
    (add_le_add
      (hSearch (reduction.toSolver distinguisher) (hClosed distinguisher hallowed))
      (hLoss distinguisher hallowed))

end FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision
