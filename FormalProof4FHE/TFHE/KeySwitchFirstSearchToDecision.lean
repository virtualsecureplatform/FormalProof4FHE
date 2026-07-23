/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputSearchToDecision
import FormalProof4FHE.TFHE.KeySwitchFirstCandidateView

/-!
# KSK-First Search-to-Decision for Native TFHE

The KSK-first candidate law compares a real key-switch key with a uniform key-switch transcript
while retaining the real bootstrapping key.  This file packages that endpoint as a genuine
`LWE.AuxiliaryInput.Problem`: the KSK is the challenge and the BRK is the correlated auxiliary
input.  The generic experiment samples these two components in the opposite order from the
native public-view code, so exact distribution equalities below justify the reordering.

The resulting one-shot reduction recovers all scalar-key coordinates and then uses the checked
centered-binomial KSK decoder to recover the ring key.  Its accounting loss is explicit: it is
the nonnegative deficit between the decision advantage and the finite coordinate union-bound
lower bound.  This packages a valid search-to-decision theorem, but does not claim that this
one-shot loss is negligible for production TFHE dimensions.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstSearchToDecision

open KeySwitchFirstCandidateView

/-- The challenge in the KSK-first formulation is the complete native key-switch transcript. -/
abbrev KeySwitchChallenge
    (q degree ringRank lweDimension keySwitchLevels : ℕ) :=
  Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels

/-- The real native bootstrapping key is retained as correlated auxiliary input. -/
abbrev BootstrapAuxiliary
    (q degree ringRank tgswLevels lweDimension : ℕ) :=
  Native.BootstrappingKey q degree ringRank tgswLevels lweDimension

/-- Native TFHE with the KSK as challenge and the real BRK as fixed correlated side input. -/
noncomputable def problem
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    LWE.AuxiliaryInput.Problem
      (AuxiliaryInput.Secret lweDimension ringRank degree)
      (KeySwitchChallenge q degree ringRank lweDimension keySwitchLevels)
      (BootstrapAuxiliary q degree ringRank tgswLevels lweDimension) where
  sampleSecret :=
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  sampleReal :=
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary
  sampleZero := fun secrets ↦
    Native.generateZeroKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
      keySwitchErrorSampler secrets.1
  sampleUniform :=
    $ᵗ (KeySwitchChallenge q degree ringRank lweDimension keySwitchLevels)
  sampleAuxiliary :=
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleReal

/-- A public distinguisher in the generic KSK-first argument order. -/
abbrev Distinguisher
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
    (KeySwitchChallenge q degree ringRank lweDimension keySwitchLevels)
    (BootstrapAuxiliary q degree ringRank tgswLevels lweDimension)

/-- Swap a generic KSK-first distinguisher into the native BRK-first calling convention. -/
def toNativeDistinguisher
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    PublicDistinguisher q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun bootstrapKey keySwitchKey ↦ distinguisher keySwitchKey bootstrapKey

/-- Swap a native public distinguisher into the generic KSK-first calling convention. -/
def ofNativeDistinguisher
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Distinguisher q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun keySwitchKey bootstrapKey ↦ distinguisher bootstrapKey keySwitchKey

/-- Sampling the KSK before the BRK in the generic real game gives the native real public
experiment exactly. -/
theorem realGame_evalDist_eq_realDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist
        (LWE.AuxiliaryInput.realGame
          (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (LWE.AuxiliaryInput.SearchToDecision.publicContinuation distinguisher)) =
      evalDist
        (realDecisionGame ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget (toNativeDistinguisher distinguisher)) := by
  simp only [LWE.AuxiliaryInput.realGame, problem,
    LWE.AuxiliaryInput.SearchToDecision.publicContinuation, realDecisionGame,
    Search.problem, LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    AuxiliaryInput.problem]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (Native.sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  refine evalDist_bind_congr' (Native.sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  exact evalDist_bind_bind_swap
    (Native.generateKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
      keySwitchErrorSampler keySwitchGadget (keyExtract ringSecret) lweSecret)
    (MonomialKDM.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret) _

/-- Sampling a uniform KSK before the real BRK gives the native
real-BRK/uniform-KSK endpoint exactly. -/
theorem uniformGame_evalDist_eq_uniformKeySwitchDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist
        (LWE.AuxiliaryInput.uniformGame
          (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (LWE.AuxiliaryInput.SearchToDecision.publicContinuation distinguisher)) =
      evalDist
        (uniformKeySwitchDecisionGame ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget (toNativeDistinguisher distinguisher)) := by
  simp only [LWE.AuxiliaryInput.uniformGame, problem,
    LWE.AuxiliaryInput.SearchToDecision.publicContinuation,
    uniformKeySwitchDecisionGame, uniformKeySwitchPublicView,
    Search.problem, LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    AuxiliaryInput.problem]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (Native.sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  refine evalDist_bind_congr' (Native.sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  exact evalDist_bind_bind_swap
    ($ᵗ (KeySwitchChallenge q degree ringRank lweDimension keySwitchLevels))
    (MonomialKDM.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret) _

/-- The generic public advantage of the swapped problem is exactly the KSK-first native
decision advantage. -/
theorem publicAdvantage_eq_keySwitchDecisionAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        distinguisher =
      keySwitchDecisionAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget (toNativeDistinguisher distinguisher) := by
  unfold LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
    LWE.AuxiliaryInput.circularLweAdvantage keySwitchDecisionAdvantage
    ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (realGame_evalDist_eq_realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher),
    probOutput_congr rfl
      (uniformGame_evalDist_eq_uniformKeySwitchDecisionGame ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)]

/-! ## Exact-search adapter -/

/-- A solver in the generic KSK-first argument order. -/
abbrev Solver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  LWE.AuxiliaryInput.Search.Solver
    (AuxiliaryInput.Secret lweDimension ringRank degree)
    (KeySwitchChallenge q degree ringRank lweDimension keySwitchLevels)
    (BootstrapAuxiliary q degree ringRank tgswLevels lweDimension)

/-- Swap an existing native BRK-first paired-key solver into the generic KSK-first order. -/
def ofNativeSolver
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (solver : Search.Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    Solver q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun keySwitchKey bootstrapKey ↦ solver bootstrapKey keySwitchKey

/-- The exact-recovery game of a swapped native solver is distributionally identical to the
existing native paired-search game. -/
theorem game_ofNativeSolver_evalDist_eq_nativeGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Search.Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist
        (LWE.AuxiliaryInput.Search.game
          (LWE.AuxiliaryInput.Search.exactRecoveryProblem
            (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
              ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget))
          (ofNativeSolver solver)) =
      evalDist
        (Search.game ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget solver) := by
  simp only [LWE.AuxiliaryInput.Search.game,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem, problem, ofNativeSolver,
    Search.game, Search.problem, AuxiliaryInput.problem]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (Native.sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  refine evalDist_bind_congr' (Native.sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  exact evalDist_bind_bind_swap
    (Native.generateKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
      keySwitchErrorSampler keySwitchGadget (keyExtract ringSecret) lweSecret)
    (MonomialKDM.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret) _

/-- Success probability is preserved by the KSK/BRK argument-order adapter. -/
theorem successProbability_ofNativeSolver_eq
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Search.Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    LWE.AuxiliaryInput.Search.successProbability
        (LWE.AuxiliaryInput.Search.exactRecoveryProblem
          (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget))
        (ofNativeSolver solver) =
      Search.successProbability ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget solver := by
  unfold LWE.AuxiliaryInput.Search.successProbability Search.successProbability
  exact probOutput_congr rfl
    (game_ofNativeSolver_evalDist_eq_nativeGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget solver)

/-! ## Concrete one-shot paired recovery -/

/-- The existing native paired-key solver obtained from KSK-first coordinate tests. -/
noncomputable def nativeSolver
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Search.Solver q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  PairedRecovery.completeScalarSolver keySwitchGadget level
    (assemble (testerOfCheck
      (fun _ ↦ KeySwitchFirstCandidateView.orientation ringErrorSampler
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget (toNativeDistinguisher distinguisher))
      (KeySwitchFirstCandidateView.toCandidateCheck
        (toNativeDistinguisher distinguisher))))

/-- The same concrete solver in the generic KSK-first argument order. -/
noncomputable def solver
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Solver q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  ofNativeSolver (nativeSolver (keySwitchEta := keySwitchEta)
    ringErrorSampler tgswGadget keySwitchGadget level distinguisher)

/-- The exact finite-coordinate lower bound delivered by one-shot candidate testing. -/
noncomputable def oneShotLowerBound
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ENNReal :=
  1 - ∑ _coordinate : Fin lweDimension,
    ENNReal.ofReal
      ((1 - LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget) distinguisher) / 2)

/-- The one-shot lower bound is achieved by the concrete generic paired-key solver. -/
theorem oneShotLowerBound_le_searchSuccess
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    oneShotLowerBound (keySwitchEta := keySwitchEta) ringErrorSampler
        tgswGadget keySwitchGadget distinguisher ≤
      LWE.AuxiliaryInput.Search.successProbability
        (LWE.AuxiliaryInput.Search.exactRecoveryProblem
          (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
            ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
            tgswGadget keySwitchGadget))
        (solver (keySwitchEta := keySwitchEta) ringErrorSampler
          tgswGadget keySwitchGadget level distinguisher) := by
  rw [show solver (keySwitchEta := keySwitchEta) ringErrorSampler
      tgswGadget keySwitchGadget level distinguisher =
      ofNativeSolver (nativeSolver (keySwitchEta := keySwitchEta)
        ringErrorSampler tgswGadget keySwitchGadget level distinguisher) from rfl,
    successProbability_ofNativeSolver_eq]
  simpa only [oneShotLowerBound,
      publicAdvantage_eq_keySwitchDecisionAdvantage, nativeSolver] using
    (KeySwitchFirstCandidateView.one_sub_sum_keySwitchDecisionError_le_pairedSearchSuccess_centeredBinomial
      ringErrorSampler tgswGadget keySwitchGadget level hmargin
      (toNativeDistinguisher distinguisher))

/-! ## Checked quantitative reduction -/

/-- The exact one-shot accounting deficit.  It is zero precisely when the coordinate union-bound
lower bound already dominates the KSK-first decision advantage. -/
noncomputable def oneShotLoss
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  max 0
    (LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget) distinguisher -
      (oneShotLowerBound (keySwitchEta := keySwitchEta) ringErrorSampler
        tgswGadget keySwitchGadget distinguisher).toReal)

theorem oneShotLoss_nonneg
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    0 ≤ oneShotLoss (keySwitchEta := keySwitchEta) ringErrorSampler
      tgswGadget keySwitchGadget distinguisher := by
  unfold oneShotLoss
  exact le_max_left _ _

/-- The KSK-first public advantage is bounded by paired-key search success plus the exact
one-shot accounting loss. -/
theorem publicAdvantage_le_searchSuccess_add_oneShotLoss
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget) distinguisher ≤
      (LWE.AuxiliaryInput.Search.successProbability
        (LWE.AuxiliaryInput.Search.exactRecoveryProblem
          (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
            ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
            tgswGadget keySwitchGadget))
        (solver (keySwitchEta := keySwitchEta) ringErrorSampler
          tgswGadget keySwitchGadget level distinguisher)).toReal +
      oneShotLoss (keySwitchEta := keySwitchEta) ringErrorSampler
        tgswGadget keySwitchGadget distinguisher := by
  let advantage := LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget) distinguisher
  let lower := oneShotLowerBound (keySwitchEta := keySwitchEta) ringErrorSampler
    tgswGadget keySwitchGadget distinguisher
  have haccount :
      advantage ≤ lower.toReal +
        oneShotLoss (keySwitchEta := keySwitchEta) ringErrorSampler
          tgswGadget keySwitchGadget distinguisher := by
    have hmax : advantage - lower.toReal ≤ max 0 (advantage - lower.toReal) :=
      le_max_right _ _
    dsimp only [advantage, lower] at hmax ⊢
    unfold oneShotLoss
    linarith
  have hsuccess := oneShotLowerBound_le_searchSuccess
    ringErrorSampler tgswGadget keySwitchGadget level hmargin distinguisher
  have hsuccessReal := ENNReal.toReal_mono probOutput_ne_top hsuccess
  exact haccount.trans (add_le_add hsuccessReal le_rfl)

/-- A fully checked generic search-to-decision certificate for the KSK-first auxiliary-input
problem.  The only quantitative cost is `oneShotLoss`. -/
noncomputable def reduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    LWE.AuxiliaryInput.SearchToDecision.Reduction
      (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget) where
  toSolver := solver (keySwitchEta := keySwitchEta) ringErrorSampler
    tgswGadget keySwitchGadget level
  loss := oneShotLoss (keySwitchEta := keySwitchEta) ringErrorSampler
    tgswGadget keySwitchGadget
  loss_nonneg := oneShotLoss_nonneg ringErrorSampler tgswGadget keySwitchGadget
  advantage_le := publicAdvantage_le_searchSuccess_add_oneShotLoss
    ringErrorSampler tgswGadget keySwitchGadget level hmargin

/-- Native paired-search hardness transfers to KSK-first public decision hardness through the
concrete reduction, with the explicit one-shot loss added once. -/
theorem publicHardAgainst_of_searchHardness
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (decisionAllowed : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (solverAllowed : Solver q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : LWE.AuxiliaryInput.SearchToDecision.RealSearchHardAgainst
      (LWE.AuxiliaryInput.Search.exactRecoveryProblem
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget)) solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed (solver (keySwitchEta := keySwitchEta) ringErrorSampler
        tgswGadget keySwitchGadget level distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      oneShotLoss (keySwitchEta := keySwitchEta) ringErrorSampler
        tgswGadget keySwitchGadget distinguisher ≤ lossBound) :
    LWE.AuxiliaryInput.SearchToDecision.PublicHardAgainst
      (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget)
      decisionAllowed (searchBound + lossBound) := by
  exact LWE.AuxiliaryInput.SearchToDecision.publicHardAgainst_of_reduction
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget)
    (reduction ringErrorSampler tgswGadget keySwitchGadget level hmargin)
    decisionAllowed solverAllowed searchBound lossBound hSearch hClosed hLoss

/-! ## Native-order hardness corollary -/

/-- KSK-first public-decision hardness stated in the native BRK-then-KSK calling convention. -/
def NativePublicHardAgainst
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    keySwitchDecisionAdvantage ringErrorSampler
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget distinguisher ≤ bound

/-- Paired native search hardness on the real BRK+KSK source distribution. -/
def NativeRealSearchHardAgainst
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : Search.Solver q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ nativeSolver, allowed nativeSolver →
    (Search.successProbability ringErrorSampler
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget nativeSolver).toReal ≤ bound

/-- Native paired-search hardness implies native KSK-first public-decision hardness, with the
same explicit one-shot loss.  This is the direct TFHE-facing form of `reduction`. -/
theorem nativePublicHardAgainst_of_nativeSearchHardness
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (decisionAllowed : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (solverAllowed : Search.Solver q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : NativeRealSearchHardAgainst (keySwitchEta := keySwitchEta)
      ringErrorSampler tgswGadget keySwitchGadget solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed (nativeSolver (keySwitchEta := keySwitchEta)
        ringErrorSampler tgswGadget keySwitchGadget level
        (ofNativeDistinguisher distinguisher)))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      oneShotLoss (keySwitchEta := keySwitchEta) ringErrorSampler
        tgswGadget keySwitchGadget (ofNativeDistinguisher distinguisher) ≤ lossBound) :
    NativePublicHardAgainst (keySwitchEta := keySwitchEta)
      ringErrorSampler tgswGadget keySwitchGadget decisionAllowed
      (searchBound + lossBound) := by
  intro distinguisher hallowed
  have hReduction := publicAdvantage_le_searchSuccess_add_oneShotLoss
    ringErrorSampler tgswGadget keySwitchGadget level hmargin
    (ofNativeDistinguisher distinguisher)
  rw [publicAdvantage_eq_keySwitchDecisionAdvantage] at hReduction
  change keySwitchDecisionAdvantage ringErrorSampler
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget distinguisher ≤
    (LWE.AuxiliaryInput.Search.successProbability
      (LWE.AuxiliaryInput.Search.exactRecoveryProblem
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget))
      (ofNativeSolver (nativeSolver (keySwitchEta := keySwitchEta)
        ringErrorSampler tgswGadget keySwitchGadget level
        (ofNativeDistinguisher distinguisher)))).toReal +
      oneShotLoss (keySwitchEta := keySwitchEta) ringErrorSampler
        tgswGadget keySwitchGadget (ofNativeDistinguisher distinguisher) at hReduction
  rw [successProbability_ofNativeSolver_eq] at hReduction
  exact hReduction.trans (add_le_add
    (hSearch _ (hClosed distinguisher hallowed))
    (hLoss distinguisher hallowed))

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstSearchToDecision
