/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInputSearchToDecision
import FormalProof4FHE.TFHE.AuxiliaryInputCircularSearch
import FormalProof4FHE.TFHE.AuxiliaryInputPairedRecovery
import FormalProof4FHE.TFHE.PointwiseCandidateView
import FormalProof4FHE.TFHE.ScalarCoordinateRecovery

/-!
# Native TFHE Search-to-Decision Boundary

This module connects the checked centered-binomial scalar-key transform to the generic
search-to-decision interface.  For every fixed native ring key, it constructs a zero-loss
`ViewRandomization`: a uniform XOR mask produces a fresh scalar key and exactly the corresponding
monomial-BRK plus real-KSK public view.

The full native secret is heterogeneous, but the retained real KSK resolves that mismatch.  Once
the scalar key is recovered, nearest-codeword KSK decryption recovers every extracted ring-key bit
under an explicit centered-binomial margin.  `ScalarSecretReduction.toPairedSecretReduction`
therefore turns a scalar-only quantitative certificate into the full paired certificate with no
additional loss.  `CoordinateSecretReduction.toScalarSecretReduction` separately discharges
whole-key assembly by a coordinate union bound.  A generic executable guess-and-check tester now
turns an exact native candidate-view transformer into one-shot error `(1 - advantage) / 2`.
Support-wise conditional gaps now feed an executable shared-context majority amplifier and the
coordinate union bound.  What remains is the concrete shifted evaluator/smudger establishing that
stronger native gap, together with its global decision-to-search accounting.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.SearchToDecision

/-- The public native evaluation-key view consumed by a decision distinguisher. -/
abbrev View (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
      q degree ringRank tgswLevels lweDimension ×
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
      q degree ringRank lweDimension keySwitchLevels

/-- The candidate-check module's native real/uniform advantage is exactly the public auxiliary-
input CircLWE advantage used by this reduction boundary. -/
theorem candidateDecisionAdvantage_eq_publicAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher :
      LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
        (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
          q degree ringRank tgswLevels lweDimension)
        (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
          q degree ringRank lweDimension keySwitchLevels)) :
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.decisionAdvantage
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher =
      LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        distinguisher := by
  rfl

/-- At the public auxiliary-input boundary, a native candidate-view transformer gives exact
one-shot coordinate error `(1 - publicAdvantage) / 2`. -/
theorem candidateViewTransformer_oneShotFailure_eq_publicAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (transformer :
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateViewTransformer
        (ringRank := ringRank) (lweDimension := lweDimension)
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher :
      LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
        (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
          q degree ringRank tgswLevels lweDimension)
        (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
          q degree ringRank lweDimension keySwitchLevels))
    (coordinate : Fin lweDimension) :
    (Pr[= false |
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateGame
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.testerOfCheck
          (fun _ =>
            Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateViewTransformer.orientation
              ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
          (transformer.toCheck distinguisher)) coordinate]).toReal =
      (1 - LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        distinguisher) / 2 := by
  rw [Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateGame_candidateViewTransformer_failureProbability,
    candidateDecisionAdvantage_eq_publicAdvantage]

/-- Zero-loss scalar-secret randomization for the exact centered-binomial native CircLWE view,
with the ring secret held fixed. -/
noncomputable def scalarViewRandomization
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ)
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      (BinarySecret lweDimension)
      (BinarySecret lweDimension)
      (View q (degree + 1) ringRank tgswLevels lweDimension keySwitchLevels) :=
  LWE.AuxiliaryInput.SearchToDecision.ViewRandomization.ofExact
    ($ᵗ BinarySecret lweDimension)
    Native.ScalarSecretRandomization.maskedSecret
    ($ᵗ BinarySecret lweDimension)
    (fun lweSecret ↦
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.fixedSecretRealView
        q (degree + 1) ringRank tgswLevels lweDimension
        keySwitchLevels (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
        keySwitchErrorSampler tgswGadget keySwitchGadget (lweSecret, ringSecret))
    (fun mask ↦ pure ∘
      Native.ScalarSecretRandomization.transformEvaluationKeyPair tgswGadget mask)
    Native.ScalarSecretRandomization.maskedSecret_uniform_evalDist
    (fun lweSecret mask ↦ by
      simpa only [← map_eq_bind_pure_comp] using
        (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.transform_fixedSecretRealView_centeredBinomial_evalDist
          (ringEta := ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget
          lweSecret mask ringSecret))

@[simp]
theorem scalarViewRandomization_error
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ)
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    (scalarViewRandomization q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret).error = 0 :=
  rfl

/-- The paper-aligned generic compiler theorem specializes to exact equality (zero TV distance)
for native scalar-key randomization with centered-binomial ring noise. -/
theorem scalarViewRandomization_tvDist_eq_zero
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ}
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    let compiler := scalarViewRandomization q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret
    tvDist (compiler.randomizedView lweSecret) compiler.freshWideView = 0 := by
  dsimp only
  let compiler := scalarViewRandomization q degree ringRank tgswLevels lweDimension
    keySwitchLevels ringEta keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret
  apply le_antisymm
  · simpa only [compiler, scalarViewRandomization_error] using
      (compiler.randomizedView_tvDist_freshWideView_le lweSecret)
  · exact tvDist_nonneg _ _

/-! ## Paired-secret reduction interface -/

/-- The exact quantitative certificate turning a public native decision distinguisher into a
solver recovering both native secrets. -/
abbrev PairedSecretReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :=
  LWE.AuxiliaryInput.SearchToDecision.Reduction
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)

/-! ## Reduction of paired recovery to scalar recovery -/

/-- The strictly smaller quantitative certificate now left by KSK source-key recovery.

Unlike `PairedSecretReduction`, its solver returns only the scalar key and its quantitative field
uses the scalar-only recovery game.  Centered-binomial KSK correctness will complete that candidate
to the full paired key without changing the success probability or reduction loss. -/
structure ScalarSecretReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toScalarSolver :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.ScalarSolver
        q degree ringRank tgswLevels lweDimension keySwitchLevels
  loss :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le : ∀ distinguisher,
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget)
        distinguisher ≤
      (Pr[= true |
        Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.scalarGame
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget (toScalarSolver distinguisher)]).toReal +
        loss distinguisher

namespace ScalarSecretReduction

/-- A scalar-only reduction certificate canonically induces the full paired-key certificate.  The
construction decrypts the real KSK with each scalar candidate; the checked support theorem makes
the paired and scalar success probabilities exactly equal. -/
noncomputable def toPairedSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : ScalarSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    PairedSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget where
  toSolver := fun distinguisher ↦
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.completeScalarSolver
      keySwitchGadget level (reduction.toScalarSolver distinguisher)
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  advantage_le := by
    intro distinguisher
    have h := reduction.advantage_le distinguisher
    rw [← Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.successProbability_completeScalarSolver_eq
      (RLWE.CenteredBinomial.sampler q degree ringEta) tgswGadget
      keySwitchGadget level (reduction.toScalarSolver distinguisher) hmargin] at h
    exact h

end ScalarSecretReduction

/-! ## Reduction of scalar recovery to coordinate tests -/

/-- A coordinatewise quantitative certificate for the remaining native scalar-key reduction.

For each public distinguisher it supplies one randomized test per scalar-key coordinate, an
upper bound on every coordinate's error probability in the common BRK+KSK experiment, and the
paper-specific inequality relating decision advantage to the resulting all-coordinate success
lower bound.  The latter is precisely where shifted evaluation, smudging, amplification, and
guess-and-check losses belong. -/
structure CoordinateSecretReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toTester :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CoordinateTester
        q degree ringRank tgswLevels lweDimension keySwitchLevels
  coordinateError :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ENNReal
  loss :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  coordinateGameFailure_le : ∀ distinguisher coordinate,
    Pr[= false |
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateGame
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget (toTester distinguisher) coordinate] ≤
        coordinateError distinguisher coordinate
  advantage_le : ∀ distinguisher,
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget)
        distinguisher ≤
      (1 - ∑ coordinate, coordinateError distinguisher coordinate).toReal +
        loss distinguisher

namespace CoordinateSecretReduction

/-- Coordinate testers canonically induce the scalar-search certificate.  The finite union bound
is discharged here, so no whole-key success proof remains in the concrete reduction. -/
noncomputable def toScalarSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : CoordinateSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget where
  toScalarSolver := fun distinguisher =>
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.assemble
      (reduction.toTester distinguisher)
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  advantage_le := by
    intro distinguisher
    have hsuccess :=
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.one_sub_sum_coordinateGameError_le_scalarSuccess
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget (reduction.toTester distinguisher)
        (reduction.coordinateError distinguisher)
        (reduction.coordinateGameFailure_le distinguisher)
    have hsuccessReal := ENNReal.toReal_mono probOutput_ne_top hsuccess
    exact (reduction.advantage_le distinguisher).trans
      (add_le_add hsuccessReal le_rfl)

end CoordinateSecretReduction

/-! ## Executable candidate-check boundary -/

/-- The remaining reduction certificate expressed directly as public candidate checks.

For every distinguisher and scalar coordinate, `toCheck` transforms the public BRK+KSK context
according to a uniformly sampled candidate and invokes a Boolean check.  `gapLowerBound_le`
is the exact scheme-specific view-law obligation: the oriented acceptance gap between checking
the true bit and its complement must meet the stated bound.  The generic binary tester and union
bound turn these fields into `CoordinateSecretReduction` automatically.

`advantage_le` retains the global one-shot decision-to-search accounting.  This interface does
not amplify an averaged gap across repetitions sharing the same public context; the stronger
`PointwiseGapAmplificationReduction` below supplies the support-wise hypothesis needed for that. -/
structure CandidateCheckReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toCheck :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateCheck
        q degree ringRank tgswLevels lweDimension keySwitchLevels
  orientation :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → Bool
  gapLowerBound :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ℝ
  loss :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  gapLowerBound_le : ∀ distinguisher coordinate,
    gapLowerBound distinguisher coordinate ≤
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.candidateCheckGap
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget (orientation distinguisher)
        (toCheck distinguisher) coordinate
  advantage_le : ∀ distinguisher,
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget)
        distinguisher ≤
      (1 - ∑ coordinate,
        ENNReal.ofReal ((1 - gapLowerBound distinguisher coordinate) / 2)).toReal +
        loss distinguisher

/-- A candidate-check reduction with sound shared-context majority amplification.

For each distinguisher and coordinate, all repeated guesses reuse one sampled BRK+KSK context.
Consequently the base gap must be bounded below after fixing every hidden-bit/context pair in the
support of `coordinateSource`; an averaged `candidateCheckGap` does not suffice.  The generic
majority tree then checks the iterated coordinate error.  Only the final global
decision-to-search inequality remains scheme-specific. -/
structure PointwiseGapAmplificationReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toCheck :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateCheck
        q degree ringRank tgswLevels lweDimension keySwitchLevels
  orientation :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → Bool
  rounds :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ℕ
  gapLowerBound :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ℝ
  gapLowerBound_nonneg : ∀ distinguisher coordinate,
    0 ≤ gapLowerBound distinguisher coordinate
  pointwiseGapLowerBound_le : ∀ distinguisher coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateSource
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget coordinate) →
      gapLowerBound distinguisher coordinate ≤
        Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.pointwiseCandidateCheckGap
          (orientation distinguisher) (toCheck distinguisher) coordinate hiddenAndContext
  loss :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le : ∀ distinguisher,
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget)
        distinguisher ≤
      (1 - ∑ coordinate,
        FormalProof4FHE.MajorityAmplification.amplifiedError
          (rounds distinguisher coordinate)
          (ENNReal.ofReal ((1 - gapLowerBound distinguisher coordinate) / 2))).toReal +
        loss distinguisher

/-- Paper-aligned conditional shifted-view certificates with generic amplification accounting.

Unlike `PointwiseGapAmplificationReduction`, this certificate does not ask the concrete TFHE
construction to prove a separate global inequality.  Its effective conditional gap is the public
decision advantage minus the correct- and wrong-view smudging distances.  The adapter below
charges the sum of amplified coordinate errors as its loss, which makes the global inequality a
generic consequence of `publicAdvantage ≤ 1`.  A security application must still prove that this
explicit loss is negligible. -/
structure PointwiseCandidateViewTransformerReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toTransformer :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PointwiseCandidateViewTransformer
        (ringRank := ringRank) (lweDimension := lweDimension)
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        (CenteredBinomial.scalarSampler q keySwitchEta) tgswGadget keySwitchGadget
  rounds :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ℕ
  effectiveGap_nonneg : ∀ distinguisher coordinate,
    0 ≤ LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
            (RLWE.CenteredBinomial.sampler q degree ringEta)
            (CenteredBinomial.scalarSampler q keySwitchEta)
            tgswGadget keySwitchGadget)
          distinguisher -
        (toTransformer distinguisher).correctError coordinate -
        (toTransformer distinguisher).wrongError coordinate

/-- The narrower scheme-level certificate left after the generic one-shot proof.

`toTransformer` is the native shifted-evaluation/smudging construction: on a correct candidate its
output law is the real BRK+KSK view, while on a wrong candidate it is uniform-BRK plus real-KSK.
The exact coordinate error then follows automatically.  The final field records the resulting
one-shot global decision-to-search accounting.  It will normally be too weak for a multi-bit key;
a useful multi-run amplifier should instead construct an amplified `CandidateCheckReduction`. -/
structure CandidateViewTransformerReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toTransformer :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateViewTransformer
        (ringRank := ringRank) (lweDimension := lweDimension)
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta) tgswGadget keySwitchGadget
  loss :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le : ∀ distinguisher,
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget)
        distinguisher ≤
      (1 - ∑ _coordinate : Fin lweDimension,
        ENNReal.ofReal ((1 - LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
            (RLWE.CenteredBinomial.sampler q degree ringEta)
            (CenteredBinomial.scalarSampler q keySwitchEta)
            tgswGadget keySwitchGadget)
          distinguisher) / 2)).toReal + loss distinguisher

namespace CandidateCheckReduction

/-- Candidate checks induce the coordinatewise reduction with the exact gap-derived error
`ofReal ((1 - gapLowerBound) / 2)`. -/
noncomputable def toCoordinateSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : CandidateCheckReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    CoordinateSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget where
  toTester := fun distinguisher =>
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.testerOfCheck
      (reduction.orientation distinguisher) (reduction.toCheck distinguisher)
  coordinateError := fun distinguisher coordinate =>
    ENNReal.ofReal ((1 - reduction.gapLowerBound distinguisher coordinate) / 2)
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  coordinateGameFailure_le := by
    intro distinguisher coordinate
    exact Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateGame_testerOfCheck_failureProbability_le_of_gap
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget (reduction.orientation distinguisher)
      (reduction.toCheck distinguisher) coordinate
      (reduction.gapLowerBound distinguisher coordinate)
      (reduction.gapLowerBound_le distinguisher coordinate)
  advantage_le := reduction.advantage_le

/-- Candidate checks induce the scalar-secret reduction after the checked one-shot tester and
coordinate union bound. -/
noncomputable def toScalarSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : CandidateCheckReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget :=
  reduction.toCoordinateSecretReduction.toScalarSecretReduction

end CandidateCheckReduction

namespace PointwiseGapAmplificationReduction

/-- A support-wise candidate gap and the checked majority tree induce the coordinatewise
reduction with exact iterated-majority error bounds. -/
noncomputable def toCoordinateSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseGapAmplificationReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    CoordinateSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget where
  toTester := fun distinguisher =>
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.amplifiedTesterOfCheck
      (reduction.rounds distinguisher) (reduction.orientation distinguisher)
      (reduction.toCheck distinguisher)
  coordinateError := fun distinguisher coordinate =>
    FormalProof4FHE.MajorityAmplification.amplifiedError
      (reduction.rounds distinguisher coordinate)
      (ENNReal.ofReal ((1 - reduction.gapLowerBound distinguisher coordinate) / 2))
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  coordinateGameFailure_le := by
    intro distinguisher coordinate
    exact
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateGame_amplifiedTesterOfCheck_failureProbability_le_of_pointwiseGap
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget (reduction.rounds distinguisher)
        (reduction.orientation distinguisher) (reduction.toCheck distinguisher) coordinate
        (reduction.gapLowerBound distinguisher coordinate)
        (reduction.gapLowerBound_nonneg distinguisher coordinate)
        (reduction.pointwiseGapLowerBound_le distinguisher coordinate)
  advantage_le := reduction.advantage_le

/-- Chaining the checked shared-context amplifier and coordinate union bound gives scalar-secret
recovery. -/
noncomputable def toScalarSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseGapAmplificationReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget :=
  reduction.toCoordinateSecretReduction.toScalarSecretReduction

end PointwiseGapAmplificationReduction

namespace PointwiseCandidateViewTransformerReduction

/-- Conditional distinguishing gap left after both smudging/freshness errors. -/
noncomputable def effectiveGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget)
    (distinguisher : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels))
    (coordinate : Fin lweDimension) : ℝ :=
  LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget)
      distinguisher -
    (reduction.toTransformer distinguisher).correctError coordinate -
    (reduction.toTransformer distinguisher).wrongError coordinate

/-- Exact iterated-majority error assigned to one scalar coordinate. -/
noncomputable def amplifiedCoordinateError
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget)
    (distinguisher : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels))
    (coordinate : Fin lweDimension) : ENNReal :=
  FormalProof4FHE.MajorityAmplification.amplifiedError
    (reduction.rounds distinguisher coordinate)
    (ENNReal.ofReal ((1 - reduction.effectiveGap distinguisher coordinate) / 2))

/-- A conditional shifted-view certificate induces the generic pointwise-gap amplifier.  Its
loss is exactly the finite sum of amplified coordinate errors. -/
noncomputable def toPointwiseGapAmplificationReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    PointwiseGapAmplificationReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget where
  toCheck := fun distinguisher =>
    (reduction.toTransformer distinguisher).toCheck distinguisher
  orientation := fun distinguisher _ =>
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateViewTransformer.orientation
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget distinguisher
  rounds := reduction.rounds
  gapLowerBound := reduction.effectiveGap
  gapLowerBound_nonneg := reduction.effectiveGap_nonneg
  pointwiseGapLowerBound_le := by
    intro distinguisher coordinate hiddenAndContext hsupport
    unfold effectiveGap
    rw [← candidateDecisionAdvantage_eq_publicAdvantage]
    exact
      (reduction.toTransformer distinguisher).decisionAdvantage_sub_errors_le_pointwiseCandidateCheckGap
        distinguisher coordinate hiddenAndContext hsupport
  loss := fun distinguisher =>
    (∑ coordinate, reduction.amplifiedCoordinateError distinguisher coordinate).toReal
  loss_nonneg := fun _ => ENNReal.toReal_nonneg
  advantage_le := by
    intro distinguisher
    let errors : Fin lweDimension → ENNReal :=
      reduction.amplifiedCoordinateError distinguisher
    have herrors_le_one : ∀ coordinate, errors coordinate ≤ 1 := by
      intro coordinate
      apply FormalProof4FHE.MajorityAmplification.amplifiedError_le_one
      exact ENNReal.ofReal_le_one.mpr (by
        have hgap := reduction.effectiveGap_nonneg distinguisher coordinate
        change 0 ≤ reduction.effectiveGap distinguisher coordinate at hgap
        linarith)
    have hsum_ne_top : (∑ coordinate, errors coordinate) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun coordinate _ =>
        ne_top_of_le_ne_top ENNReal.one_ne_top (herrors_le_one coordinate)
    have hadv := LWE.AuxiliaryInput.SearchToDecision.publicAdvantage_le_one
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget)
      distinguisher
    have hone : (1 : ℝ) ≤
        (1 - ∑ coordinate, errors coordinate).toReal +
          (∑ coordinate, errors coordinate).toReal := by
      by_cases hsum : (∑ coordinate, errors coordinate) ≤ 1
      · rw [ENNReal.toReal_sub_of_le hsum ENNReal.one_ne_top, ENNReal.toReal_one]
        linarith
      · have honeSum : 1 ≤ ∑ coordinate, errors coordinate := le_of_not_ge hsum
        rw [tsub_eq_zero_of_le honeSum, ENNReal.toReal_zero, zero_add,
          ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono hsum_ne_top honeSum
    change LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget)
        distinguisher ≤
      (1 - ∑ coordinate, errors coordinate).toReal +
        (∑ coordinate, errors coordinate).toReal
    exact hadv.trans hone

/-- The paper-aligned conditional freshness certificate therefore gives scalar-secret recovery,
with the total amplified coordinate error exposed as the reduction loss. -/
noncomputable def toScalarSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchEta tgswGadget keySwitchGadget :=
  reduction.toPointwiseGapAmplificationReduction.toScalarSecretReduction

end PointwiseCandidateViewTransformerReduction

namespace CandidateViewTransformerReduction

/-- Exact candidate-view laws discharge all one-shot candidate-check fields.  Only the explicit
one-shot global inequality is carried through from `CandidateViewTransformerReduction`. -/
noncomputable def toCandidateCheckReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : CandidateViewTransformerReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    CandidateCheckReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget where
  toCheck := fun distinguisher => (reduction.toTransformer distinguisher).toCheck distinguisher
  orientation := fun distinguisher _ =>
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateViewTransformer.orientation
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget distinguisher
  gapLowerBound := fun distinguisher _ =>
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget)
      distinguisher
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  gapLowerBound_le := by
    intro distinguisher coordinate
    rw [← candidateDecisionAdvantage_eq_publicAdvantage]
    exact
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.candidateViewTransformer_gap_eq_decisionAdvantage
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget (reduction.toTransformer distinguisher)
        distinguisher coordinate).ge
  advantage_le := reduction.advantage_le

/-- A candidate-view transformer plus its explicit one-shot accounting induces the existing
coordinatewise reduction interface. -/
noncomputable def toCoordinateSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : CandidateViewTransformerReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    CoordinateSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget :=
  reduction.toCandidateCheckReduction.toCoordinateSecretReduction

/-- Chaining the one-shot tester and finite union bound produces the scalar-search certificate. -/
noncomputable def toScalarSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : CandidateViewTransformerReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget :=
  reduction.toCoordinateSecretReduction.toScalarSecretReduction

end CandidateViewTransformerReduction

/-- Once a concrete paired-secret reduction certificate is supplied, native search hardness
implies public auxiliary-input CircLWE decision hardness with exactly the certified additive
loss. -/
theorem publicHardAgainst_of_pairedSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reduction : PairedSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (decisionAllowed : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → Prop)
    (solverAllowed : LWE.AuxiliaryInput.Search.Solver
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Secret
        lweDimension ringRank degree)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : LWE.AuxiliaryInput.SearchToDecision.RealSearchHardAgainst
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.problem
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed (reduction.toSolver distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      reduction.loss distinguisher ≤ lossBound) :
    LWE.AuxiliaryInput.SearchToDecision.PublicHardAgainst
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      decisionAllowed (searchBound + lossBound) := by
  exact LWE.AuxiliaryInput.SearchToDecision.publicHardAgainst_of_reduction
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    reduction decisionAllowed solverAllowed searchBound lossBound
    hSearch hClosed hLoss

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.SearchToDecision
