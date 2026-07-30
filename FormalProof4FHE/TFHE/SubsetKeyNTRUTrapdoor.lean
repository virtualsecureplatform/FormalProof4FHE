/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SubsetKeyNTRUDualMode

/-!
# Hidden-NTRU Posterior Identity and the Public-Compiler Boundary

This module formalizes the additional finite claims in `sketch/proofNTRUtrapdoor.md`.

The hidden descriptor is revealed only in the information-theoretic lossiness experiment.  The
public coefficient distinguisher and the TFHE-to-HNF reduction remain descriptor-free by type.
The module proves:

* the exact equality between optimal recovery of the HNF auxiliary secret and optimal recovery
  of the entropic secret after revealing the complete structured descriptor;
* the exact joint coefficient hybrid induced by an HNF solver;
* the denominator-scaled DSPR/NTRU channel identity and its bijectivity;
* the primitive four-loss hidden-NTRU composition theorem; and
* the necessity of `L ∘ A = G` for every exact public affine KSK compiler.

No concrete full-view TFHE compiler or NTRU assumption is postulated here.  Those objects remain
explicit inputs to the conditional theorem.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.SubsetKeyNTRUTrapdoor

noncomputable section

open FormalProof4FHE.RLWE.RankOneHNFLossinessRLWENTRU
open FormalProof4FHE.TFHE.SubsetKeyNTRUDualMode

/-! ## Exact hidden-descriptor posterior identity -/

/-- The public HNF transcript together with the structured coefficient descriptor.  The
descriptor is part of this information-theoretic observation, not part of the public HNF search
problem. -/
structure RevealedHNFSide (R Row Leakage Descriptor : Type) where
  descriptor : Descriptor
  view : HNFView R Row Leakage

/-- Original presentation of the joint `(X, tau, H_a)` observation. -/
def revealedHNFObservationSampler
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage)) :
    ProbComp (R × RevealedHNFSide R Row Leakage Descriptor) := do
  let descriptorAndCoefficient ← family
  let state ← stateSampler
  let auxiliarySecret ← $ᵗ R
  return (auxiliarySecret,
    { descriptor := descriptorAndCoefficient.1
      view := realHNFView auxiliarySecret state descriptorAndCoefficient.2 })

/-- Canonical presentation in which the HNF anchor is sampled independently and
`X = anchor + S`. -/
def anchoredRevealedHNFObservationSampler
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage)) :
    ProbComp (R × RevealedHNFSide R Row Leakage Descriptor) := do
  let descriptorAndCoefficient ← family
  let state ← stateSampler
  let anchor ← $ᵗ R
  return (recoverAuxiliary anchor state.secret,
    { descriptor := descriptorAndCoefficient.1
      view := anchoredHNFView anchor state descriptorAndCoefficient.2 })

/-- Sampling `X` first or sampling the independent anchor first gives exactly the same joint
observation, including the hidden descriptor. -/
theorem revealedHNFObservationSampler_evalDist_eq_anchored
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage)) :
    evalDist (revealedHNFObservationSampler family stateSampler) =
      evalDist (anchoredRevealedHNFObservationSampler family stateSampler) := by
  unfold revealedHNFObservationSampler anchoredRevealedHNFObservationSampler
  refine evalDist_bind_congr'
    (show ProbComp (Descriptor × (Row → R)) from family)
    fun descriptorAndCoefficient ↦ ?_
  refine evalDist_bind_congr' stateSampler fun state ↦ ?_
  let realInput : R → R × RevealedHNFSide R Row Leakage Descriptor :=
    fun auxiliarySecret ↦
      (auxiliarySecret,
        { descriptor := descriptorAndCoefficient.1
          view := realHNFView auxiliarySecret state descriptorAndCoefficient.2 })
  let anchoredInput : R → R × RevealedHNFSide R Row Leakage Descriptor :=
    fun anchor ↦
      (recoverAuxiliary anchor state.secret,
        { descriptor := descriptorAndCoefficient.1
          view := anchoredHNFView anchor state descriptorAndCoefficient.2 })
  let translation : R ≃ R :=
    { toFun := fun auxiliarySecret ↦ auxiliarySecret - state.secret
      invFun := fun anchor ↦ anchor + state.secret
      left_inv := by intro auxiliarySecret; simp
      right_inv := by intro anchor; simp }
  have hUniform := evalDist_map_bijective_uniform_cross
    (α := R) (β := R)
    (fun auxiliarySecret : R ↦ auxiliarySecret - state.secret) translation.bijective
  have hMapped := evalDist_map_eq_of_evalDist_eq hUniform anchoredInput
  rw [Functor.map_map] at hMapped
  simpa only [Functor.map, bind_pure_comp, revealedHNFObservationSampler,
    anchoredRevealedHNFObservationSampler, realInput, anchoredInput,
    Function.comp_apply, anchoredHNFView_eq_realHNFView,
    recoverAuxiliary, sub_add_cancel] using hMapped

@[simp]
theorem recoverAuxiliary_sub_eq_iff
    {R : Type} [AddCommGroup R] (auxiliarySecret recovered secret : R) :
    recoverAuxiliary (auxiliarySecret - secret) recovered = auxiliarySecret ↔
      recovered = secret := by
  constructor
  · intro h
    apply add_left_cancel (a := auxiliarySecret - secret)
    simpa [recoverAuxiliary] using h
  · intro h
    subst recovered
    simp [recoverAuxiliary]

/-- Transfer of every estimator gives an inequality between operational conditional guessing
probabilities. -/
theorem conditionalGuessingProbability_le_of_estimatorTransfer
    {LeftSecret LeftSide RightSecret RightSide : Type}
    [DecidableEq LeftSecret] [DecidableEq RightSecret]
    (left : ProbComp (LeftSecret × LeftSide))
    (right : ProbComp (RightSecret × RightSide))
    (transfer : Estimator LeftSecret LeftSide → Estimator RightSecret RightSide)
    (hTransfer : ∀ estimator,
      guessingSuccess left estimator ≤ guessingSuccess right (transfer estimator)) :
    conditionalGuessingProbability left ≤ conditionalGuessingProbability right := by
  apply iSup_le
  intro estimator
  exact (hTransfer estimator).trans
    (le_iSup (fun candidate ↦ guessingSuccess right candidate) (transfer estimator))

/-- Rebuild the lossy entropic observation from a descriptor-carrying HNF view. -/
def RevealedHNFSide.toLossySide
    {R Row Leakage Descriptor : Type} [CommRing R]
    (side : RevealedHNFSide R Row Leakage Descriptor) :
    LossySide R Row Leakage Descriptor :=
  let eliminated := eliminateHNF side.view
  { leakage := eliminated.2.leakage
    descriptor := side.descriptor
    coefficient := eliminated.2.coefficient
    sample := eliminated.2.body }

@[simp]
theorem RevealedHNFSide.toLossySide_anchoredHNFView
    {R Row Leakage Descriptor : Type} [CommRing R]
    (descriptor : Descriptor) (anchor : R) (state : SourceState R Row Leakage)
    (coefficient : Row → R) :
    (RevealedHNFSide.toLossySide
      { descriptor := descriptor
        view := anchoredHNFView anchor state coefficient }) =
      { leakage := state.leakage
        descriptor := descriptor
        coefficient := coefficient
        sample := fun row ↦ coefficient row * state.secret + state.error row } := by
  simp [RevealedHNFSide.toLossySide, anchoredHNFView,
    entropicRLWEView]

@[simp]
theorem anchoredHNFView_anchor
    {R Row Leakage : Type} [CommRing R]
    (anchor : R) (state : SourceState R Row Leakage) (coefficient : Row → R) :
    (anchoredHNFView anchor state coefficient).anchor = anchor := rfl

/-- An estimator for `X` induces an estimator for `S`: sample the independent anchor, rebuild
the HNF transcript, and subtract the anchor from the recovered auxiliary secret. -/
def lossyEstimatorOfRevealedHNFEstimator
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    (estimator : Estimator R (RevealedHNFSide R Row Leakage Descriptor)) :
    Estimator R (LossySide R Row Leakage Descriptor) :=
  fun side ↦ do
    let anchor ← $ᵗ R
    let recovered ← estimator
      { descriptor := side.descriptor
        view := assembleHNF (anchor, side.toEntropicRLWEView) }
    return recoverEntropic anchor recovered

/-- An estimator for `S` induces an estimator for `X`: eliminate the public HNF anchor, estimate
the entropic secret, and add the anchor back. -/
def revealedHNFEstimatorOfLossyEstimator
    {R Row Leakage Descriptor : Type} [CommRing R]
    (estimator : Estimator R (LossySide R Row Leakage Descriptor)) :
    Estimator R (RevealedHNFSide R Row Leakage Descriptor) :=
  fun side ↦ do
    let recovered ← estimator side.toLossySide
    return recoverAuxiliary side.view.anchor recovered

/-- Every `X` estimator has exactly the same success probability as its induced `S` estimator. -/
theorem guessingSuccess_revealed_eq_lossy
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (estimator : Estimator R (RevealedHNFSide R Row Leakage Descriptor)) :
    guessingSuccess (revealedHNFObservationSampler family stateSampler) estimator =
      guessingSuccess (lossyObservationSampler family stateSampler)
        (lossyEstimatorOfRevealedHNFEstimator estimator) := by
  unfold guessingSuccess
  have hObservation :=
    revealedHNFObservationSampler_evalDist_eq_anchored family stateSampler
  calc
    Pr[= true | guessingGame (revealedHNFObservationSampler family stateSampler) estimator] =
        Pr[= true |
          guessingGame (anchoredRevealedHNFObservationSampler family stateSampler)
            estimator] := by
      apply probOutput_congr rfl
      unfold guessingGame
      rw [evalDist_bind, hObservation, ← evalDist_bind]
    _ = _ := by
      simp [guessingGame, anchoredRevealedHNFObservationSampler,
        lossyObservationSampler, lossyEstimatorOfRevealedHNFEstimator,
        LossySide.toEntropicRLWEView, anchoredHNFView, entropicRLWEView,
        recoverEntropic_eq_iff, bind_assoc]

/-- Every `S` estimator has exactly the same success probability as its induced `X` estimator. -/
theorem guessingSuccess_lossy_eq_revealed
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (estimator : Estimator R (LossySide R Row Leakage Descriptor)) :
    guessingSuccess (lossyObservationSampler family stateSampler) estimator =
      guessingSuccess (revealedHNFObservationSampler family stateSampler)
        (revealedHNFEstimatorOfLossyEstimator estimator) := by
  unfold guessingSuccess
  have hObservation :=
    revealedHNFObservationSampler_evalDist_eq_anchored family stateSampler
  calc
    Pr[= true | guessingGame (lossyObservationSampler family stateSampler) estimator] =
        Pr[= true |
          guessingGame (anchoredRevealedHNFObservationSampler family stateSampler)
            (revealedHNFEstimatorOfLossyEstimator estimator)] := by
      simp [guessingGame, anchoredRevealedHNFObservationSampler,
        lossyObservationSampler, revealedHNFEstimatorOfLossyEstimator,
        RevealedHNFSide.toLossySide_anchoredHNFView,
        recoverAuxiliary, bind_assoc]
      refine probOutput_bind_congr'
        (show ProbComp (Descriptor × (Row → R)) from family) true
        fun _ ↦ ?_
      refine probOutput_bind_congr' stateSampler true fun _ ↦ ?_
      simp
    _ = _ := by
      apply probOutput_congr rfl
      unfold guessingGame
      rw [evalDist_bind, ← hObservation, ← evalDist_bind]

/-- Exact posterior identity from the sketch:

`P_guess(X | tau, H_a) = P_guess(S | Lambda, tau, a, a*S+E)`.

No independence is required among the terminal errors or between those errors, the secret, and
the leakage. -/
theorem conditionalGuessingProbability_revealedHNF_eq_averageLossiness
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage)) :
    conditionalGuessingProbability
        (revealedHNFObservationSampler family stateSampler) =
      averageLossiness family stateSampler := by
  apply le_antisymm
  · exact conditionalGuessingProbability_le_of_estimatorTransfer
      (revealedHNFObservationSampler family stateSampler)
      (lossyObservationSampler family stateSampler)
      lossyEstimatorOfRevealedHNFEstimator
      (fun estimator ↦ (guessingSuccess_revealed_eq_lossy
        family stateSampler estimator).le)
  · exact conditionalGuessingProbability_le_of_estimatorTransfer
      (lossyObservationSampler family stateSampler)
      (revealedHNFObservationSampler family stateSampler)
      revealedHNFEstimatorOfLossyEstimator
      (fun estimator ↦ (guessingSuccess_lossy_eq_revealed
        family stateSampler estimator).le)

/-- Even an estimator that is given the hidden descriptor is bounded by the exact structured
conditional-lossiness quantity. -/
theorem guessingSuccess_revealedHNF_le_averageLossiness
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (estimator : Estimator R (RevealedHNFSide R Row Leakage Descriptor)) :
    guessingSuccess (revealedHNFObservationSampler family stateSampler) estimator ≤
      averageLossiness family stateSampler := by
  rw [← conditionalGuessingProbability_revealedHNF_eq_averageLossiness
    family stateSampler]
  exact guessingSuccess_le_conditionalGuessingProbability _ _

/-- The usual smoothing/bad-event/good-event certificate bounds posterior recovery even after
the NTRU descriptor is revealed. -/
theorem guessingSuccess_revealedHNF_le_sometimesLossyBound
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    {family : CoefficientFamily Descriptor R Row}
    {stateSampler : ProbComp (SourceState R Row Leakage)}
    (certificate : SometimesLossyCertificate family stateSampler)
    (estimator : Estimator R (RevealedHNFSide R Row Leakage Descriptor)) :
    guessingSuccess (revealedHNFObservationSampler family stateSampler) estimator ≤
      certificate.bound :=
  (guessingSuccess_revealedHNF_le_averageLossiness family stateSampler estimator).trans
    certificate.averageLossiness_le_bound

/-! ## Exact public coefficient hybrid and hidden-witness separation -/

/-- Success in the structured public-coefficient branch.  The descriptor is erased before the
coefficient tuple is passed to the solver-induced distinguisher. -/
noncomputable def structuredHNFRecoverySuccess
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) : ENNReal :=
  Pr[= true | publicCoefficientSampler family >>=
    coefficientRecoveryDistinguisher stateSampler solver]

/-- A public solver in the structured branch is bounded by lossiness with the hidden descriptor
revealed in the analysis. -/
theorem structuredHNFRecoverySuccess_le_averageLossiness
    {R Row Leakage Descriptor : Type} [CommRing R] [Fintype R] [SampleableType R]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    structuredHNFRecoverySuccess family stateSampler solver ≤
      averageLossiness family stateSampler :=
  lossyCoefficientRecovery_le_averageLossiness family stateSampler solver

/-- The induced coefficient advantage is exactly the absolute gap between uniform- and
structured-coefficient HNF recovery probabilities. -/
theorem coefficientRecoveryAdvantage_eq_abs_success_sub
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    coefficientRecoveryAdvantage family stateSampler solver =
      |(anchoredHNFSearchSuccess ($ᵗ (Row → R)) stateSampler solver).toReal -
        (structuredHNFRecoverySuccess family stateSampler solver).toReal| := by
  rfl

theorem coefficientRecoveryAdvantage_nonneg
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    0 ≤ coefficientRecoveryAdvantage family stateSampler solver := by
  rw [coefficientRecoveryAdvantage_eq_abs_success_sub]
  exact abs_nonneg _

/-- One-sided form of the exact coefficient hybrid. -/
theorem uniformHNFRecovery_le_structured_add_coefficientAdvantage
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    anchoredHNFSearchSuccess ($ᵗ (Row → R)) stateSampler solver ≤
      structuredHNFRecoverySuccess family stateSampler solver +
        ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler solver) := by
  exact ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
    (($ᵗ (Row → R)) >>= coefficientRecoveryDistinguisher stateSampler solver)
    (publicCoefficientSampler family >>=
      coefficientRecoveryDistinguisher stateSampler solver)

/-- Public computations depend only on the public coefficient marginal.  Changing the hidden
descriptor while preserving that marginal cannot change any public distinguisher's output law. -/
theorem publicCoefficient_bind_evalDist_eq_of_projection_eq
    {R Row LeftDescriptor RightDescriptor Output : Type}
    (left : CoefficientFamily LeftDescriptor R Row)
    (right : CoefficientFamily RightDescriptor R Row)
    (hProjection : evalDist (publicCoefficientSampler left) =
      evalDist (publicCoefficientSampler right))
    (publicAlgorithm : (Row → R) → ProbComp Output) :
    evalDist (publicCoefficientSampler left >>= publicAlgorithm) =
      evalDist (publicCoefficientSampler right >>= publicAlgorithm) := by
  rw [evalDist_bind, hProjection, ← evalDist_bind]

/-- Specialization of descriptor erasure to the HNF recovery distinguisher. -/
theorem structuredHNFRecoverySuccess_eq_of_publicProjection_eq
    {R Row Leakage LeftDescriptor RightDescriptor : Type}
    [CommRing R] [Fintype R] [SampleableType R] [DecidableEq R]
    (left : CoefficientFamily LeftDescriptor R Row)
    (right : CoefficientFamily RightDescriptor R Row)
    (hProjection : evalDist (publicCoefficientSampler left) =
      evalDist (publicCoefficientSampler right))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : HNFSolver R Row Leakage) :
    structuredHNFRecoverySuccess left stateSampler solver =
      structuredHNFRecoverySuccess right stateSampler solver := by
  unfold structuredHNFRecoverySuccess
  exact probOutput_congr rfl
    (publicCoefficient_bind_evalDist_eq_of_projection_eq left right hProjection
      (coefficientRecoveryDistinguisher stateSampler solver))

/-! ## Explicit coordinatewise DSPR/NTRU channel -/

/-- A coordinatewise short-ratio witness `a_j = f_j⁻¹ h_j`.  It permits independent
denominators; the existing rank-one NTRU theorem is recovered by taking every denominator equal. -/
structure CoordinateRatioWitness (R Row : Type) [CommRing R] where
  denominator : Row → R
  inverse : Row → R
  numerator : Row → R
  inverse_mul_denominator : ∀ row, inverse row * denominator row = 1

def CoordinateRatioWitness.coefficient
    {R Row : Type} [CommRing R] (witness : CoordinateRatioWitness R Row) : Row → R :=
  fun row ↦ witness.inverse row * witness.numerator row

/-- Multiply each public channel coordinate by its hidden denominator. -/
def CoordinateRatioWitness.scale
    {R Row : Type} [CommRing R] (witness : CoordinateRatioWitness R Row)
    (sample : Row → R) : Row → R :=
  fun row ↦ witness.denominator row * sample row

/-- Denominator scaling is a bijection when every hidden denominator has the supplied inverse. -/
theorem CoordinateRatioWitness.scale_bijective
    {R Row : Type} [CommRing R] (witness : CoordinateRatioWitness R Row) :
    Function.Bijective witness.scale := by
  let inverseScale : (Row → R) → (Row → R) :=
    fun sample row ↦ witness.inverse row * sample row
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨inverseScale, ?_, ?_⟩
  · intro sample
    funext row
    simp [CoordinateRatioWitness.scale, inverseScale, ← mul_assoc,
      witness.inverse_mul_denominator]
  · intro sample
    funext row
    have hInverse : witness.denominator row * witness.inverse row = 1 := by
      simpa [mul_comm] using witness.inverse_mul_denominator row
    simp [CoordinateRatioWitness.scale, inverseScale, ← mul_assoc, hInverse]

/-- Exact hidden DSPR channel:
`f_j * (a_j*S + E_j) = h_j*S + f_j*E_j`. -/
theorem CoordinateRatioWitness.scale_coefficientChannel
    {R Row : Type} [CommRing R] (witness : CoordinateRatioWitness R Row)
    (secret : R) (error : Row → R) :
    witness.scale (fun row ↦ witness.coefficient row * secret + error row) =
      fun row ↦ witness.numerator row * secret + witness.denominator row * error row := by
  funext row
  have hInverse : witness.denominator row * witness.inverse row = 1 := by
    simpa [mul_comm] using witness.inverse_mul_denominator row
  simp only [CoordinateRatioWitness.scale, CoordinateRatioWitness.coefficient]
  calc
    witness.denominator row *
          ((witness.inverse row * witness.numerator row) * secret + error row) =
        (witness.denominator row * witness.inverse row) *
            witness.numerator row * secret + witness.denominator row * error row := by
      ring
    _ = witness.numerator row * secret + witness.denominator row * error row := by
      rw [hInverse, one_mul]

/-- The masked numerator gives the exact hidden channel from the sketch. -/
theorem denominator_mul_maskedRatioChannel
    {R : Type} [CommRing R] (denominator numerator inverse first second secret error : R)
    (hInverse : inverse * denominator = 1) :
    denominator *
        ((inverse * maskedNumerator denominator numerator first second) * secret + error) =
      maskedNumerator denominator numerator first second * secret + denominator * error := by
  have hInverse' : denominator * inverse = 1 := by
    simpa [mul_comm] using hInverse
  calc
    denominator *
          ((inverse * maskedNumerator denominator numerator first second) * secret + error) =
        (denominator * inverse) *
            maskedNumerator denominator numerator first second * secret +
          denominator * error := by
      ring
    _ = maskedNumerator denominator numerator first second * secret +
          denominator * error := by
      rw [hInverse', one_mul]

/-! ## Primitive four-loss composition -/

theorem averageLossiness_ne_top
    {R Row Leakage Descriptor : Type} [CommRing R] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage)) :
    averageLossiness family stateSampler ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (conditionalGuessingProbability_le_one (lossyObservationSampler family stateSampler))

/-- Direct HNF recovery bound before any analytic or computational bound is substituted. -/
theorem hnfRecovery_successProbability_le_coefficientAdvantage_add_averageLossiness
    {R Row Leakage Descriptor : Type} [CommRing R]
    [Fintype R] [SampleableType R] [Fintype Row] [SampleableType (Row → R)]
    [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : SearchSolver R (HNFView R Row Leakage) Unit) :
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (hnfRecoveryProblem stateSampler) solver ≤
      ENNReal.ofReal
          (coefficientRecoveryAdvantage family stateSampler (asHNFSolver solver)) +
        averageLossiness family stateSampler := by
  rw [hnfRecovery_successProbability_eq]
  exact realUniformHNFRecovery_le_coefficientAdvantage_add_averageLossiness
    family stateSampler (asHNFSolver solver)

/-- The complete public decision advantage is bounded by the primitive coefficient hybrid,
conditional lossiness, and compiler loss. -/
theorem publicAdvantage_le_coefficientAdvantage_add_averageLossiness_add_reductionLoss
    {DecisionSecret Challenge Auxiliary R Row Leakage Descriptor : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary)
    (reduction : DualModeReduction decisionProblem stateSampler)
    (distinguisher : PublicDistinguisher Challenge Auxiliary) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        decisionProblem distinguisher ≤
      (ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler
          (asHNFSolver (reduction.toSolver distinguisher))) +
        averageLossiness family stateSampler).toReal +
          reduction.loss distinguisher := by
  have hProbability :=
    hnfRecovery_successProbability_le_coefficientAdvantage_add_averageLossiness
      family stateSampler (reduction.toSolver distinguisher)
  have hFinite :
      ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler
          (asHNFSolver (reduction.toSolver distinguisher))) +
          averageLossiness family stateSampler ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      averageLossiness_ne_top family stateSampler⟩
  exact (reduction.advantage_le distinguisher).trans
    (add_le_add (ENNReal.toReal_mono hFinite hProbability) le_rfl)

/-- Conditional hidden-NTRU composition directly from the four primitive terms. -/
theorem kdmAdvantage_le_coefficientAdvantage_add_averageLossiness_add_reductionLoss_add_zero
    {DecisionSecret Challenge Auxiliary R Row Leakage Descriptor : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary)
    (reduction : DualModeReduction decisionProblem stateSampler)
    (distinguisher : PublicDistinguisher Challenge Auxiliary)
    (zeroBound : ℝ)
    (hZero : FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage decisionProblem
      (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
        distinguisher) ≤ zeroBound) :
    FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage decisionProblem
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          distinguisher) ≤
      ((ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler
          (asHNFSolver (reduction.toSolver distinguisher))) +
        averageLossiness family stateSampler).toReal + reduction.loss distinguisher) +
          zeroBound := by
  exact
    (FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage_le_circularLwe_add_zeroLwe
      decisionProblem
      (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
        distinguisher)).trans
      (add_le_add
        (publicAdvantage_le_coefficientAdvantage_add_averageLossiness_add_reductionLoss
          family stateSampler decisionProblem reduction distinguisher)
        hZero)

/-- The four named real losses appear exactly once.  This is Theorem 3 of the sketch in its
pointwise, certificate-free form. -/
theorem kdmAdvantage_le_hiddenNTRU_four_losses
    {DecisionSecret Challenge Auxiliary R Row Leakage Descriptor : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (family : CoefficientFamily Descriptor R Row)
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary)
    (reduction : DualModeReduction decisionProblem stateSampler)
    (distinguisher : PublicDistinguisher Challenge Auxiliary)
    (coefficientBound lossinessBound zeroBound : ℝ)
    (hCoefficient : coefficientRecoveryAdvantage family stateSampler
      (asHNFSolver (reduction.toSolver distinguisher)) ≤ coefficientBound)
    (hLossiness : (averageLossiness family stateSampler).toReal ≤ lossinessBound)
    (hZero : FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage decisionProblem
      (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
        distinguisher) ≤ zeroBound) :
    FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage decisionProblem
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          distinguisher) ≤
      ((coefficientBound + lossinessBound) + reduction.loss distinguisher) + zeroBound := by
  have hCoefficientNonneg := coefficientRecoveryAdvantage_nonneg family stateSampler
    (asHNFSolver (reduction.toSolver distinguisher))
  have hLossinessFinite := averageLossiness_ne_top family stateSampler
  have hToReal :
      (ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler
          (asHNFSolver (reduction.toSolver distinguisher))) +
        averageLossiness family stateSampler).toReal =
      coefficientRecoveryAdvantage family stateSampler
          (asHNFSolver (reduction.toSolver distinguisher)) +
        (averageLossiness family stateSampler).toReal := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hLossinessFinite,
      ENNReal.toReal_ofReal hCoefficientNonneg]
  calc
    _ ≤ ((ENNReal.ofReal (coefficientRecoveryAdvantage family stateSampler
            (asHNFSolver (reduction.toSolver distinguisher))) +
          averageLossiness family stateSampler).toReal + reduction.loss distinguisher) +
        zeroBound :=
      kdmAdvantage_le_coefficientAdvantage_add_averageLossiness_add_reductionLoss_add_zero
        family stateSampler decisionProblem reduction distinguisher zeroBound hZero
    _ = ((coefficientRecoveryAdvantage family stateSampler
            (asHNFSolver (reduction.toSolver distinguisher)) +
          (averageLossiness family stateSampler).toReal) + reduction.loss distinguisher) +
        zeroBound := by rw [hToReal]
    _ ≤ ((coefficientBound + lossinessBound) + reduction.loss distinguisher) +
        zeroBound := by gcongr

/-! ## Necessity of the affine KSK factorization -/

/-- Exact correctness of a public affine compiler on every noiseless source input is equivalent
to equality of its public offsets together with the constrained batch equation `L ∘ A = G`. -/
theorem affineNoiselessCorrect_iff_offsets_eq_and_factorization
    {R V W T : Type} [Semiring R]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W]
    [AddCommGroup T] [Module R T]
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (postprocess : W →ₗ[R] T) (sourceOffset targetOffset : T) :
    (∀ secret, sourceOffset + postprocess (source secret) =
        targetOffset + gadget secret) ↔
      sourceOffset = targetOffset ∧ postprocess.comp source = gadget := by
  constructor
  · intro hCorrect
    have hOffset : sourceOffset = targetOffset := by
      simpa using hCorrect 0
    refine ⟨hOffset, ?_⟩
    apply LinearMap.ext
    intro secret
    apply add_left_cancel (a := targetOffset)
    simpa [hOffset] using hCorrect secret
  · rintro ⟨hOffset, hFactorization⟩ secret
    have hValue := DFunLike.congr_fun hFactorization secret
    simpa [hOffset] using congrArg (fun value ↦ targetOffset + value) hValue

/-- Proposition 5 of the sketch: every exact affine compiler produces a public constrained
factorization certificate. -/
def factorizationOfAffineNoiselessCorrect
    {R V W T : Type} [Semiring R]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W]
    [AddCommGroup T] [Module R T]
    (source : V →ₗ[R] W) (gadget : V →ₗ[R] T)
    (postprocess : W →ₗ[R] T) (sourceOffset targetOffset : T)
    (hCorrect : ∀ secret, sourceOffset + postprocess (source secret) =
      targetOffset + gadget secret) :
    FormalProof4FHE.TFHE.JointSubsetKeyBRK.Factorization source gadget where
  postprocess := postprocess
  postprocess_comp :=
    (affineNoiselessCorrect_iff_offsets_eq_and_factorization source gadget postprocess
      sourceOffset targetOffset).mp hCorrect |>.2

end

end FormalProof4FHE.TFHE.SubsetKeyNTRUTrapdoor
