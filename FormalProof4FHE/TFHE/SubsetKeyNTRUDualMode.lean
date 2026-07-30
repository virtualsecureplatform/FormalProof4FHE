/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessRLWENTRU
import FormalProof4FHE.TFHE.JointSubsetKeyBRK

/-!
# NTRU Lossy Dual-Mode Boundary for Subset-Key TFHE

This module supplies the technical composition layer between the rank-one HNF lossiness
theorems and an auxiliary-input TFHE decision problem.  It deliberately does not give a public
short-preimage algorithm and never invokes LWE after revealing an NTRU descriptor.

The rank-one HNF experiment is first packaged as an ordinary exact-recovery problem.  Its public
challenge is

`b0 = X - S`, `d j = a j * X + E j`,

with the complete correlated leakage retained in the challenge.  Search success for this
problem is exactly the success probability already bounded by
`RankOneHNFLossinessRLWENTRU.HNFHardAgainst`.

A concrete TFHE application supplies a checked cross-distribution reduction from its complete
public decision problem to this HNF recovery problem.  The generic theorem then composes:

* real-versus-zero through the common uniform endpoint;
* the checked decision-to-HNF-search reduction;
* joint NTRU/DSPR coefficient pseudorandomness and conditional HNF lossiness; and
* the remaining zero-message-versus-uniform bound.

The resulting bound is conditional but non-circular.  The hidden NTRU descriptor occurs only in
the lossiness theorem.  It is neither public auxiliary input nor an input to an LWE adversary.
The concrete TFHE-to-HNF compiler, the analytic Gaussian-lossiness certificate, and the named
NTRU/DSPR assumption remain explicit premises.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.SubsetKeyNTRUDualMode

noncomputable section

open FormalProof4FHE.RLWE.RankOneHNFLossinessRLWENTRU

abbrev PublicDistinguisher (Challenge Auxiliary : Type) :=
  FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
    Challenge Auxiliary

abbrev SearchProblem (Secret Challenge Auxiliary : Type) :=
  FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem Secret Challenge Auxiliary

abbrev SearchSolver (Secret Challenge Auxiliary : Type) :=
  FormalProof4FHE.LWE.AuxiliaryInput.Search.Solver Secret Challenge Auxiliary

/-! ## The rank-one HNF experiment as an exact-recovery problem -/

/-- Exact recovery of the uniform HNF auxiliary secret `X`.  The sampled source state retains
the entropic secret, every terminal error, and arbitrary correlated public leakage. -/
def hnfRecoveryProblem
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (Row → R)] [DecidableEq R]
    (stateSampler : ProbComp (SourceState R Row Leakage)) :
    SearchProblem R (HNFView R Row Leakage) Unit where
  sampleSecret := $ᵗ R
  sampleChallenge := fun auxiliarySecret ↦ do
    let coefficient ← $ᵗ (Row → R)
    let state ← stateSampler
    return realHNFView auxiliarySecret state coefficient
  sampleAuxiliary := fun _ ↦ pure ()
  verify := fun auxiliarySecret recovered ↦ decide (recovered = auxiliarySecret)

/-- Forget the trivial auxiliary input of the exact-recovery problem. -/
def asHNFSolver
    {R Row Leakage : Type}
    (solver : SearchSolver R (HNFView R Row Leakage) Unit) :
    HNFSolver R Row Leakage :=
  fun view ↦ solver view ()

/-- The packaged exact-recovery experiment has exactly the original HNF search law.  The only
reordering is among the independently sampled auxiliary secret, coefficient vector, and complete
source state. -/
theorem hnfRecovery_successProbability_eq
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (solver : SearchSolver R (HNFView R Row Leakage) Unit) :
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (hnfRecoveryProblem stateSampler) solver =
      Pr[= true |
        realHNFSearchGame ($ᵗ (Row → R)) stateSampler (asHNFSolver solver)] := by
  unfold FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
    FormalProof4FHE.LWE.AuxiliaryInput.Search.game hnfRecoveryProblem
    realHNFSearchGame asHNFSolver
  simp only [bind_assoc, pure_bind]
  rw [probOutput_bind_bind_swap ($ᵗ R) ($ᵗ (Row → R))]
  refine probOutput_bind_congr' ($ᵗ (Row → R)) true fun coefficient ↦ ?_
  exact probOutput_bind_bind_swap ($ᵗ R) stateSampler
    (fun auxiliarySecret state ↦ do
      let recovered ← solver (realHNFView auxiliarySecret state coefficient) ()
      return decide (recovered = auxiliarySecret)) true

/-- An `ENNReal` HNF-hardness statement gives the real-valued exact-recovery bound consumed by
the decision-to-search layer. -/
theorem hnfRecovery_toReal_le
    {R Row Leakage : Type} [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    {stateSampler : ProbComp (SourceState R Row Leakage)}
    {allowed : HNFSolver R Row Leakage → Prop} {bound : ENNReal}
    (hardness : HNFHardAgainst stateSampler allowed bound)
    (solver : SearchSolver R (HNFView R Row Leakage) Unit)
    (hAllowed : allowed (asHNFSolver solver))
    (hBound : bound ≠ ⊤) :
    (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
      (hnfRecoveryProblem stateSampler) solver).toReal ≤ bound.toReal := by
  rw [hnfRecovery_successProbability_eq]
  exact ENNReal.toReal_mono hBound (hardness (asHNFSolver solver) hAllowed)

/-! ## Generic dual-mode composition -/

/-- A checked reduction from a complete public decision problem to rank-one HNF recovery.

This is the exact boundary at which a concrete TFHE normalization must be installed.  Its
`advantage_le` field includes all shifted-evaluation, mode-switch, candidate-estimation, and
amplification losses.  In particular, public-matrix indistinguishability alone is not enough to
construct this object. -/
abbrev DualModeReduction
    {DecisionSecret Challenge Auxiliary R Row Leakage : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary)
    (stateSampler : ProbComp (SourceState R Row Leakage)) :=
  FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.HeterogeneousCrossReduction
    decisionProblem (hnfRecoveryProblem stateSampler)

/-- Search hardness of the HNF source transfers through a checked dual-mode reduction to the
complete public decision problem. -/
theorem publicAdvantage_le_hnf_add_reductionLoss
    {DecisionSecret Challenge Auxiliary R Row Leakage : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    {decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary}
    {stateSampler : ProbComp (SourceState R Row Leakage)}
    {allowed : HNFSolver R Row Leakage → Prop} {bound : ENNReal}
    (hardness : HNFHardAgainst stateSampler allowed bound)
    (reduction : DualModeReduction decisionProblem stateSampler)
    (distinguisher : PublicDistinguisher Challenge Auxiliary)
    (hAllowed : allowed (asHNFSolver (reduction.toSolver distinguisher)))
    (hBound : bound ≠ ⊤) :
    FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        decisionProblem distinguisher ≤
      bound.toReal + reduction.loss distinguisher := by
  exact (reduction.advantage_le distinguisher).trans
    (add_le_add
      (hnfRecovery_toReal_le hardness (reduction.toSolver distinguisher) hAllowed hBound)
      le_rfl)

/-- Real-versus-zero security follows through the common uniform endpoint.  The first term is
bounded by HNF lossiness; the second is the genuine zero-message-versus-uniform problem and is
not silently identified with ordinary LWE in the presence of arbitrary auxiliary leakage. -/
theorem kdmAdvantage_le_hnf_add_reductionLoss_add_zero
    {DecisionSecret Challenge Auxiliary R Row Leakage : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    {decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary}
    {stateSampler : ProbComp (SourceState R Row Leakage)}
    {allowed : HNFSolver R Row Leakage → Prop} {bound : ENNReal}
    (hardness : HNFHardAgainst stateSampler allowed bound)
    (reduction : DualModeReduction decisionProblem stateSampler)
    (distinguisher : PublicDistinguisher Challenge Auxiliary)
    (hAllowed : allowed (asHNFSolver (reduction.toSolver distinguisher)))
    (hBound : bound ≠ ⊤)
    (zeroBound : ℝ)
    (hZero : FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage decisionProblem
      (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
        distinguisher) ≤ zeroBound) :
    FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage decisionProblem
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          distinguisher) ≤
      (bound.toReal + reduction.loss distinguisher) + zeroBound := by
  exact
    (FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage_le_circularLwe_add_zeroLwe
      decisionProblem
      (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
        distinguisher)).trans
      (add_le_add
        (publicAdvantage_le_hnf_add_reductionLoss hardness reduction distinguisher
          hAllowed hBound)
        hZero)

/-! ## Direct NTRU/DSPR instantiations -/

/-- The direct joint-ratio NTRU theorem, composed all the way to an arbitrary complete public
real-versus-zero decision problem.  All genuinely analytic or cryptographic inputs remain the
named premises of the existing HNF theorem. -/
theorem kdmAdvantage_le_jointNTRU_add_reductionLoss_add_zero
    {DecisionSecret Challenge Auxiliary R Row Leakage : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (witnessSampler : ProbComp (SmallRatioWitness R Row))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (allowedSolver : HNFSolver R Row Leakage → Prop)
    (allowedCoefficientDistinguisher : ((Row → R) → ProbComp Bool) → Prop)
    (coefficientBound : ℝ)
    (gaussian : SmallRatioGaussianCertificate
      (smallRatioFamily witnessSampler) stateSampler)
    (hJointRatio : CoefficientPseudorandomAgainst (smallRatioFamily witnessSampler)
      allowedCoefficientDistinguisher coefficientBound)
    (hClosure : ∀ solver, allowedSolver solver →
      allowedCoefficientDistinguisher
        (coefficientRecoveryDistinguisher stateSampler solver))
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary)
    (reduction : DualModeReduction decisionProblem stateSampler)
    (distinguisher : PublicDistinguisher Challenge Auxiliary)
    (hAllowed : allowedSolver (asHNFSolver (reduction.toSolver distinguisher)))
    (zeroBound : ℝ)
    (hZero : FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage decisionProblem
      (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
        distinguisher) ≤ zeroBound) :
    FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage decisionProblem
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          distinguisher) ≤
      ((ENNReal.ofReal coefficientBound + gaussian.sometimesLossy.bound).toReal +
          reduction.loss distinguisher) + zeroBound := by
  let hardness := jointNTRURatio_hnfHardAgainst witnessSampler stateSampler
    allowedSolver allowedCoefficientDistinguisher coefficientBound gaussian
    hJointRatio hClosure
  apply kdmAdvantage_le_hnf_add_reductionLoss_add_zero hardness reduction distinguisher
    hAllowed
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, gaussian.sometimesLossy.bound_ne_top⟩
  · exact hZero

/-- The masked single-ratio DSPR/NTRU-plus-Hermite variant of the same complete composition. -/
theorem kdmAdvantage_le_maskedNTRU_add_reductionLoss_add_zero
    {DecisionSecret Challenge Auxiliary R Row Leakage RatioDescriptor : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Row] [SampleableType (Row → R)] [DecidableEq R]
    (ratioFamily : ProbComp (RatioDescriptor × R))
    (referenceRatioSampler : ProbComp R)
    (maskSampler : ProbComp (Row → R × R))
    (stateSampler : ProbComp (SourceState R Row Leakage))
    (allowedSolver : HNFSolver R Row Leakage → Prop)
    (allowedCoefficientDistinguisher : ((Row → R) → ProbComp Bool) → Prop)
    (gaussian : SmallRatioGaussianCertificate
      (maskedRatioFamily ratioFamily maskSampler) stateSampler)
    (hybrid : MaskedRatioHybridCertificate (publicRatioSampler ratioFamily)
      referenceRatioSampler maskSampler allowedCoefficientDistinguisher)
    (hClosure : ∀ solver, allowedSolver solver →
      allowedCoefficientDistinguisher
        (coefficientRecoveryDistinguisher stateSampler solver))
    (decisionProblem : FormalProof4FHE.LWE.AuxiliaryInput.Problem
      DecisionSecret Challenge Auxiliary)
    (reduction : DualModeReduction decisionProblem stateSampler)
    (distinguisher : PublicDistinguisher Challenge Auxiliary)
    (hAllowed : allowedSolver (asHNFSolver (reduction.toSolver distinguisher)))
    (zeroBound : ℝ)
    (hZero : FormalProof4FHE.LWE.AuxiliaryInput.zeroLweAdvantage decisionProblem
      (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
        distinguisher) ≤ zeroBound) :
    FormalProof4FHE.LWE.AuxiliaryInput.kdmAdvantage decisionProblem
        (FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicContinuation
          distinguisher) ≤
      ((ENNReal.ofReal (hybrid.ratioBound + hybrid.hermiteBound) +
          gaussian.sometimesLossy.bound).toReal + reduction.loss distinguisher) +
        zeroBound := by
  let hardness := dsprNTRUStyle_hnfHardAgainst ratioFamily referenceRatioSampler
    maskSampler stateSampler allowedSolver allowedCoefficientDistinguisher gaussian
    hybrid hClosure
  apply kdmAdvantage_le_hnf_add_reductionLoss_add_zero hardness reduction distinguisher
    hAllowed
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, gaussian.sometimesLossy.bound_ne_top⟩
  · exact hZero

end

end FormalProof4FHE.TFHE.SubsetKeyNTRUDualMode
