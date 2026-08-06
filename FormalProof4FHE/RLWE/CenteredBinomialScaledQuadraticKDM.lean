/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomial
import FormalProof4FHE.RLWE.QuadraticKDM

/-!
# Centered-Binomial Fixed-Gadget Quadratic KDM

This file instantiates the factorized fixed-gadget compiler with executable centered-binomial
ring errors.  For public factors `alpha` and `beta` satisfying

`sum_r alpha j r * beta j r = g_j`,

the proof-only source publishes the two leakage families

`alpha j r * S + F_jr` and `beta j r * S + G_jr`.

The correlated source error is `sum_r F_jr * G_jr + E_j`.  The checked public compiler produces
the standard BFV/BGV relinearization row

`(A_j, A_j*S + g_j*S^2 + E_j)`.

In particular, the product of the two CBD errors is confined to the source problem.  It is not
multiplied by the gadget weight in the final evaluation-key error.  The exact game theorem below
reduces the complete joint scaled-square batch to that named correlated source problem plus the
ordinary zero-message endpoint.  It deliberately does not assert that the correlated source is
ordinary RLWE; bounding that source advantage is the remaining cryptographic obligation.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.CenteredBinomialScaledQuadraticKDM

noncomputable section

open QuadraticKDM

/- Use the executable negacyclic-ring structure selected by the CBD development. -/
local instance cbdRqCommRing (q degree : ℕ) : CommRing (Rq q degree) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree

/- Keep the concrete row sampler definitionally aligned with the generic fixed-gadget compiler.
Both available instances implement the uniform law, but exact game equalities must use the same
sampler term on both sides. -/
noncomputable local instance cbdRowSampleable (q degree rows : ℕ) [NeZero q] :
    SampleableType (Fin rows → Rq q degree) :=
  instSampleableTypePiFintype

/-! ## Executable independent CBD latent families -/

/-- Independently sample one executable CBD ring element for every row/factor pair. -/
def cbdErrorFamilySampler
    (q degree rows factors eta : ℕ) [NeZero q] :
    ProbComp (Fin rows → Fin factors → Rq q degree) :=
  Fin.mOfFn rows fun _row ↦
    Fin.mOfFn factors fun _factor ↦
      CenteredBinomial.sampler q degree eta

/-- Independently sample the narrow final error in every evaluation-key row. -/
def cbdFinalErrorSampler
    (q degree rows eta : ℕ) [NeZero q] :
    ProbComp (Fin rows → Rq q degree) :=
  Fin.mOfFn rows fun _row ↦ CenteredBinomial.sampler q degree eta

/-- A concrete latent value used by the fixed-gadget compiler. -/
def latentValue
    {R Row Factor : Type}
    (secret : R) (firstError secondError : Row → Factor → R)
    (finalError : Row → R) : QuadraticKDM.Latent R Row Factor where
  secret := secret
  firstError := firstError
  secondError := secondError
  finalError := finalError

/-- Sample the secret, two mutually independent executable CBD error families, and the desired
final evaluation-key error independently. -/
def cbdLatentSampler
    (q degree rows factors eta : ℕ) [NeZero q]
    (secretSampler : ProbComp (Rq q degree))
    (finalErrorSampler : ProbComp (Fin rows → Rq q degree)) :
    ProbComp (QuadraticKDM.Latent (Rq q degree) (Fin rows) (Fin factors)) := do
  let secret ← secretSampler
  let firstError ← cbdErrorFamilySampler q degree rows factors eta
  let secondError ← cbdErrorFamilySampler q degree rows factors eta
  let finalError ← finalErrorSampler
  return latentValue secret firstError secondError finalError

/-- The fully executable specialization: both proof-only hint errors have width `hintEta`, and
the final BFV/BGV evaluation-key errors have the independently selectable width `finalEta`. -/
def fullyCBDLatentSampler
    (q degree rows factors hintEta finalEta : ℕ) [NeZero q]
    (secretSampler : ProbComp (Rq q degree)) :
    ProbComp (QuadraticKDM.Latent (Rq q degree) (Fin rows) (Fin factors)) :=
  cbdLatentSampler q degree rows factors hintEta secretSampler
    (cbdFinalErrorSampler q degree rows finalEta)

/-- Every finite family of executable CBD samples is total. -/
@[simp]
theorem cbdErrorFamilySampler_probFailure
    (q degree rows factors eta : ℕ) [NeZero q] :
    Pr[⊥ | cbdErrorFamilySampler q degree rows factors eta] = 0 := by
  apply FormalProof4FHE.FiniteProduct.probFailure_fin_mOfFn_eq_zero
  intro row
  apply FormalProof4FHE.FiniteProduct.probFailure_fin_mOfFn_eq_zero
  intro factor
  simp [CenteredBinomial.sampler]

/-- Every finite family of final executable CBD errors is total. -/
@[simp]
theorem cbdFinalErrorSampler_probFailure
    (q degree rows eta : ℕ) [NeZero q] :
    Pr[⊥ | cbdFinalErrorSampler q degree rows eta] = 0 := by
  apply FormalProof4FHE.FiniteProduct.probFailure_fin_mOfFn_eq_zero
  intro row
  simp [CenteredBinomial.sampler]

/-- The complete CBD latent sampler is total whenever the supplied secret and final-error
samplers are total. -/
theorem cbdLatentSampler_probFailure
    (q degree rows factors eta : ℕ) [NeZero q]
    (secretSampler : ProbComp (Rq q degree))
    (finalErrorSampler : ProbComp (Fin rows → Rq q degree))
    (hSecret : Pr[⊥ | secretSampler] = 0)
    (hFinal : Pr[⊥ | finalErrorSampler] = 0) :
    Pr[⊥ | cbdLatentSampler q degree rows factors eta
      secretSampler finalErrorSampler] = 0 := by
  have hSecretNeverFails : NeverFail secretSampler :=
    NeverFail.of_probFailure_eq_zero _ hSecret
  have hErrorsNeverFail : NeverFail
      (cbdErrorFamilySampler q degree rows factors eta) :=
    NeverFail.of_probFailure_eq_zero _
      (cbdErrorFamilySampler_probFailure q degree rows factors eta)
  have hFinalNeverFails : NeverFail finalErrorSampler :=
    NeverFail.of_probFailure_eq_zero _ hFinal
  have hLatent : NeverFail
      (cbdLatentSampler q degree rows factors eta
        secretSampler finalErrorSampler) := by
    unfold cbdLatentSampler
    refine NeverFail.bind_of_forall (hx := hSecretNeverFails) (hy := ?_)
    intro secret
    refine NeverFail.bind_of_forall (hx := hErrorsNeverFail) (hy := ?_)
    intro firstError
    refine NeverFail.bind_of_forall (hx := hErrorsNeverFail) (hy := ?_)
    intro secondError
    refine NeverFail.bind_of_forall (hx := hFinalNeverFails) (hy := ?_)
    intro finalError
    infer_instance
  exact hLatent.probFailure_eq_zero

/-- The fully CBD latent sampler is total whenever its secret sampler is total. -/
theorem fullyCBDLatentSampler_probFailure
    (q degree rows factors hintEta finalEta : ℕ) [NeZero q]
    (secretSampler : ProbComp (Rq q degree))
    (hSecret : Pr[⊥ | secretSampler] = 0) :
    Pr[⊥ | fullyCBDLatentSampler q degree rows factors hintEta finalEta
      secretSampler] = 0 := by
  exact cbdLatentSampler_probFailure q degree rows factors hintEta secretSampler
    (cbdFinalErrorSampler q degree rows finalEta) hSecret
    (cbdFinalErrorSampler_probFailure q degree rows finalEta)

/-- The source terminal error is exactly the independent CBD product sum plus the selected final
error. -/
theorem terminalError_latentValue
    {R Row Factor : Type} [CommRing R] [Fintype Factor]
    (secret : R) (firstError secondError : Row → Factor → R)
    (finalError : Row → R) (row : Row) :
    QuadraticKDM.terminalError
        (latentValue secret firstError secondError finalError) row =
      ∑ factor, firstError row factor * secondError row factor + finalError row := rfl

/-- With one factor per row, the proof-only source residual is one independent ring product. -/
theorem terminalError_oneFactor
    {R Row : Type} [CommRing R]
    (secret : R) (firstError secondError : Row → Fin 1 → R)
    (finalError : Row → R) (row : Row) :
    QuadraticKDM.terminalError
        (latentValue secret firstError secondError finalError) row =
      firstError row 0 * secondError row 0 + finalError row := by
  simp [terminalError_latentValue]

/-! ## One-factor scaled gadgets -/

/-- A one-factor gadget with row weight `left_j * right_j`.  This is the direct formal form of
the two scaled hints `left_j*S + F_j` and `right_j*S + G_j`. -/
def oneFactorGadget
    {R : Type} [CommRing R] {rows : ℕ}
    (left right : Fin rows → R) :
    QuadraticKDM.Gadget R (Fin rows) (Fin 1) where
  weight row := left row * right row
  alpha row _factor := left row
  beta row _factor := right row
  factorization row := by simp

@[simp]
theorem oneFactorGadget_weight
    {R : Type} [CommRing R] {rows : ℕ}
    (left right : Fin rows → R) (row : Fin rows) :
    (oneFactorGadget left right).weight row = left row * right row := rfl

@[simp]
theorem oneFactorGadget_publicLeakage_first
    {R : Type} [CommRing R] {rows : ℕ}
    (left right : Fin rows → R)
    (latent : QuadraticKDM.Latent R (Fin rows) (Fin 1))
    (row : Fin rows) :
    (QuadraticKDM.publicLeakage (oneFactorGadget left right) latent).1 row 0 =
      left row * latent.secret + latent.firstError row 0 := rfl

@[simp]
theorem oneFactorGadget_publicLeakage_second
    {R : Type} [CommRing R] {rows : ℕ}
    (left right : Fin rows → R)
    (latent : QuadraticKDM.Latent R (Fin rows) (Fin 1))
    (row : Fin rows) :
    (QuadraticKDM.publicLeakage (oneFactorGadget left right) latent).2 row 0 =
      right row * latent.secret + latent.secondError row 0 := rfl

/-! ## Exact BFV relinearization correctness after compilation -/

/-- Compiling the correlated product-error source and then relinearizing removes every proof-only
CBD product.  The resulting phase contains exactly the target errors `E_j`. -/
theorem compiled_relinearization_phase
    {R Row Factor : Type} [CommRing R] [Fintype Row] [Fintype Factor]
    (gadget : QuadraticKDM.Gadget R Row Factor)
    (auxiliarySecret c0 c1 c2 : R)
    (latent : QuadraticKDM.Latent R Row Factor)
    (coefficient digit : Row → R)
    (hDecomposition : c2 = ∑ row, digit row * gadget.weight row) :
    let target := QuadraticKDM.compile gadget
      (QuadraticKDM.realSourceTranscript gadget auxiliarySecret latent coefficient)
    (c0 + ∑ row, digit row * target.2 row) +
        (c1 - ∑ row, digit row * target.1 row) * latent.secret =
      c0 + c1 * latent.secret + c2 * latent.secret ^ 2 +
        ∑ row, digit row * latent.finalError row := by
  dsimp only
  rw [QuadraticKDM.compile_realSourceTranscript]
  simpa only [QuadraticKDM.kdmTranscript, QuadraticKDM.evaluationKeyBody] using
    (QuadraticKDM.relinearization_phase latent.secret c0 c1 c2 digit
      gadget.weight
      (fun row ↦ coefficient row -
        QuadraticKDM.linearCorrection gadget
          (QuadraticKDM.publicLeakage gadget latent) row)
      latent.finalError hDecomposition)

/-! ## Complete joint security composition -/

/-- The executable-CBD fixed-gadget KDM advantage is bounded by exactly one complete correlated
source advantage and the ordinary zero-message endpoint.  There is no row hybrid and no gadget
weight in the final target error. -/
theorem cbd_kdmAdvantage_le_source_add_zero
    (q degree rows factors eta : ℕ) [NeZero q]
    (gadget : QuadraticKDM.Gadget (Rq q degree) (Fin rows) (Fin factors))
    (secretSampler : ProbComp (Rq q degree))
    (finalErrorSampler : ProbComp (Fin rows → Rq q degree))
    (distinguisher : QuadraticKDM.Distinguisher (Rq q degree) (Fin rows))
    (hSecret : Pr[⊥ | secretSampler] = 0)
    (hFinal : Pr[⊥ | finalErrorSampler] = 0) :
    QuadraticKDM.kdmAdvantage gadget
        (cbdLatentSampler q degree rows factors eta secretSampler finalErrorSampler)
        distinguisher ≤
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (QuadraticKDM.sourceProblem gadget
            (cbdLatentSampler q degree rows factors eta
              secretSampler finalErrorSampler))
          (QuadraticKDM.sourceReduction gadget distinguisher) +
        QuadraticKDM.zeroUniformAdvantage gadget
          (cbdLatentSampler q degree rows factors eta
            secretSampler finalErrorSampler) distinguisher := by
  let latentSampler := cbdLatentSampler q degree rows factors eta
    secretSampler finalErrorSampler
  have hLatent : Pr[⊥ | latentSampler] = 0 :=
    cbdLatentSampler_probFailure q degree rows factors eta
      secretSampler finalErrorSampler hSecret hFinal
  calc
    QuadraticKDM.kdmAdvantage gadget latentSampler distinguisher ≤
        QuadraticKDM.kdmUniformAdvantage gadget latentSampler distinguisher +
          QuadraticKDM.zeroUniformAdvantage gadget latentSampler distinguisher :=
      QuadraticKDM.kdmAdvantage_le_kdmUniform_add_zeroUniform
        gadget latentSampler distinguisher
    _ = FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (QuadraticKDM.sourceProblem gadget latentSampler)
          (QuadraticKDM.sourceReduction gadget distinguisher) +
        QuadraticKDM.zeroUniformAdvantage gadget latentSampler distinguisher := by
      exact congrArg
        (fun advantage : ℝ ↦ advantage +
          QuadraticKDM.zeroUniformAdvantage gadget latentSampler distinguisher)
        (QuadraticKDM.kdmUniformAdvantage_eq_sourceAdvantage
          gadget latentSampler distinguisher hLatent)

/-- Numerical-bound interface for the preceding exact composition. -/
theorem cbd_kdmAdvantage_le_of_source_and_zero
    (q degree rows factors eta : ℕ) [NeZero q]
    (gadget : QuadraticKDM.Gadget (Rq q degree) (Fin rows) (Fin factors))
    (secretSampler : ProbComp (Rq q degree))
    (finalErrorSampler : ProbComp (Fin rows → Rq q degree))
    (distinguisher : QuadraticKDM.Distinguisher (Rq q degree) (Fin rows))
    (sourceBound zeroBound : ℝ)
    (hSecret : Pr[⊥ | secretSampler] = 0)
    (hFinal : Pr[⊥ | finalErrorSampler] = 0)
    (hSource :
      FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (QuadraticKDM.sourceProblem gadget
            (cbdLatentSampler q degree rows factors eta
              secretSampler finalErrorSampler))
          (QuadraticKDM.sourceReduction gadget distinguisher) ≤ sourceBound)
    (hZero :
      QuadraticKDM.zeroUniformAdvantage gadget
          (cbdLatentSampler q degree rows factors eta
            secretSampler finalErrorSampler) distinguisher ≤ zeroBound) :
    QuadraticKDM.kdmAdvantage gadget
        (cbdLatentSampler q degree rows factors eta secretSampler finalErrorSampler)
        distinguisher ≤ sourceBound + zeroBound := by
  exact (cbd_kdmAdvantage_le_source_add_zero q degree rows factors eta gadget
    secretSampler finalErrorSampler distinguisher hSecret hFinal).trans
      (add_le_add hSource hZero)

/-- Strongest checked conditional endpoint for the executable-CBD instantiation.  A concrete
split-ring search-to-decision certificate may discharge the correlated source term; its search
success and certificate loss remain visible, as does ordinary zero-message RLWE. -/
theorem cbd_kdmAdvantage_le_search_add_loss_add_zero
    (q degree rows factors eta : ℕ) [NeZero q]
    {SearchChallenge SearchAuxiliary : Type}
    (gadget : QuadraticKDM.Gadget (Rq q degree) (Fin rows) (Fin factors))
    (secretSampler : ProbComp (Rq q degree))
    (finalErrorSampler : ProbComp (Fin rows → Rq q degree))
    (distinguisher : QuadraticKDM.Distinguisher (Rq q degree) (Fin rows))
    (searchProblem : FormalProof4FHE.LWE.AuxiliaryInput.Search.Problem
      (Rq q degree) SearchChallenge SearchAuxiliary)
    (certificate : QuadraticKDM.SplitSearchToDecisionCertificate
      (QuadraticKDM.sourceProblem gadget
        (cbdLatentSampler q degree rows factors eta
          secretSampler finalErrorSampler)) searchProblem)
    (searchBound lossBound zeroBound : ℝ)
    (hSecret : Pr[⊥ | secretSampler] = 0)
    (hFinal : Pr[⊥ | finalErrorSampler] = 0)
    (hSearch :
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability searchProblem
        (certificate.toSolver (QuadraticKDM.sourceReduction gadget distinguisher))).toReal ≤
          searchBound)
    (hLoss : certificate.loss
      (QuadraticKDM.sourceReduction gadget distinguisher) ≤ lossBound)
    (hZero : QuadraticKDM.zeroUniformAdvantage gadget
      (cbdLatentSampler q degree rows factors eta
        secretSampler finalErrorSampler) distinguisher ≤ zeroBound) :
    QuadraticKDM.kdmAdvantage gadget
      (cbdLatentSampler q degree rows factors eta
        secretSampler finalErrorSampler) distinguisher ≤
      (searchBound + lossBound) + zeroBound := by
  apply QuadraticKDM.kdmAdvantage_le_search_add_loss_add_zero
    gadget
    (cbdLatentSampler q degree rows factors eta secretSampler finalErrorSampler)
    distinguisher searchProblem certificate searchBound lossBound zeroBound
  · exact cbdLatentSampler_probFailure q degree rows factors eta
      secretSampler finalErrorSampler hSecret hFinal
  · exact hSearch
  · exact hLoss
  · exact hZero

end

end FormalProof4FHE.RLWE.CenteredBinomialScaledQuadraticKDM
