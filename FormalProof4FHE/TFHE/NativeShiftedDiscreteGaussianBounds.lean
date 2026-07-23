/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RingRegev
import FormalProof4FHE.TFHE.DiscreteGaussianSampler
import FormalProof4FHE.TFHE.NativeAdaptiveShiftedCandidateEvaluator
import FormalProof4FHE.TFHE.NativeConditionalSmudging
import FormalProof4FHE.TFHE.NativeShiftedResidualBounds

/-!
# Discrete-Gaussian Smudging Bounds for the Native Shifted Evaluator

This file converts the deterministic correct-residual norm budget into an explicit smudging cost
for the checked finite discrete-Gaussian sampler.

For a scalar certificate and a natural bound `B`, `scalarShiftEnvelope` is a conservative finite
sum over all bounded modular shifts.  The sharper `scalarLinearShiftBound` instead uses
translation subadditivity.  The underlying integer-Gaussian unit-shift distance is proved exactly
equal to its mass at zero, and a finite central window `W ≤ alpha * q` bounds that mass by
`exp (1 / 2) / (W + 1)`.  Coefficient and BRK-layout hybrids lift either scalar bound to the
complete construction-specific smudging cost.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.DiscreteGaussianSampler

noncomputable section

open scoped BigOperators

/-- Finite certified translation-cost envelope for every scalar modular shift with centered
absolute representative at most `bound`. -/
def scalarShiftEnvelope
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound : ℕ) : ℝ :=
  ∑ shift : ZMod q,
    if shift.valMinAbs.natAbs ≤ bound then
      2 * certificate.bound.toReal +
        ModularGaussian.shiftDistance
          (ModularGaussian.torusDistribution q alpha halpha) shift
    else 0

theorem scalarShiftEnvelope_nonneg
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound : ℕ) :
    0 ≤ scalarShiftEnvelope certificate bound := by
  unfold scalarShiftEnvelope
  apply Finset.sum_nonneg
  intro shift _
  split_ifs
  · exact add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      (PMF.tvDist_nonneg _ _)
  · exact le_rfl

/-- Sharper certified cost for any scalar shift of centered magnitude at most `bound`.  Unlike
`scalarShiftEnvelope`, this quantity does not sum over every bounded residue: subadditivity
reduces the ideal term to `bound` copies of one integer-Gaussian unit shift. -/
def scalarLinearShiftBound
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound : ℕ) : ℝ :=
  2 * certificate.bound.toReal + (bound : ℝ) *
    ModularGaussian.shiftDistance
      (LatticeCrypto.discreteGaussianDist
        (ModularGaussian.integerStddev q alpha) 0
        (ModularGaussian.integerStddev_pos q halpha)) 1

theorem scalarLinearShiftBound_nonneg
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound : ℕ) :
    0 ≤ scalarLinearShiftBound certificate bound := by
  unfold scalarLinearShiftBound
  exact add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
    (mul_nonneg (Nat.cast_nonneg _) (PMF.tvDist_nonneg _ _))

/-- The only ideal term in `scalarLinearShiftBound` is exactly the centered integer Gaussian's
mass at zero. -/
theorem scalarLinearShiftBound_eq_mass_zero
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound : ℕ) :
    scalarLinearShiftBound certificate bound =
      2 * certificate.bound.toReal + (bound : ℝ) *
        LatticeCrypto.discreteGaussianPMF
          (ModularGaussian.integerStddev q alpha) 0 0 := by
  unfold scalarLinearShiftBound
  rw [ModularGaussian.shiftDistance_discreteGaussian_unit_eq_mass_zero]

/-- Explicit finite-window estimate for the certified scalar translation cost. -/
theorem scalarLinearShiftBound_le_exp_half_window
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound window : ℕ)
    (hwindow : (window : ℝ) ≤ ModularGaussian.integerStddev q alpha) :
    scalarLinearShiftBound certificate bound ≤
      2 * certificate.bound.toReal + (bound : ℝ) *
        (Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ)) := by
  unfold scalarLinearShiftBound
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (ModularGaussian.shiftDistance_discreteGaussian_unit_le_exp_half_div_nat_succ
      (ModularGaussian.integerStddev q alpha)
      (ModularGaussian.integerStddev_pos q halpha) window hwindow)
    (Nat.cast_nonneg bound))

/-- Every bounded executable scalar translation is controlled by the linear unit-shift bound. -/
theorem addShiftDistance_scalarSampler_le_scalarLinearShiftBound
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound : ℕ)
    (shift : ZMod q) (hshift : shift.valMinAbs.natAbs ≤ bound) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (scalarSampler certificate) shift ≤
      scalarLinearShiftBound certificate bound := by
  let unitCost := ModularGaussian.shiftDistance
    (LatticeCrypto.discreteGaussianDist
      (ModularGaussian.integerStddev q alpha) 0
      (ModularGaussian.integerStddev_pos q halpha)) 1
  have hunit : 0 ≤ unitCost := PMF.tvDist_nonneg _ _
  calc
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (scalarSampler certificate) shift ≤
        2 * certificate.bound.toReal +
          ModularGaussian.shiftDistance
            (ModularGaussian.torusDistribution q alpha halpha) shift :=
      addShiftDistance_scalarSampler_le certificate shift
    _ ≤ 2 * certificate.bound.toReal +
        (shift.valMinAbs.natAbs : ℝ) * unitCost := by
      exact add_le_add le_rfl
        (ModularGaussian.shiftDistance_torusDistribution_le_natAbs_mul_unit
          q alpha halpha shift)
    _ ≤ 2 * certificate.bound.toReal + (bound : ℝ) * unitCost := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hshift) hunit)
    _ = scalarLinearShiftBound certificate bound := by
      rfl

/-- Every bounded scalar shift is controlled by the finite certified envelope. -/
theorem addShiftDistance_scalarSampler_le_scalarShiftEnvelope
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound : ℕ)
    (shift : ZMod q) (hshift : shift.valMinAbs.natAbs ≤ bound) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (scalarSampler certificate) shift ≤
      scalarShiftEnvelope certificate bound := by
  calc
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (scalarSampler certificate) shift ≤
        2 * certificate.bound.toReal +
          ModularGaussian.shiftDistance
            (ModularGaussian.torusDistribution q alpha halpha) shift :=
      addShiftDistance_scalarSampler_le certificate shift
    _ = if shift.valMinAbs.natAbs ≤ bound then
          2 * certificate.bound.toReal +
            ModularGaussian.shiftDistance
              (ModularGaussian.torusDistribution q alpha halpha) shift
        else 0 := by simp [hshift]
    _ ≤ scalarShiftEnvelope certificate bound := by
      unfold scalarShiftEnvelope
      refine Finset.single_le_sum
        (f := fun other : ZMod q =>
          if other.valMinAbs.natAbs ≤ bound then
            2 * certificate.bound.toReal +
              ModularGaussian.shiftDistance
                (ModularGaussian.torusDistribution q alpha halpha) other
          else 0)
        (s := Finset.univ) ?_ (Finset.mem_univ shift)
      intro other _
      split_ifs
      · exact add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
          (PMF.tvDist_nonneg _ _)
      · exact le_rfl

/-- Coefficientwise sampling lifts the bounded scalar envelope to one ring residual, with one
hybrid step per coefficient. -/
theorem addShiftDistance_ringSampler_le_degree_mul_scalarShiftEnvelope
    {q : ℕ} [NeZero q] (degree : ℕ)
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound : ℕ)
    (shift : RLWE.Rq q degree)
    (hshift : LatticeCrypto.cInfNorm shift ≤ bound) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (ringSampler degree certificate) shift ≤
      (degree : ℝ) * scalarShiftEnvelope certificate bound := by
  calc
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (ringSampler degree certificate) shift ≤
        ∑ coefficient, FormalProof4FHE.FiniteProduct.addShiftDistance
          (scalarSampler certificate) (LatticeCrypto.Poly.toPi shift coefficient) :=
      addShiftDistance_ringSampler_le_sum_scalar degree certificate shift
    _ ≤ ∑ _coefficient : Fin degree, scalarShiftEnvelope certificate bound := by
      apply Finset.sum_le_sum
      intro coefficient _
      apply addShiftDistance_scalarSampler_le_scalarShiftEnvelope certificate bound
      rw [← LatticeCrypto.centeredRepr_eq_valMinAbs]
      exact (LatticeCrypto.coeff_le_cInfNorm shift coefficient).trans hshift
    _ = (degree : ℝ) * scalarShiftEnvelope certificate bound := by simp

/-- Coefficientwise lift of the sharper linear unit-shift bound. -/
theorem addShiftDistance_ringSampler_le_degree_mul_scalarLinearShiftBound
    {q : ℕ} [NeZero q] (degree : ℕ)
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound : ℕ)
    (shift : RLWE.Rq q degree)
    (hshift : LatticeCrypto.cInfNorm shift ≤ bound) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (ringSampler degree certificate) shift ≤
      (degree : ℝ) * scalarLinearShiftBound certificate bound := by
  calc
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (ringSampler degree certificate) shift ≤
        ∑ coefficient, FormalProof4FHE.FiniteProduct.addShiftDistance
          (scalarSampler certificate) (LatticeCrypto.Poly.toPi shift coefficient) :=
      addShiftDistance_ringSampler_le_sum_scalar degree certificate shift
    _ ≤ ∑ _coefficient : Fin degree, scalarLinearShiftBound certificate bound := by
      apply Finset.sum_le_sum
      intro coefficient _
      apply addShiftDistance_scalarSampler_le_scalarLinearShiftBound certificate bound
      rw [← LatticeCrypto.centeredRepr_eq_valMinAbs]
      exact (LatticeCrypto.coeff_le_cInfNorm shift coefficient).trans hshift
    _ = (degree : ℝ) * scalarLinearShiftBound certificate bound := by simp

/-- Ring translation bound with the integer Gaussian eliminated in favor of a finite central
window. -/
theorem addShiftDistance_ringSampler_le_exp_half_window
    {q : ℕ} [NeZero q] (degree : ℕ)
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : ScalarCertificate q alpha halpha) (bound window : ℕ)
    (hwindow : (window : ℝ) ≤ ModularGaussian.integerStddev q alpha)
    (shift : RLWE.Rq q degree)
    (hshift : LatticeCrypto.cInfNorm shift ≤ bound) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (ringSampler degree certificate) shift ≤
      (degree : ℝ) *
        (2 * certificate.bound.toReal + (bound : ℝ) *
          (Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ))) := by
  exact (addShiftDistance_ringSampler_le_degree_mul_scalarLinearShiftBound
    degree certificate bound shift hshift).trans
      (mul_le_mul_of_nonneg_left
        (scalarLinearShiftBound_le_exp_half_window certificate bound window hwindow)
        (Nat.cast_nonneg degree))

end

end FormalProof4FHE.TFHE.DiscreteGaussianSampler

namespace FormalProof4FHE.TFHE.Native.ConditionalSmudging

noncomputable section

open FormalProof4FHE.TFHE
open scoped BigOperators

local instance rqAddFromSemiringForShiftedBounds (q degree : ℕ) :
    Add (RLWE.Rq q degree) :=
  (inferInstance : Distrib (RLWE.Rq q degree)).toAdd

local instance rqAddCommGroupFromRingForShiftedBounds (q degree : ℕ) :
    AddCommGroup (RLWE.Rq q degree) :=
  (inferInstance : Ring (RLWE.Rq q degree)).toAddCommGroup

/-- The proof-facing additive dictionary used by native conditional smudging computes the same
translation map as the executable coefficientwise `Rq` addition. -/
theorem addShiftDistance_rq_eq_executable
    {q degree : ℕ} (sampler : ProbComp (RLWE.Rq q degree))
    (shift : RLWE.Rq q degree) :
    FormalProof4FHE.FiniteProduct.addShiftDistance sampler shift =
      @FormalProof4FHE.FiniteProduct.addShiftDistance (RLWE.Rq q degree)
        (RLWE.negacyclicRing q degree).instAddPoly sampler shift := by
  unfold FormalProof4FHE.FiniteProduct.addShiftDistance
  congr 2
  funext value
  exact RLWE.RingRegev.semiringRqAdd_apply q degree shift value

/-- A zero KSK residual contributes exactly zero, so the heterogeneous evaluation-key cost
reduces to its BRK component. -/
@[simp]
theorem evaluationKeySmudgingCost_zeroKeySwitch
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise : ProbComp (ZMod q))
    (ringResidual : BootstrappingResidual q degree ringRank tgswLevels lweDimension) :
    evaluationKeySmudgingCost ringWideNoise keySwitchWideNoise ringResidual
        (0 : KeySwitchResidual q ringRank degree keySwitchLevels) =
      bootstrappingSmudgingCost ringWideNoise ringResidual := by
  simp [evaluationKeySmudgingCost, keySwitchSmudgingCost]

/-- If every native BRK residual row has norm at most `bound`, its complete discrete-Gaussian
smudging cost is bounded by the number of rows times the coefficientwise envelope. -/
theorem bootstrappingSmudgingCost_discreteGaussian_le
    {q degree ringRank tgswLevels lweDimension : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (bound : ℕ)
    (hresidual : ∀ coordinate row,
      LatticeCrypto.cInfNorm (residual coordinate row) ≤ bound) :
    bootstrappingSmudgingCost
        (DiscreteGaussianSampler.ringSampler degree certificate) residual ≤
      ((lweDimension * TGSW.rowCount ringRank tgswLevels : ℕ) : ℝ) *
        ((degree : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate bound) := by
  unfold bootstrappingSmudgingCost
  calc
    (∑ coordinate, ∑ row,
      FormalProof4FHE.FiniteProduct.addShiftDistance
        (DiscreteGaussianSampler.ringSampler degree certificate)
        (residual coordinate row)) ≤
        ∑ _coordinate : Fin lweDimension,
          ∑ _row : Fin (TGSW.rowCount ringRank tgswLevels),
            (degree : ℝ) *
              DiscreteGaussianSampler.scalarShiftEnvelope certificate bound := by
      apply Finset.sum_le_sum
      intro coordinate _
      apply Finset.sum_le_sum
      intro row _
      rw [addShiftDistance_rq_eq_executable]
      exact DiscreteGaussianSampler.addShiftDistance_ringSampler_le_degree_mul_scalarShiftEnvelope
        degree certificate bound (residual coordinate row) (hresidual coordinate row)
    _ = ((lweDimension * TGSW.rowCount ringRank tgswLevels : ℕ) : ℝ) *
        ((degree : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate bound) := by
      simp [Nat.cast_mul]
      ring

/-- Sharper complete-BRK smudging bound using the linear unit-shift cost instead of the finite
sum over all bounded residues. -/
theorem bootstrappingSmudgingCost_discreteGaussian_le_linear
    {q degree ringRank tgswLevels lweDimension : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (bound : ℕ)
    (hresidual : ∀ coordinate row,
      LatticeCrypto.cInfNorm (residual coordinate row) ≤ bound) :
    bootstrappingSmudgingCost
        (DiscreteGaussianSampler.ringSampler degree certificate) residual ≤
      ((lweDimension * TGSW.rowCount ringRank tgswLevels : ℕ) : ℝ) *
        ((degree : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate bound) := by
  unfold bootstrappingSmudgingCost
  calc
    (∑ coordinate, ∑ row,
      FormalProof4FHE.FiniteProduct.addShiftDistance
        (DiscreteGaussianSampler.ringSampler degree certificate)
        (residual coordinate row)) ≤
        ∑ _coordinate : Fin lweDimension,
          ∑ _row : Fin (TGSW.rowCount ringRank tgswLevels),
            (degree : ℝ) *
              DiscreteGaussianSampler.scalarLinearShiftBound certificate bound := by
      apply Finset.sum_le_sum
      intro coordinate _
      apply Finset.sum_le_sum
      intro row _
      rw [addShiftDistance_rq_eq_executable]
      exact
        DiscreteGaussianSampler.addShiftDistance_ringSampler_le_degree_mul_scalarLinearShiftBound
          degree certificate bound (residual coordinate row) (hresidual coordinate row)
    _ = ((lweDimension * TGSW.rowCount ringRank tgswLevels : ℕ) : ℝ) *
        ((degree : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate bound) := by
      simp [Nat.cast_mul]
      ring

/-- Complete-BRK bound with the unit-shift distance replaced by its finite-window estimate. -/
theorem bootstrappingSmudgingCost_discreteGaussian_le_exp_half_window
    {q degree ringRank tgswLevels lweDimension : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (residual : BootstrappingResidual q degree ringRank tgswLevels lweDimension)
    (bound window : ℕ)
    (hwindow : (window : ℝ) ≤ ModularGaussian.integerStddev q alpha)
    (hresidual : ∀ coordinate row,
      LatticeCrypto.cInfNorm (residual coordinate row) ≤ bound) :
    bootstrappingSmudgingCost
        (DiscreteGaussianSampler.ringSampler degree certificate) residual ≤
      ((lweDimension * TGSW.rowCount ringRank tgswLevels : ℕ) : ℝ) *
        ((degree : ℝ) *
          (2 * certificate.bound.toReal + (bound : ℝ) *
            (Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ)))) := by
  exact (bootstrappingSmudgingCost_discreteGaussian_le_linear
    certificate residual bound hresidual).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (DiscreteGaussianSampler.scalarLinearShiftBound_le_exp_half_window
            certificate bound window hwindow)
          (Nat.cast_nonneg degree))
        (Nat.cast_nonneg _))

end

end FormalProof4FHE.TFHE.Native.ConditionalSmudging

namespace FormalProof4FHE.TFHE.Native.ShiftedResidualBounds

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- The complete correct residual's discrete-Gaussian BRK smudging cost.  A bound on the source
BRK rows alone suffices because correct-candidate toggling preserves their norms. -/
theorem bootstrappingSmudgingCost_correctResidual_discreteGaussian_le
    {q degree ringRank lweDimension eta : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension) (coordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (hsource : ∀ outputCoordinate index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
        (source outputCoordinate) index) ≤ eta) :
    ConditionalSmudging.bootstrappingSmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        (ShiftedCandidateEvaluator.correctBootstrappingResidual params secret hidden
          coordinate source trueBranch) ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate
            (centeredBinomialResidualBound params (degree + 1) ringRank eta)) := by
  apply ConditionalSmudging.bootstrappingSmudgingCost_discreteGaussian_le
  intro outputCoordinate row
  obtain ⟨index, rfl⟩ := finProdFinEquiv.surjective row
  exact cInfNorm_correctBootstrappingResidual_le_centeredBinomialBound_of_source
    params secret hidden coordinate outputCoordinate source trueBranch index hsource

/-- Conservative pointwise smudging bound for the fresh-secret proof boundary.  Unlike the
centered-binomial specialization above, this theorem needs no relation between the source BRK
and the target scalar or ring secret. -/
theorem bootstrappingSmudgingCost_correctResidual_discreteGaussian_le_universal
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension) (coordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :
    ConditionalSmudging.bootstrappingSmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        (ShiftedCandidateEvaluator.correctBootstrappingResidual params secret hidden
          coordinate source trueBranch) ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate
            (universalResidualBound params (degree + 1) ringRank)) := by
  apply ConditionalSmudging.bootstrappingSmudgingCost_discreteGaussian_le
  intro outputCoordinate row
  obtain ⟨index, rfl⟩ := finProdFinEquiv.surjective row
  exact cInfNorm_correctBootstrappingResidual_le_universalBound
    params secret hidden coordinate outputCoordinate source trueBranch index

/-- Linear-unit-shift form of the coupled centered-binomial correct-residual bound. -/
theorem bootstrappingSmudgingCost_correctResidual_discreteGaussian_le_linear
    {q degree ringRank lweDimension eta : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension) (coordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (hsource : ∀ outputCoordinate index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
        (source outputCoordinate) index) ≤ eta) :
    ConditionalSmudging.bootstrappingSmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        (ShiftedCandidateEvaluator.correctBootstrappingResidual params secret hidden
          coordinate source trueBranch) ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate
            (centeredBinomialResidualBound params (degree + 1) ringRank eta)) := by
  apply ConditionalSmudging.bootstrappingSmudgingCost_discreteGaussian_le_linear
  intro outputCoordinate row
  obtain ⟨index, rfl⟩ := finProdFinEquiv.surjective row
  exact cInfNorm_correctBootstrappingResidual_le_centeredBinomialBound_of_source
    params secret hidden coordinate outputCoordinate source trueBranch index hsource

/-- Linear-unit-shift form of the independent-secret universal correct-residual bound. -/
theorem bootstrappingSmudgingCost_correctResidual_discreteGaussian_le_universal_linear
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension) (coordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :
    ConditionalSmudging.bootstrappingSmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        (ShiftedCandidateEvaluator.correctBootstrappingResidual params secret hidden
          coordinate source trueBranch) ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate
            (universalResidualBound params (degree + 1) ringRank)) := by
  apply ConditionalSmudging.bootstrappingSmudgingCost_discreteGaussian_le_linear
  intro outputCoordinate row
  obtain ⟨index, rfl⟩ := finProdFinEquiv.surjective row
  exact cInfNorm_correctBootstrappingResidual_le_universalBound
    params secret hidden coordinate outputCoordinate source trueBranch index

end

end FormalProof4FHE.TFHE.Native.ShiftedResidualBounds

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

noncomputable section

open FormalProof4FHE.TFHE
open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Direct smudging bound for the exact residual used by `concreteCorrectResidualSampler`.  Its
only row hypothesis is the centered-binomial-width bound for the transported source BRK. -/
theorem evaluationKeySmudgingCost_correctResidualAtTarget_discreteGaussian_le
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchWideNoise : ProbComp (ZMod q))
    (coordinate : Fin lweDimension)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coin : Coin q (degree + 1) ringRank params.levels lweDimension)
    (hsource : ∀ outputCoordinate index, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1))
        (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
        (embedBit (targetSecret outputCoordinate))
        ((transportedView params challenge auxiliary coin.1).1.1 outputCoordinate)
        index) ≤ eta) :
    Native.ConditionalSmudging.evaluationKeySmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        keySwitchWideNoise
        (correctResidualAtTarget params coordinate targetSecret challenge auxiliary
          ringSecret coin).1
        (correctResidualAtTarget params coordinate targetSecret challenge auxiliary
          ringSecret coin).2 ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta)) := by
  change Native.ConditionalSmudging.evaluationKeySmudgingCost
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchWideNoise
      (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
        (embedRingSecret q ringSecret) targetSecret coordinate
        (transportedView params challenge auxiliary coin.1).1.1 coin.2)
      0 ≤ _
  rw [Native.ConditionalSmudging.evaluationKeySmudgingCost_zeroKeySwitch]
  exact Native.ShiftedResidualBounds.bootstrappingSmudgingCost_correctResidual_discreteGaussian_le
    params certificate (embedRingSecret q ringSecret) targetSecret coordinate
    (transportedView params challenge auxiliary coin.1).1.1 coin.2 hsource

/-- Support-wise form matching `ConcreteStatisticalCertificate.smudgingCost_le`.  It reduces every
supported residual to the conditioned evaluator coin that produced it and applies the fixed-coin
bound above. -/
theorem evaluationKeySmudgingCost_concreteCorrectResidualSampler_discreteGaussian_le
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchWideNoise : ProbComp (ZMod q))
    (coordinate : Fin lweDimension) (sourceBit : Bool)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount)
    (secrets : Secret lweDimension ringRank (degree + 1))
    (residual : EvaluationKeyResidual q (degree + 1) ringRank params.levels
      lweDimension keySwitchLevels)
    (hresidual : residual ∈ support
      (concreteCorrectResidualSampler params coordinate sourceBit challenge auxiliary secrets))
    (hsource : ∀ coin,
      coin ∈ support (sampleConditionedCoin (degree := degree + 1)
        (ringRank := ringRank) params coordinate sourceBit secrets.1) →
      ∀ outputCoordinate index, LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1))
          (embedRingSecret q secrets.2) (Gadget.Base.ringGadget params)
          (embedBit (secrets.1 outputCoordinate))
          ((transportedView params challenge auxiliary coin.1).1.1 outputCoordinate)
          index) ≤ eta) :
    Native.ConditionalSmudging.evaluationKeySmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        keySwitchWideNoise residual.1 residual.2 ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              params (degree + 1) ringRank eta)) := by
  unfold concreteCorrectResidualSampler at hresidual
  rw [mem_support_bind_iff] at hresidual
  obtain ⟨coin, hcoin, hresidual⟩ := hresidual
  simp only [support_pure, Set.mem_singleton_iff] at hresidual
  subst residual
  exact evaluationKeySmudgingCost_correctResidualAtTarget_discreteGaussian_le
    params certificate keySwitchWideNoise coordinate secrets.1 challenge auxiliary
    secrets.2 coin (hsource coin hcoin)

/-- Direct universal bound for the exact fixed-coin residual.  This is the sound specialization
when the fresh target secret pair is quantified independently of the public source context. -/
theorem evaluationKeySmudgingCost_correctResidualAtTarget_discreteGaussian_le_universal
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchWideNoise : ProbComp (ZMod q))
    (coordinate : Fin lweDimension)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coin : Coin q (degree + 1) ringRank params.levels lweDimension) :
    Native.ConditionalSmudging.evaluationKeySmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        keySwitchWideNoise
        (correctResidualAtTarget params coordinate targetSecret challenge auxiliary
          ringSecret coin).1
        (correctResidualAtTarget params coordinate targetSecret challenge auxiliary
          ringSecret coin).2 ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate
            (Native.ShiftedResidualBounds.universalResidualBound
              params (degree + 1) ringRank)) := by
  change Native.ConditionalSmudging.evaluationKeySmudgingCost
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchWideNoise
      (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
        (embedRingSecret q ringSecret) targetSecret coordinate
        (transportedView params challenge auxiliary coin.1).1.1 coin.2)
      0 ≤ _
  rw [Native.ConditionalSmudging.evaluationKeySmudgingCost_zeroKeySwitch]
  exact
    Native.ShiftedResidualBounds.bootstrappingSmudgingCost_correctResidual_discreteGaussian_le_universal
      params certificate (embedRingSecret q ringSecret) targetSecret coordinate
      (transportedView params challenge auxiliary coin.1).1.1 coin.2

/-- Support-wise universal theorem matching the `smudgingCost_le` field of the concrete
statistical certificate.  All residual support obligations are discharged by inverting the
conditioned coin sampler; no row-bound premise remains. -/
theorem evaluationKeySmudgingCost_concreteCorrectResidualSampler_discreteGaussian_le_universal
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchWideNoise : ProbComp (ZMod q))
    (coordinate : Fin lweDimension) (sourceBit : Bool)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount)
    (secrets : Secret lweDimension ringRank (degree + 1))
    (residual : EvaluationKeyResidual q (degree + 1) ringRank params.levels
      lweDimension keySwitchLevels)
    (hresidual : residual ∈ support
      (concreteCorrectResidualSampler params coordinate sourceBit challenge auxiliary secrets)) :
    Native.ConditionalSmudging.evaluationKeySmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        keySwitchWideNoise residual.1 residual.2 ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarShiftEnvelope certificate
            (Native.ShiftedResidualBounds.universalResidualBound
              params (degree + 1) ringRank)) := by
  unfold concreteCorrectResidualSampler at hresidual
  rw [mem_support_bind_iff] at hresidual
  obtain ⟨coin, _hcoin, hresidual⟩ := hresidual
  simp only [support_pure, Set.mem_singleton_iff] at hresidual
  subst residual
  exact evaluationKeySmudgingCost_correctResidualAtTarget_discreteGaussian_le_universal
    params certificate keySwitchWideNoise coordinate secrets.1 challenge auxiliary
    secrets.2 coin

/-- Linear-unit-shift version of the universal fixed-coin residual bound. -/
theorem evaluationKeySmudgingCost_correctResidualAtTarget_discreteGaussian_le_universal_linear
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchWideNoise : ProbComp (ZMod q))
    (coordinate : Fin lweDimension)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coin : Coin q (degree + 1) ringRank params.levels lweDimension) :
    Native.ConditionalSmudging.evaluationKeySmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        keySwitchWideNoise
        (correctResidualAtTarget params coordinate targetSecret challenge auxiliary
          ringSecret coin).1
        (correctResidualAtTarget params coordinate targetSecret challenge auxiliary
          ringSecret coin).2 ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate
            (Native.ShiftedResidualBounds.universalResidualBound
              params (degree + 1) ringRank)) := by
  change Native.ConditionalSmudging.evaluationKeySmudgingCost
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchWideNoise
      (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
        (embedRingSecret q ringSecret) targetSecret coordinate
        (transportedView params challenge auxiliary coin.1).1.1 coin.2)
      0 ≤ _
  rw [Native.ConditionalSmudging.evaluationKeySmudgingCost_zeroKeySwitch]
  exact
    Native.ShiftedResidualBounds.bootstrappingSmudgingCost_correctResidual_discreteGaussian_le_universal_linear
      params certificate (embedRingSecret q ringSecret) targetSecret coordinate
      (transportedView params challenge auxiliary coin.1).1.1 coin.2

/-- Support-wise universal linear-unit-shift theorem matching the concrete certificate. -/
theorem
    evaluationKeySmudgingCost_concreteCorrectResidualSampler_discreteGaussian_le_universal_linear
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchWideNoise : ProbComp (ZMod q))
    (coordinate : Fin lweDimension) (sourceBit : Bool)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount)
    (secrets : Secret lweDimension ringRank (degree + 1))
    (residual : EvaluationKeyResidual q (degree + 1) ringRank params.levels
      lweDimension keySwitchLevels)
    (hresidual : residual ∈ support
      (concreteCorrectResidualSampler params coordinate sourceBit challenge auxiliary secrets)) :
    Native.ConditionalSmudging.evaluationKeySmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        keySwitchWideNoise residual.1 residual.2 ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate
            (Native.ShiftedResidualBounds.universalResidualBound
              params (degree + 1) ringRank)) := by
  unfold concreteCorrectResidualSampler at hresidual
  rw [mem_support_bind_iff] at hresidual
  obtain ⟨coin, _hcoin, hresidual⟩ := hresidual
  simp only [support_pure, Set.mem_singleton_iff] at hresidual
  subst residual
  exact
    evaluationKeySmudgingCost_correctResidualAtTarget_discreteGaussian_le_universal_linear
      params certificate keySwitchWideNoise coordinate secrets.1 challenge auxiliary
      secrets.2 coin

/-- The construction-wide conservative smudging loss installed by the certified
discrete-Gaussian adapter below. -/
def universalDiscreteGaussianSmudgingError
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (ringDegree ringRank lweDimension : ℕ) : ℝ :=
  ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
    ((ringDegree : ℝ) *
      DiscreteGaussianSampler.scalarShiftEnvelope certificate
        (Native.ShiftedResidualBounds.universalResidualBound
          params ringDegree ringRank))

/-- Sharper construction-wide universal loss based on one integer-Gaussian unit shift. -/
def universalDiscreteGaussianLinearSmudgingError
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (ringDegree ringRank lweDimension : ℕ) : ℝ :=
  ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
    ((ringDegree : ℝ) *
      DiscreteGaussianSampler.scalarLinearShiftBound certificate
        (Native.ShiftedResidualBounds.universalResidualBound
          params ringDegree ringRank))

/-- Explicit finite-window upper bound for the complete universal correct-side loss. -/
theorem universalDiscreteGaussianLinearSmudgingError_le_exp_half_window
    {q : ℕ} [NeZero q] {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (ringDegree ringRank lweDimension window : ℕ)
    (hwindow : (window : ℝ) ≤ ModularGaussian.integerStddev q alpha) :
    universalDiscreteGaussianLinearSmudgingError
        params certificate ringDegree ringRank lweDimension ≤
      ((lweDimension * TGSW.rowCount ringRank params.levels : ℕ) : ℝ) *
        ((ringDegree : ℝ) *
          (2 * certificate.bound.toReal +
            (Native.ShiftedResidualBounds.universalResidualBound
              params ringDegree ringRank : ℝ) *
              (Real.exp (1 / 2 : ℝ) / (window + 1 : ℕ)))) := by
  unfold universalDiscreteGaussianLinearSmudgingError
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (DiscreteGaussianSampler.scalarLinearShiftBound_le_exp_half_window
        certificate
        (Native.ShiftedResidualBounds.universalResidualBound params ringDegree ringRank)
        window hwindow)
      (Nat.cast_nonneg ringDegree))
    (Nat.cast_nonneg _)

namespace ConcreteStatisticalCertificate

/-- Fill the concrete certificate's complete support-wise smudging field with the checked
discrete-Gaussian universal bound.  Callers supply only the two genuinely remaining statistical
obligations: the correct output normal-form distance and the wrong branch freshness distance. -/
noncomputable def ofDiscreteGaussianUniversalSmudging
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (sourceRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (normalFormError freshnessError : Fin lweDimension → ℝ)
    (normalFormError_nonneg : ∀ coordinate, 0 ≤ normalFormError coordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (normalFormDistance_le : ∀ coordinate,
      tvDist
          (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
            params sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate)
          (averagedSampledResidualRealView (ringRank := ringRank)
            (queryCount := queryCount) sourceRingErrorSampler
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            keySwitchErrorSampler keySwitchErrorSampler inputErrorSampler
            (Gadget.Base.ringGadget params) keySwitchGadget coordinate
            (concreteCorrectResidualSampler params coordinate)) ≤
        normalFormError coordinate)
    (freshnessDistance_le : ∀ coordinate hiddenAndContext,
      hiddenAndContext ∈ support
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
      tvDist
          (maskedBranchExperiment params coordinate (!hiddenAndContext.1)
            hiddenAndContext.2.1 hiddenAndContext.2.2)
          (maskedUniformExperiment params hiddenAndContext.2.1
            hiddenAndContext.2.2) ≤
        freshnessError coordinate) :
    ConcreteStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget where
  normalFormError := normalFormError
  smudgingError := fun _ ↦ universalDiscreteGaussianSmudgingError
    params certificate (degree + 1) ringRank lweDimension
  freshnessError := freshnessError
  normalFormError_nonneg := normalFormError_nonneg
  smudgingError_nonneg := by
    intro _coordinate
    apply mul_nonneg
    · positivity
    · apply mul_nonneg
      · positivity
      · exact DiscreteGaussianSampler.scalarShiftEnvelope_nonneg _ _
  freshnessError_nonneg := freshnessError_nonneg
  normalFormDistance_le := normalFormDistance_le
  smudgingCost_le := by
    intro coordinate hiddenAndContext _hcontext secrets residual hresidual
    simpa only [universalDiscreteGaussianSmudgingError] using
      (evaluationKeySmudgingCost_concreteCorrectResidualSampler_discreteGaussian_le_universal
        params certificate keySwitchErrorSampler coordinate hiddenAndContext.1
        hiddenAndContext.2.1 hiddenAndContext.2.2 secrets residual hresidual)
  freshnessDistance_le := freshnessDistance_le

/-- Fill the support-wise smudging field with the sharper linear unit-shift bound.  The caller
still supplies only the correct normal-form and wrong-branch statistical obligations. -/
noncomputable def ofDiscreteGaussianUniversalLinearSmudging
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (sourceRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (normalFormError freshnessError : Fin lweDimension → ℝ)
    (normalFormError_nonneg : ∀ coordinate, 0 ≤ normalFormError coordinate)
    (freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate)
    (normalFormDistance_le : ∀ coordinate,
      tvDist
          (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
            params sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate)
          (averagedSampledResidualRealView (ringRank := ringRank)
            (queryCount := queryCount) sourceRingErrorSampler
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            keySwitchErrorSampler keySwitchErrorSampler inputErrorSampler
            (Gadget.Base.ringGadget params) keySwitchGadget coordinate
            (concreteCorrectResidualSampler params coordinate)) ≤
        normalFormError coordinate)
    (freshnessDistance_le : ∀ coordinate hiddenAndContext,
      hiddenAndContext ∈ support
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
      tvDist
          (maskedBranchExperiment params coordinate (!hiddenAndContext.1)
            hiddenAndContext.2.1 hiddenAndContext.2.2)
          (maskedUniformExperiment params hiddenAndContext.2.1
            hiddenAndContext.2.2) ≤
        freshnessError coordinate) :
    ConcreteStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget where
  normalFormError := normalFormError
  smudgingError := fun _ ↦ universalDiscreteGaussianLinearSmudgingError
    params certificate (degree + 1) ringRank lweDimension
  freshnessError := freshnessError
  normalFormError_nonneg := normalFormError_nonneg
  smudgingError_nonneg := by
    intro _coordinate
    apply mul_nonneg
    · positivity
    · apply mul_nonneg
      · positivity
      · exact DiscreteGaussianSampler.scalarLinearShiftBound_nonneg _ _
  freshnessError_nonneg := freshnessError_nonneg
  normalFormDistance_le := normalFormDistance_le
  smudgingCost_le := by
    intro coordinate hiddenAndContext _hcontext secrets residual hresidual
    simpa only [universalDiscreteGaussianLinearSmudgingError] using
      (evaluationKeySmudgingCost_concreteCorrectResidualSampler_discreteGaussian_le_universal_linear
        params certificate keySwitchErrorSampler coordinate hiddenAndContext.1
        hiddenAndContext.2.1 hiddenAndContext.2.2 secrets residual hresidual)
  freshnessDistance_le := freshnessDistance_le

end ConcreteStatisticalCertificate

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted
