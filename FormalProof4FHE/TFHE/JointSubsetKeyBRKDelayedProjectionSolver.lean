/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.JointSubsetKeyBRKDelayedProjection
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Exact solver for delayed-projection joint subset-key simulation

This file formalizes the constructive part of `sketch/delaydeprojection.md`.

It proves the exact centered-interval congruence count and its coordinatewise
product form, then constructs the disjoint-block invertible-minor solver.  Full
binary column rank exposes a minor that remains a unit over every relevant
power-of-two ring.  The resulting public matrix has disjoint row support and
satisfies the prescribed product exactly, so its factorization residual is
zero.  Failure is contained in a union of binary block-rank failures and is
bounded by

`outputCount * (2 / 2^(slack + 1))`.

The delayed-projection specialization lifts this target-ring factorization to
the large ring and proves that the projected real value contains only the
transformed source error, with no residual-secret term.  Centered modular
representatives have the automatic half-modulus bound.  Row support, bounded
derived error, exact diagonal IID covariance, and a simultaneous PSD bound
give the deterministic/covariance control used by the sketch.  Choosing the
target error to be this exact derived law gives equality of the complete joint
finite laws, hence zero statistical noise defect.

The geometric ellipsoid-volume estimate and continuous/discrete Gaussian
realization are analytic interfaces rather than finite algebraic statements;
they are not asserted here.  In particular, this module makes no unformalized
claim that a specific implementation sampler realizes a Gaussian covariance
completion.
-/

open Matrix OracleComp
open scoped ENNReal BigOperators

namespace FormalProof4FHE.TFHE.JointSubsetKeyBRKDelayedProjection

namespace CenteredIntervalCount

noncomputable def centeredInterval (bound : ℕ) : Finset ℤ :=
  Finset.Icc (-(bound : ℤ)) (bound : ℤ)

theorem ceil_add_one_div_eq_floor_add_one
    (value : ℤ) (modulus : ℕ) (modulus_positive : 0 < modulus) :
    ⌈(((value + 1 : ℤ) : ℚ) / (modulus : ℚ))⌉ =
      ⌊((value : ℚ) / (modulus : ℚ))⌋ + 1 := by
  let quotient : ℚ := (value : ℚ) / (modulus : ℚ)
  have modulus_positive_rat : (0 : ℚ) < modulus := by
    exact_mod_cast modulus_positive
  have floor_bounds :
      ((⌊quotient⌋ : ℤ) : ℚ) ≤ quotient ∧
        quotient < ((⌊quotient⌋ : ℤ) : ℚ) + 1 :=
    Int.floor_eq_iff.mp rfl
  apply Int.ceil_eq_iff.mpr
  push_cast
  constructor
  ·
    have increment_positive : (0 : ℚ) < 1 / (modulus : ℚ) := by positivity
    have quotient_step :
        (((value : ℚ) + 1) / (modulus : ℚ)) =
          quotient + 1 / (modulus : ℚ) := by
      simp only [quotient]
      ring
    rw [quotient_step]
    change ((⌊quotient⌋ : ℤ) : ℚ) + 1 - 1 < quotient + 1 / (modulus : ℚ)
    linarith
  ·
    have strict_integer_bound :
        (value : ℚ) <
          (modulus : ℚ) * (((⌊quotient⌋ : ℤ) : ℚ) + 1) := by
      have multiplied := (div_lt_iff₀ modulus_positive_rat).mp
        (show (value : ℚ) / (modulus : ℚ) <
            ((⌊quotient⌋ : ℤ) : ℚ) + 1 by
          change quotient < ((⌊quotient⌋ : ℤ) : ℚ) + 1
          exact floor_bounds.2)
      simpa [mul_comm] using multiplied
    have strict_integer_bound' :
        value < (modulus : ℤ) * (⌊quotient⌋ + 1) := by
      exact_mod_cast strict_integer_bound
    apply (div_le_iff₀ modulus_positive_rat).mpr
    have successor_bound :
        value + 1 ≤ (modulus : ℤ) * (⌊quotient⌋ + 1) := by omega
    have rational_successor_bound :
      ((value + 1 : ℤ) : ℚ) ≤
        (((modulus : ℤ) * (⌊quotient⌋ + 1) : ℤ) : ℚ) := by
      exact_mod_cast successor_bound
    simpa [mul_comm] using rational_successor_bound

/-- Exact one-coordinate box count, in the same floor/ceiling form as the
paper sketch. -/
theorem card_centeredInterval_filter_modEq
    (bound : ℕ) (residue : ℤ) (modulus : ℕ)
    (modulus_positive : 0 < modulus) :
    ((centeredInterval bound).filter fun value ↦
        value ≡ residue [ZMOD (modulus : ℤ)]).card =
      Int.toNat (max
        (⌊(((bound : ℤ) - residue : ℤ) : ℚ) / (modulus : ℚ)⌋ -
          ⌈((-(bound : ℤ) - residue : ℤ) : ℚ) / (modulus : ℚ)⌉ + 1)
        0) := by
  have interval_eq : centeredInterval bound =
      Finset.Ico (-(bound : ℤ)) ((bound : ℤ) + 1) := by
    ext value
    simp [centeredInterval]
  rw [interval_eq]
  have exactCount := Int.Ico_filter_modEq_card
    (-(bound : ℤ)) ((bound : ℤ) + 1)
      (by exact_mod_cast modulus_positive : (0 : ℤ) < modulus) residue
  push_cast at exactCount ⊢
  have firstCeil :
      ⌈((((bound : ℚ) + 1) - (residue : ℚ)) / (modulus : ℚ))⌉ =
        ⌊(((bound : ℚ) - (residue : ℚ)) / (modulus : ℚ))⌋ + 1 := by
    have shifted := ceil_add_one_div_eq_floor_add_one
      ((bound : ℤ) - residue) modulus modulus_positive
    push_cast at shifted
    rw [show (bound : ℚ) + 1 - residue = (bound - residue) + 1 by ring]
    exact shifted
  rw [firstCeil] at exactCount
  ring_nf at exactCount ⊢
  have natCount := congrArg Int.toNat exactCount
  rw [Int.toNat_natCast] at natCount
  exact natCount

/-- A residue class can occupy at most one point plus the interval width
divided by the modulus.  This is the target-independent coordinate bound from
the sketch. -/
theorem card_centeredInterval_filter_modEq_le
    (bound : ℕ) (residue : ℤ) (modulus : ℕ)
    (modulus_positive : 0 < modulus) :
    ((centeredInterval bound).filter fun value ↦
        value ≡ residue [ZMOD (modulus : ℤ)]).card ≤
      (2 * bound) / modulus + 1 := by
  rw [card_centeredInterval_filter_modEq
    bound residue modulus modulus_positive, Int.toNat_le]
  have floorDifference :
      ⌊(((bound : ℤ) - residue : ℤ) : ℚ) / (modulus : ℚ)⌋ -
          ⌈((-(bound : ℤ) - residue : ℤ) : ℚ) / (modulus : ℚ)⌉ ≤
        ⌊(((2 * bound : ℕ) : ℚ) / (modulus : ℚ))⌋ := by
    calc
      ⌊(((bound : ℤ) - residue : ℤ) : ℚ) / (modulus : ℚ)⌋ -
            ⌈((-(bound : ℤ) - residue : ℤ) : ℚ) / (modulus : ℚ)⌉ =
          ⌊(((bound : ℤ) - residue : ℤ) : ℚ) / (modulus : ℚ)⌋ +
            ⌊-(((-(bound : ℤ) - residue : ℤ) : ℚ) /
              (modulus : ℚ))⌋ := by
        rw [Int.floor_neg]
        ring
      _ ≤ ⌊((((bound : ℤ) - residue : ℤ) : ℚ) / (modulus : ℚ)) +
            -(((-(bound : ℤ) - residue : ℤ) : ℚ) /
              (modulus : ℚ))⌋ := Int.le_floor_add _ _
      _ = ⌊(((2 * bound : ℕ) : ℚ) / (modulus : ℚ))⌋ := by
        congr 1
        push_cast
        ring
  have floorWidth :
      ⌊(((2 * bound : ℕ) : ℚ) / (modulus : ℚ))⌋ =
        (((2 * bound) / modulus : ℕ) : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (2 * bound) modulus
  push_cast at floorDifference floorWidth ⊢
  rw [← floorWidth]
  apply max_le
  · omega
  · rw [floorWidth]
    positivity

end CenteredIntervalCount

namespace CompatibleBox

open Counting

variable {R Row Coordinate : Type}
  [CommRing R] [Fintype R] [DecidableEq R]
  [Fintype Row] [DecidableEq Row]
  [Fintype Coordinate] [DecidableEq Coordinate]

noncomputable def residualBox (allowed : Coordinate → Finset R) :
    Finset (Coordinate → R) :=
  Fintype.piFinset allowed

theorem compatibleResidualBox_eq
    (scale : R) (coefficient : Row → R)
    (primitive : JointSubsetKeyBRKRefined.HasUnitCoordinate coefficient)
    (target : Coordinate → R) (allowed : Coordinate → Finset R) :
    compatibleResidualCandidates
        (scaledCoefficient scale coefficient) target (residualBox allowed) =
      Fintype.piFinset (fun coordinate ↦
        (allowed coordinate).filter fun residual ↦
          target coordinate + residual ∈ (multiplyAddHom scale).range) := by
  classical
  ext residual
  simp only [compatibleResidualCandidates, residualBox, Finset.mem_filter,
    Fintype.mem_piFinset, inRowCombinationRange_scaledPrimitive_iff scale coefficient primitive,
    Pi.add_apply]
  aesop

theorem card_compatibleResidualBox_eq_prod
    (scale : R) (coefficient : Row → R)
    (primitive : JointSubsetKeyBRKRefined.HasUnitCoordinate coefficient)
    (target : Coordinate → R) (allowed : Coordinate → Finset R) :
    (compatibleResidualCandidates
        (scaledCoefficient scale coefficient) target (residualBox allowed)).card =
      ∏ coordinate,
        ((allowed coordinate).filter fun residual ↦
          target coordinate + residual ∈ (multiplyAddHom scale).range).card := by
  rw [compatibleResidualBox_eq scale coefficient primitive target allowed]
  exact Fintype.card_piFinset _

theorem card_compatibleResidualBox_le_prod
    (scale : R) (coefficient : Row → R)
    (primitive : JointSubsetKeyBRKRefined.HasUnitCoordinate coefficient)
    (target : Coordinate → R) (allowed : Coordinate → Finset R)
    (coordinateBound : Coordinate → ℕ)
    (bound : ∀ coordinate,
      ((allowed coordinate).filter fun residual ↦
        target coordinate + residual ∈ (multiplyAddHom scale).range).card ≤
          coordinateBound coordinate) :
    (compatibleResidualCandidates
        (scaledCoefficient scale coefficient) target (residualBox allowed)).card ≤
      ∏ coordinate, coordinateBound coordinate := by
  rw [card_compatibleResidualBox_eq_prod scale coefficient primitive target allowed]
  apply Finset.prod_le_prod
  · intro coordinate _
    positivity
  · intro coordinate _
    exact bound coordinate

theorem card_compatibleResidualBox_le_pow
    (scale : R) (coefficient : Row → R)
    (primitive : JointSubsetKeyBRKRefined.HasUnitCoordinate coefficient)
    (target : Coordinate → R) (allowed : Coordinate → Finset R)
    (coordinateBound : ℕ)
    (bound : ∀ coordinate,
      ((allowed coordinate).filter fun residual ↦
        target coordinate + residual ∈ (multiplyAddHom scale).range).card ≤
          coordinateBound) :
    (compatibleResidualCandidates
        (scaledCoefficient scale coefficient) target (residualBox allowed)).card ≤
      coordinateBound ^ Fintype.card Coordinate := by
  calc
    (compatibleResidualCandidates
        (scaledCoefficient scale coefficient) target (residualBox allowed)).card ≤
        ∏ _coordinate : Coordinate, coordinateBound :=
      card_compatibleResidualBox_le_prod scale coefficient primitive target allowed
        (fun _ ↦ coordinateBound) bound
    _ = coordinateBound ^ Fintype.card Coordinate := by simp

end CompatibleBox

namespace ExactCompatibleProbability

open Counting

variable {R Row Coordinate : Type}
  [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
  [Fintype Row] [DecidableEq Row]
  [Fintype Coordinate] [DecidableEq Coordinate]

noncomputable def compatibleOutputs (coefficient : Row → R) (target : Coordinate → R)
    (residualCandidates : Finset (Coordinate → R)) :=
  (Finset.univ : Finset
      (JointSubsetKeyBRKRefined.rowCombination
        (Coordinate := Coordinate) coefficient).range).filter fun output ↦
    ∃ residual ∈ residualCandidates, output.1 = target + residual

noncomputable def compatibleOutputEquivCompatibleResidual
    (coefficient : Row → R) (target : Coordinate → R)
    (residualCandidates : Finset (Coordinate → R)) :
    ↑(compatibleOutputs coefficient target residualCandidates) ≃
      ↑(compatibleResidualCandidates coefficient target residualCandidates) where
  toFun := fun output ↦ ⟨output.1.1 - target, by
    have hgood := (Finset.mem_filter.mp output.2).2
    rcases hgood with ⟨residual, hresidual, houtput⟩
    have hrecover : output.1.1 - target = residual := by
      rw [houtput]
      simp
    rw [hrecover]
    simp only [compatibleResidualCandidates, Finset.mem_filter]
    refine ⟨hresidual, ?_⟩
    change target + residual ∈ Set.range
      (JointSubsetKeyBRKRefined.rowCombination coefficient)
    rw [← houtput]
    exact output.1.2⟩
  invFun := fun residual ↦ ⟨⟨target + residual.1, by
    have hcompatible := residual.2
    simp only [compatibleResidualCandidates, Finset.mem_filter] at hcompatible
    exact hcompatible.2⟩, by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, residual.1, ?_, rfl⟩
      have hcompatible := residual.2
      simp only [compatibleResidualCandidates, Finset.mem_filter] at hcompatible
      exact hcompatible.1⟩
  left_inv := by
    intro output
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv := by
    intro residual
    apply Subtype.ext
    simp

omit [SampleableType R] in
theorem card_compatibleOutput_eq
    (coefficient : Row → R) (target : Coordinate → R)
    (residualCandidates : Finset (Coordinate → R)) :
    (compatibleOutputs coefficient target residualCandidates).card =
      (compatibleResidualCandidates coefficient target residualCandidates).card := by
  classical
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr
    (compatibleOutputEquivCompatibleResidual coefficient target residualCandidates)

noncomputable local instance matrixSampleable :
    SampleableType (Matrix Row Coordinate R) :=
  JointSubsetKeyBRKRefined.matrixSampleable

theorem probEvent_fixedCoefficient_compatibleResiduals_eq
    (coefficient : Row → R) (target : Coordinate → R)
    (residualCandidates : Finset (Coordinate → R)) :
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ residual ∈ residualCandidates,
            JointSubsetKeyBRKRefined.rowCombination coefficient matrix =
              target + residual) |
        ($ᵗ Matrix Row Coordinate R)] =
      (compatibleResidualCandidates coefficient target residualCandidates).card *
        (Fintype.card
          (JointSubsetKeyBRKRefined.rowCombination
            (Coordinate := Coordinate) coefficient).range : ENNReal)⁻¹ := by
  classical
  let transform := JointSubsetKeyBRKRefined.rowCombination
    (Coordinate := Coordinate) coefficient
  letI : SampleableType transform.range := SampleableType.ofFintype _
  let good : transform.range → Prop := fun output ↦
    ∃ residual ∈ residualCandidates, output.1 = target + residual
  have mapped_uniform :=
    JointSubsetKeyBRKRefined.evalDist_map_surjective_addHom_uniform transform.rangeRestrict
      (AddMonoidHom.rangeRestrict_surjective transform)
  calc
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ residual ∈ residualCandidates,
            JointSubsetKeyBRKRefined.rowCombination coefficient matrix =
              target + residual) |
        ($ᵗ Matrix Row Coordinate R)] =
        Pr[good | transform.rangeRestrict <$> ($ᵗ Matrix Row Coordinate R)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[good | ($ᵗ transform.range)] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl) mapped_uniform
    _ = (compatibleResidualCandidates coefficient target residualCandidates).card *
        (Fintype.card transform.range : ENNReal)⁻¹ := by
      rw [probEvent_uniformSample]
      have hcard : (Finset.univ.filter good).card =
          (compatibleResidualCandidates coefficient target residualCandidates).card := by
        change (compatibleOutputs coefficient target residualCandidates).card = _
        exact card_compatibleOutput_eq coefficient target residualCandidates
      rw [hcard]
      simp [div_eq_mul_inv]

theorem probEvent_powerOfTwoStratum_residualBox_eq
    (modulusExponent valuation : ℕ) (valuation_le : valuation ≤ modulusExponent)
    (coefficient : Row → ZMod (2 ^ modulusExponent))
    (primitive : JointSubsetKeyBRKRefined.HasUnitCoordinate coefficient)
    (target : Coordinate → ZMod (2 ^ modulusExponent))
    (allowed : Coordinate → Finset (ZMod (2 ^ modulusExponent))) :
    Pr[(fun matrix : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)) ↦
          ∃ residual ∈ CompatibleBox.residualBox allowed,
            JointSubsetKeyBRKRefined.rowCombination
                (Counting.scaledCoefficient
                  ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent)) coefficient) matrix =
              target + residual) |
        ($ᵗ Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))] =
      (∏ coordinate,
          (((allowed coordinate).filter fun residual ↦
            target coordinate + residual ∈
              (Counting.multiplyAddHom
                ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent))).range).card :
            ENNReal)) *
        ((2 : ENNReal) ^
          ((modulusExponent - valuation) * Fintype.card Coordinate))⁻¹ := by
  rw [probEvent_fixedCoefficient_compatibleResiduals_eq]
  rw [CompatibleBox.card_compatibleResidualBox_eq_prod
    ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent)) coefficient primitive]
  rw [Counting.card_rowCombination_scaledPrimitive_pow_two_range
    modulusExponent valuation valuation_le coefficient primitive]
  norm_cast

end ExactCompatibleProbability

namespace BlockMinorSolver

variable {R Output SourceRow Coordinate : Type}
  [CommRing R]
  [Fintype Output] [DecidableEq Output]
  [Fintype SourceRow] [DecidableEq SourceRow]
  [Fintype Coordinate] [DecidableEq Coordinate]

def sourceBlock
    (source : Matrix (Output × SourceRow) Coordinate R) (output : Output) :
    Matrix SourceRow Coordinate R :=
  fun row column ↦ source (output, row) column

/-- The square candidate minor selected publicly inside one source block. -/
def blockMinor
    (source : Matrix (Output × SourceRow) Coordinate R)
    (pivot : Output → Coordinate → SourceRow) (output : Output) :
    Matrix Coordinate Coordinate R :=
  (sourceBlock source output).submatrix (pivot output) (Equiv.refl Coordinate)

/-- Explicit rowwise solver supported on one selected square minor per output row. -/
def blockInversePostprocess
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate R)
    (inverse : Output → Matrix Coordinate Coordinate R) :
    Matrix Output (Output × SourceRow) R :=
  fun output sourceRow ↦
    if sourceRow.1 = output then
      ∑ pivotCoordinate,
        if sourceRow.2 = pivot output pivotCoordinate then
          ∑ coordinate,
            gadget output coordinate * inverse output coordinate pivotCoordinate
        else 0
    else 0

theorem blockInversePostprocess_mul
    (source : Matrix (Output × SourceRow) Coordinate R)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate R)
    (inverse : Output → Matrix Coordinate Coordinate R)
    (inverse_minor : ∀ output,
      inverse output * blockMinor source pivot output = 1) :
    blockInversePostprocess pivot gadget inverse * source = gadget := by
  classical
  ext output column
  calc
    (blockInversePostprocess pivot gadget inverse * source) output column =
        ((gadget * inverse output) * blockMinor source pivot output) output column := by
      simp only [Matrix.mul_apply, blockInversePostprocess, blockMinor,
        Fintype.sum_prod_type]
      simp only [ite_mul, zero_mul, Finset.sum_mul]
      rw [Finset.sum_eq_single output]
      · simp only [if_pos]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro pivotCoordinate _
        rw [Finset.sum_eq_single (pivot output pivotCoordinate)]
        · simp [sourceBlock]
        · intro other _ hother
          simp [hother]
        · simp
      · intro other _ hother
        simp [hother]
      · simp
    _ = (gadget * (inverse output * blockMinor source pivot output)) output column := by
      rw [Matrix.mul_assoc]
    _ = gadget output column := by
      rw [inverse_minor output]
      simp

omit [Fintype Output] [Fintype SourceRow] [DecidableEq Coordinate] in
theorem blockInversePostprocess_otherBlock
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate R)
    (inverse : Output → Matrix Coordinate Coordinate R)
    (output other : Output) (sourceCoordinate : SourceRow)
    (hne : other ≠ output) :
    blockInversePostprocess pivot gadget inverse output
      (other, sourceCoordinate) = 0 := by
  simp [blockInversePostprocess, hne]

omit [Fintype Output] [Fintype SourceRow] [DecidableEq Coordinate] in
/-- Distinct output rows have disjoint block support. -/
theorem blockInversePostprocess_disjoint_support
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate R)
    (inverse : Output → Matrix Coordinate Coordinate R)
    (first second : Output) (hne : first ≠ second)
    (sourceRow : Output × SourceRow) :
    blockInversePostprocess pivot gadget inverse first sourceRow = 0 ∨
      blockInversePostprocess pivot gadget inverse second sourceRow = 0 := by
  by_cases hfirst : sourceRow.1 = first
  · right
    apply blockInversePostprocess_otherBlock pivot
    exact fun hsecond ↦ hne (hfirst.symm.trans hsecond)
  · left
    simp [blockInversePostprocess, hfirst]

noncomputable def inverseMinor
    (minor : Matrix Coordinate Coordinate R) (unit : IsUnit minor) :
    Matrix Coordinate Coordinate R :=
  (unit.unit⁻¹ : (Matrix Coordinate Coordinate R)ˣ)

theorem inverseMinor_mul
    (minor : Matrix Coordinate Coordinate R) (unit : IsUnit minor) :
    inverseMinor minor unit * minor = 1 := by
  change ((unit.unit⁻¹ : (Matrix Coordinate Coordinate R)ˣ) :
      Matrix Coordinate Coordinate R) * minor = 1
  calc
    ((unit.unit⁻¹ : (Matrix Coordinate Coordinate R)ˣ) :
        Matrix Coordinate Coordinate R) * minor =
        ((unit.unit⁻¹ : (Matrix Coordinate Coordinate R)ˣ) :
          Matrix Coordinate Coordinate R) * unit.unit := by
      rw [unit.unit_spec]
    _ = 1 := Units.inv_mul _

noncomputable def publicBlockPostprocess
    (source : Matrix (Output × SourceRow) Coordinate R)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate R)
    (minorUnit : ∀ output, IsUnit (blockMinor source pivot output)) :
    Matrix Output (Output × SourceRow) R :=
  blockInversePostprocess pivot gadget fun output ↦
    inverseMinor (blockMinor source pivot output) (minorUnit output)

theorem publicBlockPostprocess_mul
    (source : Matrix (Output × SourceRow) Coordinate R)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate R)
    (minorUnit : ∀ output, IsUnit (blockMinor source pivot output)) :
    publicBlockPostprocess source pivot gadget minorUnit * source = gadget := by
  apply blockInversePostprocess_mul
  intro output
  exact inverseMinor_mul _ _

/-- The public block solver is an exact factorization object with no residual map. -/
noncomputable def publicBlockFactorization
    (source : Matrix (Output × SourceRow) Coordinate R)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate R)
    (minorUnit : ∀ output, IsUnit (blockMinor source pivot output)) :
    JointSubsetKeyBRK.Factorization source.mulVecLin gadget.mulVecLin :=
  JointSubsetKeyBRKRefined.matrixFactorizationOfProduct source gadget
    (publicBlockPostprocess source pivot gadget minorUnit)
    (publicBlockPostprocess_mul source pivot gadget minorUnit)

end BlockMinorSolver

namespace MinorExtraction

variable {F Row Coordinate : Type}
  [Field F]
  [Fintype Row]
  [Fintype Coordinate] [DecidableEq Coordinate]

/-- Full column rank over a field exposes a square invertible row minor. -/
theorem exists_invertible_row_minor
    (matrix : Matrix Row Coordinate F)
    (fullRank : matrix.rank = Fintype.card Coordinate) :
    ∃ pivot : Coordinate → Row, Function.Injective pivot ∧
      IsUnit (matrix.submatrix pivot (Equiv.refl Coordinate)) := by
  classical
  obtain ⟨rows, rows_subset, rows_card, _rows_span, rows_independent⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn F (Set.range matrix.row)
  have span_finrank :
      Module.finrank F (Submodule.span F (Set.range matrix.row)) =
        Fintype.card Coordinate := by
    rw [← matrix.rank_eq_finrank_span_row, fullRank]
  have selected_card : rows.card = Fintype.card Coordinate :=
    rows_card.trans span_finrank
  let indexEquiv : Coordinate ≃ ↑rows :=
    Fintype.equivOfCardEq (by simpa using selected_card.symm)
  have selected_mem (coordinate : Coordinate) :
      (indexEquiv coordinate : Coordinate → F) ∈ Set.range matrix.row :=
    rows_subset (indexEquiv coordinate).property
  choose pivot hpivot using selected_mem
  have pivot_injective : Function.Injective pivot := by
    intro first second hpivotEq
    apply indexEquiv.injective
    apply Subtype.ext
    rw [← hpivot first, ← hpivot second, hpivotEq]
  refine ⟨pivot, pivot_injective, ?_⟩
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  have selectedLinearIndependent :
      LinearIndependent F (fun coordinate : Coordinate ↦
        (indexEquiv coordinate : Coordinate → F)) :=
    rows_independent.linearIndependent_restrict.comp _ indexEquiv.injective
  convert selectedLinearIndependent using 1
  funext coordinate
  ext column
  exact congrFun (hpivot coordinate) column

end MinorExtraction

namespace PowerOfTwoMinor

variable {Row Coordinate : Type}
  [Fintype Row]
  [Fintype Coordinate] [DecidableEq Coordinate]

/-- A full-rank binary reduction exposes a square minor which is already a
unit over the complete scalar power-of-two ring. -/
theorem exists_invertible_row_minor_of_binary_rank
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (source : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))
    (fullRank :
      (source.map (ZMod.castHom
        (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) (ZMod 2))).rank =
          Fintype.card Coordinate) :
    ∃ pivot : Coordinate → Row, Function.Injective pivot ∧
      IsUnit (source.submatrix pivot (Equiv.refl Coordinate)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let heven : 2 ∣ 2 ^ modulusExponent :=
    pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)
  let parity : ZMod (2 ^ modulusExponent) →+* ZMod 2 :=
    ZMod.castHom heven (ZMod 2)
  letI : IsLocalHom parity :=
    FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing.isLocalHom_toZModTwo_of_nilpotent_kernel
      parity (by
        intro value parity_zero
        exact FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing.zmod_powerOfTwo_isNilpotent_of_castHom_eq_zero
          modulusExponent modulusExponent_positive value parity_zero)
  have binaryFullRank : (source.map parity).rank = Fintype.card Coordinate := by
    simpa [parity, heven] using fullRank
  obtain ⟨pivot, pivot_injective, binaryMinorUnit⟩ :=
    MinorExtraction.exists_invertible_row_minor (source.map parity) binaryFullRank
  refine ⟨pivot, pivot_injective, ?_⟩
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply (isUnit_map_iff parity _).mp
  rw [parity.map_det]
  have mappedMinor :
      parity.mapMatrix (source.submatrix pivot (Equiv.refl Coordinate)) =
        (source.map parity).submatrix pivot (Equiv.refl Coordinate) := by
    rfl
  rw [mappedMinor]
  exact (Matrix.isUnit_iff_isUnit_det _).mp binaryMinorUnit

/-- Simultaneous blockwise form.  Every successful binary-rank block yields a
publicly selected sparse postprocessing row, and all rows solve the prescribed
gadget equation together. -/
theorem exists_exact_publicBlockPostprocess_of_binary_rank
    {Output SourceRow Coordinate : Type}
    [Fintype Output] [DecidableEq Output]
    [Fintype SourceRow] [DecidableEq SourceRow]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (source : Matrix (Output × SourceRow) Coordinate
      (ZMod (2 ^ modulusExponent)))
    (gadget : Matrix Output Coordinate (ZMod (2 ^ modulusExponent)))
    (fullRank : ∀ output,
      ((BlockMinorSolver.sourceBlock source output).map
        (ZMod.castHom
          (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) (ZMod 2))).rank =
        Fintype.card Coordinate) :
    ∃ pivot : Output → Coordinate → SourceRow,
      (∀ output, Function.Injective (pivot output)) ∧
      ∃ postprocess : Matrix Output (Output × SourceRow)
          (ZMod (2 ^ modulusExponent)),
        postprocess * source = gadget ∧
        ∀ output other sourceRow, other ≠ output →
          postprocess output (other, sourceRow) = 0 := by
  classical
  have minor_exists (output : Output) :
      ∃ pivot : Coordinate → SourceRow, Function.Injective pivot ∧
        IsUnit ((BlockMinorSolver.sourceBlock source output).submatrix
          pivot (Equiv.refl Coordinate)) :=
    exists_invertible_row_minor_of_binary_rank
      modulusExponent modulusExponent_positive
      (BlockMinorSolver.sourceBlock source output) (fullRank output)
  choose pivot pivot_injective selectedMinorUnit using minor_exists
  have blockMinorUnit (output : Output) :
      IsUnit (BlockMinorSolver.blockMinor source pivot output) := by
    simpa [BlockMinorSolver.blockMinor] using
      selectedMinorUnit output
  let postprocess :=
    BlockMinorSolver.publicBlockPostprocess source pivot gadget blockMinorUnit
  refine ⟨pivot, pivot_injective, postprocess, ?_, ?_⟩
  · exact BlockMinorSolver.publicBlockPostprocess_mul
      source pivot gadget blockMinorUnit
  · intro output other sourceRow hne
    exact BlockMinorSolver.blockInversePostprocess_otherBlock pivot gadget
      (fun index ↦ BlockMinorSolver.inverseMinor
        (BlockMinorSolver.blockMinor source pivot index) (blockMinorUnit index))
      output other sourceRow hne

end PowerOfTwoMinor

namespace BlockRankProbability

variable {R Output Row Coordinate : Type}
  [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
  [Fintype Output] [DecidableEq Output]
  [Fintype Row] [DecidableEq Row]
  [Fintype Coordinate] [DecidableEq Coordinate]

def blockProjection (output : Output) :
    Matrix (Output × Row) Coordinate R →+ Matrix Row Coordinate R where
  toFun := fun matrix row coordinate ↦ matrix (output, row) coordinate
  map_zero' := rfl
  map_add' := by
    intro left right
    rfl

omit [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Output] [Fintype Row] [DecidableEq Row]
    [Fintype Coordinate] [DecidableEq Coordinate] in
theorem blockProjection_surjective (output : Output) :
    Function.Surjective
      (blockProjection (R := R) (Row := Row) (Coordinate := Coordinate) output) := by
  classical
  intro target
  let source : Matrix (Output × Row) Coordinate R := fun indexedRow coordinate ↦
    if indexedRow.1 = output then target indexedRow.2 coordinate else 0
  refine ⟨source, ?_⟩
  ext row coordinate
  simp [blockProjection, source]

noncomputable local instance largeMatrixSampleable :
    SampleableType (Matrix (Output × Row) Coordinate R) :=
  JointSubsetKeyBRKRefined.matrixSampleable

noncomputable local instance blockMatrixSampleable :
    SampleableType (Matrix Row Coordinate R) :=
  JointSubsetKeyBRKRefined.matrixSampleable

theorem evalDist_blockProjection_uniform (output : Output) :
    evalDist
        (blockProjection (R := R) (Row := Row) (Coordinate := Coordinate) output <$>
          ($ᵗ Matrix (Output × Row) Coordinate R)) =
      evalDist ($ᵗ Matrix Row Coordinate R) := by
  exact JointSubsetKeyBRKRefined.evalDist_map_surjective_addHom_uniform
    (blockProjection (R := R) (Row := Row) (Coordinate := Coordinate) output)
    (blockProjection_surjective (R := R) (Row := Row) (Coordinate := Coordinate) output)

set_option maxHeartbeats 1000000 in
theorem binaryAnyBlockRankFailure_le
    (outputCount dimension slack : ℕ) :
    Pr[(fun matrix : Matrix
          (Fin outputCount × Fin (dimension + slack)) (Fin dimension) (ZMod 2) ↦
          ∃ output : Fin outputCount,
            (blockProjection output matrix).rank < dimension) |
        ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
          (Fin dimension) (ZMod 2))] ≤
      (outputCount : ENNReal) *
        (2 / (2 : ENNReal) ^ (slack + 1)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  calc
    Pr[(fun matrix : Matrix
          (Fin outputCount × Fin (dimension + slack)) (Fin dimension) (ZMod 2) ↦
          ∃ output : Fin outputCount,
            (blockProjection output matrix).rank < dimension) |
        ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
          (Fin dimension) (ZMod 2))] ≤
        ∑ output : Fin outputCount,
          Pr[(fun matrix : Matrix
              (Fin outputCount × Fin (dimension + slack)) (Fin dimension) (ZMod 2) ↦
              (blockProjection output matrix).rank < dimension) |
            ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
              (Fin dimension) (ZMod 2))] := by
      simpa only [Finset.mem_univ, true_and] using
        (probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin outputCount))
          ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
            (Fin dimension) (ZMod 2))
          (fun output matrix ↦ (blockProjection output matrix).rank < dimension))
    _ = ∑ _output : Fin outputCount,
          Pr[(fun matrix : Matrix (Fin (dimension + slack)) (Fin dimension) (ZMod 2) ↦
              matrix.rank < dimension) |
            ($ᵗ Matrix (Fin (dimension + slack)) (Fin dimension) (ZMod 2))] := by
      apply Finset.sum_congr rfl
      intro output _
      calc
        Pr[(fun matrix : Matrix
              (Fin outputCount × Fin (dimension + slack)) (Fin dimension) (ZMod 2) ↦
              (blockProjection output matrix).rank < dimension) |
            ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
              (Fin dimension) (ZMod 2))] =
            Pr[(fun matrix : Matrix (Fin (dimension + slack))
                (Fin dimension) (ZMod 2) ↦ matrix.rank < dimension) |
              blockProjection output <$>
                ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
                  (Fin dimension) (ZMod 2))] := by
          rw [probEvent_map]
          rfl
        _ = Pr[(fun matrix : Matrix (Fin (dimension + slack))
              (Fin dimension) (ZMod 2) ↦ matrix.rank < dimension) |
            ($ᵗ Matrix (Fin (dimension + slack)) (Fin dimension) (ZMod 2))] :=
          probEvent_congr' (fun _ _ ↦ Iff.rfl)
            (evalDist_blockProjection_uniform output)
    _ ≤ ∑ _output : Fin outputCount,
          (2 / (2 : ENNReal) ^ (slack + 1)) := by
      apply Finset.sum_le_sum
      intro output _
      simpa using
        (FormalProof4FHE.FiniteFieldRank.rankFailure_le
          (F := ZMod 2) dimension slack)
    _ = (outputCount : ENNReal) *
        (2 / (2 : ENNReal) ^ (slack + 1)) := by
      simp

theorem powerOfTwoAnyBlockRankFailure_le
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (outputCount dimension slack : ℕ) :
    Pr[(fun matrix : Matrix
          (Fin outputCount × Fin (dimension + slack)) (Fin dimension)
            (ZMod (2 ^ modulusExponent)) ↦
          ∃ output : Fin outputCount,
            ((blockProjection output matrix).map
              (ZMod.castHom
                (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) (ZMod 2))).rank <
              dimension) |
        ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
          (Fin dimension) (ZMod (2 ^ modulusExponent)))] ≤
      (outputCount : ENNReal) *
        (2 / (2 : ENNReal) ^ (slack + 1)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let heven : 2 ∣ 2 ^ modulusExponent :=
    pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)
  let parity : ZMod (2 ^ modulusExponent) →+* ZMod 2 :=
    ZMod.castHom heven (ZMod 2)
  let matrixParity :
      Matrix (Fin outputCount × Fin (dimension + slack)) (Fin dimension)
          (ZMod (2 ^ modulusExponent)) →+
        Matrix (Fin outputCount × Fin (dimension + slack)) (Fin dimension) (ZMod 2) :=
    JointSubsetKeyBRKRefined.matrixMapAddHom parity.toAddMonoidHom
  have matrixParity_surjective : Function.Surjective matrixParity :=
    JointSubsetKeyBRKRefined.matrixMapAddHom_surjective parity.toAddMonoidHom
      (ZMod.castHom_surjective heven)
  have mapped_uniform :
      evalDist
          (matrixParity <$>
            ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
              (Fin dimension) (ZMod (2 ^ modulusExponent)))) =
        evalDist
          ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
            (Fin dimension) (ZMod 2)) :=
    JointSubsetKeyBRKRefined.evalDist_map_surjective_addHom_uniform
      matrixParity matrixParity_surjective
  calc
    Pr[(fun matrix : Matrix
          (Fin outputCount × Fin (dimension + slack)) (Fin dimension)
            (ZMod (2 ^ modulusExponent)) ↦
          ∃ output : Fin outputCount,
            ((blockProjection output matrix).map
              (ZMod.castHom
                (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) (ZMod 2))).rank <
              dimension) |
        ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
          (Fin dimension) (ZMod (2 ^ modulusExponent)))] =
        Pr[(fun matrix : Matrix
              (Fin outputCount × Fin (dimension + slack)) (Fin dimension) (ZMod 2) ↦
              ∃ output : Fin outputCount,
                (blockProjection output matrix).rank < dimension) |
          matrixParity <$>
            ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
              (Fin dimension) (ZMod (2 ^ modulusExponent)))] := by
      rw [probEvent_map]
      rfl
    _ = Pr[(fun matrix : Matrix
            (Fin outputCount × Fin (dimension + slack)) (Fin dimension) (ZMod 2) ↦
            ∃ output : Fin outputCount,
              (blockProjection output matrix).rank < dimension) |
        ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
          (Fin dimension) (ZMod 2))] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl) mapped_uniform
    _ ≤ (outputCount : ENNReal) *
        (2 / (2 : ENNReal) ^ (slack + 1)) :=
      binaryAnyBlockRankFailure_le outputCount dimension slack

/-- Failure to obtain one exact, disjointly supported public solution row per
output block is contained in the binary block-rank failure event. -/
theorem powerOfTwoBlockSolverFailure_le
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (outputCount dimension slack : ℕ)
    (gadget : Matrix (Fin outputCount) (Fin dimension)
      (ZMod (2 ^ modulusExponent))) :
    Pr[(fun source : Matrix
          (Fin outputCount × Fin (dimension + slack)) (Fin dimension)
            (ZMod (2 ^ modulusExponent)) ↦
          ¬ ∃ postprocess : Matrix (Fin outputCount)
              (Fin outputCount × Fin (dimension + slack))
                (ZMod (2 ^ modulusExponent)),
            postprocess * source = gadget ∧
              ∀ output other sourceRow, other ≠ output →
                postprocess output (other, sourceRow) = 0) |
        ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
          (Fin dimension) (ZMod (2 ^ modulusExponent)))] ≤
      (outputCount : ENNReal) *
        (2 / (2 : ENNReal) ^ (slack + 1)) := by
  classical
  calc
    Pr[(fun source : Matrix
          (Fin outputCount × Fin (dimension + slack)) (Fin dimension)
            (ZMod (2 ^ modulusExponent)) ↦
          ¬ ∃ postprocess : Matrix (Fin outputCount)
              (Fin outputCount × Fin (dimension + slack))
                (ZMod (2 ^ modulusExponent)),
            postprocess * source = gadget ∧
              ∀ output other sourceRow, other ≠ output →
                postprocess output (other, sourceRow) = 0) |
        ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
          (Fin dimension) (ZMod (2 ^ modulusExponent)))] ≤
        Pr[(fun source : Matrix
            (Fin outputCount × Fin (dimension + slack)) (Fin dimension)
              (ZMod (2 ^ modulusExponent)) ↦
            ∃ output : Fin outputCount,
              ((blockProjection output source).map
                (ZMod.castHom
                  (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent))
                    (ZMod 2))).rank < dimension) |
          ($ᵗ Matrix (Fin outputCount × Fin (dimension + slack))
            (Fin dimension) (ZMod (2 ^ modulusExponent)))] := by
      apply probEvent_mono
      intro source _ solverFailure
      by_contra noBadBlock
      have fullRank (output : Fin outputCount) :
          ((BlockMinorSolver.sourceBlock source output).map
            (ZMod.castHom
              (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent))
                (ZMod 2))).rank = dimension := by
        have rank_le := Matrix.rank_le_width
          ((BlockMinorSolver.sourceBlock source output).map
            (ZMod.castHom
              (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent))
                (ZMod 2)))
        have not_lt : ¬
            ((BlockMinorSolver.sourceBlock source output).map
              (ZMod.castHom
                (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent))
                  (ZMod 2))).rank < dimension := by
          intro rank_lt
          apply noBadBlock
          refine ⟨output, ?_⟩
          change ((blockProjection output source).map
            (ZMod.castHom
              (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent))
                (ZMod 2))).rank < dimension at rank_lt
          exact rank_lt
        omega
      obtain ⟨_pivot, _pivotInjective, postprocess, product_eq, disjoint⟩ :=
        PowerOfTwoMinor.exists_exact_publicBlockPostprocess_of_binary_rank
          modulusExponent modulusExponent_positive source gadget
            (fun output ↦ by simpa using fullRank output)
      exact solverFailure ⟨postprocess, product_eq, disjoint⟩
    _ ≤ (outputCount : ENNReal) *
        (2 / (2 : ENNReal) ^ (slack + 1)) :=
      powerOfTwoAnyBlockRankFailure_le modulusExponent
        modulusExponent_positive outputCount dimension slack

end BlockRankProbability

namespace BlockNoise

open BlockMinorSolver

variable {Output SourceRow Coordinate : Type}
  [Fintype Output] [DecidableEq Output]
  [Fintype SourceRow] [DecidableEq SourceRow]
  [Fintype Coordinate] [DecidableEq Coordinate]

noncomputable def rowSupport (matrix : Matrix Output (Output × SourceRow) ℝ)
    (output : Output) : Finset (Output × SourceRow) :=
  Finset.univ.filter fun sourceRow ↦ matrix output sourceRow ≠ 0

def selectedRows (pivot : Output → Coordinate → SourceRow)
    (output : Output) : Finset (Output × SourceRow) :=
  Finset.univ.image fun coordinate ↦ (output, pivot output coordinate)

omit [DecidableEq Coordinate] in
theorem blockInversePostprocess_rowSupport_subset
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ)
    (output : Output) :
    rowSupport (blockInversePostprocess pivot gadget inverse) output ⊆
      selectedRows pivot output := by
  classical
  intro sourceRow hsourceRow
  have hnonzero := (Finset.mem_filter.mp hsourceRow).2
  have hblock : sourceRow.1 = output := by
    by_contra hne
    exact hnonzero (by simp [blockInversePostprocess, hne])
  by_contra hnotSelected
  have noPivot : ∀ coordinate, sourceRow.2 ≠ pivot output coordinate := by
    intro coordinate heq
    apply hnotSelected
    apply Finset.mem_image.mpr
    refine ⟨coordinate, Finset.mem_univ coordinate, ?_⟩
    exact Prod.ext hblock.symm heq.symm
  exact hnonzero (by simp [blockInversePostprocess, hblock, noPivot])

omit [DecidableEq Coordinate] in
theorem card_blockInversePostprocess_rowSupport_le
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ)
    (output : Output) :
    (rowSupport (blockInversePostprocess pivot gadget inverse) output).card ≤
      Fintype.card Coordinate := by
  calc
    (rowSupport (blockInversePostprocess pivot gadget inverse) output).card ≤
        (selectedRows pivot output).card :=
      Finset.card_le_card (blockInversePostprocess_rowSupport_subset
        pivot gadget inverse output)
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card Coordinate := Finset.card_univ

def rowEnergy (matrix : Matrix Output (Output × SourceRow) ℝ)
    (output : Output) : ℝ :=
  ∑ sourceRow, (matrix output sourceRow) ^ 2

omit [DecidableEq Output] [DecidableEq SourceRow] in
theorem rowEnergy_eq_sum_support
    (matrix : Matrix Output (Output × SourceRow) ℝ) (output : Output) :
    rowEnergy matrix output =
      ∑ sourceRow ∈ rowSupport matrix output, (matrix output sourceRow) ^ 2 := by
  classical
  rw [rowEnergy, rowSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro sourceRow _
  by_cases hzero : matrix output sourceRow = 0 <;> simp [hzero]

omit [DecidableEq Coordinate] in
/-- If centered representatives have magnitude at most `bound`, the selected
minor construction has squared row norm at most `n * bound²`. -/
theorem blockInversePostprocess_rowEnergy_le
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (entry_bound : ∀ output sourceRow,
      |blockInversePostprocess pivot gadget inverse output sourceRow| ≤ bound)
    (output : Output) :
    rowEnergy (blockInversePostprocess pivot gadget inverse) output ≤
      Fintype.card Coordinate * bound ^ 2 := by
  rw [rowEnergy_eq_sum_support]
  calc
    ∑ sourceRow ∈ rowSupport (blockInversePostprocess pivot gadget inverse) output,
        (blockInversePostprocess pivot gadget inverse output sourceRow) ^ 2 ≤
        (rowSupport (blockInversePostprocess pivot gadget inverse) output).card *
          bound ^ 2 := by
      simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul
          (rowSupport (blockInversePostprocess pivot gadget inverse) output)
          (fun sourceRow ↦
            (blockInversePostprocess pivot gadget inverse output sourceRow) ^ 2)
          (bound ^ 2) (by
            intro sourceRow _
            have hsquare := (sq_le_sq₀
              (abs_nonneg (blockInversePostprocess pivot gadget inverse output sourceRow))
              bound_nonneg).2 (entry_bound output sourceRow)
            simpa only [sq_abs] using hsquare)
    _ ≤ Fintype.card Coordinate * bound ^ 2 := by
      gcongr
      exact card_blockInversePostprocess_rowSupport_le
        pivot gadget inverse output

omit [DecidableEq Coordinate] in
/-- Deterministic bounded-error consequence: a row with at most `n` supported
entries, coefficient bound `bound`, and source-error bound `errorBound` has
derived absolute error at most `n * bound * errorBound`. -/
theorem abs_blockInversePostprocess_mulVec_le
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ)
    (bound errorBound : ℝ) (bound_nonneg : 0 ≤ bound)
    (errorBound_nonneg : 0 ≤ errorBound)
    (entry_bound : ∀ output sourceRow,
      |blockInversePostprocess pivot gadget inverse output sourceRow| ≤ bound)
    (sourceError : Output × SourceRow → ℝ)
    (sourceError_bound : ∀ sourceRow, |sourceError sourceRow| ≤ errorBound)
    (output : Output) :
    |(blockInversePostprocess pivot gadget inverse).mulVec sourceError output| ≤
      Fintype.card Coordinate * bound * errorBound := by
  classical
  have sum_eq_support :
      (∑ sourceRow,
          |blockInversePostprocess pivot gadget inverse output sourceRow *
            sourceError sourceRow|) =
        ∑ sourceRow ∈
            rowSupport (blockInversePostprocess pivot gadget inverse) output,
          |blockInversePostprocess pivot gadget inverse output sourceRow *
            sourceError sourceRow| := by
    symm
    rw [rowSupport, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro sourceRow _
    by_cases hzero :
        blockInversePostprocess pivot gadget inverse output sourceRow = 0 <;>
      simp [hzero]
  rw [Matrix.mulVec, dotProduct]
  calc
    |∑ sourceRow,
        blockInversePostprocess pivot gadget inverse output sourceRow *
          sourceError sourceRow| ≤
        ∑ sourceRow,
          |blockInversePostprocess pivot gadget inverse output sourceRow *
            sourceError sourceRow| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ sourceRow ∈
          rowSupport (blockInversePostprocess pivot gadget inverse) output,
        |blockInversePostprocess pivot gadget inverse output sourceRow *
          sourceError sourceRow| := sum_eq_support
    _ ≤ (rowSupport
          (blockInversePostprocess pivot gadget inverse) output).card *
        (bound * errorBound) := by
      simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul
          (rowSupport (blockInversePostprocess pivot gadget inverse) output)
          (fun sourceRow ↦
            |blockInversePostprocess pivot gadget inverse output sourceRow *
              sourceError sourceRow|)
          (bound * errorBound) (by
            intro sourceRow _
            rw [abs_mul]
            exact mul_le_mul (entry_bound output sourceRow)
              (sourceError_bound sourceRow) (abs_nonneg _) bound_nonneg)
    _ ≤ Fintype.card Coordinate * (bound * errorBound) := by
      gcongr
      exact card_blockInversePostprocess_rowSupport_le
        pivot gadget inverse output
    _ = Fintype.card Coordinate * bound * errorBound := by ring

omit [DecidableEq Coordinate] in
theorem blockInversePostprocess_crossGram_eq_zero
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ)
    (first second : Output) (hne : first ≠ second) :
    ∑ sourceRow,
        blockInversePostprocess pivot gadget inverse first sourceRow *
          blockInversePostprocess pivot gadget inverse second sourceRow = 0 := by
  apply Finset.sum_eq_zero
  intro sourceRow _
  rcases blockInversePostprocess_disjoint_support
      pivot gadget inverse first second hne sourceRow with hfirst | hsecond
  · simp [hfirst]
  · simp [hsecond]

def iidDerivedCovariance (variance : ℝ)
    (postprocess : Matrix Output (Output × SourceRow) ℝ) :
    Matrix Output Output ℝ :=
  postprocess * (variance • (1 : Matrix (Output × SourceRow)
    (Output × SourceRow) ℝ)) * postprocess.transpose

theorem iidDerivedCovariance_apply
    (variance : ℝ)
    (postprocess : Matrix Output (Output × SourceRow) ℝ)
    (first second : Output) :
    iidDerivedCovariance variance postprocess first second =
      variance * ∑ sourceRow, postprocess first sourceRow * postprocess second sourceRow := by
  classical
  simp [iidDerivedCovariance, Matrix.mul_apply, mul_assoc, Finset.mul_sum]

omit [DecidableEq Coordinate] in
theorem iidDerivedCovariance_blockInversePostprocess_offDiagonal
    (variance : ℝ)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ)
    (first second : Output) (hne : first ≠ second) :
    iidDerivedCovariance variance
      (blockInversePostprocess pivot gadget inverse) first second = 0 := by
  rw [iidDerivedCovariance_apply,
    blockInversePostprocess_crossGram_eq_zero pivot gadget inverse first second hne,
    mul_zero]

omit [DecidableEq Coordinate] in
theorem iidDerivedCovariance_blockInversePostprocess_diagonal_le
    (variance bound : ℝ) (variance_nonneg : 0 ≤ variance)
    (bound_nonneg : 0 ≤ bound)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ)
    (entry_bound : ∀ output sourceRow,
      |blockInversePostprocess pivot gadget inverse output sourceRow| ≤ bound)
    (output : Output) :
    iidDerivedCovariance variance
        (blockInversePostprocess pivot gadget inverse) output output ≤
      variance * Fintype.card Coordinate * bound ^ 2 := by
  rw [iidDerivedCovariance_apply]
  have sum_eq_energy :
      (∑ sourceRow,
          blockInversePostprocess pivot gadget inverse output sourceRow *
            blockInversePostprocess pivot gadget inverse output sourceRow) =
        rowEnergy (blockInversePostprocess pivot gadget inverse) output := by
    simp [rowEnergy, pow_two]
  rw [sum_eq_energy]
  calc
    variance * rowEnergy (blockInversePostprocess pivot gadget inverse) output ≤
        variance * (Fintype.card Coordinate * bound ^ 2) := by
      gcongr
      exact blockInversePostprocess_rowEnergy_le
        pivot gadget inverse bound bound_nonneg entry_bound output
    _ = variance * Fintype.card Coordinate * bound ^ 2 := by ring

omit [DecidableEq Coordinate] in
/-- Disjoint block support makes the complete IID derived covariance exactly
diagonal, not just bounded row by row. -/
theorem iidDerivedCovariance_blockInversePostprocess_eq_diagonal
    (variance : ℝ)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ) :
    iidDerivedCovariance variance (blockInversePostprocess pivot gadget inverse) =
      Matrix.diagonal fun output ↦
        variance * rowEnergy (blockInversePostprocess pivot gadget inverse) output := by
  classical
  ext first second
  by_cases heq : first = second
  · subst second
    rw [iidDerivedCovariance_apply]
    simp [Matrix.diagonal, rowEnergy, pow_two]
  · rw [iidDerivedCovariance_blockInversePostprocess_offDiagonal
      variance pivot gadget inverse first second heq]
    simp [Matrix.diagonal, heq]

omit [DecidableEq Coordinate] in
/-- Simultaneous PSD covariance bound corresponding to the sketch's
`Sigma_der <= variance * n * bound^2 * I`. -/
theorem iidDerivedCovariance_blockInversePostprocess_psd_le
    (variance bound : ℝ) (variance_nonneg : 0 ≤ variance)
    (bound_nonneg : 0 ≤ bound)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ)
    (entry_bound : ∀ output sourceRow,
      |blockInversePostprocess pivot gadget inverse output sourceRow| ≤ bound) :
    ((variance * Fintype.card Coordinate * bound ^ 2) •
          (1 : Matrix Output Output ℝ) -
        iidDerivedCovariance variance
          (blockInversePostprocess pivot gadget inverse)).PosSemidef := by
  classical
  rw [iidDerivedCovariance_blockInversePostprocess_eq_diagonal]
  have matrix_eq :
      (variance * Fintype.card Coordinate * bound ^ 2) •
            (1 : Matrix Output Output ℝ) -
          Matrix.diagonal (fun output ↦ variance *
            rowEnergy (blockInversePostprocess pivot gadget inverse) output) =
        Matrix.diagonal (fun output ↦
          variance * Fintype.card Coordinate * bound ^ 2 -
            variance * rowEnergy
              (blockInversePostprocess pivot gadget inverse) output) := by
    ext first second
    by_cases heq : first = second <;>
      simp [Matrix.diagonal, heq]
  rw [matrix_eq]
  apply Matrix.PosSemidef.diagonal
  intro output
  apply sub_nonneg.mpr
  calc
    variance * rowEnergy
        (blockInversePostprocess pivot gadget inverse) output ≤
        variance * (Fintype.card Coordinate * bound ^ 2) := by
      gcongr
      exact blockInversePostprocess_rowEnergy_le
        pivot gadget inverse bound bound_nonneg entry_bound output
    _ = variance * Fintype.card Coordinate * bound ^ 2 := by ring

omit [DecidableEq Coordinate] in
/-- Any isotropic target variance above the simultaneous bound has a
positive-semidefinite correction covariance.  Constructing a sampler that
realizes this correction remains a separate analytic obligation. -/
theorem iidDerivedCovariance_targetCorrection_posSemidef
    (variance bound targetVariance : ℝ) (variance_nonneg : 0 ≤ variance)
    (bound_nonneg : 0 ≤ bound)
    (target_large :
      variance * Fintype.card Coordinate * bound ^ 2 ≤ targetVariance)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate ℝ)
    (inverse : Output → Matrix Coordinate Coordinate ℝ)
    (entry_bound : ∀ output sourceRow,
      |blockInversePostprocess pivot gadget inverse output sourceRow| ≤ bound) :
    (targetVariance • (1 : Matrix Output Output ℝ) -
        iidDerivedCovariance variance
          (blockInversePostprocess pivot gadget inverse)).PosSemidef := by
  classical
  let covarianceBound := variance * Fintype.card Coordinate * bound ^ 2
  have bounded :
      (covarianceBound • (1 : Matrix Output Output ℝ) -
          iidDerivedCovariance variance
            (blockInversePostprocess pivot gadget inverse)).PosSemidef := by
    exact iidDerivedCovariance_blockInversePostprocess_psd_le
      variance bound variance_nonneg bound_nonneg pivot gadget inverse entry_bound
  have slack :
      ((targetVariance - covarianceBound) •
        (1 : Matrix Output Output ℝ)).PosSemidef := by
    exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr target_large)
  have decompose :
      targetVariance • (1 : Matrix Output Output ℝ) -
          iidDerivedCovariance variance
            (blockInversePostprocess pivot gadget inverse) =
        (targetVariance - covarianceBound) •
            (1 : Matrix Output Output ℝ) +
          (covarianceBound • (1 : Matrix Output Output ℝ) -
            iidDerivedCovariance variance
              (blockInversePostprocess pivot gadget inverse)) := by
    module
  rw [decompose]
  exact slack.add bounded

end BlockNoise

namespace CenteredBlockNoise

open BlockMinorSolver BlockNoise

variable {Output SourceRow Coordinate : Type}
  [Fintype Output] [DecidableEq Output]
  [Fintype SourceRow] [DecidableEq SourceRow]
  [Fintype Coordinate] [DecidableEq Coordinate]

/-- Entrywise centered integer lift of a modular postprocessing matrix. -/
def centeredLift (modulus : ℕ)
    (matrix : Matrix Output (Output × SourceRow) (ZMod modulus)) :
    Matrix Output (Output × SourceRow) ℝ :=
  fun output sourceRow ↦ matrix output sourceRow |>.valMinAbs

def centeredBlockPostprocess (modulus : ℕ)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus)) :
    Matrix Output (Output × SourceRow) ℝ :=
  centeredLift modulus (blockInversePostprocess pivot gadget inverse)

omit [Fintype Output] [DecidableEq Output]
    [Fintype SourceRow] [DecidableEq SourceRow]
    [Fintype Coordinate] [DecidableEq Coordinate] in
/-- Every centered modular representative has the implementation-independent
half-modulus magnitude bound. -/
theorem abs_centeredLift_apply_le_half
    (modulus : ℕ) [NeZero modulus]
    (matrix : Matrix Output (Output × SourceRow) (ZMod modulus))
    (output : Output) (sourceRow : Output × SourceRow) :
    |centeredLift modulus matrix output sourceRow| ≤ (modulus / 2 : ℕ) := by
  change |((matrix output sourceRow).valMinAbs : ℝ)| ≤ (modulus / 2 : ℕ)
  calc
    |((matrix output sourceRow).valMinAbs : ℝ)| =
        ((|(matrix output sourceRow).valMinAbs| : ℤ) : ℝ) :=
      (Int.cast_abs (R := ℝ)).symm
    _ = ((((matrix output sourceRow).valMinAbs.natAbs : ℕ) : ℤ) : ℝ) :=
      congrArg (fun value : ℤ ↦ (value : ℝ))
        (Int.abs_eq_natAbs (matrix output sourceRow).valMinAbs)
    _ = ((matrix output sourceRow).valMinAbs.natAbs : ℝ) := by
      simp only [Int.cast_natCast]
    _ ≤ (modulus / 2 : ℕ) := by
      exact_mod_cast ZMod.natAbs_valMinAbs_le (matrix output sourceRow)

omit [Fintype Output] [Fintype SourceRow]
    [DecidableEq Coordinate] in
theorem centeredBlockPostprocess_otherBlock
    (modulus : ℕ)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus))
    (output other : Output) (sourceRow : SourceRow) (hne : other ≠ output) :
    centeredBlockPostprocess modulus pivot gadget inverse output
      (other, sourceRow) = 0 := by
  simp [centeredBlockPostprocess, centeredLift,
    blockInversePostprocess_otherBlock pivot gadget inverse output other sourceRow hne,
    ZMod.valMinAbs_zero]

omit [DecidableEq Coordinate] in
theorem centeredBlockPostprocess_rowSupport_subset
    (modulus : ℕ)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus))
    (output : Output) :
    rowSupport (centeredBlockPostprocess modulus pivot gadget inverse) output ⊆
      selectedRows pivot output := by
  classical
  intro sourceRow hsourceRow
  have hnonzero := (Finset.mem_filter.mp hsourceRow).2
  have hblock : sourceRow.1 = output := by
    by_contra hne
    exact hnonzero (centeredBlockPostprocess_otherBlock
      modulus pivot gadget inverse output sourceRow.1 sourceRow.2 hne)
  by_contra hnotSelected
  have noPivot : ∀ coordinate, sourceRow.2 ≠ pivot output coordinate := by
    intro coordinate heq
    apply hnotSelected
    apply Finset.mem_image.mpr
    exact ⟨coordinate, Finset.mem_univ coordinate, Prod.ext hblock.symm heq.symm⟩
  exact hnonzero (by
    simp [centeredBlockPostprocess, centeredLift, blockInversePostprocess,
      hblock, noPivot, ZMod.valMinAbs_zero])

omit [DecidableEq Coordinate] in
theorem card_centeredBlockPostprocess_rowSupport_le
    (modulus : ℕ)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus))
    (output : Output) :
    (rowSupport
      (centeredBlockPostprocess modulus pivot gadget inverse) output).card ≤
        Fintype.card Coordinate := by
  calc
    (rowSupport
        (centeredBlockPostprocess modulus pivot gadget inverse) output).card ≤
        (selectedRows pivot output).card :=
      Finset.card_le_card (centeredBlockPostprocess_rowSupport_subset
        modulus pivot gadget inverse output)
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card Coordinate := Finset.card_univ

omit [DecidableEq Coordinate] in
theorem centeredBlockPostprocess_rowEnergy_le
    (modulus : ℕ) [NeZero modulus]
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus))
    (output : Output) :
    rowEnergy (centeredBlockPostprocess modulus pivot gadget inverse) output ≤
      Fintype.card Coordinate * (modulus / 2 : ℕ) ^ 2 := by
  rw [rowEnergy_eq_sum_support]
  calc
    ∑ sourceRow ∈ rowSupport
        (centeredBlockPostprocess modulus pivot gadget inverse) output,
        (centeredBlockPostprocess modulus pivot gadget inverse
          output sourceRow) ^ 2 ≤
        (rowSupport
          (centeredBlockPostprocess modulus pivot gadget inverse) output).card *
            ((modulus / 2 : ℕ) : ℝ) ^ 2 := by
      simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul
          (rowSupport
            (centeredBlockPostprocess modulus pivot gadget inverse) output)
          (fun sourceRow ↦
            (centeredBlockPostprocess modulus pivot gadget inverse
              output sourceRow) ^ 2)
          (((modulus / 2 : ℕ) : ℝ) ^ 2) (by
            intro sourceRow _
            have hsquare := (sq_le_sq₀
              (abs_nonneg (centeredBlockPostprocess modulus pivot gadget inverse
                output sourceRow))
              (by positivity : (0 : ℝ) ≤ (modulus / 2 : ℕ))).2
                (abs_centeredLift_apply_le_half modulus
                  (blockInversePostprocess pivot gadget inverse) output sourceRow)
            simpa only [sq_abs] using hsquare)
    _ ≤ Fintype.card Coordinate * ((modulus / 2 : ℕ) : ℝ) ^ 2 := by
      gcongr
      exact card_centeredBlockPostprocess_rowSupport_le
        modulus pivot gadget inverse output

omit [DecidableEq Coordinate] in
theorem abs_centeredBlockPostprocess_mulVec_le
    (modulus : ℕ) [NeZero modulus]
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus))
    (sourceErrorBound : ℝ) (sourceErrorBound_nonneg : 0 ≤ sourceErrorBound)
    (sourceError : Output × SourceRow → ℝ)
    (sourceError_bound : ∀ sourceRow, |sourceError sourceRow| ≤ sourceErrorBound)
    (output : Output) :
    |(centeredBlockPostprocess modulus pivot gadget inverse).mulVec
        sourceError output| ≤
      Fintype.card Coordinate * (modulus / 2 : ℕ) * sourceErrorBound := by
  classical
  have sum_eq_support :
      (∑ sourceRow,
          |centeredBlockPostprocess modulus pivot gadget inverse output sourceRow *
            sourceError sourceRow|) =
        ∑ sourceRow ∈ rowSupport
            (centeredBlockPostprocess modulus pivot gadget inverse) output,
          |centeredBlockPostprocess modulus pivot gadget inverse output sourceRow *
            sourceError sourceRow| := by
    symm
    rw [rowSupport, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro sourceRow _
    by_cases hzero :
        centeredBlockPostprocess modulus pivot gadget inverse output sourceRow = 0 <;>
      simp [hzero]
  rw [Matrix.mulVec, dotProduct]
  calc
    |∑ sourceRow,
        centeredBlockPostprocess modulus pivot gadget inverse output sourceRow *
          sourceError sourceRow| ≤
        ∑ sourceRow,
          |centeredBlockPostprocess modulus pivot gadget inverse output sourceRow *
            sourceError sourceRow| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ sourceRow ∈ rowSupport
          (centeredBlockPostprocess modulus pivot gadget inverse) output,
        |centeredBlockPostprocess modulus pivot gadget inverse output sourceRow *
          sourceError sourceRow| := sum_eq_support
    _ ≤ (rowSupport
          (centeredBlockPostprocess modulus pivot gadget inverse) output).card *
        (((modulus / 2 : ℕ) : ℝ) * sourceErrorBound) := by
      simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul
          (rowSupport
            (centeredBlockPostprocess modulus pivot gadget inverse) output)
          (fun sourceRow ↦
            |centeredBlockPostprocess modulus pivot gadget inverse output sourceRow *
              sourceError sourceRow|)
          (((modulus / 2 : ℕ) : ℝ) * sourceErrorBound) (by
            intro sourceRow _
            rw [abs_mul]
            exact mul_le_mul
              (abs_centeredLift_apply_le_half modulus
                (blockInversePostprocess pivot gadget inverse) output sourceRow)
              (sourceError_bound sourceRow) (abs_nonneg _) (by positivity))
    _ ≤ Fintype.card Coordinate *
        (((modulus / 2 : ℕ) : ℝ) * sourceErrorBound) := by
      gcongr
      exact card_centeredBlockPostprocess_rowSupport_le
        modulus pivot gadget inverse output
    _ = Fintype.card Coordinate * (modulus / 2 : ℕ) *
        sourceErrorBound := by ring

omit [DecidableEq Coordinate] in
theorem centeredBlockPostprocess_crossGram_eq_zero
    (modulus : ℕ)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus))
    (first second : Output) (hne : first ≠ second) :
    ∑ sourceRow,
        centeredBlockPostprocess modulus pivot gadget inverse first sourceRow *
          centeredBlockPostprocess modulus pivot gadget inverse second sourceRow = 0 := by
  apply Finset.sum_eq_zero
  intro sourceRow _
  by_cases hfirst : sourceRow.1 = first
  · have second_zero := centeredBlockPostprocess_otherBlock modulus pivot gadget inverse
      second first sourceRow.2 hne
    have second_zero' :
        centeredBlockPostprocess modulus pivot gadget inverse second sourceRow = 0 := by
      simpa [← hfirst, Prod.eta] using second_zero
    simp [second_zero']
  · have first_zero := centeredBlockPostprocess_otherBlock modulus pivot gadget inverse
      first sourceRow.1 sourceRow.2 hfirst
    have first_zero' :
        centeredBlockPostprocess modulus pivot gadget inverse first sourceRow = 0 := by
      simpa [Prod.eta] using first_zero
    simp [first_zero']

omit [DecidableEq Coordinate] in
theorem iidDerivedCovariance_centeredBlockPostprocess_eq_diagonal
    (modulus : ℕ) (variance : ℝ)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus)) :
    iidDerivedCovariance variance
        (centeredBlockPostprocess modulus pivot gadget inverse) =
      Matrix.diagonal fun output ↦ variance *
        rowEnergy (centeredBlockPostprocess modulus pivot gadget inverse) output := by
  classical
  ext first second
  by_cases heq : first = second
  · subst second
    rw [iidDerivedCovariance_apply]
    simp [Matrix.diagonal, rowEnergy, pow_two]
  · rw [iidDerivedCovariance_apply,
      centeredBlockPostprocess_crossGram_eq_zero
        modulus pivot gadget inverse first second heq]
    simp [Matrix.diagonal, heq]

omit [DecidableEq Coordinate] in
theorem iidDerivedCovariance_centeredBlockPostprocess_psd_le
    (modulus : ℕ) [NeZero modulus]
    (variance : ℝ) (variance_nonneg : 0 ≤ variance)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus)) :
    ((variance * Fintype.card Coordinate * (modulus / 2 : ℕ) ^ 2) •
          (1 : Matrix Output Output ℝ) -
        iidDerivedCovariance variance
          (centeredBlockPostprocess modulus pivot gadget inverse)).PosSemidef := by
  classical
  rw [iidDerivedCovariance_centeredBlockPostprocess_eq_diagonal]
  have matrix_eq :
      (variance * Fintype.card Coordinate * (modulus / 2 : ℕ) ^ 2) •
            (1 : Matrix Output Output ℝ) -
          Matrix.diagonal (fun output ↦ variance *
            rowEnergy (centeredBlockPostprocess modulus pivot gadget inverse) output) =
        Matrix.diagonal (fun output ↦
          variance * Fintype.card Coordinate * (modulus / 2 : ℕ) ^ 2 -
            variance * rowEnergy
              (centeredBlockPostprocess modulus pivot gadget inverse) output) := by
    ext first second
    by_cases heq : first = second <;> simp [Matrix.diagonal, heq]
  rw [matrix_eq]
  apply Matrix.PosSemidef.diagonal
  intro output
  apply sub_nonneg.mpr
  calc
    variance * rowEnergy
        (centeredBlockPostprocess modulus pivot gadget inverse) output ≤
        variance * (Fintype.card Coordinate * (modulus / 2 : ℕ) ^ 2) := by
      gcongr
      exact centeredBlockPostprocess_rowEnergy_le
        modulus pivot gadget inverse output
    _ = variance * Fintype.card Coordinate * (modulus / 2 : ℕ) ^ 2 := by ring

omit [DecidableEq Coordinate] in
theorem iidDerivedCovariance_centeredBlockPostprocess_targetCorrection_posSemidef
    (modulus : ℕ) [NeZero modulus]
    (variance targetVariance : ℝ) (variance_nonneg : 0 ≤ variance)
    (target_large :
      variance * Fintype.card Coordinate * (modulus / 2 : ℕ) ^ 2 ≤
        targetVariance)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate (ZMod modulus))
    (inverse : Output → Matrix Coordinate Coordinate (ZMod modulus)) :
    (targetVariance • (1 : Matrix Output Output ℝ) -
        iidDerivedCovariance variance
          (centeredBlockPostprocess modulus pivot gadget inverse)).PosSemidef := by
  classical
  let covarianceBound :=
    variance * Fintype.card Coordinate * (modulus / 2 : ℕ) ^ 2
  have bounded :
      (covarianceBound • (1 : Matrix Output Output ℝ) -
          iidDerivedCovariance variance
            (centeredBlockPostprocess modulus pivot gadget inverse)).PosSemidef := by
    exact iidDerivedCovariance_centeredBlockPostprocess_psd_le
      modulus variance variance_nonneg pivot gadget inverse
  have slack :
      ((targetVariance - covarianceBound) •
        (1 : Matrix Output Output ℝ)).PosSemidef := by
    exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr target_large)
  have decompose :
      targetVariance • (1 : Matrix Output Output ℝ) -
          iidDerivedCovariance variance
            (centeredBlockPostprocess modulus pivot gadget inverse) =
        (targetVariance - covarianceBound) •
            (1 : Matrix Output Output ℝ) +
          (covarianceBound • (1 : Matrix Output Output ℝ) -
            iidDerivedCovariance variance
              (centeredBlockPostprocess modulus pivot gadget inverse)) := by
    module
  rw [decompose]
  exact slack.add bounded

end CenteredBlockNoise

namespace ScaledRingSolver

/-- A translation projection whose scale also intertwines multiplication by
lifted source coefficients with reduction to the target ring. -/
structure RingTranslationProjection (Lifted Target : Type)
    [CommRing Lifted] [CommRing Target]
    extends TranslationProjection Lifted Target where
  reduce : Lifted →+* Target
  scale_mul_reduce : ∀ target lifted,
    toTranslationProjection.scale (target * reduce lifted) =
      toTranslationProjection.scale target * lifted

variable {Lifted Target Row Coordinate Output : Type}
  [CommRing Lifted] [CommRing Target]
  [Fintype Row] [DecidableEq Row]
  [Fintype Coordinate] [DecidableEq Coordinate]
  [Fintype Output] [DecidableEq Output]

def liftTargetMatrix
    (projection : RingTranslationProjection Lifted Target)
    (matrix : Matrix Output Row Target) : Matrix Output Row Lifted :=
  fun output row ↦ projection.toTranslationProjection.scale (matrix output row)

omit [DecidableEq Row] [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Output] [DecidableEq Output] in
theorem liftTargetMatrix_mul_source
    (projection : RingTranslationProjection Lifted Target)
    (source : Matrix Row Coordinate Lifted)
    (postprocess : Matrix Output Row Target) :
    liftTargetMatrix projection postprocess * source =
      liftTargetMatrix projection (postprocess * source.map projection.reduce) := by
  classical
  ext output coordinate
  simp only [Matrix.mul_apply, liftTargetMatrix, Matrix.map_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro row _
  exact (projection.scale_mul_reduce
    (postprocess output row) (source row coordinate)).symm

omit [DecidableEq Coordinate] [Fintype Output] [DecidableEq Output] in
theorem liftTargetMatrix_mulVec
    (projection : RingTranslationProjection Lifted Target)
    (matrix : Matrix Output Coordinate Target)
    (vector : Coordinate → Lifted) :
    (liftTargetMatrix projection matrix).mulVec vector =
      fun output ↦ projection.toTranslationProjection.scale
        (matrix.mulVec (fun coordinate ↦ projection.reduce (vector coordinate)) output) := by
  classical
  funext output
  simp only [Matrix.mulVec, dotProduct, liftTargetMatrix]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact (projection.scale_mul_reduce
    (matrix output coordinate) (vector coordinate)).symm

def reduceVector
    (projection : RingTranslationProjection Lifted Target) :
    (Coordinate → Lifted) →+ (Coordinate → Target) where
  toFun := fun vector coordinate ↦ projection.reduce (vector coordinate)
  map_zero' := by
    funext coordinate
    simp
  map_add' := by
    intro left right
    funext coordinate
    simp

/-- A target-ring factorization of the reduced source lifts to an exact scaled
factorization before delayed projection. -/
def scaledFactorizationOfReducedProduct
    (projection : RingTranslationProjection Lifted Target)
    (source : Matrix Row Coordinate Lifted)
    (gadget : Matrix Output Coordinate Target)
    (postprocess : Matrix Output Row Target)
    (product_eq : postprocess * source.map projection.reduce = gadget) :
    ScaledApproximateFactorization
      source.mulVecLin.toAddMonoidHom
      (gadget.mulVecLin.toAddMonoidHom.comp (reduceVector projection))
      (projection.toTranslationProjection.coordinatewise Output).scale where
  postprocess := (liftTargetMatrix projection postprocess).mulVecLin.toAddMonoidHom
  residual := 0
  postprocess_comp := by
    apply AddMonoidHom.ext
    intro secret
    funext output
    change (liftTargetMatrix projection postprocess).mulVec (source.mulVec secret) output =
      projection.toTranslationProjection.scale
        (gadget.mulVec (fun coordinate ↦ projection.reduce (secret coordinate)) output) + 0
    rw [add_zero,
      ← congrFun (liftTargetMatrix_mulVec projection gadget secret) output]
    rw [congrFun (Matrix.mulVec_mulVec secret
      (liftTargetMatrix projection postprocess) source) output]
    rw [liftTargetMatrix_mul_source, product_eq]

omit [DecidableEq Row] [DecidableEq Coordinate]
    [Fintype Output] [DecidableEq Output] in
@[simp]
theorem scaledFactorizationOfReducedProduct_residual
    (projection : RingTranslationProjection Lifted Target)
    (source : Matrix Row Coordinate Lifted)
    (gadget : Matrix Output Coordinate Target)
    (postprocess : Matrix Output Row Target)
    (product_eq : postprocess * source.map projection.reduce = gadget) :
    (scaledFactorizationOfReducedProduct projection source gadget postprocess product_eq).residual =
      0 := rfl

variable {SourceRow : Type} [Fintype SourceRow] [DecidableEq SourceRow]

/-- The complete disjoint-block construction: reduce the public source,
invert one public square minor in every block, and lift the resulting exact
factorization through the modulus scale. -/
noncomputable def scaledPublicBlockFactorization
    (projection : RingTranslationProjection Lifted Target)
    (source : Matrix (Output × SourceRow) Coordinate Lifted)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate Target)
    (minorUnit : ∀ output,
      IsUnit (BlockMinorSolver.blockMinor
        (source.map projection.reduce) pivot output)) :
    ScaledApproximateFactorization
      source.mulVecLin.toAddMonoidHom
      (gadget.mulVecLin.toAddMonoidHom.comp (reduceVector projection))
      (projection.toTranslationProjection.coordinatewise Output).scale :=
  scaledFactorizationOfReducedProduct projection source gadget
    (BlockMinorSolver.publicBlockPostprocess
      (source.map projection.reduce) pivot gadget minorUnit)
    (BlockMinorSolver.publicBlockPostprocess_mul
      (source.map projection.reduce) pivot gadget minorUnit)

@[simp]
theorem scaledPublicBlockFactorization_residual
    (projection : RingTranslationProjection Lifted Target)
    (source : Matrix (Output × SourceRow) Coordinate Lifted)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate Target)
    (minorUnit : ∀ output,
      IsUnit (BlockMinorSolver.blockMinor
        (source.map projection.reduce) pivot output)) :
    (scaledPublicBlockFactorization projection source pivot gadget minorUnit).residual = 0 := rfl

/-- Exact delayed-projection output of the public block solver.  The only
remaining error is the linearly transformed source error; there is no
residual-secret term. -/
theorem scaledPublicBlockFactorization_project_real
    (projection : RingTranslationProjection Lifted Target)
    (source : Matrix (Output × SourceRow) Coordinate Lifted)
    (pivot : Output → Coordinate → SourceRow)
    (gadget : Matrix Output Coordinate Target)
    (minorUnit : ∀ output,
      IsUnit (BlockMinorSolver.blockMinor
        (source.map projection.reduce) pivot output))
    (secret : Coordinate → Lifted)
    (sourceError : Output × SourceRow → Lifted) :
    (projection.toTranslationProjection.coordinatewise Output).project
        ((scaledPublicBlockFactorization projection source pivot gadget minorUnit).postprocess
          (source.mulVec secret + sourceError)) =
      gadget.mulVec (fun coordinate ↦ projection.reduce (secret coordinate)) +
        (projection.toTranslationProjection.coordinatewise Output).project
          ((scaledPublicBlockFactorization projection source pivot gadget minorUnit).postprocess
            sourceError) := by
  exact ScaledApproximateFactorization.project_real_of_residual_eq_zero
    (projection.toTranslationProjection.coordinatewise Output)
    (scaledPublicBlockFactorization projection source pivot gadget minorUnit)
    rfl secret sourceError

end ScaledRingSolver

namespace FiniteError

variable {Secret Source Lifted Target : Type}
  [AddCommGroup Secret] [AddCommGroup Source]
  [AddCommGroup Lifted] [AddCommGroup Target]
  {source : Secret →+ Source} {gadget : Secret →+ Target}

/-- The exact target-error law induced by delayed projection of the
postprocessed source error. -/
def derivedTargetErrorSampler
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (sourceErrorSampler : ProbComp Source) : ProbComp Target := do
  let sourceError ← sourceErrorSampler
  return projection.project (certificate.postprocess sourceError)

/-- With zero residual and no added correction, choosing the prescribed target
error to be the exact derived law makes the complete secret/error law equal,
not merely close. -/
theorem roundedJointErrorSampler_eq_independent_derivedTargetError
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (residual_zero : certificate.residual = 0)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source) :
    roundedJointErrorSampler projection certificate secretSampler
        sourceErrorSampler (pure 0) =
      independentTargetErrorSampler secretSampler
        (derivedTargetErrorSampler projection certificate sourceErrorSampler) := by
  simp [roundedJointErrorSampler, independentTargetErrorSampler,
    derivedTargetErrorSampler, residual_zero]

theorem projectedCorrectedReal_evalDist_eq_prescribed_derivedTargetError
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (residual_zero : certificate.residual = 0)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source) :
    evalDist (projectedCorrectedRealSampler projection certificate
        secretSampler sourceErrorSampler (pure 0)) =
      evalDist (prescribedTargetSampler gadget secretSampler
        (derivedTargetErrorSampler projection certificate sourceErrorSampler)) := by
  apply projectedCorrectedReal_evalDist_eq_prescribed_of_jointError
  rw [roundedJointErrorSampler_eq_independent_derivedTargetError
    projection certificate residual_zero secretSampler sourceErrorSampler]

end FiniteError

namespace SecurityBound

open DirectSubsetKeyBRK

variable {Sample Secret Output Prefix View : Type} [Add Output]
  {problem : LearningWithErrors.Problem Sample Secret Output}
  {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}
  {constructor : PublicViewConstructor problem prefixSampler targetView}

noncomputable def blockRankBudget (outputCount slack : ℕ) : ℝ :=
  outputCount * (2 / (2 : ℝ) ^ (slack + 1))

/-- Arithmetic specialization of the joint constructor theorem.  Once the
block-rank event and complete derived-error law have been bounded, those two
budgets substitute directly, with one copy on each real branch. -/
theorem targetAdvantage_le_of_blockSolver_bounds
    (certificate : JointSubsetKeyBRK.DefectCertificate constructor)
    (factorizationBudget noiseBudget : ℝ)
    (factorization_le : certificate.factorizationError ≤ factorizationBudget)
    (noise_le : certificate.noiseError ≤ noiseBudget)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        2 * factorizationBudget + 2 * noiseBudget +
        certificate.uniformError + certificate.auxiliaryError := by
  have base := certificate.targetAdvantage_le_two_source_add_joint_errors distinguisher
  linarith

/-- Exact-derived-law specialization: the noise term vanishes and only the
two real-branch copies of the block-rank budget remain. -/
theorem targetAdvantage_le_of_blockSolver_exactDerivedLaw
    (certificate : JointSubsetKeyBRK.DefectCertificate constructor)
    (outputCount slack : ℕ)
    (factorization_le :
      certificate.factorizationError ≤ blockRankBudget outputCount slack)
    (noise_zero : certificate.noiseError = 0)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        2 * blockRankBudget outputCount slack +
        certificate.uniformError + certificate.auxiliaryError := by
  have bounded := targetAdvantage_le_of_blockSolver_bounds certificate
    (blockRankBudget outputCount slack) 0 factorization_le
      (le_of_eq noise_zero) distinguisher
  simpa using bounded

end SecurityBound

namespace TFHEpp

def reduce32To16 : ZMod (2 ^ 32) →+* ZMod (2 ^ 16) :=
  ZMod.castHom (pow_dvd_pow 2 (by norm_num : 16 ≤ 32)) (ZMod (2 ^ 16))

theorem scale16To32_mul_reduce32To16
    (target : ZMod (2 ^ 16)) (lifted : ZMod (2 ^ 32)) :
    scale16To32 (target * reduce32To16 lifted) =
      scale16To32 target * lifted := by
  obtain ⟨targetInteger, rfl⟩ := ZMod.intCast_surjective target
  obtain ⟨liftedInteger, rfl⟩ := ZMod.intCast_surjective lifted
  rw [map_intCast, ← Int.cast_mul, scale16To32_intCast,
    scale16To32_intCast, ← Int.cast_mul]
  ring_nf

def ringRoundedHighWordProjection :
    ScaledRingSolver.RingTranslationProjection
      (ZMod (2 ^ 32)) (ZMod (2 ^ 16)) where
  toTranslationProjection := roundedHighWordProjection
  reduce := reduce32To16
  scale_mul_reduce := scale16To32_mul_reduce32To16

end TFHEpp

end FormalProof4FHE.TFHE.JointSubsetKeyBRKDelayedProjection
