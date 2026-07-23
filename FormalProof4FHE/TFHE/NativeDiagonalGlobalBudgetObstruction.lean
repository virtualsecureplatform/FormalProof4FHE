/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalPairBinaryRank

/-!
# Diagonal-Slice Obstruction to the Global Native Pair Budget

The source-independent global pair-collision budget drops the retained transformed-error fiber
before summing over two difference ciphertexts.  This file proves that the resulting relaxation
cannot be negligible at an exact-capacity even-base gadget, even when the paired rectangular
binary matrix has a negligible full-rank tail.

The obstruction is the diagonal slice in which the two hidden differences are equal.  For a
non-bijective single-difference row operator, the paired zero fiber contains one copy of the
complete row space for every element of the nontrivial kernel.  Its collision excess is therefore
at least one complete challenge-space cardinality.  Summing this over the diagonal slice shows
that the normalized global budget is at least the original single-difference rank-failure
probability, which is at least one half in the exact-capacity even-base regime.

This does not lower-bound the exact retained-fiber chi-square loss.  It rules out only the step
that discards the retained-side restriction and replaces it by the unconditional global sum.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree : ℕ}

/-! ## Equal-difference zero fiber -/

/-- Additive-homomorphism packaging of one fixed-difference row operator. -/
def rowOperatorAddHom {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    (Fin (TGSW.rowCount dimension levels) → R) →+
      (Fin (TGSW.rowCount dimension levels) → R) where
  toFun := rowOperator candidate digits
  map_zero' := by
    funext row
    cases candidate <;> simp [rowOperator]
  map_add' := rowOperator_add candidate digits

/-- For two equal row operators, a colliding pair is equivalently a base point together with a
kernel element. -/
def pairedSelfZeroFiberEquiv {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    {values :
        (Fin (TGSW.rowCount dimension levels) → R) ×
          (Fin (TGSW.rowCount dimension levels) → R) //
      pairedRowDifferenceOperator candidate digits digits values = 0} ≃
      (Fin (TGSW.rowCount dimension levels) → R) ×
        {kernelValue : Fin (TGSW.rowCount dimension levels) → R //
          rowOperator candidate digits kernelValue = 0} where
  toFun values :=
    (values.1.2, ⟨values.1.1 - values.1.2, by
      have hpair := values.2
      change rowOperator candidate digits values.1.1 -
          rowOperator candidate digits values.1.2 = 0 at hpair
      change (rowOperatorAddHom candidate digits)
        (values.1.1 - values.1.2) = 0
      rw [map_sub]
      exact hpair⟩)
  invFun values :=
    ⟨(values.1 + values.2.1, values.1), by
      change rowOperator candidate digits (values.1 + values.2.1) -
          rowOperator candidate digits values.1 = 0
      rw [rowOperator_add]
      rw [values.2.2]
      simp⟩
  left_inv := by
    intro values
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      abel
    · rfl
  right_inv := by
    intro values
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp
      abel

/-- Exact cardinality of the equal-difference paired zero fiber. -/
theorem pairedRowZeroFiberCard_self_eq_card_mul_kernelCard
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    pairedRowZeroFiberCard candidate digits digits =
      Fintype.card (Fin (TGSW.rowCount dimension levels) → R) *
        Fintype.card
          {kernelValue : Fin (TGSW.rowCount dimension levels) → R //
            rowOperator candidate digits kernelValue = 0} := by
  classical
  unfold pairedRowZeroFiberCard
  rw [show
      (Finset.univ.filter fun values :
          (Fin (TGSW.rowCount dimension levels) → R) ×
            (Fin (TGSW.rowCount dimension levels) → R) =>
        pairedRowDifferenceOperator candidate digits digits values = 0).card =
        Fintype.card
          {values :
              (Fin (TGSW.rowCount dimension levels) → R) ×
                (Fin (TGSW.rowCount dimension levels) → R) //
            pairedRowDifferenceOperator candidate digits digits values = 0} by
      symm
      apply Fintype.card_of_subtype
      intro values
      simp]
  rw [Fintype.card_congr (pairedSelfZeroFiberEquiv candidate digits),
    Fintype.card_prod]

/-- A non-bijective additive endomorphism of a finite type has at least two kernel points. -/
theorem two_le_rowOperator_kernelCard_of_not_bijective
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (hfailure : ¬ Function.Bijective (rowOperator candidate digits)) :
    2 ≤ Fintype.card
      {kernelValue : Fin (TGSW.rowCount dimension levels) → R //
        rowOperator candidate digits kernelValue = 0} := by
  classical
  let f := rowOperatorAddHom candidate digits
  have hnotInjective : ¬ Function.Injective f := by
    intro hinjective
    have hsurjective : Function.Surjective f :=
      Finite.injective_iff_surjective.mp hinjective
    exact hfailure ⟨hinjective, hsurjective⟩
  obtain ⟨left, right, heq, hne⟩ := Function.not_injective_iff.mp hnotInjective
  let kernelValue := left - right
  have kernelValue_ne : kernelValue ≠ 0 := sub_ne_zero.mpr hne
  have kernelValue_mem : rowOperator candidate digits kernelValue = 0 := by
    change f kernelValue = 0
    dsimp only [kernelValue]
    rw [map_sub, heq, sub_self]
  let injection : Bool →
      {value : Fin (TGSW.rowCount dimension levels) → R //
        rowOperator candidate digits value = 0} := fun bit =>
    if bit then ⟨kernelValue, kernelValue_mem⟩
    else ⟨0, (rowOperatorAddHom candidate digits).map_zero⟩
  have injection_injective : Function.Injective injection := by
    intro leftBit rightBit heqBit
    cases leftBit <;> cases rightBit
    · rfl
    · exfalso
      apply kernelValue_ne
      have hvalue := congrArg Subtype.val heqBit
      simpa [injection] using hvalue.symm
    · exfalso
      apply kernelValue_ne
      have hvalue := congrArg Subtype.val heqBit
      simpa [injection] using hvalue
    · rfl
  have hcard := Fintype.card_le_of_injective injection injection_injective
  simpa using hcard

/-! ## One complete challenge unit on every bad diagonal pair -/

/-- In ring rank one, every non-bijective single-difference row operator contributes at least
one whole challenge-space unit of collision excess on the equal-difference diagonal pair. -/
theorem challengeCard_le_differencePairChallengeCollisionExcess_self_of_rankFailure
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) 1 params.levels)
    (hfailure : DiagonalRowRankFailure params candidate difference) :
    (Fintype.card (DiagonalChallenge q degree 1 params.levels) : ℝ) ≤
      differencePairChallengeCollisionExcess params candidate difference difference := by
  let digits := differenceEntryDigits params difference
  let Row := Fin (TGSW.rowCount 1 params.levels) → RLWE.Rq q (degree + 1)
  have hkernel : 2 ≤ Fintype.card
      {kernelValue : Row // rowOperator candidate digits kernelValue = 0} :=
    two_le_rowOperator_kernelCard_of_not_bijective candidate digits hfailure
  have hzeroFiber :
      2 * Fintype.card Row ≤ pairedRowZeroFiberCard candidate digits digits := by
    rw [pairedRowZeroFiberCard_self_eq_card_mul_kernelCard]
    dsimp only [Row] at hkernel ⊢
    simpa only [Nat.mul_comm] using
      Nat.mul_le_mul_left
        (Fintype.card
          (Fin (TGSW.rowCount 1 params.levels) → RLWE.Rq q (degree + 1))) hkernel
  have hcount :
      (2 : ℝ) * Fintype.card Row ≤
        differencePairChallengeCollisionCount params candidate difference difference := by
    unfold differencePairChallengeCollisionCount
    rw [pairedChallengeCollisionCount_eq_rowZeroFiberCard_pow]
    simp only [pow_one]
    exact_mod_cast hzeroFiber
  have hchallengeCard :
      Fintype.card (DiagonalChallenge q degree 1 params.levels) =
        Fintype.card Row := by
    change Fintype.card (Fin 1 → Row) = Fintype.card Row
    simp
  unfold differencePairChallengeCollisionExcess
  rw [hchallengeCard]
  linarith

/-! ## The global relaxation retains the square-matrix obstruction -/

/-- The source-independent global pair budget is at least the exact single-difference rank-
failure probability.  The paired rectangular rank tail cannot repair the loss introduced by
discarding the retained side fiber, because the equal-difference slice already contains the
square obstruction. -/
theorem diagonalRowRankFailureProbability_le_globalDifferencePairCollisionBudget
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) :
    diagonalRowRankFailureProbability (degree := degree) (ringRank := 1)
        params candidate ≤
      globalDifferencePairCollisionBudget
        (degree := degree) (ringRank := 1) params candidate := by
  classical
  let Difference := RingGSWCiphertext q (degree + 1) 1 params.levels
  let C : ℝ := Fintype.card (DiagonalChallenge q degree 1 params.levels)
  let D : ℝ := Fintype.card Difference
  let bad : Difference → Prop := fun difference =>
    DiagonalRowRankFailure (degree := degree) (ringRank := 1)
      params candidate difference
  let B : ℕ := ((Finset.univ : Finset Difference).filter bad).card
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast Fintype.card_pos
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast Fintype.card_pos
  have hprobability :
      diagonalRowRankFailureProbability (degree := degree) (ringRank := 1)
          params candidate = (B : ℝ) / D := by
    unfold diagonalRowRankFailureProbability
    rw [probEvent_uniformSample, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast]
    rfl
  have hdiagonal :
      (B : ℝ) * C ≤
        totalDifferencePairChallengeCollisionExcess
          (degree := degree) (ringRank := 1) params candidate := by
    unfold totalDifferencePairChallengeCollisionExcess
    calc
      (B : ℝ) * C = ∑ difference : Difference,
          if bad difference then C else 0 := by
            simp [B]
      _ ≤ ∑ leftDifference : Difference,
          ∑ rightDifference : Difference,
            differencePairChallengeCollisionExcess params candidate
              leftDifference rightDifference := by
            apply Finset.sum_le_sum
            intro difference _
            by_cases hbad : bad difference
            · simp only [hbad, if_true]
              exact
                (challengeCard_le_differencePairChallengeCollisionExcess_self_of_rankFailure
                  params candidate difference hbad).trans
                  (Finset.single_le_sum
                    (fun rightDifference _ =>
                      differencePairChallengeCollisionExcess_nonneg
                        params candidate difference rightDifference)
                    (Finset.mem_univ difference))
            · simp only [hbad, if_false]
              exact Finset.sum_nonneg fun rightDifference _ =>
                differencePairChallengeCollisionExcess_nonneg
                  params candidate difference rightDifference
  rw [hprobability]
  unfold globalDifferencePairCollisionBudget
  change (B : ℝ) / D ≤
    totalDifferencePairChallengeCollisionExcess
        (degree := degree) (ringRank := 1) params candidate / (D * C)
  apply (le_div_iff₀ (mul_pos hD hC)).2
  calc
    (B : ℝ) / D * (D * C) = (B : ℝ) * C := by
      field_simp [hD.ne']
    _ ≤ _ := hdiagonal

/-- At exact gadget capacity with a positive level count and even base, the global pair budget is
bounded below by one half for either candidate. -/
theorem one_half_le_globalDifferencePairCollisionBudget
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (halfBase : ℕ) [NeZero halfBase]
    (hbase : params.base = halfBase * 2)
    (hlevels : 0 < params.levels) (candidate : Bool) :
    (1 : ℝ) / 2 ≤
      globalDifferencePairCollisionBudget
        (degree := degree) (ringRank := 1) params candidate :=
  (one_half_le_diagonalRowDeterminantFailureProbability
      (degree := degree) (ringRank := 1)
      params hcapacity halfBase hbase hlevels candidate).trans
    (by
      rw [← diagonalRowRankFailureProbability_eq_determinantFailureProbability]
      exact diagonalRowRankFailureProbability_le_globalDifferencePairCollisionBudget
        params candidate)

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
