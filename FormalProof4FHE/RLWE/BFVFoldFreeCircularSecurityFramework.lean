/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurity
import FormalProof4FHE.Probability.FiniteSurjectiveFiber
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Corrected fold-free BFV framework: quantitative and tagged-source additions

This file formalizes the new technical claims in
`sketch/BFV_fold_free_circular_security_framework.tex` that are not already covered by
`BFVFoldFreeCircularSecurity`:

* a fixed public coefficient and fresh candidate randomizer cover only an affine line;
* the complete family of shared-pivot derived masks is jointly uniform, not merely marginally
  uniform;
* the good-secret and candidate-score constants follow from explicit real inequalities;
* finite mixed-radix tags give every distinct source pair a unit difference coordinate; and
* such a coordinate makes the support-constrained module-knapsack pair-collision probability
  exactly the inverse output cardinality, with the advertised union bound.

The cost semantics of repeated oracle calls, the external general-distribution theorem, and its
exact second-preimage interface remain outside this finite theorem layer.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurityFramework

noncomputable section

open FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurity

/-! ## The fixed-block obstruction -/

/-- Candidate randomization when the public coefficient is fixed and only the randomizer varies. -/
def fixedCoefficientCandidateMap
    {K : Type} [CommRing K]
    (secret candidate error coefficient randomizer : K) : K × K :=
  candidateRandomize candidate randomizer
    (coordinateRow secret error coefficient)

/-- A fixed-coefficient candidate output lies on one explicit affine line. -/
theorem fixedCoefficientCandidateMap_affineLine
    {K : Type} [CommRing K]
    (secret candidate error coefficient randomizer : K) :
    (fixedCoefficientCandidateMap secret candidate error coefficient randomizer).2 =
      candidate *
          (fixedCoefficientCandidateMap secret candidate error coefficient randomizer).1 +
        (coefficient * (secret - candidate) + error) := by
  simp [fixedCoefficientCandidateMap, candidateRandomize, coordinateRow]
  ring

/-- Varying the randomizer with a fixed coefficient cannot cover the whole pair space over a
nontrivial ring.  Thus the wrong-candidate bijection genuinely needs a fresh uniform coefficient
as well as a fresh randomizer. -/
theorem fixedCoefficientCandidateMap_not_surjective
    {K : Type} [CommRing K] [Nontrivial K]
    (secret candidate error coefficient : K) :
    ¬ Function.Surjective
      (fixedCoefficientCandidateMap secret candidate error coefficient) := by
  intro hSurjective
  let forbidden : K × K :=
    (coefficient, coefficient * secret + error + 1)
  obtain ⟨randomizer, hOutput⟩ := hSurjective forbidden
  have hFirst := congrArg Prod.fst hOutput
  have hRandomizer : randomizer = 0 := by
    change coefficient + randomizer = coefficient at hFirst
    simpa using hFirst
  subst randomizer
  have hSecond := congrArg Prod.snd hOutput
  simp [fixedCoefficientCandidateMap, candidateRandomize, coordinateRow, forbidden] at hSecond

/-! ## Joint uniformity of every derived shared-pivot mask -/

/-- Split a complete family of public rows into all derived mask coordinates and all unused
coordinates.  The public row transformation may be any equivalence. -/
def derivedMaskFamilyEquiv
    {R Coordinate Family : Type} [AddGroup R] [DecidableEq Coordinate]
    (rowTransform : (Coordinate → R) ≃ (Coordinate → R))
    (pivot : Coordinate) :
    (Family → Coordinate → R) ≃
      (Family → R) × (Family → ({coordinate : Coordinate // coordinate ≠ pivot} → R)) where
  toFun rows :=
    ((fun family ↦ -(rowTransform (rows family) pivot)),
      fun family coordinate ↦ rowTransform (rows family) coordinate)
  invFun output family :=
    rowTransform.symm
      ((FormalProof4FHE.LeftoverHash.tableEquivAt (G := R) pivot).symm
        (-output.1 family, output.2 family))
  left_inv rows := by
    funext family
    apply rowTransform.injective
    apply (FormalProof4FHE.LeftoverHash.tableEquivAt (G := R) pivot).injective
    apply Prod.ext
    · simp [FormalProof4FHE.LeftoverHash.tableEquivAt]
    · funext coordinate
      simp [FormalProof4FHE.LeftoverHash.tableEquivAt, coordinate.property]
  right_inv output := by
    apply Prod.ext
    · funext family
      simp [FormalProof4FHE.LeftoverHash.tableEquivAt]
    · funext family coordinate
      simp [FormalProof4FHE.LeftoverHash.tableEquivAt, coordinate.property]

/-- Apply the derived-mask operation independently to a complete row family. -/
def derivedMaskFamily
    {R Coordinate Family : Type} [AddGroup R]
    (rowTransform : (Coordinate → R) ≃ (Coordinate → R))
    (pivot : Coordinate) (rows : Family → Coordinate → R) : Family → R :=
  fun family ↦ derivedMaskCoordinate rowTransform pivot (rows family)

/-- The complete family of derived masks is exactly jointly uniform.  Because the endpoint is the
canonical uniform law on the function space, this includes independence across every indexed row
and block. -/
theorem derivedMaskFamily_uniform_evalDist
    {R Coordinate Family : Type}
    [AddGroup R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Family] [DecidableEq Family]
    (rowTransform : (Coordinate → R) ≃ (Coordinate → R))
    (pivot : Coordinate) :
    evalDist (derivedMaskFamily rowTransform pivot <$>
        ($ᵗ (Family → Coordinate → R))) =
      evalDist ($ᵗ (Family → R)) := by
  let split := derivedMaskFamilyEquiv
    (Family := Family) rowTransform pivot
  have hSplit :
      evalDist (split <$> ($ᵗ (Family → Coordinate → R))) =
        evalDist ($ᵗ ((Family → R) ×
          (Family → ({coordinate : Coordinate // coordinate ≠ pivot} → R)))) :=
    evalDist_map_bijective_uniform_cross
      (α := Family → Coordinate → R)
      (β := (Family → R) ×
        (Family → ({coordinate : Coordinate // coordinate ≠ pivot} → R)))
      split split.bijective
  calc
    evalDist (derivedMaskFamily rowTransform pivot <$>
        ($ᵗ (Family → Coordinate → R))) =
      evalDist (Prod.fst <$> (split <$> ($ᵗ (Family → Coordinate → R)))) := by
        change evalDist ((fun rows : Family → Coordinate → R ↦
            fun family ↦ -rowTransform (rows family) pivot) <$>
              ($ᵗ (Family → Coordinate → R))) = _
        simp [split, derivedMaskFamilyEquiv, Functor.map_map]
    _ = evalDist (Prod.fst <$> ($ᵗ ((Family → R) ×
          (Family → ({coordinate : Coordinate // coordinate ≠ pivot} → R)))) ) := by
        simpa only [evalDist_map] using congrArg
          (fun distribution ↦ Prod.fst <$> distribution) hSplit
    _ = evalDist ($ᵗ (Family → R)) :=
      evalDist_map_fst_uniformSample_prod

/-! ## Quantitative partial-recovery arithmetic -/

/-- Arithmetic core of the good-secret argument.  If an average gap `delta` is bounded above by
the mixture of value `1` on a good set of mass `p` and value `delta/2` outside it, then the good
mass is at least `delta/(2-delta)`. -/
theorem goodSecretMass_ge
    (delta goodMass : ℝ)
    (hDeltaLtTwo : delta < 2)
    (hMixture :
      delta ≤ goodMass + (1 - goodMass) * (delta / 2)) :
    delta / (2 - delta) ≤ goodMass := by
  apply (div_le_iff₀ (by linarith)).2
  nlinarith

/-- The manuscript's simpler `delta/2` lower bound follows whenever `delta ≤ 1`. -/
theorem halfGap_le_goodSecretMass
    (delta goodMass : ℝ)
    (hDeltaNonneg : 0 ≤ delta) (hDeltaLeOne : delta ≤ 1)
    (hMixture :
      delta ≤ goodMass + (1 - goodMass) * (delta / 2)) :
    delta / 2 ≤ goodMass := by
  have hSharp := goodSecretMass_ge delta goodMass (by linarith) hMixture
  have hCompare : delta / 2 ≤ delta / (2 - delta) := by
    by_cases hDeltaZero : delta = 0
    · simp [hDeltaZero]
    · have hDeltaPos : 0 < delta := lt_of_le_of_ne hDeltaNonneg (Ne.symm hDeltaZero)
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by linarith)).2
      nlinarith
  exact hCompare.trans hSharp

/-- Two estimates of one common wrong-candidate score differ by at most twice their individual
error. -/
theorem equalScore_estimates_close
    (common firstEstimate secondEstimate tolerance : ℝ)
    (hFirst : |firstEstimate - common| ≤ tolerance)
    (hSecond : |secondEstimate - common| ≤ tolerance) :
    |firstEstimate - secondEstimate| ≤ 2 * tolerance := by
  calc
    |firstEstimate - secondEstimate| =
        |(firstEstimate - common) - (secondEstimate - common)| := by ring_nf
    _ ≤ |firstEstimate - common| + |secondEstimate - common| := abs_sub _ _
    _ ≤ 2 * tolerance := by linarith

/-- Accurate estimates preserve a true correct-versus-wrong score gap up to twice the estimation
error. -/
theorem estimatedCorrectGap_ge
    (correctScore wrongScore correctEstimate wrongEstimate gap tolerance : ℝ)
    (hGap : gap ≤ correctScore - wrongScore)
    (hCorrect : |correctEstimate - correctScore| ≤ tolerance)
    (hWrong : |wrongEstimate - wrongScore| ≤ tolerance) :
    gap - 2 * tolerance ≤ correctEstimate - wrongEstimate := by
  have hCorrectLower : correctScore - tolerance ≤ correctEstimate := by
    rw [abs_le] at hCorrect
    linarith
  have hWrongUpper : wrongEstimate ≤ wrongScore + tolerance := by
    rw [abs_le] at hWrong
    linarith
  linarith

/-! ## Mixed-radix unit-difference tags -/

/-- One padded base-`base` digit of the canonical finite index of `source`. -/
def mixedRadixDigit
    {Source : Type} [Fintype Source]
    (base length : ℕ) (source : Source) (position : Fin length) : ℕ :=
  (Nat.digitsAppend base length (Fintype.equivFin Source source).val).getD position.val 0

/-- Every mixed-radix digit lies below the base when the allocated length has enough capacity. -/
theorem mixedRadixDigit_lt_base
    {Source : Type} [Fintype Source]
    (base length : ℕ) (hBase : 1 < base)
    (hCapacity : Fintype.card Source ≤ base ^ length)
    (source : Source) (position : Fin length) :
    mixedRadixDigit base length source position < base := by
  have hIndex : (Fintype.equivFin Source source).val < base ^ length :=
    (Fintype.equivFin Source source).isLt.trans_le hCapacity
  have hLength :
      (Nat.digitsAppend base length (Fintype.equivFin Source source).val).length =
        length :=
    Nat.length_digitsAppend hBase length hIndex
  change (Nat.digitsAppend base length
    (Fintype.equivFin Source source).val).getD position.val 0 < base
  have hPosition : position.val <
      (Nat.digitsAppend base length (Fintype.equivFin Source source).val).length := by
    rw [hLength]
    exact position.isLt
  rw [List.getD_eq_getElem _ 0 hPosition]
  apply Nat.lt_of_mem_digitsAppend hBase length
  exact List.getElem_mem _

/-- Distinct finite sources have different digits at some allocated position. -/
theorem exists_mixedRadixDigit_ne
    {Source : Type} [Fintype Source]
    (base length : ℕ) (hBase : 1 < base)
    (hCapacity : Fintype.card Source ≤ base ^ length)
    {left right : Source} (hDifferent : left ≠ right) :
    ∃ position : Fin length,
      mixedRadixDigit base length left position ≠
        mixedRadixDigit base length right position := by
  by_contra hNoPosition
  push Not at hNoPosition
  have hLeftIndex : (Fintype.equivFin Source left).val < base ^ length :=
    (Fintype.equivFin Source left).isLt.trans_le hCapacity
  have hRightIndex : (Fintype.equivFin Source right).val < base ^ length :=
    (Fintype.equivFin Source right).isLt.trans_le hCapacity
  have hLeftLength :
      (Nat.digitsAppend base length (Fintype.equivFin Source left).val).length =
        length := Nat.length_digitsAppend hBase length hLeftIndex
  have hRightLength :
      (Nat.digitsAppend base length (Fintype.equivFin Source right).val).length =
        length := Nat.length_digitsAppend hBase length hRightIndex
  have hDigits :
      Nat.digitsAppend base length (Fintype.equivFin Source left).val =
        Nat.digitsAppend base length (Fintype.equivFin Source right).val := by
    apply List.ext_getElem
    · exact hLeftLength.trans hRightLength.symm
    · intro position hLeft hRight
      let index : Fin length := ⟨position, by simpa [hLeftLength] using hLeft⟩
      have hAt := hNoPosition index
      change
        (Nat.digitsAppend base length
            (Fintype.equivFin Source left).val).getD position 0 =
          (Nat.digitsAppend base length
            (Fintype.equivFin Source right).val).getD position 0 at hAt
      rw [List.getD_eq_getElem _ 0 hLeft,
        List.getD_eq_getElem _ 0 hRight] at hAt
      exact hAt
  have hIndexEq := congrArg (Nat.ofDigits base) hDigits
  have hIndexValEq :
      (Fintype.equivFin Source left).val =
        (Fintype.equivFin Source right).val := by
    simpa only [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
      Nat.ofDigits_digits] using hIndexEq
  apply hDifferent
  apply (Fintype.equivFin Source).injective
  exact Fin.ext hIndexValEq

/-- Mixed-radix tag digit embedded as a scalar in an algebra over `ZMod modulus`. -/
def mixedRadixTag
    {Source R : Type} [Fintype Source]
    (modulus base length : ℕ)
    [CommRing R] [Algebra (ZMod modulus) R]
    (source : Source) (position : Fin length) : R :=
  algebraMap (ZMod modulus) R
    (mixedRadixDigit base length source position : ZMod modulus)

/-- Two distinct sources have a tag coordinate whose difference is a unit.  This is the exact
algebraic content of the manuscript's deterministic unit-difference tags. -/
theorem exists_mixedRadixTag_sub_isUnit
    {Source R : Type} [Fintype Source]
    (modulus base length : ℕ)
    [Fact modulus.Prime] [CommRing R] [Algebra (ZMod modulus) R]
    (hBase : 1 < base) (hBaseModulus : base < modulus)
    (hCapacity : Fintype.card Source ≤ base ^ length)
    {left right : Source} (hDifferent : left ≠ right) :
    ∃ position : Fin length,
      IsUnit (mixedRadixTag (R := R) modulus base length left position -
        mixedRadixTag (R := R) modulus base length right position) := by
  obtain ⟨position, hDigit⟩ :=
    exists_mixedRadixDigit_ne base length hBase hCapacity hDifferent
  refine ⟨position, ?_⟩
  have hLeftLt : mixedRadixDigit base length left position < modulus :=
    (mixedRadixDigit_lt_base base length hBase hCapacity left position).trans hBaseModulus
  have hRightLt : mixedRadixDigit base length right position < modulus :=
    (mixedRadixDigit_lt_base base length hBase hCapacity right position).trans hBaseModulus
  have hZModDifferent :
      (mixedRadixDigit base length left position : ZMod modulus) ≠
        (mixedRadixDigit base length right position : ZMod modulus) := by
    intro hEqual
    apply hDigit
    have hValues := congrArg ZMod.val hEqual
    simpa [ZMod.val_natCast_of_lt hLeftLt, ZMod.val_natCast_of_lt hRightLt] using hValues
  have hUnitZMod : IsUnit
      ((mixedRadixDigit base length left position : ZMod modulus) -
        (mixedRadixDigit base length right position : ZMod modulus)) := by
    rw [isUnit_iff_ne_zero]
    exact sub_ne_zero.mpr hZModDifferent
  simpa [mixedRadixTag, map_sub] using
    hUnitZMod.map (algebraMap (ZMod modulus) R)

/-- Append mixed-radix tags to an arbitrary base source vector. -/
def mixedRadixTaggedSource
    {Source R BaseRow : Type} [Fintype Source]
    (modulus base length : ℕ)
    [CommRing R] [Algebra (ZMod modulus) R]
    (baseSource : Source → BaseRow → R) (source : Source) :
    BaseRow ⊕ Fin length → R
  | Sum.inl row => baseSource source row
  | Sum.inr position =>
      mixedRadixTag (R := R) modulus base length source position

/-- Every distinct pair of complete tagged source vectors differs by a unit in a tag row. -/
theorem exists_mixedRadixTaggedSource_sub_isUnit
    {Source R BaseRow : Type} [Fintype Source]
    (modulus base length : ℕ)
    [Fact modulus.Prime] [CommRing R] [Algebra (ZMod modulus) R]
    (hBase : 1 < base) (hBaseModulus : base < modulus)
    (hCapacity : Fintype.card Source ≤ base ^ length)
    (baseSource : Source → BaseRow → R)
    {left right : Source} (hDifferent : left ≠ right) :
    ∃ selected : BaseRow ⊕ Fin length,
      IsUnit
        (mixedRadixTaggedSource modulus base length baseSource left selected -
          mixedRadixTaggedSource modulus base length baseSource right selected) := by
  obtain ⟨position, hUnit⟩ := exists_mixedRadixTag_sub_isUnit
    (R := R) modulus base length hBase hBaseModulus hCapacity hDifferent
  exact ⟨Sum.inr position, hUnit⟩

/-- The complete tagged-source compiler is injective regardless of the base source coordinates. -/
theorem mixedRadixTaggedSource_injective
    {Source R BaseRow : Type} [Fintype Source]
    (modulus base length : ℕ)
    [Fact modulus.Prime] [CommRing R] [Nontrivial R] [Algebra (ZMod modulus) R]
    (hBase : 1 < base) (hBaseModulus : base < modulus)
    (hCapacity : Fintype.card Source ≤ base ^ length)
    (baseSource : Source → BaseRow → R) :
    Function.Injective
      (mixedRadixTaggedSource modulus base length baseSource) := by
  intro left right hVectors
  by_contra hDifferent
  obtain ⟨selected, hUnit⟩ := exists_mixedRadixTaggedSource_sub_isUnit
    (R := R) modulus base length hBase hBaseModulus hCapacity baseSource hDifferent
  have hCoordinate := congrFun hVectors selected
  have hZero :
      mixedRadixTaggedSource modulus base length baseSource left selected -
          mixedRadixTaggedSource modulus base length baseSource right selected = 0 :=
    sub_eq_zero.mpr hCoordinate
  rw [hZero] at hUnit
  exact not_isUnit_zero hUnit

/-- Deterministic tags and arbitrary base coordinates preserve every source point mass exactly. -/
theorem mixedRadixTaggedSource_probOutput
    {Source R BaseRow : Type} [Fintype Source]
    (modulus base length : ℕ)
    [Fact modulus.Prime] [CommRing R] [Nontrivial R] [Algebra (ZMod modulus) R]
    (hBase : 1 < base) (hBaseModulus : base < modulus)
    (hCapacity : Fintype.card Source ≤ base ^ length)
    (baseSource : Source → BaseRow → R)
    (sourceSampler : ProbComp Source) (source : Source) :
    Pr[= mixedRadixTaggedSource modulus base length baseSource source |
        mixedRadixTaggedSource modulus base length baseSource <$> sourceSampler] =
      Pr[= source | sourceSampler] := by
  exact probOutput_map_injective sourceSampler
    (mixedRadixTaggedSource_injective modulus base length hBase hBaseModulus
      hCapacity baseSource) source

/-! ## Support-constrained module-knapsack collisions -/

/-- Public transpose-matrix hash `Aᵀ x`, represented with rows and output columns as function
tables. -/
def moduleKnapsackHash
    {R Row Column : Type} [CommRing R] [Fintype Row]
    (matrix : Row → Column → R) (source : Row → R) : Column → R :=
  fun column ↦ ∑ row, source row * matrix row column

/-- Additive map exposing the hash difference of two fixed sources. -/
def moduleKnapsackDifferenceAddHom
    {R Row Column : Type} [CommRing R] [Fintype Row]
    (left right : Row → R) :
    (Row → Column → R) →+ (Column → R) where
  toFun matrix := fun column ↦
    ∑ row, (left row - right row) * matrix row column
  map_zero' := by
    funext column
    simp
  map_add' first second := by
    funext column
    simp [mul_add, Finset.sum_add_distrib]

/-- The additive difference map is exactly the difference of the two public hashes. -/
theorem moduleKnapsackDifferenceAddHom_apply
    {R Row Column : Type} [CommRing R] [Fintype Row]
    (left right : Row → R) (matrix : Row → Column → R) :
    moduleKnapsackDifferenceAddHom left right matrix =
      moduleKnapsackHash matrix left - moduleKnapsackHash matrix right := by
  funext column
  simp [moduleKnapsackDifferenceAddHom, moduleKnapsackHash,
    Finset.sum_sub_distrib, sub_mul]

/-- A unit source-difference coordinate makes the complete transpose-matrix difference map
surjective. -/
theorem moduleKnapsackDifferenceAddHom_surjective_of_isUnit
    {R Row Column : Type} [CommRing R] [Fintype Row] [DecidableEq Row]
    (left right : Row → R) (selected : Row)
    (hUnit : IsUnit (left selected - right selected)) :
    Function.Surjective (moduleKnapsackDifferenceAddHom (Column := Column) left right) := by
  intro output
  let unit : Rˣ := hUnit.unit
  let matrix : Row → Column → R := fun row column ↦
    if row = selected then ((unit⁻¹ : Rˣ) : R) * output column else 0
  refine ⟨matrix, ?_⟩
  funext column
  change (∑ row, (left row - right row) * matrix row column) = output column
  rw [Finset.sum_eq_single selected]
  · dsimp [matrix]
    rw [if_pos rfl]
    have hUnitSpec : (unit : R) = left selected - right selected :=
      hUnit.unit_spec
    rw [← hUnitSpec, ← mul_assoc]
    simp
  · intro row _ hRow
    simp [matrix, hRow]
  · simp

/-- A surjective additive map sends the canonical finite uniform law to the canonical uniform
law. -/
theorem evalDist_map_surjective_addHom_uniform
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain] [SampleableType Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    [SampleableType Codomain]
    (transform : Domain →+ Codomain) (hSurjective : Function.Surjective transform) :
    evalDist (transform <$> ($ᵗ Domain)) = evalDist ($ᵗ Codomain) := by
  classical
  apply evalDist_ext
  intro output
  rw [probOutput_uniformSample Codomain output,
    probOutput_map_eq_sum_fintype_ite]
  simp only [probOutput_uniformSample Domain]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hFiber :
      (Finset.univ.filter fun input : Domain ↦ output = transform input).card =
        (Finset.univ.filter fun input : Domain ↦ transform input = 0).card := by
    rw [show (Finset.univ.filter fun input : Domain ↦ output = transform input) =
        Finset.univ.filter fun input : Domain ↦ transform input = output by
      ext input
      simp [eq_comm]]
    exact AddMonoidHom.card_fiber_eq_of_mem_range transform
      (Set.mem_range.2 (hSurjective output)) (Set.mem_range.2 (hSurjective 0))
  rw [hFiber]
  let zeroFiber :=
    (Finset.univ.filter fun input : Domain ↦ transform input = 0).card
  have hZeroFiberPos : 0 < zeroFiber := by
    apply Finset.card_pos.mpr
    exact ⟨0, by simp⟩
  have hCard : zeroFiber * Fintype.card Codomain = Fintype.card Domain :=
    FormalProof4FHE.FiniteSurjectiveFiber.zeroFiberCard_mul_card_eq_card_of_surjective
      transform hSurjective
  have hCardENNReal :
      (zeroFiber : ℝ≥0∞) * (Fintype.card Codomain : ℝ≥0∞) =
        (Fintype.card Domain : ℝ≥0∞) := by
    exact_mod_cast hCard
  change (zeroFiber : ℝ≥0∞) * (Fintype.card Domain : ℝ≥0∞)⁻¹ = _
  rw [← hCardENNReal]
  have hInverse :
      ((zeroFiber : ℝ≥0∞) * (Fintype.card Codomain : ℝ≥0∞))⁻¹ =
        (zeroFiber : ℝ≥0∞)⁻¹ * (Fintype.card Codomain : ℝ≥0∞)⁻¹ :=
    ENNReal.mul_inv
      (Or.inr (ENNReal.natCast_ne_top (Fintype.card Codomain)))
      (Or.inl (ENNReal.natCast_ne_top zeroFiber))
  rw [hInverse]
  rw [← mul_assoc, ENNReal.mul_inv_cancel
    (Nat.cast_ne_zero.mpr hZeroFiberPos.ne')
    (ENNReal.natCast_ne_top zeroFiber), one_mul]

/-- With a unit difference coordinate, the whole public hash difference is exactly uniform. -/
theorem moduleKnapsackDifference_uniform_evalDist
    {R Row Column : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Row] [DecidableEq Row]
    [Fintype Column] [DecidableEq Column]
    (left right : Row → R) (selected : Row)
    (hUnit : IsUnit (left selected - right selected)) :
    evalDist (moduleKnapsackDifferenceAddHom left right <$>
        ($ᵗ (Row → Column → R))) =
      evalDist ($ᵗ (Column → R)) := by
  exact evalDist_map_surjective_addHom_uniform
    (moduleKnapsackDifferenceAddHom left right)
    (moduleKnapsackDifferenceAddHom_surjective_of_isUnit left right selected hUnit)

/-- Exact pair-collision probability for a fixed pair whose difference contains a unit. -/
theorem moduleKnapsackHash_pairCollision_probability
    {R Row Column : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Row] [DecidableEq Row]
    [Fintype Column] [DecidableEq Column]
    (left right : Row → R) (selected : Row)
    (hUnit : IsUnit (left selected - right selected)) :
    Pr[(fun matrix : Row → Column → R ↦
        moduleKnapsackHash matrix left = moduleKnapsackHash matrix right) |
      ($ᵗ (Row → Column → R))] =
      (Fintype.card (Column → R) : ℝ≥0∞)⁻¹ := by
  have hUniform := moduleKnapsackDifference_uniform_evalDist
    (R := R) (Row := Row) (Column := Column) left right selected hUnit
  calc
    Pr[(fun matrix : Row → Column → R ↦
        moduleKnapsackHash matrix left = moduleKnapsackHash matrix right) |
      ($ᵗ (Row → Column → R))] =
      Pr[= (0 : Column → R) |
        moduleKnapsackDifferenceAddHom left right <$>
          ($ᵗ (Row → Column → R))] := by
        rw [probOutput_map]
        apply probEvent_congr'
        · intro matrix _
          rw [moduleKnapsackDifferenceAddHom_apply]
          constructor
          · exact sub_eq_zero.mpr
          · exact sub_eq_zero.mp
        · rfl
    _ = Pr[= (0 : Column → R) | ($ᵗ (Column → R))] :=
      evalDist_ext_iff.mp hUniform 0
    _ = (Fintype.card (Column → R) : ℝ≥0∞)⁻¹ :=
      probOutput_uniformSample _ _

/-- Union bound for a fixed source against every other point of a finite support. -/
theorem moduleKnapsackHash_secondPreimage_probability_le
    {R Row Column : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Row] [DecidableEq Row]
    [Fintype Column] [DecidableEq Column]
    (support : Finset (Row → R)) (source : Row → R) (hSource : source ∈ support)
    (hUnitDifference : ∀ candidate ∈ support, candidate ≠ source →
      ∃ selected : Row, IsUnit (candidate selected - source selected)) :
    Pr[(fun matrix : Row → Column → R ↦
        ∃ candidate ∈ support.erase source,
          moduleKnapsackHash matrix candidate = moduleKnapsackHash matrix source) |
      ($ᵗ (Row → Column → R))] ≤
      ((support.card - 1 : ℕ) : ℝ≥0∞) *
        (Fintype.card (Column → R) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[(fun matrix : Row → Column → R ↦
        ∃ candidate ∈ support.erase source,
          moduleKnapsackHash matrix candidate = moduleKnapsackHash matrix source) |
      ($ᵗ (Row → Column → R))] ≤
      ∑ candidate ∈ support.erase source,
        Pr[(fun matrix : Row → Column → R ↦
          moduleKnapsackHash matrix candidate = moduleKnapsackHash matrix source) |
          ($ᵗ (Row → Column → R))] :=
      probEvent_exists_finset_le_sum (support.erase source)
        ($ᵗ (Row → Column → R))
        (fun candidate matrix ↦
          moduleKnapsackHash matrix candidate = moduleKnapsackHash matrix source)
    _ = ∑ _candidate ∈ support.erase source,
        (Fintype.card (Column → R) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro candidate hCandidate
      obtain ⟨selected, hUnit⟩ := hUnitDifference candidate
        (Finset.mem_of_mem_erase hCandidate) (Finset.ne_of_mem_erase hCandidate)
      exact moduleKnapsackHash_pairCollision_probability
        candidate source selected hUnit
    _ = ((support.card - 1 : ℕ) : ℝ≥0∞) *
        (Fintype.card (Column → R) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, Finset.card_erase_of_mem hSource]
      simp

/-- The concrete mixed-radix tagged source satisfies the manuscript's fixed-source statistical
second-preimage bound directly, without first converting its support into a vector finset. -/
theorem mixedRadixTaggedSource_secondPreimage_probability_le
    {Source R BaseRow Column : Type}
    (modulus base length : ℕ)
    [Fintype Source] [DecidableEq Source]
    [Fintype BaseRow] [DecidableEq BaseRow]
    [Fintype Column] [DecidableEq Column]
    [Fact modulus.Prime]
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Algebra (ZMod modulus) R]
    (hBase : 1 < base) (hBaseModulus : base < modulus)
    (hCapacity : Fintype.card Source ≤ base ^ length)
    (baseSource : Source → BaseRow → R)
    (support : Finset Source) (source : Source) (hSource : source ∈ support) :
    Pr[(fun matrix : (BaseRow ⊕ Fin length) → Column → R ↦
        ∃ candidate ∈ support.erase source,
          moduleKnapsackHash matrix
              (mixedRadixTaggedSource modulus base length baseSource candidate) =
            moduleKnapsackHash matrix
              (mixedRadixTaggedSource modulus base length baseSource source)) |
      ($ᵗ ((BaseRow ⊕ Fin length) → Column → R))] ≤
      ((support.card - 1 : ℕ) : ℝ≥0∞) *
        (Fintype.card (Column → R) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[(fun matrix : (BaseRow ⊕ Fin length) → Column → R ↦
        ∃ candidate ∈ support.erase source,
          moduleKnapsackHash matrix
              (mixedRadixTaggedSource modulus base length baseSource candidate) =
            moduleKnapsackHash matrix
              (mixedRadixTaggedSource modulus base length baseSource source)) |
      ($ᵗ ((BaseRow ⊕ Fin length) → Column → R))] ≤
      ∑ candidate ∈ support.erase source,
        Pr[(fun matrix : (BaseRow ⊕ Fin length) → Column → R ↦
          moduleKnapsackHash matrix
              (mixedRadixTaggedSource modulus base length baseSource candidate) =
            moduleKnapsackHash matrix
              (mixedRadixTaggedSource modulus base length baseSource source)) |
          ($ᵗ ((BaseRow ⊕ Fin length) → Column → R))] :=
      probEvent_exists_finset_le_sum (support.erase source)
        ($ᵗ ((BaseRow ⊕ Fin length) → Column → R))
        (fun candidate matrix ↦
          moduleKnapsackHash matrix
              (mixedRadixTaggedSource modulus base length baseSource candidate) =
            moduleKnapsackHash matrix
              (mixedRadixTaggedSource modulus base length baseSource source))
    _ = ∑ _candidate ∈ support.erase source,
        (Fintype.card (Column → R) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro candidate hCandidate
      obtain ⟨selected, hUnit⟩ := exists_mixedRadixTaggedSource_sub_isUnit
        (R := R) modulus base length hBase hBaseModulus hCapacity baseSource
        (Finset.ne_of_mem_erase hCandidate)
      exact moduleKnapsackHash_pairCollision_probability
        (mixedRadixTaggedSource modulus base length baseSource candidate)
        (mixedRadixTaggedSource modulus base length baseSource source)
        selected hUnit
    _ = ((support.card - 1 : ℕ) : ℝ≥0∞) *
        (Fintype.card (Column → R) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, Finset.card_erase_of_mem hSource]
      simp

end

end FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurityFramework
