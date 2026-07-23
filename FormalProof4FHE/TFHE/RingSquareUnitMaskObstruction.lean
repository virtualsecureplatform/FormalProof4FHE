/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteSurjectiveFiber
import FormalProof4FHE.RLWE.RingRegev
import FormalProof4FHE.TFHE.BlindRotation
import FormalProof4FHE.TFHE.NativePowerOfTwoLocalRing
import FormalProof4FHE.TFHE.RingSquareRGSWSecurity

/-!
# Short-Preimage Obstructions for the Ring-Square Compiler

For the production ring `ZMod (2^k)[X]/(X^(2^d)+1)`, parity evaluation is the residue-field map
to `ZMod 2` and reflects units.  Hence exactly half of all ring elements are units.  Combined with
the inverse-weight uniformity and centered-box count in `RingSquareRGSWSecurity`, this gives a
concrete limitation of the evident one-source compiler for `RGSW_S(-S)`: conditioned on algebraic
success, a level-zero inverse weight is uniform among `q^N / 2` units, whereas at most
`(2B+1)^N` ring elements have centered coefficient norm at most `B`.

For several sources, local-ring structure gives a sharper dichotomy.  Every level-zero solution
`sum_i x_i a_i = 1` has a unit weight coordinate, so each fixed vector succeeds against uniform
masks with probability exactly `1 / q^N`.  A union bound over the complete centered box proves
that the probability of any radius-`B` solution is at most `(2B+1)^(N*m) / q^N`.  This rules out
short preimages information-theoretically below the counting threshold and identifies efficient
inhomogeneous Ring-SIS search as the remaining issue above it.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler
noncomputable section

namespace MultiSourceCounting

/-- Families of public masks or public preimage weights. -/
abbrev Vectors (R : Type) (count : ℕ) := Fin count → R

/-- The mask combination whose value must equal one at the level-zero gadget. -/
def maskCombination
    {R : Type} [CommRing R] {count : ℕ}
    (weight masks : Vectors R count) : R :=
  ∑ index, weight index * masks index

/-- For fixed weights, mask combination is an additive homomorphism of the mask family. -/
def maskCombinationAddHom
    {R : Type} [CommRing R] {count : ℕ}
    (weight : Vectors R count) : Vectors R count →+ R where
  toFun := maskCombination weight
  map_zero' := by
    classical
    simp [maskCombination]
  map_add' left right := by
    classical
    simp [maskCombination, mul_add, Finset.sum_add_distrib]

@[simp]
theorem maskCombinationAddHom_apply
    {R : Type} [CommRing R] {count : ℕ}
    (weight masks : Vectors R count) :
    maskCombinationAddHom weight masks = maskCombination weight masks := rfl

/-- A single unit weight makes the fixed-weight combination map surjective. -/
theorem maskCombinationAddHom_surjective_of_isUnit
    {R : Type} [CommRing R] {count : ℕ}
    (weight : Vectors R count)
    (selected : Fin count) (hunit : IsUnit (weight selected)) :
    Function.Surjective (maskCombinationAddHom weight) := by
  classical
  intro target
  let selectedUnit : Rˣ := hunit.unit
  refine ⟨fun index ↦
    if index = selected then
      (↑(selectedUnit⁻¹) : R) * target
    else 0, ?_⟩
  change (∑ index,
      weight index *
        (if index = selected then
          (↑(selectedUnit⁻¹) : R) * target
        else 0)) = target
  rw [Finset.sum_eq_single selected]
  · rw [if_pos rfl]
    dsimp [selectedUnit]
    calc
      weight selected * ((↑hunit.unit⁻¹ : R) * target) =
          (↑hunit.unit : R) * ((↑hunit.unit⁻¹ : R) * target) :=
        congrArg (fun value : R ↦ value * ((↑hunit.unit⁻¹ : R) * target))
          hunit.unit_spec.symm
      _ = target := by rw [← mul_assoc, Units.mul_inv, one_mul]
  · intro index _ hne
    rw [if_neg hne, mul_zero]
  · simp

/-- A finite ratio `a/(a*b)` cancels to `1/b` when `a` is positive. -/
private theorem ennreal_ratio_eq_inv_of_mul_eq
    {a b c : ℕ} (ha : 0 < a) (hmul : a * b = c) :
    (a : ENNReal) / (c : ENNReal) = (b : ENNReal)⁻¹ := by
  subst c
  push_cast
  rw [div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by exact_mod_cast ha.ne')) (Or.inl (by simp))]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast ha.ne') (by simp), one_mul]

/-- With one unit coordinate, a fixed weight vector hits any requested ring target with exact
probability `1 / |R|` under uniform public masks. -/
theorem probEvent_maskCombination_eq_of_isUnit
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {count : ℕ} [SampleableType (Vectors R count)]
    (weight : Vectors R count)
    (selected : Fin count) (hunit : IsUnit (weight selected))
    (target : R) :
    Pr[(fun masks : Vectors R count ↦
          maskCombination weight masks = target) |
        ($ᵗ Vectors R count)] =
      (Fintype.card R : ENNReal)⁻¹ := by
  classical
  let transform := maskCombinationAddHom weight
  have hsurjective : Function.Surjective transform :=
    maskCombinationAddHom_surjective_of_isUnit weight selected hunit
  have hfiber :
      (Finset.univ.filter fun masks : Vectors R count ↦
          transform masks = target).card =
        (Finset.univ.filter fun masks : Vectors R count ↦
          transform masks = 0).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range transform
      (Set.mem_range.2 (hsurjective target))
      (Set.mem_range.2 (hsurjective 0))
  have hfactor :=
    FormalProof4FHE.FiniteSurjectiveFiber.zeroFiberCard_mul_card_eq_card_of_surjective
      transform hsurjective
  have hpositive :
      0 < (Finset.univ.filter
        fun masks : Vectors R count ↦
          transform masks = 0).card := by
    rw [Finset.card_pos]
    exact ⟨0, by simp⟩
  rw [probEvent_uniformSample]
  change
    ((Finset.univ.filter fun masks : Vectors R count ↦
        transform masks = target).card : ENNReal) /
        Fintype.card (Vectors R count) = _
  rw [hfiber]
  exact ennreal_ratio_eq_inv_of_mul_eq hpositive hfactor

/-- Union bound over an arbitrary finite family of candidate preimages.  If every successful
candidate has at least one unit coordinate, then each fixed candidate succeeds with probability
exactly `1 / |R|`, and the probability that any candidate succeeds is at most
`|Candidate| / |R|`. -/
theorem probEvent_exists_candidate_le
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {count : ℕ} [SampleableType (Vectors R count)]
    {Candidate : Type} [Fintype Candidate] [DecidableEq Candidate]
    (weight : Candidate → Vectors R count)
    (target : R)
    (unitOfSuccess : ∀ candidate masks,
      maskCombination (weight candidate) masks = target →
        ∃ index, IsUnit (weight candidate index)) :
    Pr[(fun masks : Vectors R count ↦
          ∃ candidate, maskCombination (weight candidate) masks = target) |
        ($ᵗ Vectors R count)] ≤
      (Fintype.card Candidate : ENNReal) *
        (Fintype.card R : ENNReal)⁻¹ := by
  classical
  have hfixed (candidate : Candidate) :
      Pr[(fun masks : Vectors R count ↦
            maskCombination (weight candidate) masks = target) |
          ($ᵗ Vectors R count)] ≤
        (Fintype.card R : ENNReal)⁻¹ := by
    by_cases hunit : ∃ index, IsUnit (weight candidate index)
    · obtain ⟨index, hindex⟩ := hunit
      exact (probEvent_maskCombination_eq_of_isUnit
        (weight candidate) index hindex target).le
    · have himpossible : ∀ masks : Vectors R count,
          ¬maskCombination (weight candidate) masks = target := by
        intro masks hsuccess
        exact hunit (unitOfSuccess candidate masks hsuccess)
      simp [himpossible]
  calc
    _ ≤ Pr[(fun masks : Vectors R count ↦
          ∃ candidate ∈ (Finset.univ : Finset Candidate),
            maskCombination (weight candidate) masks = target) |
        ($ᵗ Vectors R count)] := by
      apply probEvent_mono
      intro masks _ hsuccess
      obtain ⟨candidate, hcandidate⟩ := hsuccess
      exact ⟨candidate, Finset.mem_univ _, hcandidate⟩
    _ ≤ ∑ candidate ∈ (Finset.univ : Finset Candidate),
          Pr[(fun masks : Vectors R count ↦
                maskCombination (weight candidate) masks = target) |
            ($ᵗ Vectors R count)] :=
      probEvent_exists_finset_le_sum (Finset.univ : Finset Candidate)
        ($ᵗ Vectors R count)
        (fun candidate masks ↦ maskCombination (weight candidate) masks = target)
    _ ≤ ∑ _candidate ∈ (Finset.univ : Finset Candidate),
          (Fintype.card R : ENNReal)⁻¹ := by
      exact Finset.sum_le_sum fun candidate _ ↦ hfixed candidate
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- In a commutative local ring, a level-zero preimage equation can hold only if at least one
weight coordinate is a unit.  Indeed, a unit finite sum has a unit summand, and a unit product
has unit factors. -/
theorem exists_isUnit_weight_of_maskCombination_eq_of_isUnit
    {R : Type} [CommRing R] [IsLocalRing R] {count : ℕ}
    (weight masks : Vectors R count)
    (target : R) (target_unit : IsUnit target)
    (hsuccess : maskCombination weight masks = target) :
    ∃ index, IsUnit (weight index) := by
  classical
  have hsum : IsUnit (∑ index, weight index * masks index) := by
    change IsUnit (maskCombination weight masks)
    rw [hsuccess]
    exact target_unit
  obtain ⟨index, _hindex, hterm⟩ :=
    IsLocalRing.exists_of_isUnit_sum (s := Finset.univ) hsum
  exact ⟨index, (IsUnit.mul_iff.mp hterm).1⟩

/-- Level-zero form of the preceding local-ring lemma. -/
theorem exists_isUnit_weight_of_maskCombination_eq_one
    {R : Type} [CommRing R] [IsLocalRing R] {count : ℕ}
    (weight masks : Vectors R count)
    (hsuccess : maskCombination weight masks = 1) :
    ∃ index, IsUnit (weight index) :=
  exists_isUnit_weight_of_maskCombination_eq_of_isUnit
    weight masks 1 isUnit_one hsuccess

/-- Local-ring specialization of the finite-candidate union bound. -/
theorem probEvent_exists_candidate_le_of_localRing
    {R : Type} [CommRing R] [IsLocalRing R] [Fintype R] [DecidableEq R]
    {count : ℕ} [SampleableType (Vectors R count)]
    {Candidate : Type} [Fintype Candidate] [DecidableEq Candidate]
    (weight : Candidate → Vectors R count)
    (target : R) (target_unit : IsUnit target) :
    Pr[(fun masks : Vectors R count ↦
          ∃ candidate, maskCombination (weight candidate) masks = target) |
        ($ᵗ Vectors R count)] ≤
      (Fintype.card Candidate : ENNReal) *
        (Fintype.card R : ENNReal)⁻¹ :=
  probEvent_exists_candidate_le weight target fun _candidate masks hsuccess ↦
    exists_isUnit_weight_of_maskCombination_eq_of_isUnit
      _ masks target target_unit hsuccess

end MultiSourceCounting

namespace SingleSourceInverse.PowerOfTwo

open Native.ShiftedCandidateEvaluator.DiagonalNormalForm

/-- The production power-of-two negacyclic ring used in the unit-mask calculation. -/
abbrev Ring (modulusExponent degreeExponent : ℕ) :=
  RLWE.Rq (2 ^ modulusExponent) (2 ^ degreeExponent)

/-- Bridge between the proof-facing unit and the executable bundled negacyclic-ring unit. -/
theorem ring_one_eq_bundled (modulusExponent degreeExponent : ℕ) :
    (1 : Ring modulusExponent degreeExponent) =
      (RLWE.negacyclicRing
        (2 ^ modulusExponent) (2 ^ degreeExponent)).one := by
  exact BlindRotation.rq_one_eq_bundled
    (2 ^ modulusExponent) (2 ^ degreeExponent)

/-- At positive degree, the unit selected by the generic proof-facing `CommRing` dictionary is
the executable bundled unit. -/
private theorem rqPositive_commRing_one_eq_bundled
    {q degree : ℕ} (degree_positive : 0 < degree) :
    @One.one (RLWE.Rq q degree)
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod q) degree).toAddGroupWithOne.toOne =
      (RLWE.negacyclicRing q degree).one := by
  cases degree with
  | zero => omega
  | succ degree => rfl

theorem ring_commRing_one_eq_bundled
    (modulusExponent degreeExponent : ℕ) :
    @One.one (Ring modulusExponent degreeExponent)
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod (2 ^ modulusExponent))
          (2 ^ degreeExponent)).toAddGroupWithOne.toOne =
      (RLWE.negacyclicRing
        (2 ^ modulusExponent) (2 ^ degreeExponent)).one :=
  rqPositive_commRing_one_eq_bundled (pow_pos (by omega) degreeExponent)

/-- Units are equivalent to ring elements equipped with an `IsUnit` certificate. -/
def unitsEquivIsUnitSubtype (R : Type) [Monoid R] :
    Rˣ ≃ {value : R // IsUnit value} where
  toFun unit := ⟨unit, unit.isUnit⟩
  invFun value := value.2.unit
  left_inv unit := by
    apply Units.ext
    exact unit.isUnit.unit_spec
  right_inv value := by
    apply Subtype.ext
    exact value.2.unit_spec

/-- Parity evaluation on the production ring. -/
def parityHom
    (modulusExponent degreeExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent) :
    Ring modulusExponent degreeExponent →+* ZMod 2 :=
  rqParityEval
    (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent))
    (pow_pos (by omega) degreeExponent)

/-- Production parity evaluation is onto the binary residue field. -/
theorem parityHom_surjective
    (modulusExponent degreeExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent) :
    Function.Surjective
      (parityHom modulusExponent degreeExponent modulusExponent_positive) := by
  exact ZMod.ringHom_surjective
    (parityHom modulusExponent degreeExponent modulusExponent_positive)

/-- The production power-of-two negacyclic ring is local, with parity evaluation as its residue
map to the binary field. -/
theorem ring_isLocalRing
    (modulusExponent degreeExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent) :
    IsLocalRing (Ring modulusExponent degreeExponent) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsLocalHom
      (parityHom modulusExponent degreeExponent modulusExponent_positive) :=
    Native.PowerOfTwoLocalRing.rqParityEval_isLocalHom_powerOfTwo
      modulusExponent modulusExponent_positive degreeExponent
  exact RingHom.domain_isLocalRing
    (parityHom modulusExponent degreeExponent modulusExponent_positive)

/-- An element of the production ring is a unit exactly when its binary residue is one. -/
theorem isUnit_iff_parityHom_eq_one
    (modulusExponent degreeExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (value : Ring modulusExponent degreeExponent) :
    IsUnit value ↔
      parityHom modulusExponent degreeExponent modulusExponent_positive value = 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let localParity : IsLocalHom
      (parityHom modulusExponent degreeExponent modulusExponent_positive) :=
    Native.PowerOfTwoLocalRing.rqParityEval_isLocalHom_powerOfTwo
      modulusExponent modulusExponent_positive degreeExponent
  constructor
  · intro hunit
    have mappedUnit : IsUnit
        (parityHom modulusExponent degreeExponent modulusExponent_positive value) :=
      hunit.map (parityHom modulusExponent degreeExponent modulusExponent_positive)
    have mappedNeZero :
        parityHom modulusExponent degreeExponent modulusExponent_positive value ≠ 0 :=
      isUnit_iff_ne_zero.mp mappedUnit
    have fermat := ZMod.pow_card_sub_one_eq_one mappedNeZero
    simpa using fermat
  · intro hparity
    letI : IsLocalHom
        (parityHom modulusExponent degreeExponent modulusExponent_positive) := localParity
    apply IsUnit.of_map
      (parityHom modulusExponent degreeExponent modulusExponent_positive) value
    rw [hparity]
    exact isUnit_one

/-- The unit masks are precisely the preimage of the singleton residue `{1}`. -/
theorem unitMaskFinset_eq_parityOne
    (modulusExponent degreeExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent) :
    (Finset.univ.filter fun value : Ring modulusExponent degreeExponent ↦ IsUnit value) =
      Finset.univ.filter fun value : Ring modulusExponent degreeExponent ↦
        parityHom modulusExponent degreeExponent modulusExponent_positive value ∈
          ({1} : Finset (ZMod 2)) := by
  classical
  ext value
  simp [isUnit_iff_parityHom_eq_one modulusExponent degreeExponent
    modulusExponent_positive value]

/-- Exactly half of the elements of a production power-of-two negacyclic ring are units.  The
division-free cardinality form avoids any side conditions about natural-number division. -/
theorem card_unitMasks_mul_two_eq_card_ring
    (modulusExponent degreeExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent) :
    (Finset.univ.filter fun value : Ring modulusExponent degreeExponent ↦ IsUnit value).card *
        2 =
      Fintype.card (Ring modulusExponent degreeExponent) := by
  classical
  let transform : Ring modulusExponent degreeExponent →+ ZMod 2 :=
    (parityHom modulusExponent degreeExponent modulusExponent_positive).toAddMonoidHom
  have hsurjective : Function.Surjective transform :=
    parityHom_surjective modulusExponent degreeExponent modulusExponent_positive
  have hunitCard :
      (Finset.univ.filter fun value : Ring modulusExponent degreeExponent ↦
          IsUnit value).card =
        (Finset.univ.filter fun value : Ring modulusExponent degreeExponent ↦
          transform value = 0).card := by
    rw [unitMaskFinset_eq_parityOne modulusExponent degreeExponent
      modulusExponent_positive]
    change
      (Finset.univ.filter fun value : Ring modulusExponent degreeExponent ↦
          transform value ∈ ({1} : Finset (ZMod 2))).card =
        (Finset.univ.filter fun value : Ring modulusExponent degreeExponent ↦
          transform value = 0).card
    rw [FormalProof4FHE.FiniteSurjectiveFiber.card_preimage_finset_eq_card_mul_zeroFiber
      transform hsurjective ({1} : Finset (ZMod 2))]
    simp
  rw [hunitCard]
  simpa only [ZMod.card] using
    (FormalProof4FHE.FiniteSurjectiveFiber.zeroFiberCard_mul_card_eq_card_of_surjective
      transform hsurjective)

/-- Equivalent statement directly in terms of the cardinality of the unit group. -/
theorem card_units_mul_two_eq_card_ring
    (modulusExponent degreeExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent) :
    Fintype.card (Ring modulusExponent degreeExponent)ˣ * 2 =
      Fintype.card (Ring modulusExponent degreeExponent) := by
  calc
    Fintype.card (Ring modulusExponent degreeExponent)ˣ * 2 =
        Fintype.card
            {value : Ring modulusExponent degreeExponent // IsUnit value} * 2 := by
      rw [Fintype.card_congr
        (unitsEquivIsUnitSubtype (Ring modulusExponent degreeExponent))]
    _ =
        (Finset.univ.filter fun value : Ring modulusExponent degreeExponent ↦
          IsUnit value).card * 2 := by
      rw [Fintype.card_subtype]
    _ = Fintype.card (Ring modulusExponent degreeExponent) :=
      card_unitMasks_mul_two_eq_card_ring
        modulusExponent degreeExponent modulusExponent_positive

/-- Closed cardinality of the production unit group. -/
theorem card_units_eq_power_div_two
    (modulusExponent degreeExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent) :
    Fintype.card (Ring modulusExponent degreeExponent)ˣ =
      (2 ^ modulusExponent) ^ (2 ^ degreeExponent) / 2 := by
  have hcard := card_units_mul_two_eq_card_ring
    modulusExponent degreeExponent modulusExponent_positive
  rw [RLWE.RingRegev.card_rq] at hcard
  omega

/-- Families of production-ring weights whose every coordinate lies in the centered coefficient
box of radius `bound`. -/
abbrev BoundedWeights
    (modulusExponent degreeExponent count bound : ℕ) :=
  {weight : MultiSourceCounting.Vectors
      (Ring modulusExponent degreeExponent) count //
    ∀ index, LatticeCrypto.cInfNorm (weight index) ≤ bound}

noncomputable instance instFintypeBoundedWeights
    (modulusExponent degreeExponent count bound : ℕ) :
    Fintype (BoundedWeights modulusExponent degreeExponent count bound) := by
  classical
  exact Fintype.ofFinite _

/-- Forgetting the shared family proof embeds bounded weight vectors into the product of
single-polynomial centered boxes. -/
def boundedWeightsToBoundedPolynomials
    {modulusExponent degreeExponent count bound : ℕ}
    (weight : BoundedWeights modulusExponent degreeExponent count bound) :
    Fin count → FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial
      (2 ^ modulusExponent) (2 ^ degreeExponent) bound :=
  fun index ↦ ⟨weight.1 index, weight.2 index⟩

theorem boundedWeightsToBoundedPolynomials_injective
    {modulusExponent degreeExponent count bound : ℕ} :
    Function.Injective
      (boundedWeightsToBoundedPolynomials :
        BoundedWeights modulusExponent degreeExponent count bound →
          Fin count → FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial
            (2 ^ modulusExponent) (2 ^ degreeExponent) bound) := by
  intro left right heq
  apply Subtype.ext
  funext index
  exact congrArg (fun encoded ↦ (encoded index).1) heq

/-- There are at most `(2B+1)^(N*m)` coefficient-bounded weight vectors with `m` source
coordinates over a degree-`N` production ring. -/
theorem card_boundedWeights_le
    (modulusExponent degreeExponent count bound : ℕ) :
    Fintype.card (BoundedWeights modulusExponent degreeExponent count bound) ≤
      (2 * bound + 1) ^ ((2 ^ degreeExponent) * count) := by
  calc
    Fintype.card (BoundedWeights modulusExponent degreeExponent count bound) ≤
        Fintype.card
          (Fin count → FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial
            (2 ^ modulusExponent) (2 ^ degreeExponent) bound) :=
      Fintype.card_le_of_injective boundedWeightsToBoundedPolynomials
        boundedWeightsToBoundedPolynomials_injective
    _ = Fintype.card
          (FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial
            (2 ^ modulusExponent) (2 ^ degreeExponent) bound) ^ count := by
      rw [Fintype.card_pi_const]
    _ ≤ ((2 * bound + 1) ^ (2 ^ degreeExponent)) ^ count :=
      pow_le_pow_left'
        (FormalProof4FHE.FiniteCenteredSupport.card_boundedPolynomial_le
          (2 ^ modulusExponent) (2 ^ degreeExponent) bound) count
    _ = (2 * bound + 1) ^ ((2 ^ degreeExponent) * count) := by
      rw [pow_mul]

/-- Concrete multi-source information-theoretic obstruction.  For `m` independent uniform
production-ring masks, the probability that *any* coefficient-bounded vector `x` solves the
level-zero inhomogeneous equation `sum_i x_i a_i = 1` is at most
`(2B+1)^(N*m) / q^N`.

This theorem quantifies over all bounded vectors, so it applies even to an unbounded search
procedure.  When the ratio is negligible, no compiler can usually find such a short preimage;
when it is not negligible, existence is no longer ruled out and efficient search becomes the
inhomogeneous Ring-SIS question. -/
theorem probEvent_exists_boundedWeights_combination_eq_bundledOne_le
    (modulusExponent degreeExponent count bound : ℕ)
    (modulusExponent_positive : 0 < modulusExponent)
    [SampleableType
      (MultiSourceCounting.Vectors (Ring modulusExponent degreeExponent) count)] :
    Pr[(fun masks : MultiSourceCounting.Vectors
          (Ring modulusExponent degreeExponent) count ↦
        ∃ weight : BoundedWeights
            modulusExponent degreeExponent count bound,
          MultiSourceCounting.maskCombination weight.1 masks =
            (RLWE.negacyclicRing
              (2 ^ modulusExponent) (2 ^ degreeExponent)).one) |
      ($ᵗ MultiSourceCounting.Vectors
        (Ring modulusExponent degreeExponent) count)] ≤
      (((2 * bound + 1) ^ ((2 ^ degreeExponent) * count) : ℕ) : ENNReal) /
        ((((2 ^ modulusExponent) ^ (2 ^ degreeExponent)) : ℕ) : ENNReal) := by
  classical
  letI : IsLocalRing (Ring modulusExponent degreeExponent) :=
    ring_isLocalRing modulusExponent degreeExponent modulusExponent_positive
  calc
    _ ≤ (Fintype.card
          (BoundedWeights modulusExponent degreeExponent count bound) : ENNReal) *
        (Fintype.card (Ring modulusExponent degreeExponent) : ENNReal)⁻¹ :=
      MultiSourceCounting.probEvent_exists_candidate_le_of_localRing
        (fun weight : BoundedWeights
          modulusExponent degreeExponent count bound ↦ weight.1)
        (RLWE.negacyclicRing
          (2 ^ modulusExponent) (2 ^ degreeExponent)).one
        (by
          rw [← ring_commRing_one_eq_bundled
            modulusExponent degreeExponent]
          exact isUnit_one)
    _ ≤ (((2 * bound + 1) ^ ((2 ^ degreeExponent) * count) : ℕ) : ENNReal) *
        (Fintype.card (Ring modulusExponent degreeExponent) : ENNReal)⁻¹ := by
      gcongr
      exact_mod_cast card_boundedWeights_le
        modulusExponent degreeExponent count bound
    _ = _ := by
      rw [RLWE.RingRegev.card_rq, div_eq_mul_inv]

/-- Proof-facing `= 1` form of the concrete multi-source obstruction. -/
theorem probEvent_exists_boundedWeights_combination_eq_one_le
    (modulusExponent degreeExponent count bound : ℕ)
    (modulusExponent_positive : 0 < modulusExponent)
    [SampleableType
      (MultiSourceCounting.Vectors (Ring modulusExponent degreeExponent) count)] :
    Pr[(fun masks : MultiSourceCounting.Vectors
          (Ring modulusExponent degreeExponent) count ↦
        ∃ weight : BoundedWeights
            modulusExponent degreeExponent count bound,
          MultiSourceCounting.maskCombination weight.1 masks = 1) |
      ($ᵗ MultiSourceCounting.Vectors
        (Ring modulusExponent degreeExponent) count)] ≤
      (((2 * bound + 1) ^ ((2 ^ degreeExponent) * count) : ℕ) : ENNReal) /
        ((((2 ^ modulusExponent) ^ (2 ^ degreeExponent)) : ℕ) : ENNReal) := by
  simpa only [ring_one_eq_bundled] using
    (probEvent_exists_boundedWeights_combination_eq_bundledOne_le
      modulusExponent degreeExponent count bound modulusExponent_positive)

/-- Every deterministic selector that is coefficient-bounded whenever it succeeds is covered by
the information-theoretic existential bound.  Adaptivity to the complete public mask family does
not improve the counting threshold. -/
theorem probEvent_bounded_selector_combination_eq_one_le
    (modulusExponent degreeExponent count bound : ℕ)
    (modulusExponent_positive : 0 < modulusExponent)
    [SampleableType
      (MultiSourceCounting.Vectors (Ring modulusExponent degreeExponent) count)]
    (selector : MultiSourceCounting.Vectors (Ring modulusExponent degreeExponent) count →
      MultiSourceCounting.Vectors (Ring modulusExponent degreeExponent) count)
    (hBounded : ∀ masks,
      MultiSourceCounting.maskCombination (selector masks) masks = 1 →
      ∀ index, LatticeCrypto.cInfNorm (selector masks index) ≤ bound) :
    Pr[(fun masks : MultiSourceCounting.Vectors
          (Ring modulusExponent degreeExponent) count ↦
        MultiSourceCounting.maskCombination (selector masks) masks = 1) |
      ($ᵗ MultiSourceCounting.Vectors
        (Ring modulusExponent degreeExponent) count)] ≤
      (((2 * bound + 1) ^ ((2 ^ degreeExponent) * count) : ℕ) : ENNReal) /
        ((((2 ^ modulusExponent) ^ (2 ^ degreeExponent)) : ℕ) : ENNReal) := by
  calc
    _ ≤ Pr[(fun masks : MultiSourceCounting.Vectors
          (Ring modulusExponent degreeExponent) count ↦
        ∃ weight : BoundedWeights modulusExponent degreeExponent count bound,
          MultiSourceCounting.maskCombination weight.1 masks = 1) |
      ($ᵗ MultiSourceCounting.Vectors
        (Ring modulusExponent degreeExponent) count)] := by
      apply probEvent_mono
      intro masks _ hSuccess
      exact ⟨⟨selector masks, hBounded masks hSuccess⟩, hSuccess⟩
    _ ≤ _ := probEvent_exists_boundedWeights_combination_eq_one_le
      modulusExponent degreeExponent count bound modulusExponent_positive

/-- Failure-probability form of the deterministic-selector obstruction.  Whenever the counting
ratio is negligible, every selector that stays inside the radius-`B` box on success fails with
probability close to one. -/
theorem one_sub_countingRatio_le_probEvent_bounded_selector_failure
    (modulusExponent degreeExponent count bound : ℕ)
    (modulusExponent_positive : 0 < modulusExponent)
    [SampleableType
      (MultiSourceCounting.Vectors (Ring modulusExponent degreeExponent) count)]
    (selector : MultiSourceCounting.Vectors (Ring modulusExponent degreeExponent) count →
      MultiSourceCounting.Vectors (Ring modulusExponent degreeExponent) count)
    (hBounded : ∀ masks,
      MultiSourceCounting.maskCombination (selector masks) masks = 1 →
      ∀ index, LatticeCrypto.cInfNorm (selector masks index) ≤ bound) :
    1 -
        (((2 * bound + 1) ^ ((2 ^ degreeExponent) * count) : ℕ) : ENNReal) /
          ((((2 ^ modulusExponent) ^ (2 ^ degreeExponent)) : ℕ) : ENNReal) ≤
      Pr[(fun masks : MultiSourceCounting.Vectors
            (Ring modulusExponent degreeExponent) count ↦
          ¬MultiSourceCounting.maskCombination (selector masks) masks = 1) |
        ($ᵗ MultiSourceCounting.Vectors
          (Ring modulusExponent degreeExponent) count)] := by
  apply probEvent_one_sub_le_of_compl_le
  · simp
  · simpa only [not_not] using
      (probEvent_bounded_selector_combination_eq_one_le
        modulusExponent degreeExponent count bound modulusExponent_positive
        selector hBounded)

/-- Coefficient-bounded units of the exact production ring. -/
abbrev BoundedUnit
    (modulusExponent degreeExponent bound : ℕ) :=
  {unit : (Ring modulusExponent degreeExponent)ˣ //
    LatticeCrypto.cInfNorm (unit : Ring modulusExponent degreeExponent) ≤ bound}

noncomputable instance instFintypeBoundedUnit
    (modulusExponent degreeExponent bound : ℕ) :
    Fintype (BoundedUnit modulusExponent degreeExponent bound) := by
  classical
  exact Fintype.ofFinite _

/-- Forgetting invertibility embeds bounded production-ring units into the complete centered
coefficient box. -/
def boundedUnitToBoundedPolynomial
    {modulusExponent degreeExponent bound : ℕ}
    (unit : BoundedUnit modulusExponent degreeExponent bound) :
    FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial
      (2 ^ modulusExponent) (2 ^ degreeExponent) bound :=
  ⟨(unit.1 : Ring modulusExponent degreeExponent), unit.2⟩

theorem boundedUnitToBoundedPolynomial_injective
    {modulusExponent degreeExponent bound : ℕ} :
    Function.Injective
      (boundedUnitToBoundedPolynomial :
        BoundedUnit modulusExponent degreeExponent bound →
          FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial
            (2 ^ modulusExponent) (2 ^ degreeExponent) bound) := by
  intro left right heq
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val heq

/-- At most `(2B+1)^N` production-ring units lie in the centered coefficient box of radius `B`. -/
theorem card_boundedUnit_le
    (modulusExponent degreeExponent bound : ℕ) :
    Fintype.card (BoundedUnit modulusExponent degreeExponent bound) ≤
      (2 * bound + 1) ^ (2 ^ degreeExponent) := by
  exact (Fintype.card_le_of_injective boundedUnitToBoundedPolynomial
    boundedUnitToBoundedPolynomial_injective).trans
      (FormalProof4FHE.FiniteCenteredSupport.card_boundedPolynomial_le
        (2 ^ modulusExponent) (2 ^ degreeExponent) bound)

/-- Concrete one-source obstruction at the level-zero gadget `g = 1`: conditioned on an
invertible uniform mask, the chance that the inverse weight has centered norm at most `B` is at
most the centered-box size divided by the exact unit-group size. -/
theorem probEvent_levelZeroInverse_cInfNorm_le
    (modulusExponent degreeExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    [SampleableType (Ring modulusExponent degreeExponent)ˣ] (bound : ℕ) :
    Pr[(fun sourceUnit : (Ring modulusExponent degreeExponent)ˣ ↦
          LatticeCrypto.cInfNorm
            (unitWeight (1 : (Ring modulusExponent degreeExponent)ˣ) sourceUnit :
              Ring modulusExponent degreeExponent) ≤ bound) |
        ($ᵗ (Ring modulusExponent degreeExponent)ˣ)] ≤
      (((2 * bound + 1) ^ (2 ^ degreeExponent) : ℕ) : ENNReal) /
        (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) / 2 : ℕ) : ENNReal) := by
  rw [probEvent_unitWeight_eq_shortUnitDensity
    (1 : (Ring modulusExponent degreeExponent)ˣ)
    (fun value : Ring modulusExponent degreeExponent ↦
      LatticeCrypto.cInfNorm value ≤ bound)]
  rw [card_units_eq_power_div_two
    modulusExponent degreeExponent modulusExponent_positive]
  apply ENNReal.div_le_div_right
  exact_mod_cast (show
    (Finset.univ.filter fun weightUnit : (Ring modulusExponent degreeExponent)ˣ ↦
      LatticeCrypto.cInfNorm
        (weightUnit : Ring modulusExponent degreeExponent) ≤ bound).card ≤
        (2 * bound + 1) ^ (2 ^ degreeExponent) by
      rw [← Fintype.card_subtype]
      exact card_boundedUnit_le modulusExponent degreeExponent bound)

end SingleSourceInverse.PowerOfTwo
end
end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler
