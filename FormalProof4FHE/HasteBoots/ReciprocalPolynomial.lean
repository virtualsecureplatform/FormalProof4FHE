module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.CharP.Basic

@[expose] public section

/-!
# Clearing the native lookup reciprocal identity

The denominator is r+hashedRow, with the native plus sign. Products include
all active source rows, including repetitions. Public multiplicities may be
arbitrary field elements. A missing hashed row forces a nonzero numerator
when the active source count is below the characteristic. The numerator has
degree at most sourceCount+tableSize-1. Challenge-domain sampling, tuple-hash
collisions, authenticated reciprocal identities and native refinement are
separate layers.
-/

open scoped BigOperators
open Polynomial

namespace FormalProof4FHE.HasteBoots.ReciprocalPolynomial

noncomputable section

variable {K : Type} [Field K] {count size : ℕ}

def factor (a : K) : K[X] := X + C a

def denominator (values : Fin count → K) : K[X] := ∏ i, factor (values i)

def cofactor (values : Fin count → K) (i : Fin count) : K[X] :=
  ∏ j ∈ Finset.univ.erase i, factor (values j)

def tableNumerator (table multiplicities : Fin size → K) : K[X] :=
  ∑ i, C (multiplicities i) * cofactor table i

def numerator (sources : Fin count → K) (table multiplicities : Fin size → K) : K[X] :=
  (denominator sources).derivative * denominator table - denominator sources * tableNumerator table multiplicities

theorem denominator_monic (values : Fin count → K) : (denominator values).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

theorem denominator_ne_zero (values : Fin count → K) : denominator values ≠ 0 :=
  (denominator_monic values).ne_zero

theorem denominator_degree (values : Fin count → K) : (denominator values).natDegree = count := by
  rw [denominator, Polynomial.natDegree_prod_of_monic Finset.univ (fun i => factor (values i))
    (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [factor, Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem cofactor_degree (values : Fin count → K) (i : Fin count) :
    (cofactor values i).natDegree = count - 1 := by
  rw [cofactor, Polynomial.natDegree_prod_of_monic (Finset.univ.erase i) (fun j => factor (values j))
    (fun _ _ => Polynomial.monic_X_add_C _)]
  simp [factor]

theorem denominator_split (values : Fin count → K) (i : Fin count) :
    denominator values = factor (values i) * cofactor values i := by
  exact (Finset.mul_prod_erase Finset.univ (fun j => factor (values j)) (Finset.mem_univ i)).symm

theorem factor_eval (a r : K) : (factor a).eval r = r + a := by simp [factor]

theorem denominator_eval (values : Fin count → K) (r : K) :
    (denominator values).eval r = ∏ i, (r + values i) := by
  simp [denominator, Polynomial.eval_prod, factor_eval]

theorem cofactor_eval (values : Fin count → K) (i : Fin count) (r : K) (nonzero : r + values i ≠ 0) :
    (cofactor values i).eval r = (denominator values).eval r * (r + values i)⁻¹ := by
  rw [denominator_split values i, Polynomial.eval_mul, factor_eval]
  rw [mul_right_comm, mul_inv_cancel₀ nonzero, one_mul]

theorem derivative_denominator (values : Fin count → K) :
    (denominator values).derivative = ∑ i, cofactor values i := by
  simp only [denominator, Polynomial.derivative_prod_finset, factor, Polynomial.derivative_add,
    Polynomial.derivative_X, Polynomial.derivative_C, add_zero, mul_one, cofactor]

theorem derivative_eval (values : Fin count → K) (r : K) (nonzero : ∀ i, r + values i ≠ 0) :
    (denominator values).derivative.eval r = (denominator values).eval r * ∑ i, (r + values i)⁻¹ := by
  rw [derivative_denominator, Polynomial.eval_finsetSum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => cofactor_eval values i r (nonzero i))

theorem tableNumerator_eval (table multiplicities : Fin size → K) (r : K) (nonzero : ∀ i, r + table i ≠ 0) :
    (tableNumerator table multiplicities).eval r =
      (denominator table).eval r * ∑ i, multiplicities i * (r + table i)⁻¹ := by
  simp only [tableNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [cofactor_eval table i r (nonzero i)]
  ring

theorem identity_implies_root (sources : Fin count → K) (table multiplicities : Fin size → K) (r : K)
    (sourceNonzero : ∀ i, r + sources i ≠ 0) (tableNonzero : ∀ i, r + table i ≠ 0)
    (identity : (∑ i, (r + sources i)⁻¹) = ∑ i, multiplicities i * (r + table i)⁻¹) :
    (numerator sources table multiplicities).eval r = 0 := by
  rw [numerator, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    derivative_eval sources r sourceNonzero, tableNumerator_eval table multiplicities r tableNonzero, identity]
  ring

theorem reciprocal_forced (r source helper : K) (valid : helper * (r + source) = 1) :
    r + source ≠ 0 ∧ helper = (r + source)⁻¹ := by
  have nonzero : r + source ≠ 0 := by
    intro zero
    rw [zero, mul_zero] at valid
    exact zero_ne_one valid
  refine ⟨nonzero, ?_⟩
  apply mul_right_cancel₀ nonzero
  rw [valid, inv_mul_cancel₀ nonzero]

theorem helper_identity_implies_root (sources : Fin count → K) (table multiplicities : Fin size → K)
    (helpers : Fin count → K) (r : K) (valid : ∀ i, helpers i * (r + sources i) = 1)
    (tableNonzero : ∀ i, r + table i ≠ 0)
    (identity : (∑ i, helpers i) = ∑ i, multiplicities i * (r + table i)⁻¹) :
    (numerator sources table multiplicities).eval r = 0 := by
  apply identity_implies_root sources table multiplicities r
    (fun i => (reciprocal_forced _ _ _ (valid i)).1) tableNonzero
  rw [← identity]
  exact Finset.sum_congr rfl (fun i _ => (reciprocal_forced _ _ _ (valid i)).2.symm)

theorem tableNumerator_degree (table multiplicities : Fin size → K) :
    (tableNumerator table multiplicities).natDegree ≤ size - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact Polynomial.natDegree_mul_le.trans (by simp [cofactor_degree])

theorem numerator_degree (sources : Fin count → K) (table multiplicities : Fin size → K) (positive : 0 < count) :
    (numerator sources table multiplicities).natDegree ≤ count + size - 1 := by
  by_cases empty : size = 0
  · subst size
    simpa [numerator, denominator, tableNumerator] using
      (Polynomial.natDegree_derivative_le (denominator sources)).trans_eq (by rw [denominator_degree])
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · have derivative := Polynomial.natDegree_derivative_le (denominator sources)
    rw [denominator_degree] at derivative
    have product := Polynomial.natDegree_mul_le (p := (denominator sources).derivative) (q := denominator table)
    rw [denominator_degree] at product
    omega
  · have product := Polynomial.natDegree_mul_le (p := denominator sources) (q := tableNumerator table multiplicities)
    rw [denominator_degree] at product
    have tableBound := tableNumerator_degree table multiplicities
    omega

theorem denominator_eval_ne_zero (values : Fin count → K) (r : K) (nonzero : ∀ i, r + values i ≠ 0) :
    (denominator values).eval r ≠ 0 := by
  rw [denominator_eval]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => nonzero i)

theorem denominator_root (sources : Fin count → K) (i : Fin count) :
    (denominator sources).IsRoot (-sources i) := by
  rw [Polynomial.IsRoot, denominator_split sources i, Polynomial.eval_mul, factor_eval]
  simp

theorem multiplicity_bound (sources : Fin count → K) (r : K) :
    (denominator sources).rootMultiplicity r ≤ count := by
  have bound := Polynomial.natDegree_le_of_dvd
    (Polynomial.pow_rootMultiplicity_dvd (denominator sources) r) (denominator_ne_zero sources)
  simpa only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one, denominator_degree] using bound

variable {p : ℕ} [CharP K p]

theorem natCast_ne_zero {n : ℕ} (positive : 0 < n) (small : n < p) : (n : K) ≠ 0 := by
  intro zero
  exact Nat.not_dvd_of_pos_of_lt positive small ((CharP.cast_eq_zero_iff K p n).mp zero)

theorem derivative_ne_zero (sources : Fin count → K) (positive : 0 < count) (small : count < p) :
    (denominator sources).derivative ≠ 0 := by
  have top := denominator_monic sources
  change (denominator sources).coeff (denominator sources).natDegree = 1 at top
  rw [denominator_degree] at top
  intro zero
  have coefficient := congrArg (fun f : K[X] => f.coeff (count - 1)) zero
  have index : count - 1 + 1 = count := by omega
  simp only [Polynomial.coeff_derivative, index, top, one_mul, Polynomial.coeff_zero] at coefficient
  rw [← Nat.cast_add_one, index] at coefficient
  exact natCast_ne_zero positive small coefficient

/-- Repeated missing source rows have multiplicity between 1 and count<p,
so their pole cannot vanish in the field or be cancelled by public terms. -/
theorem numerator_ne_zero (sources : Fin count → K) (table multiplicities : Fin size → K)
    (bad : ∃ i, ∀ j, sources i ≠ table j) (small : count < p) : numerator sources table multiplicities ≠ 0 := by
  obtain ⟨i, outside⟩ := bad
  have positive : 0 < count := by have := i.isLt; omega
  have root := denominator_root sources i
  have rootPositive := (Polynomial.rootMultiplicity_pos (denominator_ne_zero sources)).mpr root
  have multiplicitySmall := (multiplicity_bound sources (-sources i)).trans_lt small
  have orderDerivative := Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors root
    (mem_nonZeroDivisors_of_ne_zero (natCast_ne_zero rootPositive multiplicitySmall))
  have notRoot : ¬(denominator table).IsRoot (-sources i) := by
    exact denominator_eval_ne_zero table (-sources i) (fun j equal => outside j (neg_add_eq_zero.mp equal))
  have leftNonzero := mul_ne_zero (derivative_ne_zero sources positive small) (denominator_ne_zero table)
  intro zero
  have equal : (denominator sources).derivative * denominator table =
      denominator sources * tableNumerator table multiplicities := sub_eq_zero.mp zero
  have rightNonzero : denominator sources * tableNumerator table multiplicities ≠ 0 := by
    rw [← equal]
    exact leftNonzero
  have orders := congrArg (fun f : K[X] => f.rootMultiplicity (-sources i)) equal
  rw [Polynomial.rootMultiplicity_mul leftNonzero, Polynomial.rootMultiplicity_mul rightNonzero,
    orderDerivative, Polynomial.rootMultiplicity_eq_zero notRoot, add_zero] at orders
  omega

end

end FormalProof4FHE.HasteBoots.ReciprocalPolynomial
