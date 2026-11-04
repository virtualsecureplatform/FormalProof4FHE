module

public import FormalProof4FHE.HasteBoots.NativeInterpolationSafety
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# Consecutive-node denominators for the native interpolation loop

The signed factorial expression is proved equal to the actual product of
node differences. Its adjacent-index identity is the algebraic invariant
needed by the literal descending accumulator.
-/

namespace FormalProof4FHE.HasteBoots.NativeInterpolationWeights

open scoped BigOperators

noncomputable section

variable {K : Type} [Field K]

def denominator (degree index : ℕ) : K :=
  (index.factorial : K) * (-1) ^ (degree - index) * ((degree - index).factorial : K)

def skipProduct (degree index : ℕ) : K :=
  ∏ other ∈ Finset.range (degree + 1), if other = index then 1 else (index : K) - (other : K)

theorem lower_product (index : ℕ) :
    (∏ other ∈ Finset.range index, ((index : K) - (other : K))) = (index.factorial : K) := by
  rw [Finset.prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]

theorem denominator_product (degree index : ℕ) (inside : index ≤ degree) :
    skipProduct degree index = (denominator degree index : K) := by
  induction degree generalizing index with
  | zero =>
    have same : index = 0 := by omega
    simp [same, skipProduct, denominator]
  | succ degree ih =>
    by_cases top : index = degree + 1
    · subst index
      rw [skipProduct, Finset.prod_range_succ]
      simp only [ite_true, mul_one]
      have regular : (∏ other ∈ Finset.range (degree + 1),
          if other = degree + 1 then (1 : K) else ((degree + 1 : ℕ) : K) - (other : K)) =
          ∏ other ∈ Finset.range (degree + 1), (((degree + 1 : ℕ) : K) - (other : K)) := by
        apply Finset.prod_congr rfl
        intro other member
        exact ite_eq_right (by have bound := Finset.mem_range.mp member; omega)
      rw [regular, lower_product]
      simp only [denominator, Nat.sub_self, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    · have below : index ≤ degree := by omega
      rw [skipProduct, Finset.prod_range_succ]
      change skipProduct degree index * (if degree + 1 = index then 1 else (index : K) - ((degree + 1 : ℕ) : K)) = _
      rw [ih index below, ite_eq_right (Ne.symm top)]
      have difference : degree + 1 - index = (degree - index) + 1 := by omega
      simp only [denominator, difference, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [Nat.cast_sub below]
      ring

theorem denominator_top (degree : ℕ) : (denominator degree degree : K) = (degree.factorial : K) := by
  simp only [denominator, Nat.sub_self, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]

/-- The denominator recurrence exactly matches `up *= -remaining` and
`down *= index`, without replacing either update by a division. -/
theorem denominator_step (degree index : ℕ) (inside : index + 1 ≤ degree) :
    ((index + 1 : ℕ) : K) * denominator degree index =
      -((degree - index : ℕ) : K) * denominator degree (index + 1) := by
  have difference : degree - index = (degree - (index + 1)) + 1 := by omega
  simp only [denominator, difference, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem denominator_nonzero (degree index : ℕ) (inside : index ≤ degree)
    (nodes : ∀ j, 0 < j → j ≤ degree → (j : K) ≠ 0) : (denominator degree index : K) ≠ 0 := by
  unfold denominator
  exact mul_ne_zero (mul_ne_zero
    (NativeInterpolationSafety.factorial_nonzero index (fun j positive small => nodes j positive (small.trans inside)))
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
    (NativeInterpolationSafety.factorial_nonzero (degree - index)
      (fun j positive small => nodes j positive (small.trans (Nat.sub_le _ _))))

/-- The signed factorial is the denominator of the actual finite-node
Lagrange basis, with the evaluation node omitted. -/
theorem denominator_fin (degree : ℕ) (node : Fin (degree + 1)) :
    (denominator degree node.val : K) =
      ∏ other ∈ Finset.univ.erase node, ((node.val : K) - (other.val : K)) := by
  have all := denominator_product (K := K) degree node.val (by have bound := node.isLt; omega)
  have finite : skipProduct degree node.val =
      ∏ other : Fin (degree + 1), if other = node then (1 : K) else (node.val : K) - (other.val : K) := by
    rw [skipProduct, Finset.prod_range]
    apply Finset.prod_congr rfl
    intro other _
    simp only [Fin.ext_iff]
  rw [← all, finite]
  have erased := Finset.prod_erase (Finset.univ : Finset (Fin (degree + 1)))
    (a := node)
    (f := fun other : Fin (degree + 1) => if other = node then (1 : K) else (node.val : K) - (other.val : K))
    (by simp)
  rw [← erased]
  apply Finset.prod_congr rfl
  intro other member
  exact ite_eq_right (Finset.mem_erase.mp member).1

/-- The reciprocal denominator is the library's Lagrange nodal weight. -/
theorem nodalWeight_value (degree : ℕ) (node : Fin (degree + 1)) :
    Lagrange.nodalWeight Finset.univ (fun index : Fin (degree + 1) => (index.val : K)) node =
      (denominator degree node.val : K)⁻¹ := by
  rw [Lagrange.nodalWeight, Finset.prod_inv_distrib, denominator_fin]

end

end FormalProof4FHE.HasteBoots.NativeInterpolationWeights
