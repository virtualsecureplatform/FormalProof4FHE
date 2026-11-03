module

public import FormalProof4FHE.HasteBoots.ReciprocalPolynomial

@[expose] public section

/-!
# The exact native masked reciprocal identity

For partial lookup tables the native identity is r*h+mask*g*h-mask, not
h*(r+g)-mask. It forces active reciprocals and, for nonzero r, zero helper
padding without any zero-padding premise on original sources. The full helper
sum therefore equals the reciprocal sum over the public active prefix.
EQ/ZeroCheck enforcement, authentication and native refinement remain open.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.ReciprocalMask

noncomputable section

variable {K : Type} [Field K]

def residual (r source helper : K) (active : Bool) : K :=
  r * helper + (if active then 1 else 0) * source * helper - (if active then 1 else 0)

theorem active_forced (r source helper : K) (valid : residual r source helper true = 0) :
    r + source ≠ 0 ∧ helper = (r + source)⁻¹ := by
  have sum : r * helper + source * helper = 1 := sub_eq_zero.mp (by simpa [residual] using valid)
  apply ReciprocalPolynomial.reciprocal_forced
  calc helper * (r + source) = r * helper + source * helper := by ring
       _ = 1 := sum

theorem inactive_forced (r source helper : K) (rNonzero : r ≠ 0) (valid : residual r source helper false = 0) :
    helper = 0 := by
  have product : r * helper = 0 := by simpa [residual] using valid
  exact (mul_eq_zero.mp product).resolve_left rNonzero

theorem honest_active (r source : K) (nonzero : r + source ≠ 0) :
    residual r source (r + source)⁻¹ true = 0 := by
  have inverse := mul_inv_cancel₀ nonzero
  simp only [residual, reduceIte, one_mul]
  calc r * (r + source)⁻¹ + source * (r + source)⁻¹ - 1 = (r + source) * (r + source)⁻¹ - 1 := by ring
       _ = 0 := by rw [inverse, sub_self]

theorem honest_inactive (r source : K) : residual r source 0 false = 0 := by simp [residual]

theorem prefix_sum {count padding : ℕ} (r : K) (sources helpers : Fin (count + padding) → K)
    (rNonzero : r ≠ 0) (valid : ∀ i, residual r (sources i) (helpers i) (decide (i.val < count)) = 0) :
    (∑ i, helpers i) = ∑ i : Fin count, (r + sources (i.castAdd padding))⁻¹ := by
  rw [Fin.sum_univ_add]
  have activeSum : (∑ i : Fin count, helpers (i.castAdd padding)) =
      ∑ i : Fin count, (r + sources (i.castAdd padding))⁻¹ := by
    apply Finset.sum_congr rfl
    intro i _
    have flag : decide ((i.castAdd padding).val < count) = true := by simp
    exact (active_forced _ _ _ (by simpa only [flag] using valid (i.castAdd padding))).2
  have paddingSum : (∑ i : Fin padding, helpers (Fin.natAdd count i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have flag : decide ((Fin.natAdd count i).val < count) = false := by simp
    exact inactive_forced _ _ _ rNonzero (by simpa only [flag] using valid (Fin.natAdd count i))
  rw [activeSum, paddingSum, add_zero]

/-- The exact masked relation and the full helper sum imply the active-source
polynomial root, without constraining original source padding. -/
theorem prefix_identity_implies_root {count padding size : ℕ} (r : K)
    (sources helpers : Fin (count + padding) → K) (table multiplicities : Fin size → K)
    (rNonzero : r ≠ 0) (valid : ∀ i, residual r (sources i) (helpers i) (decide (i.val < count)) = 0)
    (tableNonzero : ∀ i, r + table i ≠ 0)
    (total : (∑ i, helpers i) = ∑ i, multiplicities i * (r + table i)⁻¹) :
    (ReciprocalPolynomial.numerator (fun i : Fin count => sources (i.castAdd padding)) table multiplicities).eval r = 0 := by
  refine ReciprocalPolynomial.identity_implies_root _ table multiplicities r ?_ tableNonzero ?_
  · intro i
    have flag : decide ((i.castAdd padding).val < count) = true := by simp
    exact (active_forced _ _ _ (by simpa only [flag] using valid (i.castAdd padding))).1
  · exact (prefix_sum r sources helpers rNonzero valid).symm.trans total

end

end FormalProof4FHE.HasteBoots.ReciprocalMask
