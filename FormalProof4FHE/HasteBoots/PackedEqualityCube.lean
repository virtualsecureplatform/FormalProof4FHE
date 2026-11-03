module

public import FormalProof4FHE.HasteBoots.PackedZeroEquality
public import FormalProof4FHE.HasteBoots.FlatMatrixFold

@[expose] public section

/-!
# Equality suffixes in Boolean-cube and native flat order

The first semantic cube bit is coordinate zero and the low native address bit.
The equality kernel is transported without permuting its point coordinates.
These adapters connect the first-round multilinear probability space to the
ordered matrix-fold source tables.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.PackedEqualityCube

/-- Coordinate zero is the first bit removed by the packed fold. -/
def bits : (n : ℕ) → MatrixFold.Cube n ≃ PackedZeroEquality.Cell n
  | 0 => show Unit ≃ (Fin 0 → Fin 2) from Equiv.ofUnique _ _
  | n + 1 => {
    toFun := fun cell => Fin.cons (finTwoEquiv.symm cell.1) (bits n cell.2)
    invFun := fun cell => (finTwoEquiv (cell 0), (bits n).symm (fun index => cell index.succ))
    left_inv := by
      rintro ⟨bit, suffix⟩
      simp only [Fin.cons_zero, Fin.cons_succ, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      rfl
    right_inv := by
      intro cell
      funext index
      refine Fin.cases ?_ (fun i => ?_) index
      · simp only [Equiv.symm_apply_apply, Fin.cons_zero]
      · simp only [Equiv.apply_symm_apply, Fin.cons_succ] }

theorem bits_zero {n : ℕ} (bit : Bool) (suffix : MatrixFold.Cube n) :
    bits (n + 1) (bit, suffix) 0 = finTwoEquiv.symm bit := rfl

theorem bits_succ {n : ℕ} (bit : Bool) (suffix : MatrixFold.Cube n) (index : Fin n) :
    bits (n + 1) (bit, suffix) index.succ = bits n suffix index := rfl

/-- The complete native flat address is the little-endian Boolean expansion. -/
theorem index_eq_sum_bits (n : ℕ) (cell : MatrixFold.Cube n) :
    (FlatMatrixFold.index n cell).val = ∑ index : Fin n, 2 ^ index.val * (bits n cell index).val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases cell with ⟨bit, suffix⟩
    rw [FlatMatrixFold.index_succ_val, Fin.sum_univ_succ]
    simp only [bits_zero, bits_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    rw [ih suffix]
    cases bit <;> simp [finTwoEquiv, Finset.mul_sum, Nat.mul_assoc, Nat.mul_comm, Nat.add_comm]

noncomputable section

variable {F : Type} [Field F] {n : ℕ}

def weight (point : Fin n → F) (cell : MatrixFold.Cube n) : F :=
  PackedZeroEquality.equality point (bits n cell)

theorem weight_zero (point : Fin 0 → F) (cell : MatrixFold.Cube 0) : weight point cell = 1 := by
  simp only [weight, PackedZeroEquality.equality_prod, Finset.univ_eq_empty, Finset.prod_empty]

theorem weight_succ (point : Fin (n + 1) → F) (bit : Bool) (suffix : MatrixFold.Cube n) :
    weight point (bit, suffix) =
      (if bit then point 0 else 1 - point 0) * weight (fun index => point index.succ) suffix := by
  simp only [weight, PackedZeroEquality.equality_prod, Fin.prod_univ_succ, bits_zero, bits_succ]
  cases bit <;> rfl

/-- Reindexing a weighted suffix sum preserves the exact point coordinates. -/
theorem weighted_sum (point : Fin n → F) (values : MatrixFold.Cube n → F) :
    (∑ cell, weight point cell * values cell) =
      ∑ cell : PackedZeroEquality.Cell n, PackedZeroEquality.equality point cell * values ((bits n).symm cell) := by
  simpa only [weight, Equiv.symm_apply_apply] using
    (bits n).sum_comp (fun cell => PackedZeroEquality.equality point cell * values ((bits n).symm cell))

end

end FormalProof4FHE.HasteBoots.PackedEqualityCube
