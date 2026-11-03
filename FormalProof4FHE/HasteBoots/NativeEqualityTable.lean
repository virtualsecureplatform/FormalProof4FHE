module

public import FormalProof4FHE.HasteBoots.PackedEqualityCube

@[expose] public section

/-!
# Native equality-table construction in flat order

The native loop starts at [1]. For each next point coordinate r it appends the
two blocks (1-r)*old and r*old. Its typed array semantics below therefore adds
the next coordinate as the high address bit. The resulting table equals the
multilinear equality weights with coordinate zero at the low bit.
Allocation, machine-index bounds and Rust memory refinement remain separate.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.NativeEqualityTable

def address (n : ℕ) : PackedZeroEquality.Cell n ≃ Fin (2 ^ n) :=
  (PackedEqualityCube.bits n).symm.trans (FlatMatrixFold.index n)

theorem address_val (n : ℕ) (cell : PackedZeroEquality.Cell n) :
    (address n cell).val = ∑ index : Fin n, 2 ^ index.val * (cell index).val := by
  simpa only [address, Equiv.trans_apply, Equiv.apply_symm_apply] using
    PackedEqualityCube.index_eq_sum_bits n ((PackedEqualityCube.bits n).symm cell)

theorem address_succ {n : ℕ} (cell : PackedZeroEquality.Cell (n + 1)) :
    (address (n + 1) cell).val = (address n (fun index => cell index.castSucc)).val +
      2 ^ n * (cell (Fin.last n)).val := by
  rw [address_val, Fin.sum_univ_castSucc, address_val]
  rfl

variable {F : Type} [Field F]

/-- The two native output blocks, represented as a fixed-size array. -/
def table : (n : ℕ) → (Fin n → F) → Fin (2 ^ n) → F
  | 0, _, _ => 1
  | n + 1, point, position =>
    if low : position.val < 2 ^ n then
      (1 - point (Fin.last n)) * table n (fun index => point index.castSucc) ⟨position.val, low⟩
    else
      point (Fin.last n) * table n (fun index => point index.castSucc)
        ⟨position.val - 2 ^ n, by
          have bound := position.isLt
          have power : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
          omega⟩

noncomputable section

theorem equality_succ {n : ℕ} (point : Fin (n + 1) → F) (cell : PackedZeroEquality.Cell (n + 1)) :
    PackedZeroEquality.equality point cell =
      PackedZeroEquality.equality (fun index => point index.castSucc) (fun index => cell index.castSucc) *
        (if cell (Fin.last n) = 0 then 1 - point (Fin.last n) else point (Fin.last n)) := by
  simp only [PackedZeroEquality.equality_prod, Fin.prod_univ_castSucc]

/-- The actual high-block construction has exactly the equality-polynomial
values in the original coordinate order. -/
theorem table_address (n : ℕ) (point : Fin n → F) (cell : PackedZeroEquality.Cell n) :
    table n point (address n cell) = PackedZeroEquality.equality point cell := by
  induction n with
  | zero => simp only [table, PackedZeroEquality.equality_prod, Finset.univ_eq_empty, Finset.prod_empty]
  | succ n ih =>
    have splitAddress := address_succ cell
    have prefixBound := (address n (fun index => cell index.castSucc)).isLt
    by_cases lastZero : cell (Fin.last n) = 0
    · have low : (address (n + 1) cell).val < 2 ^ n := by
        simp only [lastZero, Fin.val_zero, mul_zero, add_zero] at splitAddress
        omega
      rw [table, dite_eq_left low]
      have same : (⟨(address (n + 1) cell).val, low⟩ : Fin (2 ^ n)) =
          address n (fun index => cell index.castSucc) := by
        apply Fin.ext
        simpa only [lastZero, Fin.val_zero, mul_zero, add_zero] using splitAddress
      rw [same, ih, equality_succ]
      simp only [lastZero, reduceIte, mul_comm]
    · have lastOne : cell (Fin.last n) = 1 := by
        have bit := (cell (Fin.last n)).isLt
        apply Fin.ext
        have nonzero : (cell (Fin.last n)).val ≠ 0 := fun equal => lastZero (Fin.ext equal)
        omega
      have high : ¬(address (n + 1) cell).val < 2 ^ n := by
        simp only [lastOne, Fin.val_one, mul_one] at splitAddress
        omega
      rw [table, dite_eq_right high]
      have same : (address (n + 1) cell).val - 2 ^ n = (address n (fun index => cell index.castSucc)).val := by
        simp only [lastOne, Fin.val_one, mul_one] at splitAddress
        omega
      have sameFin (bound : (address (n + 1) cell).val - 2 ^ n < 2 ^ n) :
          (⟨(address (n + 1) cell).val - 2 ^ n, bound⟩ : Fin (2 ^ n)) =
            address n (fun index => cell index.castSucc) := Fin.ext same
      rw [sameFin, ih, equality_succ]
      simp only [lastZero, ite_false, mul_comm]

/-- Native flat construction agrees with the cube weights used by matrix folds. -/
theorem table_index (n : ℕ) (point : Fin n → F) (cell : MatrixFold.Cube n) :
    table n point (FlatMatrixFold.index n cell) = PackedEqualityCube.weight point cell := by
  simpa only [address, Equiv.trans_apply, Equiv.symm_apply_apply, PackedEqualityCube.weight] using
    table_address n point (PackedEqualityCube.bits n cell)

end

end FormalProof4FHE.HasteBoots.NativeEqualityTable
