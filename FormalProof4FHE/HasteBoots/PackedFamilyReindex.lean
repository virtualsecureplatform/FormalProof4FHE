module
public import FormalProof4FHE.HasteBoots.OriginalJobOrdinal
@[expose] public section

/-! Whole packed-table equality survives the exact dependent row casts used
by original allocated source/helper functions. No coordinate or padding lane
is dropped when transporting these native dimensions. -/
namespace FormalProof4FHE.HasteBoots.PackedFamilyReindex
open MatrixFold (Cube)
open NativeFields (Goldilocks)

theorem table {leftFull rightFull leftRows rightRows leftPadding rightPadding : ℕ}
    (left : Cube leftFull → Fin (3+leftPadding) → Goldilocks)
    (right : Cube rightFull → Fin (3+rightPadding) → Goldilocks)
    (leftDimension : leftFull = leftRows) (rightDimension : rightFull = rightRows)
    (rows : leftRows = rightRows) (padding : leftPadding = rightPadding) (same : HEq left right) :
    HEq (fun cell : Cube leftRows => left (cast (congrArg Cube leftDimension.symm) cell))
      (fun cell : Cube rightRows => right (cast (congrArg Cube rightDimension.symm) cell)) := by
  subst rightRows
  subst rightPadding
  subst leftFull
  subst rightFull
  cases same
  rfl

theorem family {leftCount rightCount leftRows rightRows leftPadding rightPadding : ℕ}
    (left : Fin leftCount → Cube leftRows → Fin (3+leftPadding) → Goldilocks)
    (right : Fin rightCount → Cube rightRows → Fin (3+rightPadding) → Goldilocks)
    (count : leftCount = rightCount) (rows : leftRows = rightRows) (padding : leftPadding = rightPadding)
    (tables : ∀ leftIndex rightIndex, leftIndex.val = rightIndex.val → HEq (left leftIndex) (right rightIndex)) : HEq left right := by
  subst rightCount
  subst rightRows
  subst rightPadding
  apply heq_of_eq
  funext index
  exact eq_of_heq (tables index index rfl)

end FormalProof4FHE.HasteBoots.PackedFamilyReindex
