module
public import FormalProof4FHE.HasteBoots.NTTSourceQuery
@[expose] public section

/-! Native masked PCS extends logical queries with fixed high-variable (I,0)
pairs. They select the zero-padding slice of the SAME physical source; its
other private padding coordinates are neither exposed nor constrained. -/
namespace FormalProof4FHE.HasteBoots.QueryHighZeroPadding
open scoped BigOperators
open Matrix
noncomputable section
open PackedSumcheckSubclaim
variable {F : Type} [Field F] {b n : ℕ}

def zeroCell : (padding : ℕ) → MatrixFold.Cube padding
  | 0 => ()
  | padding+1 => (false,zeroCell padding)

def query (padding : ℕ) (logical : Query F b n) : Query F b (padding+n) :=
  NTTSourceQuery.append logical (NTTSourceQuery.rowQuery (fun _ : Fin padding => (0 : F)))

def source (padding : ℕ) (physical : MatrixFold.Cube (padding+n) → Fin b → F) : MatrixFold.Cube n → Fin b → F :=
  fun cell => physical (NTTSourceQuery.join n padding cell (zeroCell padding))

/-- The fixed suffix selects the all-zero high-variable slice exactly. -/
theorem zero_query_fold (padding : ℕ) (physical : MatrixFold.Cube padding → Fin b → F) :
    (NTTSourceQuery.rowQuery (fun _ : Fin padding => (0 : F))).fold physical = physical (zeroCell padding) := by
  induction padding with
  | zero => rfl
  | succ padding ih =>
    rw [NTTSourceQuery.rowQuery,Query.fold]
    have selected : MatrixFold.foldFirst
        (fun bit => (if bit then (0 : F) else 1-0) • (1 : Matrix (Fin b) (Fin b) F)) physical =
        (fun cell => physical (false,cell)) := by
      funext cell
      simp [MatrixFold.foldFirst]
    rw [selected]
    exact ih (fun cell => physical (false,cell))

/-- Extending a logical query never introduces a virtual commitment or a new
source: it evaluates the logical slice of the original physical decoder. -/
theorem fold (padding : ℕ) (logical : Query F b n)
    (physical : MatrixFold.Cube (padding+n) → Fin b → F) :
    logical.fold (source padding physical) = (query padding logical).fold physical := by
  rw [query,NTTSourceQuery.append_fold,zero_query_fold]
  rfl

/-- Original low-variable addresses are unchanged by selecting zero high bits. -/
theorem source_address (padding : ℕ) (cell : MatrixFold.Cube n) :
    (FlatMatrixFold.index (padding+n) (NTTSourceQuery.join n padding cell (zeroCell padding))).val =
      (FlatMatrixFold.index n cell).val := by
  have zeroIndex : ∀ padding, (FlatMatrixFold.index padding (zeroCell padding)).val = 0 := by
    intro padding
    induction padding with
    | zero => rfl
    | succ padding ih => simpa [zeroCell,FlatMatrixFold.index_succ_val] using ih
  rw [NTTSourceQuery.join_index,zeroIndex,mul_zero,add_zero]

end
end FormalProof4FHE.HasteBoots.QueryHighZeroPadding
