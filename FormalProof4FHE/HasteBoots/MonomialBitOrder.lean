module
public import FormalProof4FHE.HasteBoots.PublicMonomialTable
@[expose] public section

/-! Bit-order identities needed by the public monomial evaluator. These are
finite mathematical addresses; machine shifts and usize bounds are separate. -/
namespace FormalProof4FHE.HasteBoots.MonomialBitOrder

def snoc : {n : ℕ} → MatrixFold.Cube n → Bool → MatrixFold.Cube (n+1)
  | 0, _, bit => (bit,())
  | _+1, (head,tail), bit => (head,snoc tail bit)

theorem flat_snoc {n : ℕ} (cell : MatrixFold.Cube n) (bit : Bool) :
    (FlatMatrixFold.index (n+1) (snoc cell bit)).val =
      (FlatMatrixFold.index n cell).val + 2^n*(if bit then 1 else 0) := by
  induction n with
  | zero => cases cell; cases bit <;> rfl
  | succ n ih =>
    rcases cell with ⟨head,tail⟩
    simp only [snoc, FlatMatrixFold.index_succ_val, ih, pow_succ]
    ring

theorem output_snoc {n : ℕ} (cell : MatrixFold.Cube n) (bit : Bool) :
    (NTTButterfly.outputIndex (n+1) (snoc cell bit)).val =
      2*(NTTButterfly.outputIndex n cell).val + (if bit then 1 else 0) := by
  induction n with
  | zero => cases cell; cases bit <;> rfl
  | succ n ih =>
    rcases cell with ⟨head,tail⟩
    simp only [snoc, NTTButterfly.outputIndex_succ_val, ih, pow_succ]
    cases head <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> ring

def reverseCube : {n : ℕ} → MatrixFold.Cube n → MatrixFold.Cube n
  | 0, _ => ()
  | _+1, (head,tail) => snoc (reverseCube tail) head

theorem flat_reverse {n : ℕ} (cell : MatrixFold.Cube n) :
    FlatMatrixFold.index n (reverseCube cell) = NTTButterfly.outputIndex n cell := by
  induction n with
  | zero => exact Subsingleton.elim (α := Fin 1) _ _
  | succ n ih =>
    rcases cell with ⟨head,tail⟩
    apply Fin.ext
    simp only [reverseCube, flat_snoc, ih, NTTButterfly.outputIndex_succ_val]
    cases head <;> simp [Nat.add_comm]

theorem output_reverse {n : ℕ} (cell : MatrixFold.Cube n) :
    NTTButterfly.outputIndex n (reverseCube cell) = FlatMatrixFold.index n cell := by
  induction n with
  | zero => exact Subsingleton.elim (α := Fin 1) _ _
  | succ n ih =>
    rcases cell with ⟨head,tail⟩
    apply Fin.ext
    simp only [reverseCube, output_snoc, ih, FlatMatrixFold.index_succ_val]

theorem reverse_flat {n : ℕ} (cell : MatrixFold.Cube n) :
    NTTButterfly.reverseIndex n (FlatMatrixFold.index n cell) = NTTButterfly.outputIndex n cell := by
  rw [← output_reverse cell, NTTButterfly.reverseIndex_outputIndex, flat_reverse]

def append : {front back : ℕ} → MatrixFold.Cube front → MatrixFold.Cube back → MatrixFold.Cube (back+front)
  | 0, _, _, suffix => suffix
  | _+1, _, (head,tail), suffix => (head,append tail suffix)

theorem flat_append {front back : ℕ} (first : MatrixFold.Cube front) (last : MatrixFold.Cube back) :
    (FlatMatrixFold.index (back+front) (append first last)).val =
      (FlatMatrixFold.index front first).val + 2^front*(FlatMatrixFold.index back last).val := by
  induction front with
  | zero => cases first; simp [append, FlatMatrixFold.index]
  | succ front ih =>
    rcases first with ⟨head,tail⟩
    change (FlatMatrixFold.index ((back+front)+1) (head,append tail last)).val = _
    rw [FlatMatrixFold.index_succ_val, FlatMatrixFold.index_succ_val, ih, pow_succ]
    ring

theorem output_append {front back : ℕ} (first : MatrixFold.Cube front) (last : MatrixFold.Cube back) :
    (NTTButterfly.outputIndex (back+front) (append first last)).val =
      2^back*(NTTButterfly.outputIndex front first).val + (NTTButterfly.outputIndex back last).val := by
  induction front with
  | zero => cases first; simp [append, NTTButterfly.outputIndex]
  | succ front ih =>
    rcases first with ⟨head,tail⟩
    change (NTTButterfly.outputIndex ((back+front)+1) (head,append tail last)).val = _
    rw [NTTButterfly.outputIndex_succ_val, NTTButterfly.outputIndex_succ_val, ih, pow_add]
    cases head <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring

end FormalProof4FHE.HasteBoots.MonomialBitOrder
