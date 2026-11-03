module

public import FormalProof4FHE.HasteBoots.ExtensionLookupTerminal

@[expose] public section

/-!
# Original packed sources as the full scalar lookup table

Scalar addresses are lane+width*row. Splitting the full Boolean point puts
lane coordinates first, with no change to the original table or root. The
native scalar query terminal equals the ordinary MLE of this flattened table,
and tuple compression agrees with the lookup identity's hashed scalar source.
Machine/Rust representation and cryptographic stage composition remain open.
-/

open scoped BigOperators Classical

namespace FormalProof4FHE.HasteBoots.LookupSourceFlattening

noncomputable section

variable {c row d padding : ℕ}

def coordinates : PackedZeroEquality.Cell (c + row) ≃
    PackedZeroEquality.Cell c × PackedZeroEquality.Cell row where
  toFun cell := (fun i => cell (i.castAdd row), fun i => cell (Fin.natAdd c i))
  invFun pair := Fin.addCases pair.1 pair.2
  left_inv cell := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv pair := by
    rcases pair with ⟨low, high⟩
    simp

def split : MatrixFold.Cube (c + row) ≃ MatrixFold.Cube c × MatrixFold.Cube row :=
  (PackedEqualityCube.bits (c + row)).trans
    (coordinates.trans (Equiv.prodCongr (PackedEqualityCube.bits c).symm (PackedEqualityCube.bits row).symm))

theorem low_bits (cell : MatrixFold.Cube (c + row)) (i : Fin c) :
    PackedEqualityCube.bits c (split cell).1 i = PackedEqualityCube.bits (c + row) cell (i.castAdd row) := by
  simp [split, coordinates]

theorem high_bits (cell : MatrixFold.Cube (c + row)) (i : Fin row) :
    PackedEqualityCube.bits row (split cell).2 i = PackedEqualityCube.bits (c + row) cell (Fin.natAdd c i) := by
  simp [split, coordinates]

theorem split_address (cell : MatrixFold.Cube (c + row)) :
    (FlatMatrixFold.index (c + row) cell).val =
      (FlatMatrixFold.index c (split cell).1).val + 2 ^ c * (FlatMatrixFold.index row (split cell).2).val := by
  rw [PackedEqualityCube.index_eq_sum_bits, Fin.sum_univ_add,
    PackedEqualityCube.index_eq_sum_bits, PackedEqualityCube.index_eq_sum_bits]
  simp only [low_bits, high_bits, Fin.val_castAdd, Fin.val_natAdd, pow_add, Finset.mul_sum, mul_assoc]

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem split_weight (point : Fin (c + row) → K) (cell : MatrixFold.Cube (c + row)) :
    PackedEqualityCube.weight point cell =
      PackedEqualityCube.weight (fun i => point (i.castAdd row)) (split cell).1 *
        PackedEqualityCube.weight (fun i => point (Fin.natAdd c i)) (split cell).2 := by
  simp only [PackedEqualityCube.weight, PackedZeroEquality.equality_prod, Fin.prod_univ_add, low_bits, high_bits]

/-- Interpolation over the full cube equals nested low-lane/high-row
interpolation, with every point coordinate and source entry preserved. -/
theorem evaluate_split (point : Fin (c + row) → K) (table : MatrixFold.Cube (c + row) → K) :
    ExtensionQuery.evaluate (c + row) point table =
      ∑ high, PackedEqualityCube.weight (fun i => point (Fin.natAdd c i)) high *
        ∑ low, PackedEqualityCube.weight (fun i => point (i.castAdd row)) low * table (split.symm (low, high)) := by
  rw [ExtensionQuery.evaluate_eq_sum, ← split.symm.sum_comp]
  simp only [split_weight, Equiv.apply_symm_apply, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro high _
  apply Finset.sum_congr rfl
  intro low _
  ring

/-- No new source is committed: this only interprets existing scalar entries. -/
def flatten (shape : d + padding = 2 ^ c)
    (table : MatrixFold.Cube row → Fin (d + padding) → F) : MatrixFold.Cube (c + row) → F :=
  fun cell => table (split cell).2 ((ExtensionQuery.nativeLanes shape).symm (split cell).1)

theorem flatten_address (shape : d + padding = 2 ^ c) (cell : MatrixFold.Cube (c + row)) :
    (FlatMatrixFold.index (c + row) cell).val =
      ((ExtensionQuery.nativeLanes shape).symm (split cell).1).val +
        (d + padding) * (FlatMatrixFold.index row (split cell).2).val := by
  rw [split_address]
  have same : (FlatMatrixFold.index c (split cell).1).val =
      ((ExtensionQuery.nativeLanes shape).symm (split cell).1).val := by
    simpa only [Equiv.apply_symm_apply] using
      ExtensionQuery.nativeLanes_index shape ((ExtensionQuery.nativeLanes shape).symm (split cell).1)
  exact congrArg₂ (fun first width : ℕ => first + width * (FlatMatrixFold.index row (split cell).2).val) same shape.symm

omit [Field F] in
theorem flatten_recover (shape : d + padding = 2 ^ c)
    (table : MatrixFold.Cube row → Fin (d + padding) → F) (cell : MatrixFold.Cube row) (lane : Fin (d + padding)) :
    flatten shape table (split.symm (ExtensionQuery.nativeLanes shape lane, cell)) = table cell lane := by
  simp only [flatten, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

omit [Field F] in
theorem flatten_injective (shape : d + padding = 2 ^ c) :
    Function.Injective (flatten (F := F) (row := row) shape) := by
  intro first second equal
  funext cell lane
  have entry := congrFun equal (split.symm (ExtensionQuery.nativeLanes shape lane, cell))
  simpa only [flatten_recover] using entry

/-- The terminal's packed-source interpretation is the exact full scalar MLE. -/
theorem sourceTruth_eq_evaluate (shape : d + padding = 2 ^ c) (point : Fin (c + row) → K)
    (table : MatrixFold.Cube row → Fin (d + padding) → F) :
    ExtensionLookupTerminal.sourceTruth shape point table =
      ExtensionQuery.evaluate (c + row) point (fun cell => algebraMap F K (flatten shape table cell)) := by
  rw [ExtensionLookupTerminal.source_tensor, evaluate_split]
  apply Finset.sum_congr rfl
  intro high _
  congr 1
  rw [← (ExtensionQuery.nativeLanes shape).sum_comp]
  simp only [flatten, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The actual base-field scalar source query evaluates this same full table. -/
theorem source_query_evaluate (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (point : Fin (c + row) → K) (table : MatrixFold.Cube row → Fin (d + padding) → F) :
    (ExtensionLookupTerminal.sourceQuery basis shape point).evaluate table =
      PaddedExtension.encode basis
        (ExtensionQuery.evaluate (c + row) point (fun cell => algebraMap F K (flatten shape table cell))) := by
  rw [ExtensionLookupTerminal.source_evaluate, sourceTruth_eq_evaluate]

/-- Native tuple compression and the identity polynomial use exactly the same
original flattened sources, with no extra source-count soundness factor. -/
theorem hash_evaluate {count : ℕ} (shape : d + padding = 2 ^ c) (point : Fin (c + row) → K) (y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F) :
    (∑ i, y ^ i.val * ExtensionLookupTerminal.sourceTruth shape point (sources i)) =
      ExtensionQuery.evaluate (c + row) point
        (ExtensionLookupIdentity.hashTable y (fun i => flatten shape (sources i))) := by
  rw [ExtensionLookupIdentity.evaluate_hash]
  exact Finset.sum_congr rfl (fun _ _ => congrArg (_ * ·) (sourceTruth_eq_evaluate shape point _))

/-- Rewrite the truthful terminal branch directly as the partial-table
identity grammar over the original flattened scalar sources. -/
theorem terminal_eq_identity {count : ℕ} (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint point : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F) :
    ExtensionLookupIdentity.terminal eqPoint point r
      (∑ i, y ^ i.val * ExtensionLookupTerminal.sourceTruth shape point (sources i))
      (ExtensionQuery.evaluate (c + row) point (fun cell => PaddedExtension.decode basis (helpers cell))) active enough =
    PackedSumcheckRound.expression ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
      (fun factor => ExtensionQuery.evaluate (c + row) point
        (ExtensionLookupIdentity.factors eqPoint y (fun i => flatten shape (sources i))
          (fun cell => PaddedExtension.decode basis (helpers cell)) active factor)) := by
  rw [ExtensionLookupIdentity.partial_terminal, ← hash_evaluate]

/-- Full-table degree-three identity, including the native affine g+r factor. -/
theorem terminal_eq_full_identity {count : ℕ} (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint point : Fin (c + row) → K) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F) :
    ExtensionLookupIdentity.terminal eqPoint point r
      (∑ i, y ^ i.val * ExtensionLookupTerminal.sourceTruth shape point (sources i))
      (ExtensionQuery.evaluate (c + row) point (fun cell => PaddedExtension.decode basis (helpers cell))) (2 ^ (c + row)) le_rfl =
    PackedSumcheckRound.expression ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun factor => ExtensionQuery.evaluate (c + row) point (fun cell =>
        if factor = .hash then ExtensionLookupIdentity.hashTable y (fun i => flatten shape (sources i)) cell + r else
          ExtensionLookupIdentity.factors eqPoint y (fun i => flatten shape (sources i))
            (fun cell => PaddedExtension.decode basis (helpers cell)) (2 ^ (c + row)) factor cell)) := by
  rw [ExtensionLookupIdentity.full_terminal, ← hash_evaluate]

end

end FormalProof4FHE.HasteBoots.LookupSourceFlattening
