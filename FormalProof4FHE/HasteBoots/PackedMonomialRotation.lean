module
public import FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck
public import FormalProof4FHE.HasteBoots.PackedNTTBinding
@[expose] public section

/-! Decode the actual monomial check layout into complete polynomial rows.
The public factor is the fixed native plan, including padded rows and the
original ciphertext-half order. NTT relations and source associations remain
explicit; no accepted proof is identified with a true relation by definition. -/
namespace FormalProof4FHE.HasteBoots.PackedMonomialRotation
noncomputable section
variable {q lanes cells rows rounds : ℕ} [Fact q.Prime]

/-- The native NTT's row index has round bits low and ciphertext half high. -/
def rowIndex (position : Fin (2^rows)) (half : Bool) : MatrixFold.Cube (rows+1) :=
  (FlatMatrixFold.index (rows+1)).symm
    (PackedMonomialLayout.join rows 1 (position,finTwoEquiv.symm half))

theorem rowIndex_val (position : Fin (2^rows)) (half : Bool) :
    (FlatMatrixFold.index (rows+1) (rowIndex position half)).val =
      position.val+2^rows*(if half then 1 else 0) := by
  simp only [rowIndex,Equiv.apply_symm_apply,PackedMonomialLayout.join_val]
  cases half <;> rfl

/-- Change only the grouping of dimensions; every flat scalar address stays
fixed. This identifies the public-product and NTT source allocations. -/
def reindex {A : Type} (source : MatrixFold.Cube ((cells+rows)+1) → A) :
    MatrixFold.Cube ((rows+1)+cells) → A :=
  fun cell => source ((FlatMatrixFold.index ((cells+rows)+1)).symm
    (finCongr (congrArg (2^·) (by omega : (rows+1)+cells = (cells+rows)+1)) (FlatMatrixFold.index ((rows+1)+cells) cell)))

/-- Construct each coefficient-domain polynomial from its full original row. -/
def polynomial (source : MatrixFold.Cube ((rows+1)+cells) → Fin (2^lanes) → ZMod q)
    (position : Fin (2^rows)) (half : Bool) : NativeBlindRotation.Poly q (2^(cells+lanes)) :=
  PackedNTTBinding.row (Nat.pow_add 2 cells lanes).symm source (rowIndex position half)

/-- The fixed public source decodes to the actual materialized monomial row,
with no assumed node-power or public-row binding premise. -/
theorem public_polynomial (psi : ZMod q)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes))))
    (position : Fin (2^rows)) (half : Bool) :
    polynomial (reindex (MonomialPublicZeroCheck.table (rows := rows) psi rotations)) position half =
      PublicMonomialTable.table psi rotations half position := by
  funext index
  let coordinate := (PackedNTT.address (Nat.pow_add 2 cells lanes).symm).symm index
  have address : PublicMonomialEvaluation.flatAddress lanes cells
      (FlatMatrixFold.index cells coordinate.1) coordinate.2 = index := by
    change PackedNTT.address (Nat.pow_add 2 cells lanes).symm coordinate = index
    exact Equiv.apply_symm_apply _ index
  change PackedMonomialLayout.word (rows := rows) psi rotations
    (FlatMatrixFold.index ((cells+rows)+1)
      ((FlatMatrixFold.index ((cells+rows)+1)).symm
        (finCongr _ (FlatMatrixFold.index ((rows+1)+cells)
          (NTTSourceQuery.join cells (rows+1) coordinate.1 (rowIndex position half)))))).val coordinate.2 = _
  simp only [Equiv.apply_symm_apply,finCongr_apply,Fin.val_cast,NTTSourceQuery.join_index,rowIndex_val]
  rw [PackedMonomialLayout.word_coordinate]
  change PublicMonomialTable.table psi rotations half position
    (PublicMonomialEvaluation.flatAddress lanes cells (FlatMatrixFold.index cells coordinate.1) coordinate.2) = _
  rw [address]

/-- Reindexing preserves the entire checked product equation, including
inactive padding; the theorem does not restrict the relation to queried rows. -/
theorem polynomial_product (psi : ZMod q)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes))))
    (sources : Bool → MatrixFold.Cube ((cells+rows)+1) → Fin (2^lanes) → ZMod q)
    (product : ∀ cell lane, sources true cell lane =
      sources false cell lane * MonomialPublicZeroCheck.table psi rotations cell lane)
    (position : Fin (2^rows)) (half : Bool) :
    polynomial (reindex (sources true)) position half =
      polynomial (reindex (sources false)) position half *
        PublicMonomialTable.table psi rotations half position := by
  rw [← public_polynomial psi rotations position half]
  funext index
  exact product _ _

/-- Two original NTT relations and the native public product imply every
active coefficient-domain rotation, at the original round and half indices. -/
theorem rotate_of_relations (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(cells+lanes+1)))
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes))))
    (coefficients : Bool → MatrixFold.Cube ((rows+1)+cells) → Fin (2^lanes) → ZMod q)
    (evaluations : Bool → MatrixFold.Cube ((cells+rows)+1) → Fin (2^lanes) → ZMod q)
    (transforms : ∀ side, PackedNTT.Relation (Nat.pow_add 2 cells lanes).symm psi
      (NTTCompression.sourceRows cells (rows+1) (coefficients side))
      (NTTCompression.sourceRows cells (rows+1) (reindex (evaluations side))))
    (product : ∀ cell lane, evaluations true cell lane =
      evaluations false cell lane * MonomialPublicZeroCheck.table psi rotations cell lane)
    (position : Fin (2^rows)) (active : position.val < rounds) (half : Bool) :
    polynomial (coefficients true) position half =
      NativeBlindRotation.rotate (rotations ⟨position.val,active⟩).val
        (polynomial (coefficients false) position half) := by
  apply BlindRotationMonomial.rotate_of_pointwise (cells+lanes) psi primitive
  have input := PackedNTTBinding.transform_of_relation (Nat.pow_add 2 cells lanes).symm psi primitive
    (coefficients false) (reindex (evaluations false)) (transforms false) (rowIndex position half)
  have output := PackedNTTBinding.transform_of_relation (Nat.pow_add 2 cells lanes).symm psi primitive
    (coefficients true) (reindex (evaluations true)) (transforms true) (rowIndex position half)
  change BlindRotationNTT.transform (cells+lanes) psi (polynomial (coefficients false) position half) = polynomial (reindex (evaluations false)) position half at input
  change BlindRotationNTT.transform (cells+lanes) psi (polynomial (coefficients true) position half) = polynomial (reindex (evaluations true)) position half at output
  rw [output,polynomial_product psi rotations evaluations product position half,
    ← input,PublicMonomialTable.table_active psi primitive rotations half position active]

end
end FormalProof4FHE.HasteBoots.PackedMonomialRotation
