module
public import FormalProof4FHE.HasteBoots.QueryHighZeroPadding
public import FormalProof4FHE.HasteBoots.QueryReindex
@[expose] public section

/-! Every native high-zero logical view reads the same low physical address.
This removes padding and tensor-split presentation from source interpretation;
it does not assert equality of independently chosen decoders. -/
namespace FormalProof4FHE.HasteBoots.PaddedSourceAddress
noncomputable section
variable {F : Type} [Field F] {b front suffix n m : ℕ}

/-- Canonical native-address view of one decoded physical matrix. -/
def logical (n : ℕ) (table : Fin (2^front) → Fin (2^suffix) → Fin b → F) :
    MatrixFold.Cube n → Fin b → F :=
  fun cell => SubclaimSourceLayout.lookup table (FlatMatrixFold.index n cell).val

/-- Dimension equality transports the type, without permuting native bits. -/
theorem index_transport (equal : n = m) (cell : MatrixFold.Cube n) :
    (FlatMatrixFold.index m (equal ▸ cell)).val = (FlatMatrixFold.index n cell).val := by
  cases equal
  rfl

/-- High-zero padding selects the canonical low-address logical source. -/
theorem padded_source (padding : ℕ) (dimensions : padding+n = front+suffix)
    (table : Fin (2^front) → Fin (2^suffix) → Fin b → F) :
    QueryHighZeroPadding.source padding
      (QueryReindex.source dimensions (SubclaimSourceLayout.source table)) = logical n table := by
  funext cell lane
  change SubclaimSourceLayout.lookup table
    (FlatMatrixFold.index (front+suffix) (dimensions ▸ NTTSourceQuery.join n padding cell (QueryHighZeroPadding.zeroCell padding))).val lane = _
  rw [index_transport,QueryHighZeroPadding.source_address]
  rfl

/-- Reindexing a logical dimension preserves all source values. -/
theorem logical_reindex (equal : n = m)
    (table : Fin (2^front) → Fin (2^suffix) → Fin b → F) :
    QueryReindex.source equal (logical m table) = logical n table := by
  funext cell lane
  change SubclaimSourceLayout.lookup table (FlatMatrixFold.index m (equal ▸ cell)).val lane = _
  rw [index_transport]
  rfl

/-- Different logical presentations agree whenever their native addresses agree. -/
theorem same_address (table : Fin (2^front) → Fin (2^suffix) → Fin b → F)
    (left : MatrixFold.Cube n) (right : MatrixFold.Cube m)
    (address : (FlatMatrixFold.index n left).val = (FlatMatrixFold.index m right).val) :
    logical n table left = logical m table right := by
  unfold logical
  rw [address]

/-- Distinct padding counts and logical dimensions cannot change a shared
address of one fixed decoded physical source. -/
theorem padded_same_address (leftPadding rightPadding : ℕ)
    (leftDimensions : leftPadding+n = front+suffix) (rightDimensions : rightPadding+m = front+suffix)
    (table : Fin (2^front) → Fin (2^suffix) → Fin b → F)
    (left : MatrixFold.Cube n) (right : MatrixFold.Cube m)
    (address : (FlatMatrixFold.index n left).val = (FlatMatrixFold.index m right).val) :
    QueryHighZeroPadding.source leftPadding
      (QueryReindex.source leftDimensions (SubclaimSourceLayout.source table)) left =
    QueryHighZeroPadding.source rightPadding
      (QueryReindex.source rightDimensions (SubclaimSourceLayout.source table)) right := by
  rw [padded_source,padded_source]
  exact same_address table left right address

variable {Position : Type} [Fintype Position] [DecidableEq F] {degree : ℕ}

/-- The exact decoder used in PCS has the same canonical logical view. -/
theorem padded_decoded_source (padding : ℕ) (dimensions : padding+n = front+suffix)
    (domain : Position ↪ F) (capacity : 2^suffix ≤ degree*b) (radius : ℕ)
    (word : Position → (Fin (2^front) × Fin b) → Fin b → F) :
    QueryHighZeroPadding.source padding
      (QueryReindex.source dimensions (SubclaimSourceLayout.decodedSource domain capacity radius word)) =
    logical n (MatrixOpeningSecurity.extract domain capacity radius word) :=
  padded_source padding dimensions _

end
end FormalProof4FHE.HasteBoots.PaddedSourceAddress
