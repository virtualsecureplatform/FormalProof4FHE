module
public import FormalProof4FHE.HasteBoots.KeySwitchExtraction
public import FormalProof4FHE.HasteBoots.NTTCompression
public import FormalProof4FHE.HasteBoots.PackedNTT
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
@[expose] public section

/-! Construct coefficient-domain ciphertexts from complete logical source
views. Packing and unpacking are inverse on every table; no source-value
interpretation certificate is needed to name the decoded increment. -/
namespace FormalProof4FHE.HasteBoots.PackedCipherSource
open NativeBlindRotation (Cipher)
noncomputable section
variable {q c lanes : ℕ} [Fact q.Prime]

/-- Native low coefficient bits followed by the ciphertext-half bit. -/
def point (cell : MatrixFold.Cube c) (half : Bool) : MatrixFold.Cube (c+1) :=
  (Nat.add_comm c 1).symm ▸ MonomialBitOrder.append cell (show MatrixFold.Cube 1 from (half,()))

theorem transport_cancel {n m : ℕ} (equal : n = m) (cell : MatrixFold.Cube m) :
    equal ▸ (equal.symm ▸ cell) = cell := by
  cases equal
  rfl

/-- Every complete source position has one coefficient cell and half. -/
theorem point_surjective (position : MatrixFold.Cube (c+1)) :
    ∃ cell half, point cell half = position := by
  let physical : MatrixFold.Cube (1+c) := Nat.add_comm c 1 ▸ position
  let split := AccumulatorQuerySplit.cubeSplit c 1 physical
  have rebuilt : MonomialBitOrder.append split.1 (show MatrixFold.Cube 1 from (split.2.1,())) = physical := by
    apply (AccumulatorQuerySplit.cubeSplit c 1).injective
    rw [AccumulatorQuerySplit.cubeSplit_append]
    exact Prod.ext rfl (Prod.ext rfl (Subsingleton.elim (α := Unit) _ _))
  refine ⟨split.1,split.2.1,?_⟩
  unfold point
  rw [rebuilt]
  exact transport_cancel (Nat.add_comm c 1).symm position

/-- The existing extraction packing uses the same exact point and polynomial
address as the coefficient-domain source interpretation. -/
theorem pack_point (value : Cipher q (2^(c+lanes))) (cell : MatrixFold.Cube c)
    (half : Bool) (lane : Fin (2^lanes)) :
    KeySwitchExtraction.pack value (point cell half) lane =
      value half (PackedAccumulatorTrace.polynomial c lanes (cell,lane)) := by
  unfold KeySwitchExtraction.pack point QueryReindex.source
  rw [transport_cancel,AccumulatorEndpointSoundness.publicTable_append]
  rfl

/-- Read a coefficient-domain ciphertext directly from its full logical table. -/
def unpack (table : MatrixFold.Cube (c+1) → Fin (2^lanes) → ZMod q) : Cipher q (2^(c+lanes)) :=
  fun half index =>
    let position := (PackedAccumulatorTrace.polynomial c lanes).symm index
    table (point position.1 half) position.2

/-- Unpacking retains every coefficient, lane and half. -/
theorem unpack_pack (value : Cipher q (2^(c+lanes))) :
    unpack (KeySwitchExtraction.pack (c := c) (lanes := lanes) value) = value := by
  funext half index
  simp only [unpack,pack_point,Prod.mk.eta,Equiv.apply_symm_apply]

/-- Every decoded table is exactly the packing of its constructed ciphertext. -/
theorem pack_unpack (table : MatrixFold.Cube (c+1) → Fin (2^lanes) → ZMod q) :
    KeySwitchExtraction.pack (unpack table) = table := by
  funext position lane
  obtain ⟨cell,half,same⟩ := point_surjective position
  rw [←same,pack_point]
  simp only [unpack,Equiv.symm_apply_apply]

/-- Complete source tables and coefficient-domain ciphertexts are equivalent. -/
def equivalence : Cipher q (2^(c+lanes)) ≃ (MatrixFold.Cube (c+1) → Fin (2^lanes) → ZMod q) where
  toFun := KeySwitchExtraction.pack
  invFun := unpack
  left_inv := unpack_pack
  right_inv := pack_unpack
/-- NTT row coordinates and coefficient concatenation have identical bit order. -/
theorem join_append {r : ℕ} (cell : MatrixFold.Cube c) (row : MatrixFold.Cube r) :
    NTTSourceQuery.join c r cell row = MonomialBitOrder.append cell row := by
  induction c with
  | zero => cases cell; rfl
  | succ c ih =>
    rcases cell with ⟨bit,tail⟩
    exact congrArg (Prod.mk bit) (ih tail)

/-- The complete NTT source rows are the two polynomials of the same ciphertext. -/
theorem ntt_rows (value : Cipher q (2^(c+lanes))) (half : Bool)
    (cell : MatrixFold.Cube c) (lane : Fin (2^lanes)) :
    NTTCompression.sourceRows c 1
      (QueryReindex.source (Nat.add_comm c 1).symm (KeySwitchExtraction.pack value)) (half,()) (cell,lane) =
      value half (PackedAccumulatorTrace.polynomial c lanes (cell,lane)) := by
  change KeySwitchExtraction.pack value
    ((Nat.add_comm c 1).symm ▸ NTTSourceQuery.join c 1 cell (half,())) lane = _
  erw [join_append]
  exact pack_point value cell half lane

/-- Construct a ciphertext from the full table in native NTT row dimensions. -/
def ofRows (table : MatrixFold.Cube (1+c) → Fin (2^lanes) → ZMod q) : Cipher q (2^(c+lanes)) :=
  unpack (QueryReindex.source (Nat.add_comm c 1) table)

theorem pack_ofRows (table : MatrixFold.Cube (1+c) → Fin (2^lanes) → ZMod q) :
    KeySwitchExtraction.pack (ofRows table) = QueryReindex.source (Nat.add_comm c 1) table :=
  pack_unpack _

/-- No row-source interpretation premise is required: every native NTT table
has the constructed coefficient-domain value at each polynomial address. -/
theorem rows_ofRows (table : MatrixFold.Cube (1+c) → Fin (2^lanes) → ZMod q)
    (half : Bool) (cell : MatrixFold.Cube c) (lane : Fin (2^lanes)) :
    NTTCompression.sourceRows c 1 table (half,()) (cell,lane) =
      ofRows table half (PackedAccumulatorTrace.polynomial c lanes (cell,lane)) := by
  have same := pack_point (ofRows table) cell half lane
  rw [pack_ofRows] at same
  change table (Nat.add_comm c 1 ▸ ((Nat.add_comm c 1).symm ▸ MonomialBitOrder.append cell (half,()))) lane = _ at same
  rw [transport_cancel] at same
  change table (NTTSourceQuery.join c 1 cell (half,())) lane = _
  erw [join_append]
  exact same

/-- Flattening a native polynomial row yields the constructed ciphertext half. -/
theorem flatten_rows (table : MatrixFold.Cube (1+c) → Fin (2^lanes) → ZMod q) (half : Bool) :
    PackedNTT.flatten (Nat.pow_add 2 c lanes).symm (NTTCompression.sourceRows c 1 table (half,())) =
      ofRows table half := by
  funext index
  change NTTCompression.sourceRows c 1 table (half,()) ((PackedAccumulatorTrace.polynomial c lanes).symm index) = _
  have same := rows_ofRows table half ((PackedAccumulatorTrace.polynomial c lanes).symm index).1
    ((PackedAccumulatorTrace.polynomial c lanes).symm index).2
  simpa only [Prod.mk.eta,Equiv.apply_symm_apply] using same

variable {Cfg Input Digest Index : Type} {heights : Cfg → ℕ} [DecidableEq Digest]

/-- The coefficient-domain value of an anchored root is constructed from its
actual decoded table, not supplied as a semantic interpretation witness. -/
def familyCipher (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (index : Index) :
    Cipher q (2^(c+lanes)) :=
  unpack (RecordedPaddedSourceFamily.logical family enc dummy (c+1) index)

theorem pack_familyCipher (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (index : Index) :
    KeySwitchExtraction.pack (familyCipher (c := c) family enc dummy index) =
      RecordedPaddedSourceFamily.logical family enc dummy (c+1) index :=
  pack_unpack _
/-- The family's NTT-row and extraction presentations construct one ciphertext. -/
theorem ofRows_family (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (index : Index) :
    ofRows (RecordedPaddedSourceFamily.logical family enc dummy (1+c) index) =
      familyCipher (c := c) family enc dummy index := by
  unfold ofRows familyCipher RecordedPaddedSourceFamily.logical RecordedPaddedSource.logical
  rw [PaddedSourceAddress.logical_reindex]

/-- Common owner families supply every complete native NTT polynomial row. -/
theorem family_ntt_rows (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (index : Index)
    (half : Bool) (cell : MatrixFold.Cube c) (lane : Fin (2^lanes)) :
    NTTCompression.sourceRows c 1 (RecordedPaddedSourceFamily.logical family enc dummy (1+c) index) (half,()) (cell,lane) =
      familyCipher (c := c) family enc dummy index half (PackedAccumulatorTrace.polynomial c lanes (cell,lane)) := by
  rw [rows_ofRows,ofRows_family]

end
end FormalProof4FHE.HasteBoots.PackedCipherSource
