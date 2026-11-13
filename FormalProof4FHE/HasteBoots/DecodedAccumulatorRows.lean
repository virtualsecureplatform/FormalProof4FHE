module
public import FormalProof4FHE.HasteBoots.PackedAccumulatorTrace
public import FormalProof4FHE.HasteBoots.PackedMonomialRotation
public import FormalProof4FHE.HasteBoots.RecordedPaddedSource
@[expose] public section

/-! Construct coefficient-domain accumulator rows from the full original
source, preserving every padded row, polynomial coefficient and half. -/
namespace FormalProof4FHE.HasteBoots.DecodedAccumulatorRows
noncomputable section
variable {q cells lanes rows : ℕ} [Fact q.Prime]

/-- Decode the actual coefficient source, without choosing a separate trace. -/
def decode (source : AccumulatorMatrixSoundness.Table (ZMod q) (2^lanes) cells rows)
    (position : Fin (2^rows)) (half : Bool) : NativeBlindRotation.Poly q (2^(cells+lanes)) :=
  fun index =>
    let coefficient := (PackedAccumulatorTrace.polynomial cells lanes).symm index
    source (AccumulatorPackedQueries.coordinate coefficient.1 ((FlatMatrixFold.index rows).symm position) half) coefficient.2

/-- Packing the decoded rows returns the complete original table, including
padding. It is not an assumption that the prover supplied a packed trace. -/
theorem pack_decode (source : AccumulatorMatrixSoundness.Table (ZMod q) (2^lanes) cells rows) :
    PackedAccumulatorTrace.pack (RingHom.id (ZMod q)) (decode source) = source := by
  funext position lane
  obtain ⟨⟨cell,row,half⟩,rebuild⟩ := (AccumulatorQuerySplit.coordinates cells rows).symm.surjective position
  rw [AccumulatorQuerySplit.coordinates_inverse] at rebuild
  rw [← rebuild,PackedAccumulatorTrace.pack_coordinate]
  simp only [decode,Equiv.symm_apply_apply,RingHom.id_apply]

/-- Honest packed fixtures decode back to their original row ciphertexts. -/
theorem decode_pack (values : Fin (2^rows) → NativeBlindRotation.Cipher q (2^(cells+lanes))) :
    decode (PackedAccumulatorTrace.pack (RingHom.id (ZMod q)) values) = values := by
  funext position half index
  simp only [decode,PackedAccumulatorTrace.pack_coordinate,Prod.mk.eta,Equiv.apply_symm_apply,RingHom.id_apply]

/-- Regroup dimensions without moving any scalar in the native allocation. -/
def nttView (source : AccumulatorMatrixSoundness.Table (ZMod q) (2^lanes) cells rows) :
    MatrixFold.Cube ((rows+1)+cells) → Fin (2^lanes) → ZMod q :=
  fun cell => source ((FlatMatrixFold.index ((1+rows)+cells)).symm
    (finCongr (congrArg (2^·) (by omega : (rows+1)+cells = (1+rows)+cells))
      (FlatMatrixFold.index ((rows+1)+cells) cell)))

omit [Fact q.Prime] in
/-- The monomial NTT row and the accumulator decode read the same original
coefficient address, with round low and ciphertext half high. -/
theorem polynomial_nttView (source : AccumulatorMatrixSoundness.Table (ZMod q) (2^lanes) cells rows)
    (position : Fin (2^rows)) (half : Bool) :
    PackedMonomialRotation.polynomial (nttView source) position half = decode source position half := by
  funext index
  let coefficient := (PackedNTT.address (Nat.pow_add 2 cells lanes).symm).symm index
  have same : (FlatMatrixFold.index ((1+rows)+cells)).symm
      (finCongr (congrArg (2^·) (by omega : (rows+1)+cells = (1+rows)+cells))
        (FlatMatrixFold.index ((rows+1)+cells)
          (NTTSourceQuery.join cells (rows+1) coefficient.1 (PackedMonomialRotation.rowIndex position half)))) =
      AccumulatorPackedQueries.coordinate coefficient.1 ((FlatMatrixFold.index rows).symm position) half := by
    apply (FlatMatrixFold.index ((1+rows)+cells)).injective
    apply Fin.ext
    simp only [Equiv.apply_symm_apply,finCongr_apply,Fin.val_cast,NTTSourceQuery.join_index,
      PackedMonomialRotation.rowIndex_val,AccumulatorPackedQueries.coordinate_index]
  exact congrArg (fun address => source address coefficient.2) same

/-- The regrouped table is still the same original physical decoder. -/
theorem nttView_logical {Cfg Input Digest : Type} [DecidableEq Digest] {heights : Cfg → ℕ}
    (parameters : RecordedPaddedSource.Parameters (ZMod q) Cfg heights (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) parameters) :
    nttView (RecordedPaddedSource.logical parameters enc dummy ((1+rows)+cells) owner) =
      RecordedPaddedSource.logical parameters enc dummy ((rows+1)+cells) owner := by
  funext cell lane
  apply congrFun (RecordedPaddedSource.logical_same_address parameters enc dummy owner _ cell ?_) lane
  simp only [Equiv.apply_symm_apply,finCongr_apply,Fin.val_cast]

/-- Decode all five original arithmetic tables into one coefficient trace. -/
def tables (sources : AccumulatorMatrixSoundness.Sources (ZMod q) (2^lanes) cells rows) :
    AccumulatorTrace.Tables q (2^(cells+lanes)) (2^rows) where
  input := decode sources.input
  product := decode sources.product
  difference := decode sources.difference
  external := decode sources.external
  output := decode sources.output

end
end FormalProof4FHE.HasteBoots.DecodedAccumulatorRows
