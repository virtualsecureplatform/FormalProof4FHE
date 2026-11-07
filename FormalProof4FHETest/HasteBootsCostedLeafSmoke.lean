module
import all FormalProof4FHE.HasteBoots.FixedByteReadCost
import all FormalProof4FHE.HasteBoots.CostedMerkleNode
import all FormalProof4FHE.HasteBoots.BytePrefixMatchCost
import all FormalProof4FHE.HasteBoots.IntegerEncodingCost
import all FormalProof4FHE.HasteBoots.RowEncodingCost
import all FormalProof4FHE.HasteBoots.CostedMerkleLeaf
import all FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
import all FormalProof4FHE.HasteBoots.PreparedMerklePayloads
import all FormalProof4FHE.HasteBoots.BytePrefixCost
import all FormalProof4FHE.HasteBoots.IntegerPrefixCost
import all FormalProof4FHE.HasteBoots.UsizeVectorCost
import all FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
import all FormalProof4FHE.HasteBoots.NativeLookupRequestWire
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.NativeIntegerPrefix
import all FormalProof4FHE.HasteBoots.NativeFieldWire
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all FormalProof4FHE.HasteBoots.NativeByteCodec
import all FormalProof4FHE.HasteBoots.SolverOperationCost
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input)
open NativeGoldColumnAuthentication (leafInput)
private def usize (n : Nat) : NativeUsizeMessage.Usize := ⟨n % 2^64,Nat.mod_lt _ (by decide)⟩
private def emptyRow : NativeLookupRequestWire.Row := ⟨[],by decide⟩
private def row : NativeLookupRequestWire.Row := ⟨[usize 0,usize 251,usize (2^64-1)],by decide⟩
private def domainSize : Nat := NativeFieldWire.columnDomain.length
private def digest : NativeRootMessage.Digest := fun _ => 11

/-- info: true -/
#guard_msgs in
#eval let result := BytePrefixMatchCost.matchPrefix [1,2] [1,2,3,4]
      decide (result.value = some [3,4] ∧ result.cost = 13 ∧
        (BytePrefixMatchCost.equal [1,2] [1,2,3,4]).value = false)

/-- info: true -/
#guard_msgs in
#eval decide ((BytePrefixMatchCost.matchPrefix [1,2] [1]).value = none ∧
      (BytePrefixMatchCost.matchPrefix [1,2] [1]).cost = 7 ∧
      (BytePrefixMatchCost.equal [1,2,3] [1,2,4]).cost = 21 ∧
      (BytePrefixMatchCost.equal [1,2,3] [1,2,3]).cost = 22)

/-- info: [5, 5, 19, 19, 33, 33, 59, 59] -/
#guard_msgs in
#eval [0,250,251,65535,65536,2^32-1,2^32,2^64-1].map (fun value =>
      (IntegerEncodingCost.encode (usize value)).cost)

/-- info: true -/
#guard_msgs in
#eval [0,250,251,65535,65536,2^32-1,2^32,2^64-1].all (fun value =>
      decide ((IntegerEncodingCost.encode (usize value)).value = NativeUsizeMessage.encode (usize value)))

/-- info: true -/
#guard_msgs in
#eval decide ((RowEncodingCost.encode row).value = NativeLookupRequestWire.rowCodec.encode row ∧
      (RowEncodingCost.encode row).cost = 164 ∧
      (CostedMerkleLeaf.encode row).value = leafInput row ∧
      (CostedMerkleLeaf.encode row).cost = 3*domainSize+167)

/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleLeaf.decode (leafInput emptyRow)
      decide (result.value = some emptyRow ∧ result.cost = 15*domainSize+58)

-- Every native raw u64 spelling is retained, including lazy Goldilocks values.
/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleLeaf.decode (leafInput row)
      decide (result.value = some row ∧ result.cost = 15*domainSize+448 ∧
        NativeMerkleRoleDecoders.leaf.decode (leafInput row) = some row)

-- Wider structural integers parse but fail exact canonical re-encoding.
/-- info: true -/
#guard_msgs in
#eval let input := NativeFieldWire.columnDomain++[251,1,0,251,1,0]
      let result := CostedMerkleLeaf.decode input
      decide (result.value = none ∧ result.cost = 15*domainSize+143)

/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleLeaf.decode (leafInput emptyRow++[99])
      decide (result.value = none ∧ result.cost = 6*domainSize+27)

-- A maximum row count with no payload is rejected after the first failed word.
/-- info: true -/
#guard_msgs in
#eval let input := NativeFieldWire.columnDomain++NativeUsizeMessage.encode (usize (2^64-1))
      let result := CostedMerkleLeaf.decode input
      decide (result.value = none ∧ result.cost = 6*domainSize+120)

/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleLeaf.decode []
      decide (result.value = none ∧ result.cost = 6)

-- Stored-log preparation includes both strict decodes. Lookup skips the first
-- malformed candidate while preserving first-valid selection and input order.
/-- info: true -/
#guard_msgs in
#eval let stored := PreparedMerklePayloads.store digest
      let prepared := PreparedMerklePayloads.prepareStoredWithCost [([],stored),(leafInput row,stored)]
      let found := PreparedMerklePayloads.scan prepared.value stored
      decide (prepared.cost = 15*domainSize+463 ∧ found.value = some row ∧ found.cost = 778)

-- Compare the new default role with its complete guarded reference on several
-- malformed cases, including truncated payloads and the wrong role.
/-- info: true -/
#guard_msgs in
#eval [[],[99],leafInput row,leafInput row++[0],(leafInput row).dropLast,
        NativeFieldWire.columnDomain++[254]].all (fun input =>
      decide (NativeMerkleRoleDecoders.leaf.decode input =
        (NativeMerkleRoleDecoders.guarded leafInput NativeMerkleRoleDecoders.parseLeaf
          NativeMerkleRoleDecoders.parseLeaf_encode).decode input))
