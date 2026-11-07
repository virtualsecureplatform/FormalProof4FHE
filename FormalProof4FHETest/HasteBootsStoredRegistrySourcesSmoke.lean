module
import all FormalProof4FHE.HasteBoots.StoredSourceVectorReadCost
import all FormalProof4FHE.HasteBoots.StoredSourceVectorCost
import all FormalProof4FHE.HasteBoots.StoredRegistrySourcesCost
import all FormalProof4FHE.HasteBoots.NativeCanonicalLookupWire
import all FormalProof4FHE.HasteBoots.StoredDigestVectorReadCost
import all FormalProof4FHE.HasteBoots.StoredDigestVectorCost
import all FormalProof4FHE.HasteBoots.StoredHelperRootsCost
import all FormalProof4FHE.HasteBoots.NativeRootMessage
import all FormalProof4FHE.HasteBoots.NativeLookupEquality
import all FormalProof4FHE.HasteBoots.ParentSeedRequestCost
import all FormalProof4FHE.HasteBoots.ParentInputHistoryCost
import all FormalProof4FHE.HasteBoots.HistoryParentCandidatesCost
import all FormalProof4FHE.HasteBoots.NativeParentLedgerPools
import all FormalProof4FHE.HasteBoots.SizedFrameCost
import all FormalProof4FHE.HasteBoots.TranscriptFrameCost
import all FormalProof4FHE.HasteBoots.TranscriptFrameStreamCost
import all FormalProof4FHE.HasteBoots.StoredChildSeedQuote
import all FormalProof4FHE.HasteBoots.PublicSourceByteInputs
import all FormalProof4FHE.HasteBoots.NativeParentLedger
import all FormalProof4FHE.HasteBoots.StoredShakeByteCache
import all FormalProof4FHE.HasteBoots.StoredParentSeedCheck
import all FormalProof4FHE.HasteBoots.StoredShakeHistory
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
import all FormalProof4FHE.HasteBoots.PreparedMerkleNodes
import all FormalProof4FHE.HasteBoots.StoredDigestView
import all FormalProof4FHE.HasteBoots.CostedMerkleTree
import all VCVio.CryptoFoundations.MerkleTree.Extractor
import all ToMathlib.Data.IndexedBinaryTree.Perfect
import all ToMathlib.Data.IndexedBinaryTree.Basic
import all FormalProof4FHE.HasteBoots.MerkleLeafIndexCost
import all FormalProof4FHE.HasteBoots.CostedMerkleLeafAccess
import all FormalProof4FHE.HasteBoots.CostedMerkleWord
import all FormalProof4FHE.HasteBoots.NativeGoldRawAvailability





open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Byte)
private def sources (pairs : List (Nat × Nat)) : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨(pairs.take 16).map (fun pair =>
    ((fun _ => Fin.ofNat 256 pair.1),(fun _ => Fin.ofNat 256 pair.2))),by
      have bound := List.length_take_le 16 pairs
      simp only [List.length_map]
      omega⟩
private def bytes (pairs : List (Nat × Nat)) := NativeCanonicalLookupWire.sourcesCodec.encode (sources pairs)
private def values (pairs : StoredSourceVectorReadCost.Sources) : List (Nat × Nat) :=
  pairs.val.map (fun pair => ((pair.1.get 0).val,(pair.2.get 0).val))
private def registry (message : List Byte) : TranscriptFrame.Frame := ⟨1,StoredRegistrySourcesCost.label,message⟩
private def frames : List TranscriptFrame.Frame :=
  [registry (bytes [(1,9),(2,9)]),⟨0,[],[]⟩,registry (bytes [(1,9)])]

-- Huge declared counts stop on a truncated context OR root, without a trial cap.
/-- info: true -/
#guard_msgs in
#eval let count := 2^64-1
  [[],List.replicate 63 (7 : Byte),List.replicate 64 7,List.replicate 127 7,List.replicate 128 7].all
    (fun input => let result := StoredSourceVectorReadCost.readCount count input
      decide (result.value.isNone ∧ result.cost ≤ 916*(min count (input.length/128)+1)))

-- Prefix decoding preserves the arbitrary suffix and ordered context/root pairs.
/-- info: true -/
#guard_msgs in
#eval let result := StoredSourceVectorReadCost.read (bytes [(1,9),(2,9),(1,9)] ++ [42])
  decide (result.value.map (fun pair => (values pair.1,pair.2)) = some ([(1,9),(2,9),(1,9)],[42]))

-- Shared root bytes do not merge distinct contexts or original duplicate entries.
/-- info: true -/
#guard_msgs in
#eval let input := bytes [(1,9),(2,9),(1,9)]
  let result := StoredSourceVectorCost.decode input
  decide (result.value.map values = some [(1,9),(2,9),(1,9)] ∧
    result.cost ≤ 1764*(input.length/128+1)+6*input.length+1)

-- Every byte in both fields retains its exact spelling and role.
/-- info: true -/
#guard_msgs in
#eval let context := (List.range 64).map (fun i => Fin.ofNat 256 i)
  let root := (List.range 64).map (fun i => Fin.ofNat 256 (i+64))
  let result := StoredSourceVectorCost.decode (1::context ++ root)
  decide (result.value.map (fun pairs => pairs.val.map (fun pair => (pair.1.toList,pair.2.toList))) = some [(context,root)])

-- Structural count reading remains permissive; complete canonical decoding rejects aliases.
/-- info: true -/
#guard_msgs in
#eval let input := [251,1,0] ++ List.replicate 128 (9 : Byte)
  decide ((StoredSourceVectorReadCost.read input).value.isSome ∧
    (StoredSourceVectorCost.decode input).value.isNone ∧
    (StoredSourceVectorCost.decode ([251,0,0] : List Byte)).value.isNone)

-- Truncated pairs, trailing bytes, invalid count tags and huge counts fail closed.
/-- info: true -/
#guard_msgs in
#eval [((bytes [(1,9)]).take 128),bytes [(1,9)] ++ [0],([254] : List Byte),253::List.replicate 8 255].all
  (fun input => (StoredSourceVectorCost.decode input).value.isNone)

-- A valid context followed by a missing root retains the spent first-read cost.
/-- info: true -/
#guard_msgs in
#eval let result := StoredSourceVectorReadCost.readSource (List.replicate 64 7)
  decide (result.value.isNone ∧ result.cost = 460 ∧
    (StoredSourceVectorCost.decode [0]).value.map values = some [] ∧
    (StoredSourceVectorCost.decode []).value.isNone)

-- Registry parsing checks the exact kind/label and leaves other source formats separate.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredRegistrySourcesCost.frameSources (registry (bytes [(1,9)]))).value.map values = some [(1,9)] ∧
  (StoredRegistrySourcesCost.frameSources ⟨0,StoredRegistrySourcesCost.label,bytes [(1,9)]⟩).value.isNone ∧
  (StoredRegistrySourcesCost.frameSources ⟨1,NativeCanonicalLookupWire.label,bytes [(1,9)]⟩).value.isNone)

-- Collect every registry occurrence in order, retaining aliases and duplicates.
/-- info: true -/
#guard_msgs in
#eval let input := TranscriptFrame.encodeMany frames
  let result := StoredRegistrySourcesCost.fromInput input
  decide (result.value.map (fun pair => ((pair.1.get 0).val,(pair.2.get 0).val)) = [(1,9),(2,9),(1,9)] ∧
    result.cost ≤ (3624+6*StoredRegistrySourcesCost.label.length)*input.length+5)

-- Invalid registry payloads contribute no pairs; malformed outer framing rejects all.
/-- info: true -/
#guard_msgs in
#eval let bad := registry ([251,1,0] ++ List.replicate 128 9)
  let input := TranscriptFrame.encodeMany [registry (bytes [(1,9)]),bad,registry (bytes [(2,9)])]
  decide ((StoredRegistrySourcesCost.fromInput input).value.map
      (fun pair => ((pair.1.get 0).val,(pair.2.get 0).val)) = [(1,9),(2,9)] ∧
    (StoredRegistrySourcesCost.fromInput (input ++ [255])).value = [])

/-- info: [50, 2582, 7646, 119, 11012] -/
#guard_msgs in
#eval [(StoredSourceVectorCost.decode [0]).cost,(StoredSourceVectorCost.decode (bytes [(1,9)])).cost,
  (StoredSourceVectorCost.decode (bytes [(1,9),(2,9),(1,9)])).cost,
  (StoredSourceVectorCost.decode (253::List.replicate 8 255)).cost,
  (StoredRegistrySourcesCost.fromInput (TranscriptFrame.encodeMany frames)).cost]
