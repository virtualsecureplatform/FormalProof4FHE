module
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
private def roots (values : List Nat) : List NativeRootMessage.Digest :=
  (values.take 16).map (fun value => fun _ => Fin.ofNat 256 value)
private def bytes (values : List Nat) : List Byte :=
  NativeRootMessage.encode (roots values) (by
    have bound := List.length_take_le 16 values
    simp only [roots,List.length_map]
    omega)
private def values (roots : StoredDigestVectorReadCost.Roots) : List Nat :=
  roots.val.map (fun root => (root.get 0).val)
private def helper (message : List Byte) : TranscriptFrame.Frame := ⟨1,StoredHelperRootsCost.label,message⟩
private def frames : List TranscriptFrame.Frame :=
  [helper (bytes [1,2]),⟨0,[],[]⟩,helper (bytes [2]),helper (bytes [1])]

-- Huge declared counts stop at the first truncated supplied digest, without a cap.
/-- info: true -/
#guard_msgs in
#eval let count := 2^64-1
  [[],List.replicate 63 (7 : Byte),List.replicate 64 7].all (fun input =>
    let result := StoredDigestVectorReadCost.readCount count input
    decide (result.value.isNone ∧ result.cost ≤ 457*(min count (input.length/64)+1)))

-- Structural prefix reading preserves the arbitrary suffix and repeated-root order.
/-- info: true -/
#guard_msgs in
#eval let input := bytes [1,2,1] ++ [42]
  let result := StoredDigestVectorReadCost.read input
  decide (result.value.map (fun pair => (values pair.1,pair.2)) = some ([1,2,1],[42]))

-- Strict complete decoding accepts every raw root byte and preserves duplicates.
/-- info: true -/
#guard_msgs in
#eval let input := bytes [255,0,255]
  let result := StoredDigestVectorCost.decode input
  decide (result.value.map values = some [255,0,255] ∧
    result.cost ≤ 787*(input.length/64+1)+6*input.length+1)

-- Permissive structural count prefixes remain distinct from strict canonical decoding.
/-- info: true -/
#guard_msgs in
#eval let input := [251,1,0] ++ List.replicate 64 (9 : Byte)
  decide ((StoredDigestVectorReadCost.read input).value.isSome ∧
    (StoredDigestVectorCost.decode input).value.isNone ∧
    (StoredDigestVectorCost.decode ([251,0,0] : List Byte)).value.isNone)

-- Truncation, trailing bytes, invalid tags and a huge count all fail closed.
/-- info: true -/
#guard_msgs in
#eval [((bytes [9]).take 64),bytes [9] ++ [0],([254] : List Byte),253::List.replicate 8 255].all
  (fun input => (StoredDigestVectorCost.decode input).value.isNone)

-- Empty vectors have their canonical one-byte spelling; empty input rejects.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredDigestVectorCost.decode [0]).value.map values = some [] ∧
  (StoredDigestVectorCost.decode []).value.isNone)

-- Varying bytes within one digest retain their exact original 64-byte spelling.
/-- info: true -/
#guard_msgs in
#eval let payload := (List.range 64).map (fun i => Fin.ofNat 256 i)
  let result := StoredDigestVectorCost.decode (1::payload)
  decide (result.value.map (fun roots => roots.val.map Vector.toList) = some [payload])

-- Only the original helper-root kind and exact label recognize a vector.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredHelperRootsCost.frameRoots (helper (bytes [1,2]))).value.map values = some [1,2] ∧
  (StoredHelperRootsCost.frameRoots ⟨0,StoredHelperRootsCost.label,bytes [1]⟩).value.isNone ∧
  (StoredHelperRootsCost.frameRoots ⟨1,[],bytes [1]⟩).value.isNone)

-- Root collection preserves every frame/root occurrence, including repetitions.
/-- info: true -/
#guard_msgs in
#eval let input := TranscriptFrame.encodeMany frames
  let result := StoredHelperRootsCost.fromInput input
  decide (result.value.map (fun root => (root.get 0).val) = [1,2,2,1] ∧
    result.cost ≤ (1644+6*StoredHelperRootsCost.label.length)*input.length+5)

-- An invalid helper payload contributes no roots; malformed outer framing rejects all.
/-- info: true -/
#guard_msgs in
#eval let bad := helper ([251,1,0] ++ List.replicate 64 9)
  let input := TranscriptFrame.encodeMany [helper (bytes [7]),bad,helper (bytes [8])]
  decide ((StoredHelperRootsCost.fromInput input).value.map (fun root => (root.get 0).val) = [7,8] ∧
    (StoredHelperRootsCost.fromInput (input ++ [255])).value = [])

/-- info: [50, 1221, 3563, 116, 7810] -/
#guard_msgs in
#eval [(StoredDigestVectorCost.decode [0]).cost,(StoredDigestVectorCost.decode (bytes [9])).cost,
  (StoredDigestVectorCost.decode (bytes [1,2,1])).cost,
  (StoredDigestVectorCost.decode (253::List.replicate 8 255)).cost,
  (StoredHelperRootsCost.fromInput (TranscriptFrame.encodeMany frames)).cost]
