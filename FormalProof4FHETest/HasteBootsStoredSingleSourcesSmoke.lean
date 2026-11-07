module
import all FormalProof4FHE.HasteBoots.VectorWireReadCost
import all FormalProof4FHE.HasteBoots.VectorWireEncodeCost
import all FormalProof4FHE.HasteBoots.GoldQueryWireCost
import all FormalProof4FHE.HasteBoots.StoredSingleOpeningCost
import all FormalProof4FHE.HasteBoots.StoredSingleSourcesCost
import all FormalProof4FHE.HasteBoots.NativeGoldPcsWire
import all FormalProof4FHE.HasteBoots.UsizeVectorSuccessCost
import all FormalProof4FHE.HasteBoots.TableWireCost
import all FormalProof4FHE.HasteBoots.ConfigWireCost
import all FormalProof4FHE.HasteBoots.StoredCanonicalBindingCost
import all FormalProof4FHE.HasteBoots.StoredBindingFramesCost
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
open InputIndexedOracle (Byte Input)
private def word (value : Nat) : NativeUsizeMessage.Usize := ⟨value % 2^64,Nat.mod_lt _ (by decide)⟩
private def row (values : List Nat) : NativeLookupRequestWire.Row :=
  ⟨(values.take 16).map word,by have bound := List.length_take_le 16 values; simp only [List.length_map]; omega⟩
private def zero : NativeGoldPcsWire.Matrix := ⟨word 3,row [1,2]⟩
private def one : NativeGoldPcsWire.Matrix := ⟨word 4,row [3,4,5]⟩
private def query : NativeGoldPcsWire.Query := ⟨[(zero,one),(one,zero)],by decide⟩
private def wire : Input := NativeGoldPcsWire.opening (fun _ => 9) query (row [7,8])
private def matrixData (matrix : NativeGoldPcsWire.Matrix) := (matrix.width.val,matrix.values.val.map Fin.val)
private def queryData (data : NativeGoldPcsWire.Query) := data.val.map (fun pair => (matrixData pair.1,matrixData pair.2))
private def openingData (data : StoredSingleOpeningCost.Stored) :=
  ((data.root.get 0).val,queryData data.query,data.values.val.map Fin.val)
private def contextFrame (id : Nat) : TranscriptFrame.Frame :=
  ⟨1,StoredSingleSourcesCost.contextLabel,List.replicate 64 (Fin.ofNat 256 id)⟩
private def openingFrame (message : Input) : TranscriptFrame.Frame := ⟨1,StoredSingleSourcesCost.openingLabel,message⟩
private def pairData (sources : List StoredSourceVectorReadCost.Source) :=
  sources.map (fun pair => ((pair.1.get 0).val,(pair.2.get 0).val))

-- Huge query/matrix-row counts stop on supplied bytes, without a trial cap.
/-- info: true -/
#guard_msgs in
#eval decide ((GoldQueryWireCost.read (253::List.replicate 8 255)).value.isNone ∧
  (GoldQueryWireCost.readMatrix (0::253::List.replicate 8 255)).value.isNone ∧
  (GoldQueryWireCost.readPair []).value.isNone)

-- Width then values, zero then one, and original query order are retained.
/-- info: true -/
#guard_msgs in
#eval let result := GoldQueryWireCost.read (NativeGoldPcsWire.queryCodec.encode query ++ [42])
  decide (result.value.map (fun pair => queryData pair.1) = some
    [((3,[1,2]),(4,[3,4,5])),((4,[3,4,5]),(3,[1,2]))] ∧
    result.value.map Prod.snd = some ([42] : Input))

-- Empty queries are valid structural vectors; no post-map is serialized.
/-- info: true -/
#guard_msgs in
#eval let empty : NativeGoldPcsWire.Query := ⟨[],by decide⟩
  decide ((GoldQueryWireCost.encode empty).value = [0] ∧
    (GoldQueryWireCost.read [0]).value.map (fun pair => queryData pair.1) = some [])

-- Full single-opening decoding preserves the root, every query and response word.
/-- info: true -/
#guard_msgs in
#eval let result := StoredSingleOpeningCost.decode wire
  decide (result.value.map (fun data => (data.root.get 0).val) = some 9) &&
  decide (result.value.map (fun data => queryData data.query) = some (queryData query)) &&
  decide (result.value.map (fun data => data.values.val.map Fin.val) = some [7,8]) &&
  decide (result.cost ≤ 419*wire.length+1400)


-- Root bytes alone never recognize a complete opening.
/-- info: true -/
#guard_msgs in
#eval [List.replicate 64 (9 : Byte),wire.take (wire.length-1),wire ++ [0],
    List.replicate 64 9 ++ [254]].all (fun input => (StoredSingleOpeningCost.decode input).value.isNone)

-- Structural query/width/response aliases fail whole-message canonicality.
/-- info: true -/
#guard_msgs in
#eval let root : Input := List.replicate 64 9
  [root ++ [251,0,0,0],root ++ [1,251,3,0,0,4,0,0],root ++ [0,251,0,0]].all
    (fun input => (StoredSingleOpeningCost.read input).value.isSome &&
      (StoredSingleOpeningCost.decode input).value.isNone)

-- Prefix reading retains suffixes; stored re-encoding reconstructs the exact native message.
/-- info: true -/
#guard_msgs in
#eval let prefixRead := StoredSingleOpeningCost.read (wire ++ [42])
  decide (prefixRead.value.map Prod.snd = some ([42] : Input)) &&
  match (StoredSingleOpeningCost.decode wire).value with
  | none => false
  | some value => decide ((StoredSingleOpeningCost.encode value).value = wire)

-- Both original frame roles and exact context digest width are required.
/-- info: true -/
#guard_msgs in
#eval let valid := StoredSingleSourcesCost.single (contextFrame 7) (openingFrame wire)
  decide (valid.value.map (fun pair => ((pair.1.get 0).val,(pair.2.get 0).val)) = some (7,9) ∧
    (StoredSingleSourcesCost.single ⟨0,StoredSingleSourcesCost.contextLabel,List.replicate 64 7⟩ (openingFrame wire)).value.isNone ∧
    (StoredSingleSourcesCost.single (contextFrame 7) ⟨1,[],wire⟩).value.isNone ∧
    (StoredSingleSourcesCost.single ⟨1,StoredSingleSourcesCost.contextLabel,List.replicate 65 7⟩ (openingFrame wire)).value.isNone)

-- Repeated roots under different contexts and duplicate pairs survive in order.
/-- info: true -/
#guard_msgs in
#eval let frames := [contextFrame 7,openingFrame wire,contextFrame 8,openingFrame wire,contextFrame 7,openingFrame wire]
  let input := TranscriptFrame.encodeMany frames
  let result := StoredSingleSourcesCost.fromInput input
  decide (pairData result.value = [(7,9),(8,9),(7,9)] ∧
    result.cost ≤ (2346+6*(StoredSingleSourcesCost.contextLabel.length+StoredSingleSourcesCost.openingLabel.length))*input.length+5)

-- Only original adjacency counts: intervening frames do not create a source.
/-- info: true -/
#guard_msgs in
#eval let separated := TranscriptFrame.encodeMany [contextFrame 7,⟨0,[],[]⟩,openingFrame wire]
  let neighboring := TranscriptFrame.encodeMany [contextFrame 7,contextFrame 8,openingFrame wire]
  decide ((StoredSingleSourcesCost.fromInput separated).value = [] ∧
    pairData (StoredSingleSourcesCost.fromInput neighboring).value = [(8,9)])

-- Invalid opening payloads contribute nothing; malformed outer framing rejects all.
/-- info: true -/
#guard_msgs in
#eval let input := TranscriptFrame.encodeMany [contextFrame 7,openingFrame [],contextFrame 8,openingFrame wire]
  decide (pairData (StoredSingleSourcesCost.fromInput input).value = [(8,9)] ∧
    (StoredSingleSourcesCost.fromInput (input ++ [255])).value = [])

/-- info: [321, 2190, 4318] -/
#guard_msgs in
#eval [(GoldQueryWireCost.read (NativeGoldPcsWire.queryCodec.encode query)).cost,
  (StoredSingleOpeningCost.decode wire).cost,
  (StoredSingleSourcesCost.fromInput (TranscriptFrame.encodeMany [contextFrame 7,openingFrame wire])).cost]
