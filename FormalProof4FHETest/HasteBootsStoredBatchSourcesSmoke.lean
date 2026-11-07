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







import all FormalProof4FHE.HasteBoots.GoldBatchQueriesCost
import all FormalProof4FHE.HasteBoots.StoredBatchMessageCost
import all FormalProof4FHE.HasteBoots.StoredBatchFramesCost
import all FormalProof4FHE.HasteBoots.StoredSourceMentionsCost
import all FormalProof4FHE.HasteBoots.NativeGoldBatchMessage

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


private def batch : NativeGoldBatchMessage.Data :=
  ⟨(fun _ => 3),(fun _ => 11),⟨[query,⟨[],by decide⟩,query],by decide⟩,
    ⟨[row [18446744069414584322],row [],row [5,6]],by decide⟩⟩
private def batchWire : Input := NativeGoldBatchMessage.codec.encode batch
private def batchFrame (message : Input) : TranscriptFrame.Frame := ⟨1,StoredBatchFramesCost.label,message⟩
private def sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨[((fun _ => 1),(fun _ => 9)),((fun _ => 2),(fun _ => 9)),((fun _ => 1),(fun _ => 9))],by decide⟩
private def registryFrame : TranscriptFrame.Frame :=
  ⟨1,StoredRegistrySourcesCost.label,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩
private def binding : NativeCanonicalLookupWire.Binding :=
  ⟨⟨word 4,⟨[row [1,2],row []],by decide⟩,word 2⟩,(fun _ => 7),sources⟩
private def bindingFrame : TranscriptFrame.Frame :=
  ⟨1,StoredBindingFramesCost.label,NativeCanonicalLookupWire.payload binding⟩

-- Native fixture: nested queries, empty query, ragged values, and a raw lazy word.
/-- info: true -/
#guard_msgs in
#eval let parsed := StoredBatchMessageCost.read (batchWire ++ [42])
  match parsed.value with
  | none => false
  | some (data,rest) =>
    decide ((data.source.1.get 0).val = 3 ∧ (data.source.2.get 0).val = 11 ∧ rest = [42]) &&
    decide (data.queries.val.map queryData = [queryData query,[],queryData query]) &&
    decide (data.values.val.map (fun (row : NativeLookupRequestWire.Row) => row.val.map Fin.val) = [[18446744069414584322],[],[5,6]])

-- Complete canonical acceptance and rejection beyond the root prefix.
/-- info: true -/
#guard_msgs in
#eval (StoredBatchMessageCost.decode batchWire).value.isSome &&
  (StoredBatchMessageCost.decode (batchWire ++ [42])).value.isNone &&
  (StoredBatchMessageCost.decode (batchWire.take 128)).value.isNone &&
  (StoredBatchMessageCost.decode (List.replicate 128 0 ++ [253,0,0,0,0,0,0,0,0,0])).value.isNone

-- Untrusted outer query and response counts stop at supplied bytes.
/-- info: true -/
#guard_msgs in
#eval [List.replicate 128 0 ++ (253::List.replicate 8 255),
    List.replicate 128 0 ++ [0] ++ (253::List.replicate 8 255),
    List.replicate 128 0 ++ [1] ++ (253::List.replicate 8 255)].all (fun input =>
  let result := StoredBatchMessageCost.decode input
  result.value.isNone && decide (result.cost ≤ 557*input.length+2400))

-- Structural decoding retains mismatched query/value counts for later semantic checks.
/-- info: true -/
#guard_msgs in
#eval let data := { batch with values := ⟨[],by decide⟩ }
  let result := StoredBatchMessageCost.decode (NativeGoldBatchMessage.codec.encode data)
  decide (result.value.map (fun stored => (stored.queries.val.length,stored.values.val.length)) = some (3,0))

-- All original formats interleave, with duplicates and unused aliases retained.
/-- info: true -/
#guard_msgs in
#eval let frames := [registryFrame,contextFrame 4,openingFrame wire,batchFrame batchWire,bindingFrame,
    batchFrame (batchWire ++ [42]),contextFrame 5,openingFrame wire,registryFrame]
  let input := TranscriptFrame.encodeMany frames
  let result := StoredSourceMentionsCost.fromInput input
  decide (pairData result.value = [(1,9),(2,9),(1,9),(4,9),(3,11),(1,9),(2,9),(1,9),(5,9),(1,9),(2,9),(1,9)] ∧
    result.cost ≤ (9456+12*StoredSourceMentionsCost.frameLabelBytes+6*StoredSourceMentionsCost.singleLabelBytes)*input.length+5)

-- No single source jumps across an intervening frame; malformed frame streams fail closed.
/-- info: true -/
#guard_msgs in
#eval let frames := [contextFrame 4,batchFrame batchWire,openingFrame wire]
  let input := TranscriptFrame.encodeMany frames
  decide (pairData (StoredSourceMentionsCost.fromInput input).value = [(3,11)] ∧
    (StoredSourceMentionsCost.fromInput (input ++ [255])).value = [])
