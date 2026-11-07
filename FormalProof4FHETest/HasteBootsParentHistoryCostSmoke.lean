module
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
private def request : TranscriptFrame.Frame := ⟨2,ParentSeedRequestCost.label,ParentSeedRequestCost.message⟩
private def fork (id : Byte) : TranscriptFrame.Frame := ⟨6,[id],[id]⟩
private def parent (id : Byte) : List Byte := TranscriptFrame.encodeMany [fork id,request]
private def emptyFrame : TranscriptFrame.Frame := ⟨0,[],[]⟩
private def child : List Byte := TranscriptFrame.encodeMany
  (List.replicate 5 emptyFrame ++ [⟨1,StoredChildSeedQuote.seedLabel,List.replicate 64 7⟩])
private def history : List NativeTranscript.Observation :=
  [.start (parent 1),.hash (parent 1) (List.replicate 64 0),.output (parent 2) 0 [8],
   .output (parent 1) 0 [7],.start (parent 3),.start [255],.output (parent 4) 0 []]

-- Every original terminal request field is required, including exact u64 length 64.
/-- info: true -/
#guard_msgs in
#eval let valid := ParentSeedRequestCost.parse (parent 1)
  let bad : List TranscriptFrame.Frame :=
    [⟨1,ParentSeedRequestCost.label,ParentSeedRequestCost.message⟩,
     ⟨2,[],ParentSeedRequestCost.message⟩,
     ⟨2,ParentSeedRequestCost.label,TranscriptFrame.littleEndian 8 63⟩,
     ⟨2,ParentSeedRequestCost.label,ParentSeedRequestCost.message ++ [0]⟩]
  valid.value.isSome && bad.all (fun req =>
    (ParentSeedRequestCost.parse (TranscriptFrame.encodeMany [fork 1,req])).value.isNone)

-- The terminal pair decides; earlier matching pairs cannot override a later frame.
/-- info: true -/
#guard_msgs in
#eval decide ((ParentSeedRequestCost.parse (TranscriptFrame.encodeMany [request])).value.isNone ∧
  (ParentSeedRequestCost.parse (TranscriptFrame.encodeMany [⟨5,[],[]⟩,request])).value.isNone ∧
  (ParentSeedRequestCost.parse (parent 1 ++ TranscriptFrame.encode emptyFrame)).value.isNone ∧
  (ParentSeedRequestCost.parse (parent 1 ++ [255])).value.isNone)

-- Reverse traversal and terminal checks preserve full frame spellings and order.
/-- info: true -/
#guard_msgs in
#eval let frames := [emptyFrame,emptyFrame,fork 1,request]
  decide ((ParentSeedRequestCost.parse (TranscriptFrame.encodeMany frames)).value = some frames ∧
    (ParentSeedRequestCost.reverseAux frames [emptyFrame]).value = frames.reverse ++ [emptyFrame] ∧
    (ParentSeedRequestCost.reverseAux frames []).cost = 13)

-- Discover starts, hashes and outputs, including zero-byte output and duplicates.
/-- info: true -/
#guard_msgs in
#eval let result := ParentInputHistoryCost.replay history
  decide (result.value = [parent 4,parent 3,parent 1,parent 2,parent 1,parent 1] ∧
    result.value.length ≤ history.length ∧
    ParentInputHistoryCost.storedBytes result.value ≤ ParentInputHistoryCost.inputBytes history ∧
    result.cost ≤ 27*ParentInputHistoryCost.inputBytes history+
      ParentInputHistoryCost.perObservation*history.length+1)

-- Partial observed SHAKE bytes remove only the exposed conflicting parent.
-- Unknown parents and all duplicate compatible parent observations survive.
/-- info: true -/
#guard_msgs in
#eval let result := HistoryParentCandidatesCost.run history child
  decide (result.value = [parent 4,parent 3,parent 1,parent 1,parent 1])

-- A hash output is separate from observed SHAKE coordinates and adds a duplicate parent.
/-- info: true -/
#guard_msgs in
#eval decide ((HistoryParentCandidatesCost.run
  [.start (parent 1),.hash (parent 1) (List.replicate 64 0)] child).value = [parent 1,parent 1])

-- An unrecognized child yields no candidates but retains all replay/parse work.
/-- info: true -/
#guard_msgs in
#eval let result := HistoryParentCandidatesCost.run history [255]
  let parents := ParentInputHistoryCost.replay history
  let cache := StoredShakeHistory.replay history
  let quote := StoredChildSeedQuote.quote [255]
  decide (result.value = [] ∧ result.cost = parents.cost+cache.cost+quote.cost+5)

-- The complete raw-history path includes every discovery and comparison cost.
/-- info: true -/
#guard_msgs in
#eval let result := HistoryParentCandidatesCost.run history child
  let inputs := ParentInputHistoryCost.inputBytes history
  let bytes := StoredShakeHistory.bytes history
  decide (result.cost ≤ 27*inputs+8*bytes+(ParentInputHistoryCost.perObservation+459)*history.length+
    24*child.length+6*StoredChildSeedQuote.seedLabel.length+497+64*(6*inputs+14*history.length)*bytes)

-- Empty histories are valid and return no parents, with all parser work retained.
/-- info: true -/
#guard_msgs in
#eval decide ((ParentInputHistoryCost.replay []).cost = 1 ∧
  (HistoryParentCandidatesCost.run [] child).value = [])

/-- info: [724, 4388, 115074] -/
#guard_msgs in
#eval [(ParentSeedRequestCost.parse (parent 1)).cost,
  (ParentInputHistoryCost.replay history).cost,(HistoryParentCandidatesCost.run history child).cost]
