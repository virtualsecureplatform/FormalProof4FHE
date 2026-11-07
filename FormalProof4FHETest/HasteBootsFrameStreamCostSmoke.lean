module
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
private def frame : TranscriptFrame.Frame := ⟨8,[1,2],[3,4,5]⟩
private def emptyFrame : TranscriptFrame.Frame := ⟨0,[],[]⟩
private def seedFrame (kind : Fin 9) (label : List Byte) (size byte : Nat) : TranscriptFrame.Frame :=
  ⟨kind,label,List.replicate size (Fin.ofNat 256 byte)⟩
private def child (value : TranscriptFrame.Frame) : List Byte :=
  TranscriptFrame.encodeMany (List.replicate 5 emptyFrame ++ [value])
private def quoted : List Byte := child (seedFrame 1 StoredChildSeedQuote.seedLabel 64 9)

-- A forged all-ones u64 width traverses only the bytes actually supplied.
/-- info: true -/
#guard_msgs in
#eval (List.range 40).all (fun size =>
  let result := SizedFrameCost.read (List.replicate size 255)
  decide (result.value.isNone ∧ result.cost ≤ 10*size+10))

-- Every raw kind byte is checked; zero-sized fields remain valid structural frames.
/-- info: true -/
#guard_msgs in
#eval (List.range 256).all (fun kind =>
  let result := TranscriptFrameCost.decode (Fin.ofNat 256 kind::List.replicate 16 0)
  decide (result.value.isSome = decide (kind < 9) ∧ result.cost ≤ 20*17+2))

-- One-frame decoding preserves the exact arbitrary suffix.
/-- info: true -/
#guard_msgs in
#eval let result := TranscriptFrameCost.decode (TranscriptFrame.encode frame ++ [255,0])
  decide (result.value = some (frame,[255,0]))

-- Complete-stream parsing preserves all original frames and order.
/-- info: true -/
#guard_msgs in
#eval let frames := [emptyFrame,frame,emptyFrame]
  let result := TranscriptFrameStreamCost.decodeAll (TranscriptFrame.encodeMany frames)
  decide (result.value = some frames)

-- Every proper nonempty prefix of one frame rejects, as does a trailing bad byte.
/-- info: true -/
#guard_msgs in
#eval let bytes := TranscriptFrame.encode frame
  (List.range bytes.length).all (fun size =>
    let result := TranscriptFrameStreamCost.decodeAll (bytes.take size)
    decide (result.value.isSome = (size == 0) ∧ result.cost ≤ 24*size+1)) &&
  (TranscriptFrameStreamCost.decodeAll (bytes ++ [255])).value.isNone

-- Linear bound includes a long sequence of minimum-sized frames.
/-- info: true -/
#guard_msgs in
#eval let frames := List.replicate 64 emptyFrame
  let bytes := TranscriptFrame.encodeMany frames
  let result := TranscriptFrameStreamCost.decodeAll bytes
  decide (result.value = some frames ∧ result.cost = 12097 ∧ result.cost ≤ 24*bytes.length+1)

-- Only the original fixed slot supplies a seed. Later matching labels cannot replace it.
/-- info: true -/
#guard_msgs in
#eval let later := TranscriptFrame.encode (seedFrame 1 StoredChildSeedQuote.seedLabel 64 7)
  let expected := some (List.replicate 64 (9 : Byte))
  decide ((StoredChildSeedQuote.quote quoted).value.map Vector.toList = expected ∧
    (StoredChildSeedQuote.quote (quoted ++ later)).value.map Vector.toList = expected ∧
    (StoredChildSeedQuote.quote (quoted ++ [255])).value.isNone)

-- Wrong kind/label, short/long seeds and missing slot all reject the quote.
/-- info: true -/
#guard_msgs in
#eval [seedFrame 0 StoredChildSeedQuote.seedLabel 64 9,
       seedFrame 1 [] 64 9,seedFrame 1 StoredChildSeedQuote.seedLabel 63 9,
       seedFrame 1 StoredChildSeedQuote.seedLabel 65 9].all (fun value =>
    (StoredChildSeedQuote.quote (child value)).value.isNone) &&
    (StoredChildSeedQuote.quote (TranscriptFrame.encodeMany (List.replicate 5 emptyFrame))).value.isNone

-- Parsed quotes feed every compatible parent, retaining duplicates and unknowns.
/-- info: true -/
#guard_msgs in
#eval let cache := (StoredShakeByteCache.write
    (StoredShakeByteCache.write [] [1] 0 [9]).value [2] 0 [8]).value
  let state : NativeParentLedger.State :=
    ⟨[⟨[1],[],[]⟩,⟨[2],[],[]⟩,⟨[3],[],[]⟩,⟨[1],[],[]⟩],∅⟩
  let result := StoredChildSeedQuote.active cache state quoted
  decide (result.value.map (fun parent => parent.input) = [[1],[3],[1]] ∧
    result.cost ≤ 24*quoted.length+6*StoredChildSeedQuote.seedLabel.length+491+
      64*(6*StoredParentSeedCheck.parentInputBytes state.parents+14*state.parents.length)*cache.length+
      454*state.parents.length)

-- Whole-input quote decoding and rejection are included in the reported charge.
/-- info: true -/
#guard_msgs in
#eval [quoted,quoted ++ [255],[]].all (fun input =>
  decide ((StoredChildSeedQuote.quote input).cost ≤ 24*input.length+6*StoredChildSeedQuote.seedLabel.length+487))

/-- info: [104, 211, 215, 2057] -/
#guard_msgs in
#eval [(SizedFrameCost.read (TranscriptFrame.sized [1,2,3])).cost,
  (TranscriptFrameCost.decode (TranscriptFrame.encode frame)).cost,
  (TranscriptFrameStreamCost.decodeAll (TranscriptFrame.encode frame)).cost,
  (StoredChildSeedQuote.quote quoted).cost]

-- Complete prior history replay feeds raw child parsing and all-parent filtering.
/-- info: true -/
#guard_msgs in
#eval let history : List NativeTranscript.Observation :=
    [.output [1] 0 [9],.output [2] 0 [8],.start quoted]
  let state : NativeParentLedger.State :=
    ⟨[⟨[1],[],[]⟩,⟨[2],[],[]⟩,⟨[3],[],[]⟩,⟨[1],[],[]⟩],∅⟩
  let replay := StoredShakeHistory.replay history
  let selected := StoredChildSeedQuote.active replay.value state quoted
  let result := StoredChildSeedQuote.activeFromHistory history state quoted
  decide (result.value.map (fun parent => parent.input) = [[1],[3],[1]] ∧
    result.cost = replay.cost+selected.cost+1)
