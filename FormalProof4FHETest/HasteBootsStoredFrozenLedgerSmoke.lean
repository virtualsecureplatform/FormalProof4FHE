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

import all FormalProof4FHE.HasteBoots.ClosedByteMachineRootBudget
import all FormalProof4FHE.HasteBoots.StoredMetadataCost
import all FormalProof4FHE.HasteBoots.StoredParentContributionsCost
import all FormalProof4FHE.HasteBoots.StoredParentResolutionCost
import all FormalProof4FHE.HasteBoots.StoredBindingHelpersCost
import all FormalProof4FHE.HasteBoots.StoredParentContextsCost
import all FormalProof4FHE.HasteBoots.StoredParentMetadataHistory
import all FormalProof4FHE.HasteBoots.StoredParentMetadataBudget
import all FormalProof4FHE.HasteBoots.StoredHistorySourceResolutionCost

import all FormalProof4FHE.HasteBoots.StoredFrozenRequestsCost
import all FormalProof4FHE.HasteBoots.StoredFrozenLedgerHistory
import all FormalProof4FHE.HasteBoots.StoredFrozenLedgerBudget

open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte)
private def root (value : Nat) : StoredMetadataCost.Root := Vector.replicate 64 (Fin.ofNat 256 value)
private def pair (context rootId : Nat) : StoredSourceVectorReadCost.Source := (root context,root rootId)
private def pairData (sources : List StoredSourceVectorReadCost.Source) :=
  sources.map (fun source => ((source.1.get 0).val,(source.2.get 0).val))
private def rootData (roots : List StoredMetadataCost.Root) := roots.map (fun root => (root.get 0).val)
private def word (value : Nat) : NativeUsizeMessage.Usize := ⟨value % 2^64,Nat.mod_lt _ (by decide)⟩
private def sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨[((fun _ => 1),(fun _ => 9)),((fun _ => 2),(fun _ => 9)),((fun _ => 1),(fun _ => 9))],by decide⟩
private def registry : TranscriptFrame.Frame :=
  ⟨1,StoredRegistrySourcesCost.label,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩
private def binding : NativeCanonicalLookupWire.Binding :=
  ⟨⟨word 4,⟨[],by decide⟩,word 2⟩,(fun _ => 7),sources⟩
private def boundFrame : TranscriptFrame.Frame :=
  ⟨1,StoredBindingFramesCost.label,NativeCanonicalLookupWire.payload binding⟩
private def emptyFrame : TranscriptFrame.Frame := ⟨0,[],[]⟩
private def seed (value : Byte) : TranscriptFrame.Frame := ⟨1,StoredChildSeedQuote.seedLabel,List.replicate 64 value⟩
private def roots (value : Byte) : TranscriptFrame.Frame :=
  ⟨1,StoredHelperRootsCost.label,(NativePrefixCodec.vector NativeByteCodec.digest).encode ⟨[(fun _ => value)],by simp only [List.length_singleton]; decide⟩⟩
private def request : TranscriptFrame.Frame := ⟨2,ParentSeedRequestCost.label,ParentSeedRequestCost.message⟩
private def fork (id : Byte) : TranscriptFrame.Frame := ⟨6,[id],[]⟩
private def parentA : Input := TranscriptFrame.encodeMany
  [registry,boundFrame,roots 11,emptyFrame,emptyFrame,seed 7,fork 1,request]
private def parentB : Input := TranscriptFrame.encodeMany
  [roots 13,emptyFrame,emptyFrame,emptyFrame,emptyFrame,seed 7,fork 2,request]
private def child (value : Byte) : Input := TranscriptFrame.encodeMany
  [roots 17,emptyFrame,emptyFrame,emptyFrame,emptyFrame,seed value]
private def before : List NativeTranscript.Observation := [.start parentA,.output parentA 0 [8]]
private def history : List NativeTranscript.Observation :=
  before ++ [.hash parentB (List.replicate 64 6),.output parentB 0 [],.start [255]]
private def metadata (parent : StoredParentContributionsCost.Parent) :=
  (pairData parent.sources,rootData parent.helpers)


-- Context/root pairs remain distinct even when roots coincide; request order is native.
/-- info: true -/
#guard_msgs in
#eval let input := TranscriptFrame.encodeMany [registry]
  let result := StoredFrozenRequestsCost.prepare [] [] [pair 1 9] input
  decide (pairData result.value.requests = [(2,9)] ∧ pairData result.value.frozen = [(1,9),(2,9)])

-- Hashes, starts and empty outputs discover metadata but never freeze requests.
/-- info: true -/
#guard_msgs in
#eval [NativeTranscript.Observation.start parentA,.hash parentA (List.replicate 64 1),.output parentA 0 []].all
  (fun entry => let result := StoredFrozenLedgerHistory.record StoredFrozenLedgerHistory.initial entry
    decide (result.value.requests = [] ∧ result.value.next.frozen = [] ∧ result.value.next.metadata.parents.length = 1))

-- A nonempty output freezes before installing its new conflicting cache byte.
/-- info: true -/
#guard_msgs in
#eval let state := (StoredFrozenLedgerHistory.reconstruct [.start parentA]).value
  let result := StoredFrozenLedgerHistory.record state (.output parentA 0 [8])
  decide (pairData result.value.requests = [(2,9),(1,9),(7,11)] ∧
    pairData result.value.next.frozen = [(2,9),(1,9),(7,11)] ∧
    (StoredShakeByteCache.lookup result.value.next.metadata.cache parentA 0).value = some 8)

-- Fresh frozen keys are not repeated by subsequent outputs, including corrections.
/-- info: true -/
#guard_msgs in
#eval let state := (StoredFrozenLedgerHistory.reconstruct before).value
  let first := StoredFrozenLedgerHistory.record state (.output parentA 0 [7])
  let second := StoredFrozenLedgerHistory.record first.value.next (.output parentA 0 [7])
  decide (first.value.requests = [] ∧ second.value.requests = [] ∧
    pairData second.value.next.frozen = [(2,9),(1,9),(7,11)])

-- Earlier unused complete aliases freeze too; later claims cannot refreeze their keys.
/-- info: true -/
#guard_msgs in
#eval let input := TranscriptFrame.encodeMany [registry]
  let state := (StoredFrozenLedgerHistory.reconstruct [.output input 0 [8]]).value
  let later := StoredFrozenLedgerHistory.record state (.output parentA 0 [7])
  decide (pairData state.frozen = [(2,9),(1,9)] ∧ later.value.requests = [])

-- Whole causal ledger replay retains old frozen sources through later incompatibility.
/-- info: true -/
#guard_msgs in
#eval let result := StoredFrozenLedgerHistory.reconstruct history
  decide (pairData result.value.frozen = [(2,9),(1,9),(7,11)] ∧
    result.value.metadata.parents.length = 4 ∧
    result.cost ≤ StoredFrozenLedgerBudget.stepBound (ClosedByteMachineRootBudget.inputWork history)
      history.length (StoredShakeHistory.bytes history)*history.length+1 ∧
    result.value.frozen.length ≤ 4*(ClosedByteMachineRootBudget.inputWork history)^2)

-- A malformed stream supplies no source while observation/cache work is retained.
/-- info: true -/
#guard_msgs in
#eval let result := StoredFrozenLedgerHistory.reconstruct [.output [255] 12 [4,5]]
  decide (result.value.frozen = [] ∧ result.value.metadata.parents.length = 0 ∧
    result.value.metadata.cache.length = 2 ∧
    (StoredShakeByteCache.lookup result.value.metadata.cache [255] 13).value = some 5)

/-- info: true -/
#guard_msgs in
#eval decide ((StoredFrozenLedgerHistory.reconstruct []).cost = 1 ∧
  (StoredFrozenLedgerHistory.reconstruct []).value.frozen = [])
