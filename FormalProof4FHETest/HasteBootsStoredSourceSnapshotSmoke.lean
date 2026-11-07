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

import all FormalProof4FHE.HasteBoots.StoredGoldPublicSource
import all FormalProof4FHE.HasteBoots.StoredHashLogCost
import all FormalProof4FHE.HasteBoots.StoredSourceSnapshotHistory
import all FormalProof4FHE.HasteBoots.StoredSourceSnapshotBudget
import all FormalProof4FHE.HasteBoots.StoredSourceSnapshotSelection

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



private def logData (log : StoredGoldPublicSource.Log) := log.map (fun entry =>
  ((entry.1.head?.getD 0).val,(entry.2.val.head?.getD 0).val))
private def snapshotHistory : List NativeTranscript.Observation :=
  [.hash [101] (List.replicate 64 9),.start parentA,.output parentA 0 [8],
   .hash [102] (List.replicate 64 10),.hash [101] (List.replicate 64 9),
   .output parentA 0 [7],.hash [103] (List.replicate 64 11)]
private def registryFor (context : Byte) : Input := TranscriptFrame.encodeMany
  [⟨1,StoredRegistrySourcesCost.label,NativeCanonicalLookupWire.sourcesCodec.encode
    ⟨[((fun _ => context),(fun _ => 9))],by simp only [List.length_singleton]; decide⟩⟩]

-- Analysis hash decoding preserves the reference zero-padding/truncation behavior.
-- This does not accept malformed outputs in a native protocol deserializer.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredHashLogCost.digest []).value.val.map Fin.val = List.replicate 64 0 ∧
  (StoredHashLogCost.digest [7,8]).value.val.map Fin.val = [7,8] ++ List.replicate 62 0 ∧
  (StoredHashLogCost.digest (List.replicate 64 9 ++ [88])).value.val.map Fin.val = List.replicate 64 9 ∧
  (StoredHashLogCost.digest []).cost ≤ 259)

-- Repeated and unrelated hash events remain in exact original order.
/-- info: true -/
#guard_msgs in
#eval let result := StoredSourceSnapshotHistory.reconstruct snapshotHistory
  decide (logData result.value.hashes = [(101,9),(102,10),(101,9),(103,11)] ∧
    result.value.snapshots.length = 3 ∧
    pairData (result.value.snapshots.map StoredSourceSnapshotHistory.Snapshot.source) = [(2,9),(1,9),(7,11)])

-- Every first-frozen key shares the exact earlier log; later hashes do not alter it.
/-- info: true -/
#guard_msgs in
#eval let result := StoredSourceSnapshotHistory.reconstruct snapshotHistory
  decide (result.value.snapshots.map (fun snapshot => logData snapshot.log) =
    [[(101,9)],[(101,9)],[(101,9)]])

-- Full context/root lookup returns frozen logs, with current-log fallback only for missing keys.
/-- info: true -/
#guard_msgs in
#eval let result := StoredSourceSnapshotHistory.reconstruct snapshotHistory
  decide (logData (StoredSourceSnapshotSelection.select result.value (pair 1 9)).value = [(101,9)] ∧
    logData (StoredSourceSnapshotSelection.select result.value (pair 7 11)).value = [(101,9)] ∧
    logData (StoredSourceSnapshotSelection.select result.value (pair 3 9)).value = [(101,9),(102,10),(101,9),(103,11)] ∧
    logData (StoredSourceSnapshotSelection.select result.value (pair 1 10)).value = [(101,9),(102,10),(101,9),(103,11)])

-- Distinct contexts sharing the same root may freeze at distinct causal boundaries.
/-- info: true -/
#guard_msgs in
#eval let history : List NativeTranscript.Observation :=
    [.hash [101] (List.replicate 64 9),.output (registryFor 1) 0 [7],
     .hash [102] (List.replicate 64 10),.output (registryFor 3) 0 [7],.hash [103] (List.replicate 64 11)]
  decide (logData (StoredSourceSnapshotSelection.run history (pair 1 9)).value = [(101,9)] ∧
    logData (StoredSourceSnapshotSelection.run history (pair 3 9)).value = [(101,9),(102,10)])

-- A snapshot of an empty log is a real snapshot, not a missing-key fallback.
/-- info: true -/
#guard_msgs in
#eval let history : List NativeTranscript.Observation :=
    [.output (registryFor 1) 0 [7],.hash [101] (List.replicate 64 9)]
  decide ((StoredSourceSnapshotSelection.run history (pair 1 9)).value = [] ∧
    logData (StoredSourceSnapshotSelection.run history (pair 2 9)).value = [(101,9)])

-- Empty outputs and hashes cannot freeze sources, even when their inputs mention keys.
/-- info: true -/
#guard_msgs in
#eval let history : List NativeTranscript.Observation :=
    [.start parentA,.hash (registryFor 1) (List.replicate 64 9),.output (registryFor 1) 0 []]
  let result := StoredSourceSnapshotHistory.reconstruct history
  decide (result.value.snapshots.length = 0 ∧ result.value.ledger.frozen.length = 0 ∧ result.value.hashes.length = 1)

-- Derived replay and lookup bounds include all complete-history work.
/-- info: true -/
#guard_msgs in
#eval let result := StoredSourceSnapshotSelection.run snapshotHistory (pair 1 9)
  let n := ClosedByteMachineRootBudget.inputWork snapshotHistory
  let p := snapshotHistory.length
  let q := StoredShakeHistory.bytes snapshotHistory
  decide (result.cost ≤ StoredSourceSnapshotBudget.stepBound n p q*p+5308*n^2+5 ∧
    (StoredSourceSnapshotHistory.reconstruct snapshotHistory).value.snapshots.length ≤ 4*n^2)

/-- info: true -/
#guard_msgs in
#eval decide ((StoredSourceSnapshotSelection.run [] (pair 1 9)).value = [] ∧
  (StoredSourceSnapshotHistory.reconstruct []).cost = 1)
