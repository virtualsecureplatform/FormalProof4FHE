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

-- Concrete byte equality checks all positions and keeps contexts distinct.
/-- info: true -/
#guard_msgs in
#eval let changed : StoredMetadataCost.Root := Vector.ofFn (fun i => if i.val = 63 then 2 else 1)
  (StoredMetadataCost.rootEqual (root 1) (root 1)).value &&
  !(StoredMetadataCost.rootEqual (root 1) changed).value &&
  !(StoredMetadataCost.sourceEqual (pair 1 9) (pair 2 9)).value &&
  decide ((StoredMetadataCost.sourceEqual (pair 1 9) (pair 1 9)).cost ≤ 1323)

-- Match compact-ledger last occurrences, with no owner choice or root-only collapse.
/-- info: true -/
#guard_msgs in
#eval decide (pairData (StoredMetadataCost.dedupSources [pair 1 9,pair 2 9,pair 1 9]).value = [(2,9),(1,9)] ∧
  rootData (StoredMetadataCost.dedupRoots [root 7,root 8,root 7]).value = [8,7] ∧
  (StoredMetadataCost.containsSource (pair 2 9) [pair 1 9,pair 2 9]).value = true)

-- Every wildcard/compatible record remains; only exposed disagreement rejects.
/-- info: true -/
#guard_msgs in
#eval let parents : List StoredParentContributionsCost.Parent :=
    [⟨[1],[pair 1 9],[root 7]⟩,⟨[2],[pair 2 9],[root 8]⟩,⟨[1],[pair 3 9],[]⟩]
  let cache := (StoredShakeByteCache.write [] [2] 63 [8]).value
  let result := StoredParentContributionsCost.select cache (root 7) parents
  decide (result.value.map (fun parent => pairData parent.sources) = [[(1,9)],[(3,9)]])

-- Ordered cross-products retain duplicate helpers, duplicate roots and parent order.
/-- info: true -/
#guard_msgs in
#eval let parents : List StoredParentContributionsCost.Parent :=
    [⟨[],[pair 1 9],[root 7,root 7]⟩,⟨[],[pair 2 9],[root 8]⟩]
  let result := StoredParentContributionsCost.inheritSources [root 11,root 12] parents
  decide (pairData result.value = [(1,9),(7,11),(7,12),(7,11),(7,12),(2,9),(8,11),(8,12)] ∧
    result.cost ≤ 6*StoredParentContributionsCost.sourceCount parents+
      (9*2+6)*StoredParentContributionsCost.helperCount parents+10*parents.length+1)

-- Before-write compatibility inherits a novel helper/root pair on the same input.
-- Writing the conflicting byte first would incorrectly lose (7,11).
/-- info: true -/
#guard_msgs in
#eval let result := StoredParentMetadataHistory.reconstruct before
  decide (result.value.parents.map metadata =
    [([(2,9),(1,9),(7,11)],[7]), ([(2,9),(1,9)],[7])])

-- Hashes and empty output observations discover parents; malformed inputs do not.
-- Previously stored metadata survives; cache bytes are never invented from hashes.
/-- info: true -/
#guard_msgs in
#eval let result := StoredParentMetadataHistory.reconstruct history
  decide (result.value.parents.map metadata =
    [([],[]),([],[]), ([(2,9),(1,9),(7,11)],[7]), ([(2,9),(1,9)],[7])] ∧
    (StoredShakeByteCache.lookup result.value.cache parentA 0).value = some 8 ∧
    (StoredShakeByteCache.lookup result.value.cache parentB 0).value = none)

-- Later observations cannot retrospectively add helpers/sources to old parentB.
-- Current active-parent filtering still uses all current exposed coordinates.
/-- info: true -/
#guard_msgs in
#eval let result := StoredHistorySourceResolutionCost.run history (child 7)
  decide (pairData result.value = [])

-- A later correction changes current compatibility while leaving earlier metadata intact.
/-- info: true -/
#guard_msgs in
#eval let later := history ++ [.output parentA 0 [7]]
  let result := StoredHistorySourceResolutionCost.run later (child 7)
  let pairs := pairData result.value
  decide ((7,11) ∈ pairs ∧ (7,17) ∈ pairs ∧
    result.cost ≤ (StoredParentMetadataBudget.stepBound (ClosedByteMachineRootBudget.inputWork later)
      later.length (StoredShakeHistory.bytes later)+8*StoredShakeHistory.bytes later+8)*later.length+
      StoredHistorySourceResolutionCost.resolutionBound (ClosedByteMachineRootBudget.inputWork later)
        later.length (StoredShakeHistory.bytes later) (child 7).length+2)

-- Empty history is valid and all public-input parsing work is still included.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredParentMetadataHistory.reconstruct []).cost = 1 ∧
  (StoredParentMetadataHistory.reconstruct []).value.parents.length = 0 ∧
  (StoredHistorySourceResolutionCost.run [] [255]).value = [])
