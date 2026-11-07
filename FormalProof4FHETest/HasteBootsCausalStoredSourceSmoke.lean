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

import all FormalProof4FHE.HasteBoots.PublicGoldByteExtraction
import all FormalProof4FHE.HasteBoots.RawGoldColumnCost
import all FormalProof4FHE.HasteBoots.ScalarDistanceCost
import all FormalProof4FHE.HasteBoots.DenseCandidateCheck
import all FormalProof4FHE.HasteBoots.DenseBerlekampWelch
import all FormalProof4FHE.HasteBoots.BerlekampWelchPowers
import all FormalProof4FHE.HasteBoots.BerlekampWelchSystem
import all FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
import all FormalProof4FHE.HasteBoots.BlockEvaluationCost
import all FormalProof4FHE.HasteBoots.ColumnDistanceCost
import all FormalProof4FHE.HasteBoots.ExecutableRectangularMatrixExtraction
import all FormalProof4FHE.HasteBoots.CommonSourceReindex
import all FormalProof4FHE.HasteBoots.ExecutableSourceCoefficients
import all FormalProof4FHE.HasteBoots.ExecutableCommonSource
import all FormalProof4FHE.HasteBoots.DenseCommonSource
import all FormalProof4FHE.HasteBoots.DenseSourceExtraction
import all FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
import all FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialDivision
import all FormalProof4FHE.HasteBoots.DenseMonicDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialStepCost
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.ExecutablePolynomial
import all FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
import all FormalProof4FHE.HasteBoots.FiniteMatrixSolver
import all FormalProof4FHE.HasteBoots.FiniteLinearSolver
import all FormalProof4FHE.HasteBoots.RowLayout
import all FormalProof4FHE.HasteBoots.NativeFields
import all ArkLib.Data.CodingTheory.BerlekampWelch.Condition
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
import all FormalProof4FHE.HasteBoots.NativeGoldExecutableExtraction
import all FormalProof4FHE.HasteBoots.NativeGoldPublicSource
import all FormalProof4FHE.HasteBoots.NativeGoldBlockCode
import all FormalProof4FHE.HasteBoots.NativeFieldRepresentation
import all FormalProof4FHE.HasteBoots.NTTDomainCost
import all FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability
import all FormalProof4FHE.HasteBoots.CausalPrefixReadCost
import all FormalProof4FHE.HasteBoots.CausalStoredSourceRecovery
import all FormalProof4FHE.HasteBoots.CausalStoredGoldExtraction

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


private def usize (n : Nat) : NativeUsizeMessage.Usize := ⟨n % 2^64,Nat.mod_lt _ (by decide)⟩
private def digest : NativeRootMessage.Digest := fun _ => 0
private def ctx : NativeGoldBatchPcsProgram.Context :=
  ⟨⟨fun _ => false,fun _ => false,fun _ => none⟩,
    ⟨usize 3,usize 3,usize 1,usize 0,
      ⟨usize 3,usize 2,usize 2,usize 4,⟨[],by decide⟩,usize 3⟩⟩,
    NativeTranscript.new [] digest,digest,⟨[],by decide⟩,⟨[],by decide⟩,
    ⟨⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩⟩,0⟩



private def target : Input := child 7
private def exposedHistory : List NativeTranscript.Observation := snapshotHistory ++
  [.start target,.output target 17 [],.output target 9000 [4],
   .hash [104] (List.replicate 64 12),.output target 0 [5,6],.hash [105] (List.replicate 64 13)]

-- Any positive offset is the boundary; starts, hashes and empty reads remain before it.
/-- info: true -/
#guard_msgs in
#eval let before : List NativeTranscript.Observation :=
    [.start [7],.hash [7] [9],.output [7] 17 [],.output [8] 0 [1],.hash [8] [10]]
  let history := before ++ [.output [7] 1000000 [3],.hash [7] [11],.output [7] 0 [4]]
  let result := CausalPrefixReadCost.recover [7] history
  decide (result.value = some before ∧ result.cost ≤ (6*1+16)*history.length+1)

-- No positive exposure returns none, including empty streams and empty outputs.
/-- info: true -/
#guard_msgs in
#eval decide ((CausalPrefixReadCost.recover [] [.start [],.hash [] [],.output [] 0 []]).value = none ∧
  (CausalPrefixReadCost.recover [7] [.output [8] 0 [1]]).value = none ∧
  (CausalPrefixReadCost.recover [7] []).cost = 1)

-- Exact whole-input byte comparison avoids merging distinct stream inputs.
/-- info: true -/
#guard_msgs in
#eval let history : List NativeTranscript.Observation := [.output [7,8] 0 [1],.output [7] 8 [2]]
  decide ((CausalPrefixReadCost.recover [7] history).value = some [.output [7,8] 0 [1]] ∧
    (CausalPrefixReadCost.recover [7,8] history).value = some [])

-- A prior partial read wins over later complete reads of the same original input.
/-- info: true -/
#guard_msgs in
#eval let history : List NativeTranscript.Observation := [.hash [7] [9],.output [7] 63 [1],
    .hash [8] [10],.output [7] 0 (List.replicate 64 1)]
  decide ((CausalPrefixReadCost.recover [7] history).value = some [.hash [7] [9]])

-- Recovered selection retains the original frozen snapshot, excluding descendant hashes.
/-- info: true -/
#guard_msgs in
#eval let result := CausalStoredSourceRecovery.run exposedHistory target (pair 1 9)
  decide (result.value.map logData = some [(101,9)] ∧
    result.cost ≤ (6*target.length+16)*exposedHistory.length+
      StoredSourceSnapshotBudget.stepBound (ClosedByteMachineRootBudget.inputWork exposedHistory)
        exposedHistory.length (StoredShakeHistory.bytes exposedHistory)*exposedHistory.length+
      5308*(ClosedByteMachineRootBudget.inputWork exposedHistory)^2+9)

-- For an unfrozen key, fallback is the first-read prefix log, never the later full log.
/-- info: true -/
#guard_msgs in
#eval decide ((CausalStoredSourceRecovery.run exposedHistory target (pair 8 9)).value.map logData =
  some [(101,9),(102,10),(101,9),(103,11)])

-- Extending a completed history preserves the originally recovered source.
/-- info: true -/
#guard_msgs in
#eval let extra : List NativeTranscript.Observation := [.hash [106] (List.replicate 64 14),.output target 1 [9]]
  decide ((CausalStoredSourceRecovery.run (exposedHistory ++ extra) target (pair 1 9)).value.map logData =
    (CausalStoredSourceRecovery.run exposedHistory target (pair 1 9)).value.map logData)

-- Integrated extraction agrees with the byte adapter on the manually expected frozen log.
/-- info: true -/
#guard_msgs in
#eval let before : List NativeTranscript.Observation := [.hash [0] (List.replicate 64 0),
    .hash [1] (List.replicate 64 1),.output (registryFor 1) 0 [7],.hash [2] (List.replicate 64 2)]
  let history := before ++ [.output target 9000 [3],.hash [3] (List.replicate 64 3)]
  let result := CausalStoredGoldExtraction.run history target (pair 1 9) (root 0) ctx 0 (by decide)
  let expected := PublicGoldByteExtraction.run (List.replicate 64 0) (List.replicate 64 9) ctx
    [([0],List.replicate 64 0),([1],List.replicate 64 1)] 0 (by decide)
  decide (result.value = expected.value)

-- Unseen streams reject before extraction and retain the measured recovery charge.
/-- info: true -/
#guard_msgs in
#eval let result := CausalStoredGoldExtraction.run snapshotHistory target (pair 1 9) (root 0) ctx 0 (by decide)
  let recovered := CausalStoredSourceRecovery.run snapshotHistory target (pair 1 9)
  decide (result.value.isNone ∧ result.cost = recovered.cost+2)
