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

import all FormalProof4FHE.HasteBoots.FrameMatchCost
import all FormalProof4FHE.HasteBoots.GoldBatchFieldCountCost
import all FormalProof4FHE.HasteBoots.StoredGoldBatchFieldInputCost
import all FormalProof4FHE.HasteBoots.StoredGoldFieldSourceRecovery
import all FormalProof4FHE.HasteBoots.StoredGoldFieldExtraction
import all FormalProof4FHE.HasteBoots.NativeGoldBatchFieldInputView
import all FormalProof4FHE.HasteBoots.NativeGoldBatchExposure
import all FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude
import all FormalProof4FHE.HasteBoots.NativePrimeRequest
import all FormalProof4FHE.HasteBoots.TypedFieldRequest

import all FormalProof4FHE.HasteBoots.StoredGeometryArithmeticCost
import all FormalProof4FHE.HasteBoots.StoredGoldGeometryCost
import all FormalProof4FHE.HasteBoots.ValidatedGoldFieldExtraction
import all FormalProof4FHE.HasteBoots.StoredRegistryOwnerCost
import all FormalProof4FHE.HasteBoots.NativeBrakedownParameters
import all FormalProof4FHE.HasteBoots.NativeGoldSolinas
import all FormalProof4FHE.HasteBoots.NativeBrakedownContext
import all FormalProof4FHE.HasteBoots.NativeGoldBatchPcsProgram
import all Mathlib.Data.Nat.Size
import all Init.Data.Nat.Bitwise.Basic

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


private def fieldData : NativeGoldBatchMessage.Data :=
  ⟨(fun _ => 1),(fun _ => 9),⟨[],by decide⟩,
    ⟨[⟨[],by decide⟩,⟨[word 18446744069414584322],by decide⟩],by decide⟩⟩
private def nativeField : NativeGoldBatchFieldInputView.View := ⟨[emptyFrame],fieldData,word 3⟩
private def fieldInput : Input := TranscriptFrame.encodeMany nativeField.frames
private def frameInput (batch typed prime field : TranscriptFrame.Frame) : Input :=
  TranscriptFrame.encodeMany [batch,typed,prime,field]
private def batchField : TranscriptFrame.Frame := NativeGoldBatchFieldInputView.batchFrame fieldData
private def primeField : TranscriptFrame.Frame := NativeGoldBatchFieldInputView.primeFrame
private def typedField : TranscriptFrame.Frame := NativeGoldBatchFieldInputView.typedFrame
private def challenge : TranscriptFrame.Frame := NativeGoldBatchFieldInputView.fieldFrame (word 3)
private def rawHistory : List NativeTranscript.Observation :=
  [.hash [0] (List.replicate 64 0),.hash [1] (List.replicate 64 1),.output (registryFor 1) 0 [7],
   .hash [2] (List.replicate 64 2),.start fieldInput,.output fieldInput 17 [],.output fieldInput 9000 [3],
   .hash [3] (List.replicate 64 3)]


private def parameters : StoredGoldGeometryCost.Parameters :=
  ⟨word 3,word 3,word 1,word 2,
    ⟨word 4,word 2,word 2,word 4,NativeBrakedownContext.modulus,word 3⟩⟩
private def ownedSources : StoredSourceVectorReadCost.Sources :=
  ⟨[pair 1 9,pair 2 9,pair 1 9,pair 1 10,pair 2 9],by decide⟩

-- Arithmetic loops compute powers and bit lengths, including word-boundary values.
/-- info: true -/
#guard_msgs in
#eval (List.range 64).all (fun n =>
  decide ((StoredGeometryArithmeticCost.power2 n).value = 2^n ∧
    (StoredGeometryArithmeticCost.power2 n).cost = 3*n+1)) &&
  [0,1,2,3,2^63,2^64-1].all (fun n =>
    decide ((StoredGeometryArithmeticCost.bitLength n).value = n.size ∧
      (StoredGeometryArithmeticCost.bitLength n).cost = 4*n.size+1))

-- Dimensions and one shared random-count are computed from the retained object.
/-- info: true -/
#guard_msgs in
#eval let result := StoredGoldGeometryCost.build parameters
  decide (result.value.map (fun g => [g.columns,g.blocks,g.blockWidth,g.rows,g.stride,g.columnWords,
    g.responseWords,g.height,g.randomCount.val]) = some [4,4,2,6,8,12,12,2,18] ∧ result.cost ≤ 1500)

-- Native basic gates reject huge exponents before entering their power loops.
/-- info: true -/
#guard_msgs in
#eval [{parameters with width := word 0},{parameters with queries := word 0},
    {parameters with numVariables := word 64},{parameters with numVariables := word (2^64-1)},
    {parameters with leftVariables := word 4}].all (fun p =>
      let result := StoredGoldGeometryCost.build p
      result.value.isNone && decide (result.cost = 24))

-- Retained code-shape and actual allocation overflows fail closed with bounded work.
/-- info: true -/
#guard_msgs in
#eval [{parameters with code := {parameters.code with messageLength := word 3}},
    {parameters with code := {parameters.code with blocks := word 0}},
    {parameters with code := {parameters.code with blockWidth := word 0}},
    {parameters with width := word (2^64-1)},
    {parameters with code := {parameters.code with blocks := word (2^63)}}].all (fun p =>
      let result := StoredGoldGeometryCost.build p
      result.value.isNone && decide (result.cost ≤ 1500))

-- Capacity is produced at runtime, with the exact native geometry gate kept separate.
/-- info: true -/
#guard_msgs in
#eval let noCapacity := {parameters with code := {parameters.code with messageBlocks := word 1}}
  decide ((StoredGoldGeometryCost.build noCapacity).value.isSome ∧
    (ValidatedGoldFieldExtraction.validate noCapacity).value.isNone ∧
    (ValidatedGoldFieldExtraction.validate parameters).value.isSome ∧
    (ValidatedGoldFieldExtraction.validate parameters).cost ≤ 1516)

-- Actual constructor success supplies padded capacity; no capacity certificate is passed.
/-- info: true -/
#guard_msgs in
#eval let tables : NativeGoldBlockCode.Tables := ⟨fun _ => true,fun _ => true,fun _ => some ⟨3,by decide⟩⟩
  match NativeGoldBlockCode.build tables (word 4) (word 2) (word 2) with
  | .error _ => false
  | .ok code =>
    let p := {parameters with code := code}
    let result := ValidatedGoldFieldExtraction.validate p
    decide (result.value.isSome ∧ code.messageBlocks.val = 2 ∧ code.blocks.val = 32)

-- First ORIGINAL ownership includes earlier unused aliases, with full context/root identity.
/-- info: true -/
#guard_msgs in
#eval decide ((List.finRange ownedSources.val.length).map (fun index =>
    (StoredRegistryOwnerCost.owner ownedSources index).value) =
    [some 0,some 1,some 0,some 3,some 1])

-- Ownership lookup charges both index access and full-key comparisons.
/-- info: true -/
#guard_msgs in
#eval (List.finRange ownedSources.val.length).all (fun index =>
  decide ((StoredRegistryOwnerCost.owner ownedSources index).cost ≤ 1329*ownedSources.val.length+6))

-- The validated entry point generates its capacity witness and runs the original stored extraction.
/-- info: true -/
#guard_msgs in
#eval let context := {ctx with parameters := parameters}
  let input := TranscriptFrame.encodeMany ({nativeField with count := word 18}).frames
  let history : List NativeTranscript.Observation := [.hash [0] (List.replicate 64 0),
    .output (registryFor 1) 0 [7],.output input 9000 [3]]
  let result := ValidatedGoldFieldExtraction.run history input (root 0) context 0
  let expected := StoredGoldFieldExtraction.run history input (root 0) context 0 (by decide)
  decide (result.value.map (fun pair => pair.2) = expected.value.map (fun pair => pair.2)) &&
    result.value.isSome &&
    decide (result.cost ≤ 1519+ValidatedGoldFieldExtraction.extractionBound history input context 0)

-- Invalid public dimensions reject before parsing/causal replay/extraction.
/-- info: true -/
#guard_msgs in
#eval let context := {ctx with parameters := {parameters with width := word 0}}
  let result := ValidatedGoldFieldExtraction.run rawHistory fieldInput (root 0) context 0
  decide (result.value.isNone ∧ result.cost ≤ 1518)
