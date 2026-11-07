module
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
private def table : NativeLookupRequestWire.Table := ⟨[row [1,2],row [],row [3]],by decide⟩
private def config : NativeLookupRequestWire.Config := ⟨word 4,table,word 2⟩
private def sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨[((fun _ => 1),(fun _ => 9)),((fun _ => 2),(fun _ => 9)),((fun _ => 1),(fun _ => 9))],by decide⟩
private def native : NativeCanonicalLookupWire.Binding := ⟨config,(fun _ => 7),sources⟩
private def wire : Input := NativeCanonicalLookupWire.payload native
private def configData (cfg : NativeLookupRequestWire.Config) :=
  (cfg.logicalLength.val,cfg.table.val.map (fun row => row.val.map Fin.val),cfg.repetitions.val)
private def bindingData (binding : StoredCanonicalBindingCost.Stored) :=
  (configData binding.config,(binding.helper.get 0).val,
    binding.sources.val.map (fun pair => ((pair.1.get 0).val,(pair.2.get 0).val)))
private def tailBytes : Input := [3] ++ List.replicate 64 7 ++ [0]
private def bindingFrame (message : Input) : TranscriptFrame.Frame := ⟨1,StoredBindingFramesCost.label,message⟩

-- Nested huge table/row counts stop on supplied bytes, including empty-row prefixes.
/-- info: true -/
#guard_msgs in
#eval let count := 2^64-1
  [[],[0],[0,0]].all (fun input : Input =>
    let result := TableWireCost.readCount count input
    decide (result.value.isNone ∧ result.cost ≤ 113*(input.length+1))) &&
  (TableWireCost.read (253::List.replicate 8 255)).value.isNone &&
  (TableWireCost.read (1::253::List.replicate 8 255)).value.isNone

-- Prefix reading retains empty/ragged rows and the untouched suffix.
/-- info: true -/
#guard_msgs in
#eval let result := TableWireCost.read (NativeLookupRequestWire.tableCodec.encode table ++ [42])
  decide (result.value.map (fun pair => (pair.1.val.map (fun row => row.val.map Fin.val),pair.2)) =
    some ([[1,2],[],[3]],[42]))

-- Exact configuration fields are read without an independent columns field.
/-- info: true -/
#guard_msgs in
#eval let result := ConfigWireCost.read (NativeLookupRequestWire.configCodec.encode config ++ [42])
  decide (result.value.map (fun pair => (configData pair.1,pair.2)) = some ((4,[[1,2],[],[3]],2),[42]) ∧
    (ConfigWireCost.encode config).value = NativeLookupRequestWire.configCodec.encode config)

-- Raw lazy u64 public-table entries are preserved, without field normalization.
/-- info: true -/
#guard_msgs in
#eval let lazy : Nat := 18446744069414584322
  let cfg : NativeLookupRequestWire.Config := ⟨word 1,⟨[row [lazy]],by decide⟩,word 1⟩
  let result := ConfigWireCost.read (NativeLookupRequestWire.configCodec.encode cfg)
  decide (result.value.map (fun pair => configData pair.1) = some (1,[[lazy]],1))

-- Full canonical bindings preserve configuration, helper and all source aliases.
/-- info: true -/
#guard_msgs in
#eval let result := StoredCanonicalBindingCost.decode wire
  decide (result.value.map bindingData = some ((4,[[1,2],[],[3]],2),7,[(1,9),(2,9),(1,9)]) ∧
    result.cost ≤ 302*wire.length+1764*(wire.length/128+1)+1100)

-- Prefix reading returns arbitrary suffixes, while complete decoding rejects them.
/-- info: true -/
#guard_msgs in
#eval let result := StoredCanonicalBindingCost.read (wire ++ [42])
  decide (result.value.map (fun pair => bindingData pair.1) =
    some ((4,[[1,2],[],[3]],2),7,[(1,9),(2,9),(1,9)])) &&
  decide (result.value.map Prod.snd = some ([42] : Input)) &&
  (StoredCanonicalBindingCost.decode (wire ++ [42])).value.isNone


-- Degree 3 is the original serialized extension field; other values reject.
/-- info: true -/
#guard_msgs in
#eval let bad := NativeLookupRequestWire.configCodec.encode config ++ [2] ++ List.replicate 64 7 ++
    NativeCanonicalLookupWire.sourcesCodec.encode sources
  decide ((StoredCanonicalBindingCost.read bad).value.isNone ∧
    (StoredCanonicalBindingCost.read (NativeLookupRequestWire.configCodec.encode config ++ [3] ++ List.replicate 63 7)).value.isNone)

-- Structural aliases of nested counts and degree accept prefixes but fail canonicality.
/-- info: true -/
#guard_msgs in
#eval let alternatives : List Input :=
    [([251,0,0,0,1] ++ tailBytes),([0,251,1,0,0,1] ++ tailBytes),
     ([0,1,251,0,0,1] ++ tailBytes),([0,0,1,251,3,0] ++ List.replicate 64 7 ++ [0]),
     ([0,0,1,3] ++ List.replicate 64 7 ++ [251,0,0])]
  alternatives.all (fun input => (StoredCanonicalBindingCost.read input).value.isSome &&
    (StoredCanonicalBindingCost.decode input).value.isNone)

-- Re-encoding a decoded stored binding reconstructs the exact original message.
/-- info: true -/
#guard_msgs in
#eval match (StoredCanonicalBindingCost.decode wire).value with
  | none => false
  | some value => decide ((StoredCanonicalBindingCost.encode value).value = wire)

-- Binding frames require the exact original kind and label.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredBindingFramesCost.frameBinding (bindingFrame wire)).value.map bindingData =
      some ((4,[[1,2],[],[3]],2),7,[(1,9),(2,9),(1,9)]) ∧
    (StoredBindingFramesCost.frameBinding ⟨0,StoredBindingFramesCost.label,wire⟩).value.isNone ∧
    (StoredBindingFramesCost.frameBinding ⟨1,NativeCanonicalLookupWire.registryLabel,wire⟩).value.isNone)

-- Every original binding frame survives in order; malformed payloads are ignored.
/-- info: true -/
#guard_msgs in
#eval let input := TranscriptFrame.encodeMany [bindingFrame wire,bindingFrame [],bindingFrame wire]
  let result := StoredBindingFramesCost.fromInput input
  decide (result.value.map (fun binding => (binding.helper.get 0).val) = [7,7] ∧
    result.cost ≤ (4971+6*StoredBindingFramesCost.label.length)*input.length+5 ∧
    (StoredBindingFramesCost.fromInput (input ++ [255])).value = [])

/-- info: [128, 156, 9283, 12334] -/
#guard_msgs in
#eval [(TableWireCost.read (NativeLookupRequestWire.tableCodec.encode table)).cost,
  (ConfigWireCost.read (NativeLookupRequestWire.configCodec.encode config)).cost,
  (StoredCanonicalBindingCost.decode wire).cost,
  (StoredBindingFramesCost.fromInput (TranscriptFrame.encodeMany [bindingFrame wire])).cost]
