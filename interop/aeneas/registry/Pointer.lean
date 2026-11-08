/-! Actual extracted field reads and pointer-backed constructor provenance at
one original index. Both registry runs must produce the same model registry.
This compatibility premise is explicit: it is not a Rust heap simulation or
an allocator, context-byte, instruction-cost or complete security proof. -/
namespace HasteBootsExtractedRegistryPointer
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open NativeGoldParameterStore (Entry GoodEntry)
open NativeGoldPointerRegistry (Borrow)
open NativePointerStorage (Cell)
open HasteBootsExtractedRegistryDecode (Source Model decode root)
open HasteBootsExtractedParametersDecode (decodeParameters)
open NativePrefixCodec (Vector)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (World Input)
open OracleProgram (run)
open formalproof4fhe_native_registry_fixture (registry_get)

theorem slot (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (heap : List (Cell ℕ)) (borrows : Vector Borrow) (source : Slice Source)
    (models : Vector Model) (decoded : HasteBootsExtractedRegistry.registry source = some models)
    (retained : NativeGoldPointerRegistry.registry entries heap borrows = some models)
    (index : Fin models.val.length) :
    ∃ (word : Usize) (actual : Source) (borrowed : Borrow) (cell : Cell ℕ) (entry : Entry),
      word.val = index.val ∧
      registry_get source word = .ok (some (actual.parameters,actual.commitment.root)) ∧
      borrows.val[index.val]? = some borrowed ∧ cell ∈ heap ∧
      borrowed.pointer.provenance = some cell.origin ∧ borrowed.pointer.address = cell.address ∧
      entries[cell.value]? = some entry ∧ GoodEntry entry ∧
      models.val.get index = ⟨entry.initialized.parameters,borrowed.root⟩ ∧
      decodeParameters actual.parameters = some entry.initialized.parameters ∧
      root actual.commitment.root = borrowed.root := by
  obtain ⟨borrowed,cell,entry,atBorrow,member,origin,address,atEntry,good,same⟩ :=
    NativeGoldPointerRegistry.registry_slot entries reachable heap borrows models retained index
  obtain ⟨word,actual,wordValue,read,represented⟩ :=
    HasteBootsExtractedRegistry.registry_slot source models decoded index
  have fields := HasteBootsExtractedRegistryDecode.decode_fields actual (models.val.get index) represented
  exact ⟨word,actual,borrowed,cell,entry,wordValue,read,atBorrow,member,origin,address,atEntry,good,same,
    by simpa only [same] using fields.1,by simpa only [same] using fields.2.symm⟩

theorem initialized_original (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (heap : List (Cell ℕ)) (borrows : Vector Borrow) (source : Slice Source)
    (models : Vector Model) (decoded : HasteBootsExtractedRegistry.registry source = some models)
    (retained : NativeGoldPointerRegistry.registry entries heap borrows = some models)
    (parent : Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.1 = some initialized)
    (position : Fin initialized.sources.val.length) :
    ∃ (original : Fin models.val.length) (word : Usize) (actual : Source) (borrowed : Borrow) (cell : Cell ℕ) (entry : Entry),
      original.val = (NativeSourceRegistry.owner initialized.sources position).val ∧ original.val ≤ position.val ∧
      word.val = original.val ∧ registry_get source word = .ok (some (actual.parameters,actual.commitment.root)) ∧
      borrows.val[original.val]? = some borrowed ∧ cell ∈ heap ∧
      borrowed.pointer.provenance = some cell.origin ∧ borrowed.pointer.address = cell.address ∧
      entries[cell.value]? = some entry ∧ GoodEntry entry ∧
      decodeParameters actual.parameters = some entry.initialized.parameters ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row entry.initialized.parameters) world).run.1 =
        some (initialized.sources.val.get position).1 ∧
      root actual.commitment.root = (initialized.sources.val.get position).2 ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row entry.initialized.parameters) world).run.2.Sublist
        (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.2 := by
  obtain ⟨original,selected,before,context,rootEq⟩ := NativeSourceRegistry.initialized_owner
    NativeGoldBlockCode.description.row models parent world initialized executed position
  obtain ⟨word,actual,borrowed,cell,entry,wordValue,read,atBorrow,member,origin,address,atEntry,good,same,parameters,rootValue⟩ :=
    slot entries reachable heap borrows source models decoded retained original
  refine ⟨original,word,actual,borrowed,cell,entry,selected,before,wordValue,read,atBorrow,member,origin,address,atEntry,good,parameters,?_,?_,?_⟩
  · simpa only [same] using context
  · exact rootValue.trans (by simpa only [same] using rootEq)
  · have included := NativeRegistryContextTrace.initialized_slot NativeGoldBlockCode.description.row models parent world initialized executed original
    simpa only [same] using included

theorem extraction_original (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (heap : List (Cell ℕ)) (borrows : Vector Borrow) (source : Slice Source)
    (models : Vector Model) (decoded : HasteBootsExtractedRegistry.registry source = some models)
    (retained : NativeGoldPointerRegistry.registry entries heap borrows = some models)
    (parent : Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.1 = some initialized)
    (sources : StoredSourceVectorReadCost.Sources)
    (storedDecoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length) (history : List Observation)
    (included : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.2.Sublist history)
    (input : Input) (dummy : Vector InputIndexedOracle.Byte 64) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index) (truthful : ObservationReplay.Agrees world history)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history) :
    ∃ (original : Fin models.val.length) (word : Usize) (actual : Source) (borrowed : Borrow) (cell : Cell ℕ) (entry : Entry),
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧ original.val ≤ index.val ∧
      word.val = original.val ∧ registry_get source word = .ok (some (actual.parameters,actual.commitment.root)) ∧
      borrows.val[original.val]? = some borrowed ∧ cell ∈ heap ∧
      borrowed.pointer.provenance = some cell.origin ∧ borrowed.pointer.address = cell.address ∧
      entries[cell.value]? = some entry ∧ GoodEntry entry ∧
      ctx.parameters = entry.initialized.parameters ∧ decodeParameters actual.parameters = some ctx.parameters ∧
      root actual.commitment.root = output.1.data.source.2.get := by
  obtain ⟨original,selected,before,parameters,rootEq⟩ := StoredGoldRegistryAssociation.extraction_decoded_original
    models parent world initialized executed sources storedDecoded index history included input dummy ctx radius output accepted key truthful safe
  obtain ⟨word,actual,borrowed,cell,entry,wordValue,read,atBorrow,member,origin,address,atEntry,good,same,decodedParameters,rootValue⟩ :=
    slot entries reachable heap borrows source models decoded retained original
  have parametersEq : ctx.parameters = entry.initialized.parameters := by simpa only [same] using parameters
  refine ⟨original,word,actual,borrowed,cell,entry,selected,before,wordValue,read,atBorrow,member,origin,address,atEntry,good,parametersEq,?_,?_⟩
  · rw [parametersEq]; exact decodedParameters
  · exact rootValue.trans (by simpa only [same] using rootEq)

end HasteBootsExtractedRegistryPointer
