module
public import FormalProof4FHE.HasteBoots.NativeGoldParameterStore
public import FormalProof4FHE.HasteBoots.StoredGoldRegistryAssociation
@[expose] public section

/-! Registry ownership and observed extraction inherit parameter/code constructor
provenance from actual logical allocations and original references. No code
identity, geometry or primitive-root certificate is supplied separately.
Logical handles/receipts still require actual Rust heap/source refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldConstructedRegistry
open NativeGoldParameterStore (Entry Reference GoodEntry)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (World Input Byte)
open OracleProgram (run)
noncomputable section

theorem initialized_original (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldParameterStore.registry entries references = some registry)
    (parent : Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (position : Fin initialized.sources.val.length) :
    ∃ (original : Fin registry.val.length) (reference : Reference) (entry : Entry),
      original.val = (NativeSourceRegistry.owner initialized.sources position).val ∧ original.val ≤ position.val ∧
      references.val[original.val]? = some reference ∧ entries[reference.handle]? = some entry ∧ GoodEntry entry ∧
      (registry.val.get original).parameters = entry.initialized.parameters ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row entry.initialized.parameters) world).run.1 =
        some (initialized.sources.val.get position).1 ∧ reference.root = (initialized.sources.val.get position).2 ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row entry.initialized.parameters) world).run.2.Sublist
        (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2 := by
  obtain ⟨original,selected,before,context,root⟩ := NativeSourceRegistry.initialized_owner
    NativeGoldBlockCode.description.row registry parent world initialized executed position
  obtain ⟨reference,entry,atReference,atEntry,good,same⟩ := NativeGoldParameterStore.registry_slot entries reachable references registry retained original
  refine ⟨original,reference,entry,selected,before,atReference,atEntry,good,?_,?_,?_,?_⟩
  · rw [same]
  · simpa only [same] using context
  · simpa only [same] using root
  · have included := NativeRegistryContextTrace.initialized_slot NativeGoldBlockCode.description.row registry parent world initialized executed original
    simpa only [same] using included

theorem extraction_original (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldParameterStore.registry entries references = some registry)
    (parent : Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (sources : StoredSourceVectorReadCost.Sources)
    (decoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length) (history : List Observation)
    (included : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2.Sublist history)
    (input : Input) (dummy : Vector Byte 64) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index) (truthful : ObservationReplay.Agrees world history)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history) :
    ∃ (original : Fin registry.val.length) (reference : Reference) (entry : Entry),
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧ original.val ≤ index.val ∧
      references.val[original.val]? = some reference ∧ entries[reference.handle]? = some entry ∧ GoodEntry entry ∧
      ctx.parameters = entry.initialized.parameters ∧ reference.root = output.1.data.source.2.get := by
  obtain ⟨original,selected,before,parameters,root⟩ := StoredGoldRegistryAssociation.extraction_decoded_original
    registry parent world initialized executed sources decoded index history included input dummy ctx radius output accepted key truthful safe
  obtain ⟨reference,entry,atReference,atEntry,good,same⟩ := NativeGoldParameterStore.registry_slot entries reachable references registry retained original
  refine ⟨original,reference,entry,selected,before,atReference,atEntry,good,?_,?_⟩
  · simpa only [same] using parameters
  · simpa only [same] using root

theorem extracted_code_meaning (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldParameterStore.registry entries references = some registry)
    (parent : Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (sources : StoredSourceVectorReadCost.Sources)
    (decoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length) (history : List Observation)
    (included : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2.Sublist history)
    (input : Input) (dummy : Vector Byte 64) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index) (truthful : ObservationReplay.Agrees world history)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history) :
    IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)) ∧
      ∃ geometry, NativeBrakedownParameters.build NativeGoldBlockCode.description ctx.parameters = some geometry := by
  obtain ⟨_,_,entry,_,_,_,_,good,parameters,_⟩ := extraction_original entries reachable references registry retained
    parent world initialized executed sources decoded index history included input dummy ctx radius output accepted key truthful safe
  rw [parameters]
  exact ⟨NativeGoldParameterInitialization.code_primitive entry.header entry.request entry.config good.1 entry.initialized good.2,
    entry.initialized.geometry,NativeGoldParameterInitialization.parameter_geometry entry.header entry.config entry.initialized good.2⟩

end
end FormalProof4FHE.HasteBoots.NativeGoldConstructedRegistry
