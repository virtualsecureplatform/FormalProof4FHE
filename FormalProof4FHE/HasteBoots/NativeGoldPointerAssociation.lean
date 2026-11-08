module
public import FormalProof4FHE.HasteBoots.NativeGoldPointerRegistry
public import FormalProof4FHE.HasteBoots.StoredGoldRegistryAssociation
@[expose] public section

/-! First-original ownership and observed extraction through pointer-resolved
parameter storage. Pointer matches and constructor provenance are conclusions
of successful resolution, not per-read hypotheses. The operational heap still
requires a Rust allocator/source and physical-work refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPointerAssociation
open NativeGoldParameterStore (Entry GoodEntry)
open NativeGoldPointerRegistry (Borrow)
open NativePointerStorage (Cell)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (World Input Byte)
open OracleProgram (run)
noncomputable section

/-- Every original borrow is resolved, even if no later claim uses it. -/
theorem unreadable_original_rejected (entries : List Entry) (heap : List (Cell ℕ))
    (borrows : Vector Borrow) (index : Fin borrows.val.length)
    (unreadable : NativePointerStorage.read heap (borrows.val.get index).pointer = none) :
    NativeGoldPointerRegistry.registry entries heap borrows = none := by
  cases executed : NativeGoldPointerRegistry.registry entries heap borrows with
  | none => rfl
  | some output =>
    obtain ⟨resolved,resolution,_⟩ := NativeGoldPointerRegistry.registry_resolves entries heap borrows output executed
    have values := NativeGoldPointerRegistry.references_values heap borrows resolved resolution
    obtain ⟨borrowed,reference,selected,_,found,_⟩ :=
      NativeGoldPointerRegistry.resolve_slot heap borrows.val resolved.val values.1 index.val index.isLt
    have same : borrows.val.get index = borrowed :=
      Option.some.inj ((List.getElem?_eq_getElem index.isLt).symm.trans selected)
    rw [← same,unreadable] at found
    cases found

/-- Reusing a retired address cannot rescue a stale original registry borrow. -/
theorem stale_original_rejected (entries : List Entry) (heap : List (Cell ℕ))
    (old fresh : Cell ℕ) (different : old.origin ≠ fresh.origin)
    (borrows : Vector Borrow) (index : Fin borrows.val.length)
    (selected : (borrows.val.get index).pointer = NativePointerStorage.pointer old) :
    NativeGoldPointerRegistry.registry entries
      (fresh::NativePointerStorage.retire heap old.origin) borrows = none := by
  apply unreadable_original_rejected entries _ borrows index
  rw [selected]
  exact NativePointerStorage.reused_address_stale heap old fresh different

theorem initialized_original (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (heap : List (Cell ℕ)) (borrows : Vector Borrow) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldPointerRegistry.registry entries heap borrows = some registry)
    (parent : Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (position : Fin initialized.sources.val.length) :
    ∃ (original : Fin registry.val.length) (borrowed : Borrow) (cell : Cell ℕ) (entry : Entry),
      original.val = (NativeSourceRegistry.owner initialized.sources position).val ∧ original.val ≤ position.val ∧
      borrows.val[original.val]? = some borrowed ∧ cell ∈ heap ∧
      borrowed.pointer.provenance = some cell.origin ∧ borrowed.pointer.address = cell.address ∧
      entries[cell.value]? = some entry ∧ GoodEntry entry ∧
      (registry.val.get original).parameters = entry.initialized.parameters ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row entry.initialized.parameters) world).run.1 =
        some (initialized.sources.val.get position).1 ∧ borrowed.root = (initialized.sources.val.get position).2 ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row entry.initialized.parameters) world).run.2.Sublist
        (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2 := by
  obtain ⟨original,selected,before,context,root⟩ := NativeSourceRegistry.initialized_owner
    NativeGoldBlockCode.description.row registry parent world initialized executed position
  obtain ⟨borrowed,cell,entry,atBorrow,member,origin,address,atEntry,good,same⟩ :=
    NativeGoldPointerRegistry.registry_slot entries reachable heap borrows registry retained original
  refine ⟨original,borrowed,cell,entry,selected,before,atBorrow,member,origin,address,atEntry,good,?_,?_,?_,?_⟩
  · rw [same]
  · simpa only [same] using context
  · simpa only [same] using root
  · have included := NativeRegistryContextTrace.initialized_slot NativeGoldBlockCode.description.row registry parent world initialized executed original
    simpa only [same] using included

theorem extraction_original (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (heap : List (Cell ℕ)) (borrows : Vector Borrow) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldPointerRegistry.registry entries heap borrows = some registry)
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
    ∃ (original : Fin registry.val.length) (borrowed : Borrow) (cell : Cell ℕ) (entry : Entry),
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧ original.val ≤ index.val ∧
      borrows.val[original.val]? = some borrowed ∧ cell ∈ heap ∧
      borrowed.pointer.provenance = some cell.origin ∧ borrowed.pointer.address = cell.address ∧
      entries[cell.value]? = some entry ∧ GoodEntry entry ∧
      ctx.parameters = entry.initialized.parameters ∧ borrowed.root = output.1.data.source.2.get := by
  obtain ⟨original,selected,before,parameters,root⟩ := StoredGoldRegistryAssociation.extraction_decoded_original
    registry parent world initialized executed sources decoded index history included input dummy ctx radius output accepted key truthful safe
  obtain ⟨borrowed,cell,entry,atBorrow,member,origin,address,atEntry,good,same⟩ :=
    NativeGoldPointerRegistry.registry_slot entries reachable heap borrows registry retained original
  refine ⟨original,borrowed,cell,entry,selected,before,atBorrow,member,origin,address,atEntry,good,?_,?_⟩
  · simpa only [same] using parameters
  · simpa only [same] using root

theorem extracted_code_meaning (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (heap : List (Cell ℕ)) (borrows : Vector Borrow) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldPointerRegistry.registry entries heap borrows = some registry)
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
  obtain ⟨_,_,_,entry,_,_,_,_,_,_,_,good,parameters,_⟩ := extraction_original entries reachable heap borrows registry retained
    parent world initialized executed sources decoded index history included input dummy ctx radius output accepted key truthful safe
  rw [parameters]
  exact ⟨NativeGoldParameterInitialization.code_primitive entry.header entry.request entry.config good.1 entry.initialized good.2,
    entry.initialized.geometry,NativeGoldParameterInitialization.parameter_geometry entry.header entry.config entry.initialized good.2⟩

end
end FormalProof4FHE.HasteBoots.NativeGoldPointerAssociation
