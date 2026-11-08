/-! Simulation of immutable parameter reads from a whole-heap representation.
The relation is independent of the registry and applies to every pointer. It
must still be established by Rust allocation/borrow/source refinement; the
materializer is an operational specification, not new native verifier code. -/
namespace HasteBootsExtractedRegistryHeap
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open NativePointerStorage (Cell Pointer)
open NativeGoldParameterStore (Entry Reference GoodEntry)
open HasteBootsExtractedParametersProof (Params)
open HasteBootsExtractedParametersDecode (decodeParameters)
open HasteBootsExtractedRegistryDecode (Source Model decode root)
open HasteBootsExtractedRegistryProof (Digest)
open NativePrefixCodec (Vector)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (World Input)
open OracleProgram (run)
open formalproof4fhe_native_registry_fixture (registry_get)

abbrev Commitment := formalproof4fhe_native_registry_fixture.pcs.matrix_weighted.Commitment Digest

structure Borrow where
  pointer : Pointer
  commitment : Commitment

def modelBorrow (borrowed : Borrow) : NativeGoldPointerRegistry.Borrow :=
  ⟨borrowed.pointer,root borrowed.commitment.root⟩

def CellRep (entries : List Entry) (actual : Cell Params) (model : Cell ℕ) : Prop :=
  actual.origin = model.origin ∧ actual.address = model.address ∧
    ∃ entry, entries[model.value]? = some entry ∧
      decodeParameters actual.value = some entry.initialized.parameters

def HeapRep (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ)) : Prop :=
  List.Forall₂ (CellRep entries) actual model

theorem heap_rep_empty (entries : List Entry) : HeapRep entries [] [] := .nil

theorem heap_rep_append (entries last : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) : HeapRep (entries++last) actual model := by
  induction represented with
  | nil => exact .nil
  | @cons actualCell modelCell actualTail modelTail related remaining ih =>
    obtain ⟨origin,address,entry,stored,decoded⟩ := related
    have bound : modelCell.value < entries.length := by
      by_contra outside
      have absent : entries[modelCell.value]? = none := List.getElem?_eq_none (by omega)
      rw [absent] at stored
      cases stored
    exact .cons ⟨origin,address,entry,(List.getElem?_append_left bound).trans stored,decoded⟩ ih

theorem heap_rep_extend (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (cell : Cell Params) (entry : Entry)
    (decoded : decodeParameters cell.value = some entry.initialized.parameters) :
    HeapRep (entries++[entry]) (cell::actual)
      (⟨cell.origin,cell.address,cell.nonzero,entries.length⟩::model) := by
  apply List.Forall₂.cons
  · refine ⟨rfl,rfl,entry,?_,decoded⟩
    simp
  · exact heap_rep_append entries [entry] actual model represented

theorem heap_rep_retire (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (origin : NativePointerStorage.Origin) :
    HeapRep entries (NativePointerStorage.retire actual origin) (NativePointerStorage.retire model origin) := by
  change List.Forall₂ (CellRep entries) (NativePointerStorage.retire actual origin) (NativePointerStorage.retire model origin)
  induction represented with
  | nil => exact .nil
  | @cons actualCell modelCell actualTail modelTail related remaining ih =>
    by_cases retired : actualCell.origin = origin
    · simpa only [NativePointerStorage.retire,← related.1,retired,ite_true] using ih
    · simpa only [NativePointerStorage.retire,← related.1,retired,ite_false] using List.Forall₂.cons related ih

theorem read_simulation (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (pointer : Pointer) (parameters : Params)
    (executed : NativePointerStorage.read actual pointer = some parameters) :
    ∃ handle entry, NativePointerStorage.read model pointer = some handle ∧ entries[handle]? = some entry ∧
      decodeParameters parameters = some entry.initialized.parameters := by
  induction represented with
  | nil => cases executed
  | @cons actualCell modelCell actualTail modelTail related remaining ih =>
    obtain ⟨origin,address,entry,stored,decoded⟩ := related
    by_cases matched : pointer.provenance = some actualCell.origin ∧ pointer.address = actualCell.address
    · rw [NativePointerStorage.read,ite_eq_left matched] at executed
      cases executed
      have modelMatched : pointer.provenance = some modelCell.origin ∧ pointer.address = modelCell.address :=
        ⟨matched.1.trans (congrArg some origin),matched.2.trans address⟩
      exact ⟨modelCell.value,entry,by rw [NativePointerStorage.read,ite_eq_left modelMatched],stored,decoded⟩
    · have later : NativePointerStorage.read actualTail pointer = some parameters := by simpa only [NativePointerStorage.read,matched,ite_false] using executed
      obtain ⟨handle,selected,found,atEntry,parametersDecoded⟩ := ih later
      exact ⟨handle,selected,by simpa only [NativePointerStorage.read,← origin,← address,matched,ite_false] using found,atEntry,parametersDecoded⟩

theorem read_failure_iff (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (pointer : Pointer) :
    NativePointerStorage.read actual pointer = none ↔ NativePointerStorage.read model pointer = none := by
  induction represented with
  | nil => simp [NativePointerStorage.read]
  | @cons actualCell modelCell actualTail modelTail related remaining ih =>
    simp only [NativePointerStorage.read,← related.1,← related.2.1]
    split <;> simp_all

def materialize (heap : List (Cell Params)) : List Borrow → Option (List Source)
  | [] => some []
  | borrowed::tail =>
    match NativePointerStorage.read heap borrowed.pointer with
    | none => none
    | some parameters => (materialize heap tail).map (fun rest => ⟨parameters,borrowed.commitment⟩::rest)

theorem materialize_failure_witness (actual : List (Cell Params)) (borrows : List Borrow) :
    materialize actual borrows = none ↔
      ∃ borrowed ∈ borrows, NativePointerStorage.read actual borrowed.pointer = none := by
  induction borrows with
  | nil => simp [materialize]
  | cons borrowed tail ih =>
    cases found : NativePointerStorage.read actual borrowed.pointer with
    | none =>
      constructor
      · intro _
        exact ⟨borrowed,List.mem_cons_self,found⟩
      · intro _
        simp only [materialize,found]
    | some parameters =>
      constructor
      · intro failed
        have restFailure : materialize actual tail = none := by
          cases rest : materialize actual tail with
          | none => rfl
          | some output => simp only [materialize,found,rest,Option.map_some] at failed; cases failed
        obtain ⟨selected,member,unreadable⟩ := ih.mp restFailure
        exact ⟨selected,List.mem_cons_of_mem borrowed member,unreadable⟩
      · rintro ⟨selected,member,unreadable⟩
        rcases List.mem_cons.mp member with same | later
        · subst selected
          rw [found] at unreadable
          cases unreadable
        · have restFailure := ih.mpr ⟨selected,later,unreadable⟩
          simp only [materialize,found,restFailure,Option.map_none]

theorem materialize_failure_iff (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (borrows : List Borrow) :
    materialize actual borrows = none ↔
      NativeGoldPointerRegistry.resolve model (borrows.map modelBorrow) = none := by
  induction borrows with
  | nil => simp only [materialize,List.map_nil,NativeGoldPointerRegistry.resolve,reduceCtorEq]
  | cons borrowed tail ih =>
    have same := read_failure_iff entries actual model represented borrowed.pointer
    cases nativeRead : NativePointerStorage.read actual borrowed.pointer with
    | none =>
      have modelRead := same.mp nativeRead
      simp only [materialize,nativeRead,List.map_cons,NativeGoldPointerRegistry.resolve,modelBorrow,modelRead]
    | some parameters =>
      cases modelRead : NativePointerStorage.read model borrowed.pointer with
      | none =>
        have impossible := same.mpr modelRead
        rw [nativeRead] at impossible
        cases impossible
      | some handle =>
        simp only [materialize,nativeRead,List.map_cons,NativeGoldPointerRegistry.resolve,modelBorrow,modelRead]
        cases nativeRest : materialize actual tail <;> cases modelRest : NativeGoldPointerRegistry.resolve model (tail.map modelBorrow) <;> simp_all

theorem collect_simulation (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (borrows : List Borrow) (sources : List Source)
    (executed : materialize actual borrows = some sources) :
    ∃ references, NativeGoldPointerRegistry.resolve model (borrows.map modelBorrow) = some references ∧
      NativeGoldParameterStore.collect entries references = HasteBootsExtractedRegistry.collect sources := by
  induction borrows generalizing sources with
  | nil => cases executed; exact ⟨[],rfl,rfl⟩
  | cons borrowed tail ih =>
    simp only [materialize] at executed
    cases found : NativePointerStorage.read actual borrowed.pointer with
    | none => simp only [found] at executed; cases executed
    | some parameters =>
      simp only [found] at executed
      cases rest : materialize actual tail with
      | none => simp only [rest,Option.map_none] at executed; cases executed
      | some output =>
        simp only [rest,Option.map_some] at executed
        cases executed
        obtain ⟨handle,entry,modelRead,atEntry,parametersDecoded⟩ := read_simulation entries actual model represented borrowed.pointer parameters found
        obtain ⟨references,resolved,collected⟩ := ih output rest
        refine ⟨⟨handle,root borrowed.commitment.root⟩::references,?_,?_⟩
        · simp only [List.map_cons,NativeGoldPointerRegistry.resolve,modelBorrow,modelRead,resolved,Option.map_some]
        · simp only [NativeGoldParameterStore.collect,atEntry,HasteBootsExtractedRegistry.collect,
            decode,parametersDecoded,Option.map_some,Option.bind_some,collected]

theorem materialized_decodes (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (borrows : List Borrow) (sources : List Source)
    (executed : materialize actual borrows = some sources) :
    ∃ models, HasteBootsExtractedRegistry.collect sources = some models := by
  induction borrows generalizing sources with
  | nil => cases executed; exact ⟨[],rfl⟩
  | cons borrowed tail ih =>
    simp only [materialize] at executed
    cases found : NativePointerStorage.read actual borrowed.pointer with
    | none => simp only [found] at executed; cases executed
    | some parameters =>
      simp only [found] at executed
      cases rest : materialize actual tail with
      | none => simp only [rest,Option.map_none] at executed; cases executed
      | some output =>
        simp only [rest,Option.map_some] at executed
        cases executed
        obtain ⟨_,entry,_,_,parametersDecoded⟩ := read_simulation entries actual model represented borrowed.pointer parameters found
        obtain ⟨models,collected⟩ := ih output rest
        exact ⟨⟨entry.initialized.parameters,root borrowed.commitment.root⟩::models,by
          simp only [HasteBootsExtractedRegistry.collect,decode,parametersDecoded,Option.map_some,Option.bind_some,collected]⟩

def modelBorrows (borrows : NativePrefixCodec.Vector Borrow) :
    NativePrefixCodec.Vector NativeGoldPointerRegistry.Borrow :=
  ⟨borrows.val.map modelBorrow,by simpa only [List.length_map] using borrows.property⟩

theorem registry_failure_iff (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (borrows : Vector Borrow) :
    NativeGoldPointerRegistry.registry entries model (modelBorrows borrows) = none ↔
      materialize actual borrows.val = none := by
  constructor
  · intro failed
    cases native : materialize actual borrows.val with
    | none => rfl
    | some sources =>
      obtain ⟨references,resolved,collected⟩ := collect_simulation entries actual model represented borrows.val sources native
      obtain ⟨decodedValues,decodedCollection⟩ := materialized_decodes entries actual model represented borrows.val sources native
      have projected : NativeGoldPointerRegistry.resolve model (modelBorrows borrows).val = some references := resolved
      unfold NativeGoldPointerRegistry.registry at failed
      cases retained : NativeGoldPointerRegistry.references model (modelBorrows borrows) with
      | none =>
        unfold NativeGoldPointerRegistry.references at retained
        split at retained
        · rename_i rejected
          cases rejected.symm.trans projected
        · cases retained
      | some retainedReferences =>
        have kept := NativeGoldPointerRegistry.references_values model (modelBorrows borrows) retainedReferences retained
        have same : references = retainedReferences.val := Option.some.inj (projected.symm.trans kept.1)
        have successfulCollect : NativeGoldParameterStore.collect entries retainedReferences.val = some decodedValues := by
          simpa only [same] using collected.trans decodedCollection
        simp only [retained,Option.bind_some] at failed
        unfold NativeGoldParameterStore.registry at failed
        split at failed
        · rename_i rejected
          cases rejected.symm.trans successfulCollect
        · cases failed
  · intro failed
    cases executed : NativeGoldPointerRegistry.registry entries model (modelBorrows borrows) with
    | none => rfl
    | some output =>
      obtain ⟨references,resolved,_⟩ := NativeGoldPointerRegistry.registry_resolves entries model (modelBorrows borrows) output executed
      have accepted := (NativeGoldPointerRegistry.references_values model (modelBorrows borrows) references resolved).1
      have rejected : NativeGoldPointerRegistry.resolve model (modelBorrows borrows).val = none :=
        (materialize_failure_iff entries actual model represented borrows.val).mp failed
      rw [rejected] at accepted
      cases accepted

theorem registry_simulation (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (borrows : NativePrefixCodec.Vector Borrow)
    (source : Slice Source) (materialized : materialize actual borrows.val = some source.val)
    (models : NativePrefixCodec.Vector Model) (decoded : HasteBootsExtractedRegistry.registry source = some models) :
    NativeGoldPointerRegistry.registry entries model (modelBorrows borrows) = some models := by
  obtain ⟨references,resolved,collected⟩ := collect_simulation entries actual model represented borrows.val source.val materialized
  have collectedModel : NativeGoldParameterStore.collect entries references = some models.val :=
    collected.trans (HasteBootsExtractedRegistry.registry_values source models decoded)
  have bounded : references.length < 2^64 := by
    rw [NativeGoldPointerRegistry.resolve_length model (borrows.val.map modelBorrow) references resolved,List.length_map]
    exact borrows.property
  let resolvedVector : NativePrefixCodec.Vector Reference := ⟨references,bounded⟩
  have resolvedRun : NativeGoldPointerRegistry.references model (modelBorrows borrows) = some resolvedVector := by
    have known : NativeGoldPointerRegistry.resolve model (modelBorrows borrows).val = some references := resolved
    unfold NativeGoldPointerRegistry.references
    split
    · rename_i absent
      cases absent.symm.trans known
    · rename_i values selected
      have same : values = references := Option.some.inj (selected.symm.trans known)
      subst values
      rfl
  have retained : NativeGoldParameterStore.registry entries resolvedVector = some models := by
    have known : NativeGoldParameterStore.collect entries resolvedVector.val = some models.val := collectedModel
    unfold NativeGoldParameterStore.registry
    split
    · rename_i absent
      cases absent.symm.trans known
    · rename_i values selected
      have same : values = models.val := Option.some.inj (selected.symm.trans known)
      subst values
      rfl
  simpa only [NativeGoldPointerRegistry.registry,resolvedRun,Option.bind_some] using retained

theorem materialized_registries (entries : List Entry) (actual : List (Cell Params)) (model : List (Cell ℕ))
    (represented : HeapRep entries actual model) (borrows : Vector Borrow) (source : Slice Source)
    (materialized : materialize actual borrows.val = some source.val) :
    ∃ models, HasteBootsExtractedRegistry.registry source = some models ∧
      NativeGoldPointerRegistry.registry entries model (modelBorrows borrows) = some models := by
  obtain ⟨values,collected⟩ := materialized_decodes entries actual model represented borrows.val source.val materialized
  cases decoded : HasteBootsExtractedRegistry.registry source with
  | none =>
    unfold HasteBootsExtractedRegistry.registry at decoded
    split at decoded
    · rename_i absent
      cases absent.symm.trans collected
    · cases decoded
  | some models => exact ⟨models,rfl,registry_simulation entries actual model represented borrows source materialized models decoded⟩

theorem initialized_original (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (actualHeap : List (Cell Params)) (modelHeap : List (Cell ℕ))
    (represented : HeapRep entries actualHeap modelHeap) (borrows : Vector Borrow) (source : Slice Source)
    (models : Vector Model) (decoded : HasteBootsExtractedRegistry.registry source = some models)
    (materialized : materialize actualHeap borrows.val = some source.val)
    (parent : Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.1 = some initialized)
    (position : Fin initialized.sources.val.length) :
    ∃ (original : Fin models.val.length) (word : Usize) (actual : Source) (borrowed : NativeGoldPointerRegistry.Borrow) (cell : Cell ℕ) (entry : Entry),
      original.val = (NativeSourceRegistry.owner initialized.sources position).val ∧ original.val ≤ position.val ∧
      word.val = original.val ∧ registry_get source word = .ok (some (actual.parameters,actual.commitment.root)) ∧
      (modelBorrows borrows).val[original.val]? = some borrowed ∧ cell ∈ modelHeap ∧
      borrowed.pointer.provenance = some cell.origin ∧ borrowed.pointer.address = cell.address ∧
      entries[cell.value]? = some entry ∧ GoodEntry entry ∧
      decodeParameters actual.parameters = some entry.initialized.parameters ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row entry.initialized.parameters) world).run.1 =
        some (initialized.sources.val.get position).1 ∧
      root actual.commitment.root = (initialized.sources.val.get position).2 ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row entry.initialized.parameters) world).run.2.Sublist
        (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.2 := by
  exact HasteBootsExtractedRegistryPointer.initialized_original entries reachable modelHeap (modelBorrows borrows) source models decoded
    (registry_simulation entries actualHeap modelHeap represented borrows source materialized models decoded)
    parent world initialized executed position

theorem extraction_original (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (actualHeap : List (Cell Params)) (modelHeap : List (Cell ℕ))
    (represented : HeapRep entries actualHeap modelHeap) (borrows : Vector Borrow) (source : Slice Source)
    (models : Vector Model) (decoded : HasteBootsExtractedRegistry.registry source = some models)
    (materialized : materialize actualHeap borrows.val = some source.val)
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
    ∃ (original : Fin models.val.length) (word : Usize) (actual : Source) (borrowed : NativeGoldPointerRegistry.Borrow) (cell : Cell ℕ) (entry : Entry),
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧ original.val ≤ index.val ∧
      word.val = original.val ∧ registry_get source word = .ok (some (actual.parameters,actual.commitment.root)) ∧
      (modelBorrows borrows).val[original.val]? = some borrowed ∧ cell ∈ modelHeap ∧
      borrowed.pointer.provenance = some cell.origin ∧ borrowed.pointer.address = cell.address ∧
      entries[cell.value]? = some entry ∧ GoodEntry entry ∧
      ctx.parameters = entry.initialized.parameters ∧ decodeParameters actual.parameters = some ctx.parameters ∧
      root actual.commitment.root = output.1.data.source.2.get := by
  exact HasteBootsExtractedRegistryPointer.extraction_original entries reachable modelHeap (modelBorrows borrows) source models decoded
    (registry_simulation entries actualHeap modelHeap represented borrows source materialized models decoded)
    parent world initialized executed sources storedDecoded index history included input dummy ctx radius output accepted key truthful safe

end HasteBootsExtractedRegistryHeap
