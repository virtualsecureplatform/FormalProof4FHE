module
public import FormalProof4FHE.HasteBoots.NativeGoldParameterInitialization
public import FormalProof4FHE.HasteBoots.NativeSourceRegistry
@[expose] public section

/-! Logical immutable parameter allocations and borrowed registry references.
Allocation records actual constructor/parameter outcomes once; registry aliases
read the retained object instead of rebuilding it. Every original reference is
kept in order, including duplicates and unused entries. Logical handles are not
a Rust pointer/heap refinement; physical allocation and source linking remain
separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldParameterStore
open NativeGoldBlockCodeProgram (Request Config)
open NativeGoldEncodedParameters (Header Initialized)
open NativeSharedLookupParent (Oracle)

structure Entry where
  request : Request
  header : Header
  config : Config
  initialized : Initialized

structure Allocation where
  handle : ℕ
  entries : List Entry

def allocate (before : List Entry) (request : Request) (header : Header) (config : Config) :
    Option (Except NativeGoldEncodedParameters.Error Allocation) :=
  (NativeGoldParameterInitialization.finish header config).map (fun result => result.map (fun initialized =>
    ⟨before.length,before++[⟨request,header,config,initialized⟩]⟩))

theorem allocate_post (before : List Entry) (request : Request) (header : Header) (config : Config) (after : Allocation)
    (executed : allocate before request header config = some (.ok after)) :
    ∃ initialized, NativeGoldParameterInitialization.finish header config = some (.ok initialized) ∧
      after.handle = before.length ∧ after.entries = before++[⟨request,header,config,initialized⟩] := by
  unfold allocate at executed
  cases finished : NativeGoldParameterInitialization.finish header config with
  | none => simp only [finished,Option.map_none] at executed; cases executed
  | some result =>
    cases result with
    | error error => simp only [finished,Option.map_some] at executed; cases executed
    | ok initialized =>
      simp only [finished,Option.map_some] at executed
      cases executed
      exact ⟨initialized,rfl,rfl,rfl⟩

def GoodEntry (entry : Entry) : Prop :=
  NativeGoldBlockCodeProgram.Reachable entry.request entry.config ∧
    NativeGoldParameterInitialization.finish entry.header entry.config = some (.ok entry.initialized)

inductive Reachable : List Entry → Prop where
  | empty : Reachable []
  | allocate (before : List Entry) (request : Request) (header : Header) (config : Config) (after : Allocation)
      (prior : Reachable before) (constructed : NativeGoldBlockCodeProgram.Reachable request config)
      (executed : allocate before request header config = some (.ok after)) : Reachable after.entries

theorem reachable_good (entries : List Entry) (reachable : Reachable entries) : ∀ entry ∈ entries, GoodEntry entry := by
  induction reachable with
  | empty => simp
  | allocate before request header config after prior constructed executed ih =>
    obtain ⟨initialized,finished,_,shape⟩ := allocate_post before request header config after executed
    rw [shape]
    intro entry member
    rcases List.mem_append.mp member with earlier | added
    · exact ih entry earlier
    · have same := List.mem_singleton.mp added
      cases same
      exact ⟨constructed,finished⟩

structure Reference where
  handle : ℕ
  root : NativeRootMessage.Digest

def collect (entries : List Entry) : List Reference → Option (List (Oracle NativeGoldBlockCode.Stored))
  | [] => some []
  | reference::tail =>
    match entries[reference.handle]? with
    | none => none
    | some entry => (collect entries tail).map (fun rest => ⟨entry.initialized.parameters,reference.root⟩::rest)

theorem collect_length (entries : List Entry) (references : List Reference) (registry : List (Oracle NativeGoldBlockCode.Stored))
    (executed : collect entries references = some registry) : registry.length = references.length := by
  induction references generalizing registry with
  | nil => cases executed; rfl
  | cons reference tail ih =>
    simp only [collect] at executed
    cases found : entries[reference.handle]? with
    | none => simp only [found] at executed; cases executed
    | some entry =>
      simp only [found] at executed
      cases rest : collect entries tail with
      | none => simp only [rest,Option.map_none] at executed; cases executed
      | some output =>
        simp only [rest,Option.map_some] at executed
        cases executed
        simpa only [List.length_cons] using congrArg Nat.succ (ih output rest)

theorem collect_slot (entries : List Entry) (references : List Reference) (registry : List (Oracle NativeGoldBlockCode.Stored))
    (executed : collect entries references = some registry) (index : ℕ) (bound : index < references.length) :
    ∃ reference entry, references[index]? = some reference ∧ entries[reference.handle]? = some entry ∧
      registry[index]? = some ⟨entry.initialized.parameters,reference.root⟩ := by
  induction references generalizing registry index with
  | nil => cases bound
  | cons reference tail ih =>
    simp only [collect] at executed
    cases found : entries[reference.handle]? with
    | none => simp only [found] at executed; cases executed
    | some entry =>
      simp only [found] at executed
      cases rest : collect entries tail with
      | none => simp only [rest,Option.map_none] at executed; cases executed
      | some output =>
        simp only [rest,Option.map_some] at executed
        cases executed
        cases index with
        | zero => exact ⟨reference,entry,rfl,found,rfl⟩
        | succ index =>
          obtain ⟨selected,stored,atReference,atEntry,atOracle⟩ := ih output rest index (by simpa using bound)
          exact ⟨selected,stored,atReference,atEntry,atOracle⟩

def registry (entries : List Entry) (references : NativePrefixCodec.Vector Reference) :
    Option (NativePrefixCodec.Vector (Oracle NativeGoldBlockCode.Stored)) :=
  match executed : collect entries references.val with
  | none => none
  | some output => some ⟨output,by rw [collect_length entries references.val output executed]; exact references.property⟩

theorem registry_values (entries : List Entry) (references : NativePrefixCodec.Vector Reference)
    (output : NativePrefixCodec.Vector (Oracle NativeGoldBlockCode.Stored)) (executed : registry entries references = some output) :
    collect entries references.val = some output.val ∧ output.val.length = references.val.length := by
  unfold registry at executed
  split at executed
  · cases executed
  · rename_i values collected
    cases executed
    exact ⟨collected,collect_length entries references.val values collected⟩

theorem registry_slot (entries : List Entry) (reachable : Reachable entries) (references : NativePrefixCodec.Vector Reference)
    (output : NativePrefixCodec.Vector (Oracle NativeGoldBlockCode.Stored)) (executed : registry entries references = some output)
    (index : Fin output.val.length) :
    ∃ reference entry, references.val[index.val]? = some reference ∧ entries[reference.handle]? = some entry ∧
      GoodEntry entry ∧ output.val.get index = ⟨entry.initialized.parameters,reference.root⟩ := by
  have values := registry_values entries references output executed
  obtain ⟨reference,entry,selected,stored,source⟩ := collect_slot entries references.val output.val values.1 index.val (by rw [← values.2]; exact index.isLt)
  have member : entry ∈ entries := List.mem_of_getElem? stored
  have oracle := Option.some.inj ((List.getElem?_eq_getElem index.isLt).symm.trans source)
  exact ⟨reference,entry,selected,stored,reachable_good entries reachable entry member,oracle⟩

theorem registry_code_primitive (entries : List Entry) (reachable : Reachable entries) (references : NativePrefixCodec.Vector Reference)
    (output : NativePrefixCodec.Vector (Oracle NativeGoldBlockCode.Stored)) (executed : registry entries references = some output)
    (index : Fin output.val.length) :
    IsPrimitiveRoot (NativeFieldRepresentation.goldValue (output.val.get index).parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize (output.val.get index).parameters.code+1)) := by
  obtain ⟨reference,entry,_,_,good,same⟩ := registry_slot entries reachable references output executed index
  rw [same]
  exact NativeGoldParameterInitialization.code_primitive entry.header entry.request entry.config good.1 entry.initialized good.2

theorem registry_geometry (entries : List Entry) (reachable : Reachable entries) (references : NativePrefixCodec.Vector Reference)
    (output : NativePrefixCodec.Vector (Oracle NativeGoldBlockCode.Stored)) (executed : registry entries references = some output)
    (index : Fin output.val.length) :
    ∃ geometry, NativeBrakedownParameters.build NativeGoldBlockCode.description (output.val.get index).parameters = some geometry := by
  obtain ⟨reference,entry,_,_,good,same⟩ := registry_slot entries reachable references output executed index
  rw [same]
  exact ⟨entry.initialized.geometry,NativeGoldParameterInitialization.parameter_geometry entry.header entry.config entry.initialized good.2⟩

end FormalProof4FHE.HasteBoots.NativeGoldParameterStore
