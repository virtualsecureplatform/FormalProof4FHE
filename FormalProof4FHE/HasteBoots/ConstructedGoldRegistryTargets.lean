module
public import FormalProof4FHE.HasteBoots.ConstructedGoldTargets
@[expose] public section

/-! Calibration admission is tracked separately from the generic native
parameter constructor. Original registry references, including aliases and
unused positions, retain their constructor and checked policy provenance.
This is a logical arena/registry connection, not a Rust heap refinement. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldRegistryTargets
open ConstructedGoldTargets (admitted target)
open NativeGoldParameterStore (Entry Reference GoodEntry)
open NativeGoldBlockCodeProgram (Request Config)
open NativeGoldEncodedParameters (Header)
open NativeGoldBatchPcsProgram (Context)
open NativeBrakedownCalibration (Role)
open NativePrefixCodec (Vector)
noncomputable section

def classify (request : Request) (header : Header) : Option Role :=
  if admitted .source request header then some .source else
  if admitted .helper request header then some .helper else
  if admitted .finalSource request header then some .finalSource else
  if admitted .finalHelper request header then some .finalHelper else none

theorem classify_sound (request : Request) (header : Header) (role : Role)
    (accepted : classify request header = some role) : admitted role request header = true := by
  unfold classify at accepted
  split at accepted
  · rename_i passed
    cases accepted
    exact passed
  · split at accepted
    · rename_i passed
      cases accepted
      exact passed
    · split at accepted
      · rename_i passed
        cases accepted
        exact passed
      · split at accepted
        · rename_i passed
          cases accepted
          exact passed
        · cases accepted

def Approved (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, ∃ role, classify entry.request entry.header = some role

theorem approved_empty : Approved [] := by intro entry member; cases member

/-- Successful allocation retains the admitted request/header rather than
substituting another object or recalculating parameters for registry aliases. -/
theorem approved_allocate (before : List Entry) (approved : Approved before)
    (request : Request) (header : Header) (config : Config) (role : Role)
    (accepted : classify request header = some role) (after : NativeGoldParameterStore.Allocation)
    (executed : NativeGoldParameterStore.allocate before request header config = some (.ok after)) : Approved after.entries := by
  obtain ⟨initialized, _, _, shape⟩ := NativeGoldParameterStore.allocate_post before request header config after executed
  rw [shape]
  intro entry member
  rcases List.mem_append.mp member with earlier | added
  · exact approved entry earlier
  · have same := List.mem_singleton.mp added
    subst entry
    exact ⟨role, accepted⟩

/-- Trusted-configuration evidence accompanies the same native allocation
receipts. The generic allocator itself does not execute this classifier. -/
inductive Configured : List Entry → Prop where
  | empty : Configured []
  | allocate (before : List Entry) (request : Request) (header : Header) (config : Config)
      (role : Role) (after : NativeGoldParameterStore.Allocation)
      (prior : Configured before) (constructed : NativeGoldBlockCodeProgram.Reachable request config)
      (accepted : classify request header = some role)
      (executed : NativeGoldParameterStore.allocate before request header config = some (.ok after)) : Configured after.entries

theorem configured_reachable (entries : List Entry) (configured : Configured entries) :
    NativeGoldParameterStore.Reachable entries := by
  induction configured with
  | empty => exact .empty
  | allocate before request header config role after prior constructed accepted executed ih =>
    exact .allocate before request header config after ih constructed executed

theorem configured_approved (entries : List Entry) (configured : Configured entries) : Approved entries := by
  induction configured with
  | empty => exact approved_empty
  | allocate before request header config role after prior constructed accepted executed ih =>
    exact approved_allocate before ih request header config role accepted after executed

def checkReferences (entries : List Entry) : List Reference → Bool
  | [] => true
  | reference::rest => match entries[reference.handle]? with
    | none => false
    | some entry => (classify entry.request entry.header).isSome && checkReferences entries rest

theorem checked_reference (entries : List Entry) (references : List Reference)
    (checked : checkReferences entries references = true) (reference : Reference) (member : reference ∈ references) :
    ∃ entry role, entries[reference.handle]? = some entry ∧ classify entry.request entry.header = some role := by
  induction references with
  | nil => cases member
  | cons head rest ih =>
    cases found : entries[head.handle]? with
    | none => simp only [checkReferences, found, Bool.false_eq_true] at checked
    | some entry =>
      have parts : (classify entry.request entry.header).isSome = true ∧ checkReferences entries rest = true := by
        simpa only [checkReferences, found, Bool.and_eq_true] using checked
      rcases List.mem_cons.mp member with same | later
      · subst reference
        cases classified : classify entry.request entry.header with
        | none =>
          have impossible := parts.1
          simp only [classified, Option.isSome_none, Bool.false_eq_true] at impossible
        | some role => exact ⟨entry, role, found, classified⟩
      · exact ih parts.2 later

structure Binding (entries : List Entry) (references : Vector Reference) (ctx : Context) where
  original : ℕ
  reference : Reference
  entry : Entry
  atReference : references.val[original]? = some reference
  atEntry : entries[reference.handle]? = some entry
  good : GoodEntry entry
  role : Role
  classified : classify entry.request entry.header = some role
  parameters : ctx.parameters = entry.initialized.parameters

def Binding.target {entries : List Entry} {references : Vector Reference} {ctx : Context}
    (bound : Binding entries references ctx) : PrivateCoinExecutableSoundness.Target :=
  ConstructedGoldTargets.target bound.entry bound.good bound.role (classify_sound _ _ _ bound.classified) ctx bound.parameters

theorem registry_binding (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (approved : Approved entries) (references : Vector Reference)
    (registry : Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldParameterStore.registry entries references = some registry)
    (index : Fin registry.val.length) (ctx : Context) (same : ctx.parameters = (registry.val.get index).parameters) :
    ∃ bound : Binding entries references ctx, bound.original = index.val := by
  obtain ⟨reference, entry, atReference, atEntry, good, source⟩ :=
    NativeGoldParameterStore.registry_slot entries reachable references registry retained index
  obtain ⟨role, classified⟩ := approved entry (List.mem_of_getElem? atEntry)
  refine ⟨⟨index.val, reference, entry, atReference, atEntry, good, role, classified, ?_⟩, rfl⟩
  rw [same, source]

theorem checked_registry_binding (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (checked : checkReferences entries references.val = true)
    (registry : Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldParameterStore.registry entries references = some registry)
    (index : Fin registry.val.length) (ctx : Context) (same : ctx.parameters = (registry.val.get index).parameters) :
    ∃ bound : Binding entries references ctx, bound.original = index.val := by
  obtain ⟨reference, entry, atReference, atEntry, good, source⟩ :=
    NativeGoldParameterStore.registry_slot entries reachable references registry retained index
  obtain ⟨selected, role, found, classified⟩ := checked_reference entries references.val checked reference (List.mem_of_getElem? atReference)
  have sameEntry : selected = entry := Option.some.inj (found.symm.trans atEntry)
  subst selected
  refine ⟨⟨index.val, reference, entry, atReference, atEntry, good, role, classified, ?_⟩, rfl⟩
  rw [same, source]

/-- A successful public extraction selects its original stored object. Policy
and constructor evidence follow that owner, including repeated registry slots. -/
theorem extraction_binding (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (approved : Approved entries) (references : Vector Reference)
    (registry : Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldParameterStore.registry entries references = some registry)
    (parent : NativeTranscript.Transcript) (world : InputIndexedOracle.World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (sources : StoredSourceVectorReadCost.Sources)
    (decoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length) (history : List NativeTranscript.Observation)
    (included : (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2.Sublist history)
    (input : InputIndexedOracle.Input) (dummy : Vector InputIndexedOracle.Byte 64) (ctx : Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index) (truthful : ObservationReplay.Agrees world history)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history) :
    ∃ bound : Binding entries references ctx,
      (StoredRegistryOwnerCost.owner sources index).value = some bound.original ∧
      bound.original ≤ index.val ∧ bound.reference.root = output.1.data.source.2.get := by
  obtain ⟨original, reference, entry, owner, before, atReference, atEntry, good, parameters, root⟩ :=
    NativeGoldConstructedRegistry.extraction_original entries reachable references registry retained parent world initialized executed
      sources decoded index history included input dummy ctx radius output accepted key truthful safe
  obtain ⟨role, classified⟩ := approved entry (List.mem_of_getElem? atEntry)
  exact ⟨⟨original.val, reference, entry, atReference, atEntry, good, role, classified, parameters⟩, owner, before, root⟩
/-- This version admits arbitrary other arena objects. Every original
registered reference is checked, including duplicates and unused positions. -/
theorem checked_extraction_binding (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (checked : checkReferences entries references.val = true)
    (registry : Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (retained : NativeGoldParameterStore.registry entries references = some registry)
    (parent : NativeTranscript.Transcript) (world : InputIndexedOracle.World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (sources : StoredSourceVectorReadCost.Sources)
    (decoded : (StoredSourceVectorCost.decode (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources)).value = some sources)
    (index : Fin sources.val.length) (history : List NativeTranscript.Observation)
    (included : (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2.Sublist history)
    (input : InputIndexedOracle.Input) (dummy : Vector InputIndexedOracle.Byte 64) (ctx : Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index) (truthful : ObservationReplay.Agrees world history)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history) :
    ∃ bound : Binding entries references ctx,
      (StoredRegistryOwnerCost.owner sources index).value = some bound.original ∧
      bound.original ≤ index.val ∧ bound.reference.root = output.1.data.source.2.get := by
  obtain ⟨original, reference, entry, owner, before, atReference, atEntry, good, parameters, root⟩ :=
    NativeGoldConstructedRegistry.extraction_original entries reachable references registry retained parent world initialized executed
      sources decoded index history included input dummy ctx radius output accepted key truthful safe
  obtain ⟨selected, role, found, classified⟩ := checked_reference entries references.val checked reference (List.mem_of_getElem? atReference)
  have sameEntry : selected = entry := Option.some.inj (found.symm.trans atEntry)
  subst selected
  exact ⟨⟨original.val, reference, entry, atReference, atEntry, good, role, classified, parameters⟩, owner, before, root⟩

end
end FormalProof4FHE.HasteBoots.ConstructedGoldRegistryTargets
