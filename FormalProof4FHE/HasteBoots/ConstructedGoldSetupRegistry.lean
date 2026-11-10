module
public import FormalProof4FHE.HasteBoots.ConstructedGoldObjectSetup
@[expose] public section

/-! Derive registry reachability/admission from successful setup and collection
receipts. The registry is the actual collected vector, including aliases and
unused positions. Native descriptor/heap/dispatch refinement and full PBS
coverage remain separate; trusted security admission is explicit. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldSetupRegistry
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open ConstructedGoldRegistryTargets (Approved Configured classify checkReferences configured_approved configured_reachable)
open ConstructedGoldObjectSetup (Job allocate)
open ConstructedGoldRegisteredSecurity (Registry)
open InputIndexedOracle (Input law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

theorem collected_checked (entries : List Entry) (approved : Approved entries) (references : List Reference)
    (registry : List (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.collect entries references = some registry) :
    checkReferences entries references = true := by
  induction references generalizing registry with
  | nil => rfl
  | cons reference rest ih =>
    cases found : entries[reference.handle]? with
    | none => simp only [NativeGoldParameterStore.collect, found] at collected; cases collected
    | some entry =>
      obtain ⟨role, classified⟩ := approved entry (List.mem_of_getElem? found)
      simp only [NativeGoldParameterStore.collect, found] at collected
      obtain ⟨remaining, continued, _⟩ := Option.map_eq_some_iff.mp collected
      simp only [checkReferences, found, classified, Option.isSome_some, Bool.true_and]
      exact ih remaining continued

/-- No independent reference-check or reachability certificate is an input.
Those facts follow from the configured allocation trace and actual collection. -/
def registered (entries : List Entry) (configured : Configured entries) (references : Vector Reference)
    (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) : Registry where
  entries := entries
  reachable := configured_reachable entries configured
  references := references
  checked := collected_checked entries (configured_approved entries configured) references.val registry.val
    (NativeGoldParameterStore.registry_values entries references registry collected).1
  registry := registry
  retained := collected

def ofSetup (jobs : List Job)
    (constructed : ∀ job ∈ jobs, NativeGoldBlockCodeProgram.Reachable job.request job.config)
    (admitted : ∀ job ∈ jobs, ∃ role, classify job.request job.header = some role)
    (entries : List Entry) (executed : allocate [] jobs = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) : Registry :=
  registered entries (ConstructedGoldObjectSetup.configured [] .empty jobs constructed admitted entries executed)
    references registry collected

/-- The construction retains the supplied complete source vector verbatim. -/
theorem ofSetup_retained (jobs : List Job)
    (constructed : ∀ job ∈ jobs, NativeGoldBlockCodeProgram.Reachable job.request job.config)
    (admitted : ∀ job ∈ jobs, ∃ role, classify job.request job.header = some role)
    (entries : List Entry) (executed : allocate [] jobs = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) :
    (ofSetup jobs constructed admitted entries executed references registry collected).references = references ∧
      (ofSetup jobs constructed admitted entries executed references registry collected).registry = registry := ⟨rfl, rfl⟩

theorem setup_work_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (jobs : List Job) (constructed : ∀ job ∈ jobs, NativeGoldBlockCodeProgram.Reachable job.request job.config)
    (admitted : ∀ job ∈ jobs, ∃ role, classify job.request job.header = some role)
    (entries : List Entry) (executed : allocate [] jobs = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) (bounded : jobs.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy
      (ofSetup jobs constructed admitted entries executed references registry collected) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ConstructedGoldObjectSetup.setup_work_bound coins Memory code publicData privateData dummy
    (ofSetup jobs constructed admitted entries executed references registry collected) jobs executed bounded
end
end FormalProof4FHE.HasteBoots.ConstructedGoldSetupRegistry
