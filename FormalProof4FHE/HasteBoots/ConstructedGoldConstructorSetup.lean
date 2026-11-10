module
public import FormalProof4FHE.HasteBoots.ConstructedGoldSetupRegistry
@[expose] public section

/-! Constructor runs, checked security admission, allocation and full registry
collection compose without supplied reachability/reference certificates.
The run length observes a prefix; no fixed constructor retry limit is imposed.
The general setup interface still permits reachable warm/concurrent caches.
Native descriptor/heap/dispatch refinement and complete PBS remain open. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldConstructorSetup
open NativeGoldBlockCodeProgram (Request Config Reachable tick)
open NativeGoldEncodedParameters (Header)
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open ConstructedGoldRegistryTargets (classify)
open ConstructedGoldObjectSetup (Job allocate)
open InputIndexedOracle (Input law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

def advance (request : Request) : ℕ → Config → Config
  | 0, config => config
  | n+1, config => advance request n (tick request config)

theorem advance_reachable (request : Request) (steps : ℕ) (config : Config) (prior : Reachable request config) :
    Reachable request (advance request steps config) := by
  induction steps generalizing config with
  | zero => exact prior
  | succ steps ih => exact ih _ (.tick prior)

structure Invocation where
  request : Request
  header : Header
  steps : ℕ

def job (invocation : Invocation) : Job :=
  ⟨invocation.request, invocation.header, advance invocation.request invocation.steps {}⟩

def jobs (invocations : List Invocation) : List Job := invocations.map job

/-- Security qualification remains separate from constructor success. The
native generic constructor accepts quotas below the calibrated threshold. -/
def admitted (invocations : List Invocation) : Bool :=
  invocations.all fun invocation => (classify invocation.request invocation.header).isSome

theorem jobs_reachable (invocations : List Invocation) :
    ∀ value ∈ jobs invocations, Reachable value.request value.config := by
  intro value member
  obtain ⟨invocation, _, same⟩ := List.mem_map.mp member
  subst value
  exact advance_reachable invocation.request invocation.steps {} .initial

theorem jobs_admitted (invocations : List Invocation) (accepted : admitted invocations = true) :
    ∀ value ∈ jobs invocations, ∃ role, classify value.request value.header = some role := by
  intro value member
  obtain ⟨invocation, present, same⟩ := List.mem_map.mp member
  subst value
  have checked : (classify invocation.request invocation.header).isSome = true :=
    List.all_eq_true.mp accepted invocation present
  cases classified : classify invocation.request invocation.header with
  | none => simp only [classified, Option.isSome_none, Bool.false_eq_true] at checked
  | some role => exact ⟨role, classified⟩

def registered (invocations : List Invocation) (accepted : admitted invocations = true)
    (entries : List Entry) (allocated : allocate [] (jobs invocations) = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) : ConstructedGoldRegisteredSecurity.Registry :=
  ConstructedGoldSetupRegistry.ofSetup (jobs invocations) (jobs_reachable invocations) (jobs_admitted invocations accepted)
    entries allocated references registry collected

theorem retained (invocations : List Invocation) (accepted : admitted invocations = true)
    (entries : List Entry) (allocated : allocate [] (jobs invocations) = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) :
    (registered invocations accepted entries allocated references registry collected).references = references ∧
      (registered invocations accepted entries allocated references registry collected).registry = registry := ⟨rfl, rfl⟩

theorem work_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (invocations : List Invocation) (accepted : admitted invocations = true)
    (entries : List Entry) (allocated : allocate [] (jobs invocations) = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) (bounded : invocations.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy
      (registered invocations accepted entries allocated references registry collected) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  ConstructedGoldSetupRegistry.setup_work_bound coins Memory code publicData privateData dummy (jobs invocations)
    (jobs_reachable invocations) (jobs_admitted invocations accepted) entries allocated references registry collected
    (by simpa only [jobs, List.length_map] using bounded)

theorem four_role_work_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (source helper finalSource finalHelper : Invocation) (accepted : admitted [source,helper,finalSource,finalHelper] = true)
    (entries : List Entry) (allocated : allocate [] (jobs [source,helper,finalSource,finalHelper]) = some (.ok entries))
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy
      (registered [source,helper,finalSource,finalHelper] accepted entries allocated references registry collected) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  work_bound coins Memory code publicData privateData dummy _ accepted entries allocated references registry collected
    (by change 4 ≤ 256; decide +kernel)
end
end FormalProof4FHE.HasteBoots.ConstructedGoldConstructorSetup
