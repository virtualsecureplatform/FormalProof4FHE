module
public import FormalProof4FHE.HasteBoots.ConstructedGoldObjectSecurity
@[expose] public section

/-! Sequential composition of actual logical parameter-store allocations.
Success retains every object; pending initialization and constructor errors
propagate rather than dropping a role. A native descriptor/loop/heap refinement
is still required; the trusted admission check is not added to the allocator. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldObjectSetup
open NativeGoldParameterStore (Entry Allocation)
open ConstructedGoldRegistryTargets (Configured classify)
open InputIndexedOracle (Input law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

structure Job where
  request : NativeGoldBlockCodeProgram.Request
  header : NativeGoldEncodedParameters.Header
  config : NativeGoldBlockCodeProgram.Config

def allocate (before : List Entry) : List Job → Option (Except NativeGoldEncodedParameters.Error (List Entry))
  | [] => some (.ok before)
  | job::rest => match NativeGoldParameterStore.allocate before job.request job.header job.config with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok next) => allocate next.entries rest

theorem allocation_length (before : List Entry) (jobs : List Job) (after : List Entry)
    (executed : allocate before jobs = some (.ok after)) : after.length = before.length + jobs.length := by
  induction jobs generalizing before with
  | nil => cases executed; simp
  | cons job rest ih =>
    simp only [allocate] at executed
    cases allocated : NativeGoldParameterStore.allocate before job.request job.header job.config with
    | none => simp only [allocated] at executed; cases executed
    | some result =>
      cases result with
      | error error => simp only [allocated] at executed; cases executed
      | ok next =>
        simp only [allocated] at executed
        obtain ⟨_, _, _, shape⟩ := NativeGoldParameterStore.allocate_post before job.request job.header job.config next allocated
        have length := ih next.entries executed
        rw [shape, List.length_append, List.length_singleton] at length
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using length

theorem configured (before : List Entry) (prior : Configured before) (jobs : List Job)
    (constructed : ∀ job ∈ jobs, NativeGoldBlockCodeProgram.Reachable job.request job.config)
    (admitted : ∀ job ∈ jobs, ∃ role, classify job.request job.header = some role)
    (after : List Entry) (executed : allocate before jobs = some (.ok after)) : Configured after := by
  induction jobs generalizing before with
  | nil => cases executed; exact prior
  | cons job rest ih =>
    simp only [allocate] at executed
    cases allocated : NativeGoldParameterStore.allocate before job.request job.header job.config with
    | none => simp only [allocated] at executed; cases executed
    | some result =>
      cases result with
      | error error => simp only [allocated] at executed; cases executed
      | ok next =>
        simp only [allocated] at executed
        obtain ⟨role, accepted⟩ := admitted job (by simp)
        exact ih next.entries (.allocate before job.request job.header job.config role next prior
          (constructed job (by simp)) accepted allocated)
          (fun later member => constructed later (List.mem_cons_of_mem _ member))
          (fun later member => admitted later (List.mem_cons_of_mem _ member)) executed

/-- The parameter count follows the executed setup, not the number of roots
or references retained by later source registration. -/
theorem setup_work_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : ConstructedGoldRegisteredSecurity.Registry) (jobs : List Job)
    (executed : allocate [] jobs = some (.ok registered.entries)) (bounded : jobs.length ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have length := allocation_length [] jobs registered.entries executed
  have objects : registered.entries.length ≤ 256 := by
    simp only [List.length_nil, zero_add] at length
    omega
  exact ConstructedGoldObjectSecurity.arena_work_bound coins Memory code publicData privateData dummy registered objects

/-- Four successful role allocations suffice, with no hypothesis limiting
registry slots, root reuse, profile identifiers or attacker attempts. -/
theorem four_role_work_bound (coins : Measure Tape) (Memory : Type) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (registered : ConstructedGoldRegisteredSecurity.Registry) (source helper finalSource finalHelper : Job)
    (executed : allocate [] [source,helper,finalSource,finalHelper] = some (.ok registered.entries)) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | ConstructedGoldAnyProfileSecurity.Failure Memory code publicData privateData dummy registered execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData :=
  setup_work_bound coins Memory code publicData privateData dummy registered _ executed (by change 4 ≤ 256; decide +kernel)
end
end FormalProof4FHE.HasteBoots.ConstructedGoldObjectSetup
