module

public import FormalProof4FHE.HasteBoots.NativeDeferredBatchVerification
@[expose] public section

/-! Original registry length makes every first-owner lookup available.
The actual seal gate makes group and packet counts equal, so ordered dispatch
cannot produce its auxiliary index/packet-unavailability outcomes.
PCS encoding/sampling/worker domains and security remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeDeferredBatchDomain
open NativePrefixCodec (Vector)
open NativeGoldBlockCode (Stored Tables)
open NativeSharedLookupParent (Oracle)
open NativeGoldBatchOpening (Opening)
open NativeGoldBatchPcsProgram (Scheduler)
open NativeDeferredBatchVerification (Call Progress Result Context Outcome call loop program)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def Available {Memory : Type} : Result Memory → Prop
  | .indexingUnavailable _ _ _ | .packetUnavailable _ => False
  | _ => True

def OutcomeAvailable {Memory : Type} : Outcome Memory → Prop
  | .sealRejected _ _ => True
  | .verification result => Available result

theorem call_complete (registry : Vector (Oracle Stored)) (state : NativeDeferredOpeningBatch.State)
    (group : Fin (NativeSourceRegistry.groupCount state.sources)) (opening : Opening)
    (sources : state.sources.val.length = registry.val.length) : ∃ planned, call registry state group opening = some planned := by
  unfold call
  cases found : registry.val[(NativeSourceRegistry.representative state.sources group).val]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp found
    have inside := (NativeSourceRegistry.representative state.sources group).isLt
    omega
  | some oracle =>
    simp only [found,Option.map_some]
    exact ⟨_,rfl⟩

theorem loop_available {Memory : Type} (tables : Tables) (registry : Vector (Oracle Stored)) (state : NativeDeferredOpeningBatch.State)
    (fieldFuel : ℕ) (choose : Scheduler Memory) (workerFuel : ℕ)
    (groups : List (Fin (NativeSourceRegistry.groupCount state.sources))) (openings : List Opening) (before : Progress Memory) (world : World)
    (sources : state.sources.val.length = registry.val.length) (count : groups.length = openings.length) :
    Available (run (loop tables registry state fieldFuel choose workerFuel groups openings before) world).run.1 := by
  induction groups generalizing openings before with
  | nil =>
    cases openings with
    | nil => trivial
    | cons opening rest => simp only [List.length_nil,List.length_cons] at count; omega
  | cons group rest ih =>
    cases openings with
    | nil => simp only [List.length_nil,List.length_cons] at count; omega
    | cons opening openings =>
      obtain ⟨planned,computed⟩ := call_complete registry state group opening sources
      simp only [loop,computed,OracleProgram.run_bind,ObservationReplay.run_bind]
      cases advanced : NativeDeferredBatchVerification.advance before planned
          (run (NativeGoldBatchPcsProgram.program (planned.context tables fieldFuel before.parent) choose workerFuel before.memory) world).run.1 with
      | none => trivial
      | some after => exact ih openings after (by simpa only [List.length_cons,Nat.succ.injEq] using count)

theorem program_available {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (sources : ctx.state.sources.val.length = ctx.registry.val.length) :
    OutcomeAvailable (run (program ctx choose memory) world).run.1 := by
  simp only [program]
  cases sealed : (NativeDeferredOpeningBatch.sealBatch ctx.state ctx.proof.val.length).2 with
  | error reason => trivial
  | ok value =>
    cases value
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure,OutcomeAvailable]
    exact loop_available ctx.tables ctx.registry ctx.state ctx.fieldFuel choose ctx.workerFuel
      (NativeDeferredOpeningBatch.usedGroups ctx.state) ctx.proof.val
      ⟨(NativeDeferredOpeningBatch.sealBatch ctx.state ctx.proof.val.length).1.parent,memory,[]⟩ world sources
      (NativeDeferredOpeningBatch.seal_spec ctx.state ctx.proof.val.length sealed).1.symm
end
end FormalProof4FHE.HasteBoots.NativeDeferredBatchDomain
