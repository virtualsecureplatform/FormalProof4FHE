module

public import FormalProof4FHE.HasteBoots.NativeDeferredBatchVerification
@[expose] public section

/-! Every receipt emitted by the actual deferred dispatcher retains its computed first-original registry owner and original grouped claims, including accepted receipts retained before a later stopped result. -/
namespace FormalProof4FHE.HasteBoots.NativeDeferredBatchOwnership
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeGoldBlockCode (Stored)
open NativeDeferredBatchVerification (Call Receipt Progress Result Trace Context program)
open NativeGoldBatchPcsProgram (Scheduler)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def OriginalCall (registry : Vector (Oracle Stored)) (state : NativeDeferredOpeningBatch.State) (planned : Call) : Prop :=
  ∃ (group : Fin (NativeSourceRegistry.groupCount state.sources)) (opening : NativeGoldBatchOpening.Opening),
    NativeDeferredBatchVerification.call registry state group opening = some planned

theorem trace_owners {Memory : Type} {tables : NativeGoldBlockCode.Tables} {registry : Vector (Oracle Stored)}
    {state : NativeDeferredOpeningBatch.State} {fieldFuel : ℕ} {choose : Scheduler Memory} {workerFuel : ℕ} {world : World}
    {groups : List (Fin (NativeSourceRegistry.groupCount state.sources))} {openings : List NativeGoldBatchOpening.Opening}
    {before : Progress Memory} {result : Result Memory} {log : List NativeTranscript.Observation}
    (trace : Trace tables registry state fieldFuel choose workerFuel world groups openings before result log) :
    ∀ receipt ∈ result.progress.receipts, receipt ∈ before.receipts ∨ OriginalCall registry state receipt.call := by
  induction trace with
  | done before => intro receipt member; exact Or.inl member
  | packets groups openings before mismatch => intro receipt member; exact Or.inl member
  | index group rest opening openings before missing => intro receipt member; exact Or.inl member
  | stopped group rest opening openings before planned outcome log computed executed failed => intro receipt member; exact Or.inl member
  | passed group rest opening openings before after planned outcome log result later computed executed advanced tail ih =>
    obtain ⟨work,completion,next,_,_,same⟩ := NativeDeferredBatchVerification.advance_spec before planned outcome after advanced
    intro receipt member
    rcases ih receipt member with previous | owned
    · rw [same] at previous
      rcases List.mem_append.mp previous with old | added
      · exact Or.inl old
      · obtain rfl := List.mem_singleton.mp added
        exact Or.inr ⟨group,opening,computed⟩
    · exact Or.inr owned

theorem program_owners {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (program ctx choose memory) world).run.1 = .verification result) :
    ∀ receipt ∈ result.progress.receipts, OriginalCall ctx.registry ctx.state receipt.call := by
  intro receipt member
  rcases trace_owners (NativeDeferredBatchVerification.program_trace ctx choose memory world result executed).2 receipt member with impossible | owned
  · cases impossible
  · exact owned

/-- Ownership refers to the first ORIGINAL registry slot, including unused earlier aliases. -/
theorem original_spec (registry : Vector (Oracle Stored)) (state : NativeDeferredOpeningBatch.State) (planned : Call)
    (owned : OriginalCall registry state planned) :
    ∃ group : Fin (NativeSourceRegistry.groupCount state.sources),
      planned.group = group.val ∧ planned.slot = (NativeSourceRegistry.representative state.sources group).val ∧
      registry.val[planned.slot]? = some planned.oracle ∧
      planned.queries = NativeDeferredOpeningBatch.groupQueries state group ∧
      planned.values = NativeDeferredOpeningBatch.groupValues state group ∧
      ∀ earlier : Fin state.sources.val.length, earlier.val < planned.slot →
        state.sources.val.get earlier ≠ state.sources.val.get (NativeSourceRegistry.representative state.sources group) := by
  obtain ⟨group,opening,computed⟩ := owned
  have spec := NativeDeferredBatchVerification.call_spec registry state group opening planned computed
  refine ⟨group,spec.1,spec.2.1,spec.2.2.1,spec.2.2.2.1,spec.2.2.2.2.1,?_⟩
  intro earlier before
  rw [spec.2.1] at before
  exact NativeSourceRegistry.representative_first state.sources group earlier before
end
end FormalProof4FHE.HasteBoots.NativeDeferredBatchOwnership
