module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchReadExposure
@[expose] public section

/-! The actual context-hash computation is an observed subtrace of every completed native batch. Agreement with the complete history replays the same context digest. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchContextHistory
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler)
open NativeGoldBlockCode (description)
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem prepared_context_log (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.2.Sublist
      (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2 := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,columnsLog⟩ := NativeGoldBatchColumns.columns_log description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  obtain ⟨_,bound,_,_⟩ := NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude
  obtain ⟨_,_,_,_,bindingLog⟩ := NativeGoldBatchBinding.bound_origin description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound
  rw [NativeGoldBatchPcsProgram.run_prepareProgram,columnsLog,
    NativeGoldBatchPrelude.sampling_log description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude,bindingLog]
  exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)

theorem completed_context_log {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world : World) (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion) :
    (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.2.Sublist
      (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2 := by
  have origin := NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed
  rw [origin.log]
  exact (prepared_context_log ctx world work origin.prepared).trans (List.sublist_append_left _ _)

theorem context_replay {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world other : World) (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (history : List NativeTranscript.Observation)
    (observed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history)
    (agrees : ObservationReplay.Agrees other history) :
    (run (NativeBrakedownContext.context description.row ctx.parameters) other).run =
      (run (NativeBrakedownContext.context description.row ctx.parameters) world).run :=
  (OracleProgram.run_replay _).replay world other
    (fun entry member => agrees entry (((completed_context_log ctx choose fuel memory world work completion executed).trans observed).subset member))
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchContextHistory
