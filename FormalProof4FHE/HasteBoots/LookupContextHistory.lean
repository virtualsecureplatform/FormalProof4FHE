module
public import FormalProof4FHE.HasteBoots.NativeGoldLookupAvailability
public import FormalProof4FHE.HasteBoots.NativeGoldBatchContextHistory
@[expose] public section

/-! Both contexts in a source-alias comparison are actual observations of the
enclosing native lookup: the used original slot and its accepted batch owner. -/
namespace FormalProof4FHE.HasteBoots.LookupContextHistory
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription)
open NativeLookupRequestWire (Request Row)
open NativeGoldPcsWire (Query)
open NativeSharedSourceClaims (Progress)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem loop_context {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slots : List (Fin registry.val.length)) (before after : Progress) (world : World)
    (success : (run (NativeSharedSourceClaims.loop row registry requests query values slots before) world).run.1 = .done after)
    (slot : Fin registry.val.length) (member : slot ∈ slots) (used : NativeSharedSourceClaims.used requests slot = true) :
    (run (NativeBrakedownContext.context row (registry.val.get slot).parameters) world).run.2.Sublist
      (run (NativeSharedSourceClaims.loop row registry requests query values slots before) world).run.2 := by
  induction slots generalizing before with
  | nil => cases member
  | cons first rest ih =>
    cases current : (run (NativeSharedSourceClaims.step row registry requests query values first before) world).run.1 with
    | stopped progress reason =>
      simp only [NativeSharedSourceClaims.loop,OracleProgram.run_bind,ObservationReplay.run_bind,current,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
      contradiction
    | done next =>
      simp only [NativeSharedSourceClaims.loop,OracleProgram.run_bind,ObservationReplay.run_bind,current] at success ⊢
      rcases List.mem_cons.mp member with same | member
      · subst first
        have observations := NativeSharedSourceClaims.step_observations row registry requests query values slot before world
        rw [used,ite_eq_left rfl] at observations
        rw [observations]
        exact List.sublist_append_left _ _
      · exact (ih next success member).trans (List.sublist_append_right _ _)

theorem program_context {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (after : Progress) (world : World)
    (success : (run (NativeSharedSourceClaims.program row registry requests query values state) world).run.1 = .done after)
    (slot : Fin registry.val.length) (used : NativeSharedSourceClaims.used requests slot = true) :
    (run (NativeBrakedownContext.context row (registry.val.get slot).parameters) world).run.2.Sublist
      (run (NativeSharedSourceClaims.program row registry requests query values state) world).run.2 :=
  loop_context row registry requests query values _ ⟨state,[]⟩ after world success slot (List.mem_finRange _) used

variable {Memory : Type} (ctx : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : Progress) (result : NativeDeferredBatchVerification.Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification result))

include executed

theorem used_context (slot : Fin ctx.registry.val.length) (used : NativeSharedSourceClaims.used ctx.requests slot = true) :
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (ctx.registry.val.get slot).parameters) world).run.2.Sublist
      (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2 := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress (.verification result) executed
  have sourceLog := program_context NativeGoldBlockCode.description.row ctx.registry ctx.requests lookup.query ctx.proof.sources
    (NativeGoldLookupVerification.initial lookup) progress world origin.2.1 slot used
  apply sourceLog.trans
  rw [origin.2.2.2]
  exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)

theorem receipt_context (receipt : NativeDeferredBatchVerification.Receipt Memory) (member : receipt ∈ result.progress.receipts) :
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row receipt.call.oracle.parameters) world).run.2.Sublist
      (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2 := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress (.verification result) executed
  obtain ⟨checked,observed⟩ := NativeDeferredBatchVerification.program_receipts (NativeGoldLookupVerification.batchContext ctx progress)
    chooseBatch lookup.helpers.memory world result origin.2.2.1 receipt member
  have contextLog := NativeGoldBatchContextHistory.completed_context_log (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
    chooseBatch ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1
  exact contextLog.trans (observed.trans (NativeGoldLookupAvailability.batch_log_sublist ctx chooseHelper chooseBatch memory world lookup progress _ executed))

end
end FormalProof4FHE.HasteBoots.LookupContextHistory
