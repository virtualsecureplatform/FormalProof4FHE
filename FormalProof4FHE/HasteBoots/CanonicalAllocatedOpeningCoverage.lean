module
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedFamilyFixation
@[expose] public section

/-! Wrong canonical public folds yield original opening lifetime failures
at each source/helper's own calibrated decoding radius. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedOpeningCoverage
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeFieldRepresentation (goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeExtensionFields (goldilocksBasis)
open OracleProgram (Program run)
open AllocatedFamilyFunctions (Allocation)
noncomputable section

variable {Memory A : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : NativeDeferredBatchVerification.Progress Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) (allocation : Allocation ctx)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (program : Program A)


variable (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist (run program world).run.2)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (admitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (framing : ∀ receipt ∈ after.receipts, NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (responseFits : ∀ receipt ∈ after.receipts, (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)

include executed observed admitted framing responseFits

theorem source_no_bad
    (wrong : ∃ column, (fun lane => goldValue (job.view.inputs column lane)) ≠
      (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ job.view.shape)
        (fun j => goldExtensionValue (job.view.point j))).query.fold (CanonicalAllocatedTables.sources allocation origin index job geometry dummy (run program world).run.2 column))
    (noBad : ¬NativeRootFamilyLifetime.Bad dummy (run program world).run.2) :
    ∃ slot, CacheBackedBatchLifetimeSoundness.Failure Memory dummy (RegistryPublicSource.context ctx slot)
      (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
        (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1 slot)
      (CanonicalAllocatedTables.sourceRadius ctx slot) (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world := by
  obtain ⟨column,different⟩ := wrong
  let radius := CanonicalAllocatedTables.sourceRadius ctx (job.slots.slot column)
  have small : 3*radius < (ctx.registry.val.get (job.slots.slot column)).parameters.code.blocks.val-
      (ctx.registry.val.get (job.slots.slot column)).parameters.code.messageBlocks.val+1 :=
    ParameterDecodingRadius.source_small (RegistryPublicSource.context ctx (job.slots.slot column))
      (AllocatedScalarSource.origin allocation.entries allocation.reachable allocation.helperHandle allocation.references allocation.template ctx allocation.assembled
        (job.slots.slot column)) (sourceRole (job.slots.slot column)) (admitted (job.slots.slot column))
  have truthful := (OracleProgram.run_replay program).truthful world
  obtain ⟨receipt,member,parameters,root,_,_,pair,received,inserted,receivedAt,queryAt,rowAt,matched,_⟩ :=
    LookupSourceParameterAssociation.associated_no_bad ctx chooseHelper chooseBatch memory world lookup progress after executed
      (job.slots.slot column) (job.used column) dummy (run program world).run.2 truthful observed noBad
  obtain ⟨original,originalAt,rawEq⟩ := job.opening column
  have sameRow := Option.some.inj (originalAt.symm.trans receivedAt)
  have receivedEq : received.val = List.ofFn (job.view.inputs column) := sameRow ▸ rawEq
  have fields := (NativeGoldPcsClaim.equal_iff inserted.val received.val).mp matched
  have encoded : inserted.val.map goldValue = List.ofFn (fun lane => goldValue (job.view.inputs column lane)) := by
    simpa only [receivedEq,List.map_ofFn,Function.comp_def] using fields
  have mismatch : inserted.val.map goldValue ≠ List.ofFn
      ((ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ job.view.shape)
        (fun j => goldExtensionValue (job.view.point j))).query.fold (AllocatedLookupTables.sources origin index job allocation.entries allocation.reachable allocation.helperHandle allocation.references allocation.template allocation.assembled geometry dummy (run program world).run.2 radius column)) := by
    intro equal
    exact different (List.ofFn_injective (encoded.symm.trans equal))
  refine ⟨job.slots.slot column,?_⟩
  apply ProgramOpeningLifetime.batch program world dummy (RegistryPublicSource.context ctx (job.slots.slot column)) _
    (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
      (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1 (job.slots.slot column)) radius
  apply SourceOpeningObligationLifetime.witness ctx chooseHelper chooseBatch memory world lookup progress (.done after) executed receipt member
    dummy allocation.entries allocation.reachable allocation.references (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1 (RegistryPublicSource.context ctx (job.slots.slot column)) parameters rfl radius
    (framing receipt member) (responseFits receipt member) (run program world).run.2 observed
  intro decoded parsed
  let owner := RegistryBatchCodeOrigin.ofReceipt ctx chooseHelper chooseBatch memory world lookup progress (.done after) executed receipt member
    allocation.entries allocation.reachable allocation.references (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1
  exact AllocatedSourceWrongObligation.wrong ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job
    allocation.entries allocation.reachable allocation.helperHandle allocation.references allocation.template allocation.assembled geometry dummy (run program world).run.2 radius column _ owner receipt.work
    (SourceOpeningObligationLifetime.preparation ctx chooseHelper chooseBatch memory world lookup progress (.done after) executed receipt member)
    parameters root small (framing receipt member) (responseFits receipt member) decoded parsed pair inserted queryAt rowAt mismatch

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedOpeningCoverage
