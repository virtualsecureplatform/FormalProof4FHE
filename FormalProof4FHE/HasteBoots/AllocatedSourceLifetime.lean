module
public import FormalProof4FHE.HasteBoots.AllocatedSourceWrongObligation
@[expose] public section

/-! Original allocated source mismatches enter the existing batch lifetime
witness using actual accepted owners, outside one shared full-history hash
event. Constructor provenance is recovered from the same registry store. -/
namespace FormalProof4FHE.HasteBoots.AllocatedSourceLifetime
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldParameterStore (Entry Reference)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeFieldRepresentation (goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeExtensionFields (goldilocksBasis)
open OracleProgram (run)
noncomputable section

variable {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : NativeDeferredBatchVerification.Progress Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ)
    (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation) (radius : ℕ)

local notation "sources" => AllocatedLookupTables.sources origin index job entries reachable helperHandle references template assembled geometry dummy history radius

def Witness : Prop :=
  ∃ column : Fin (origin.ready.jobs.get index).tag.request.columns,
    ∃ (receipt : NativeDeferredBatchVerification.Receipt Memory) (member : receipt ∈ after.receipts)
      (parameters : receipt.call.oracle.parameters = (ctx.registry.val.get (job.slots.slot column)).parameters),
      Nonempty (CacheBackedBatchLifetimeSoundness.Witness Memory dummy (RegistryPublicSource.context ctx (job.slots.slot column))
        (SourceOpeningLifetimeWitness.origin ctx chooseHelper chooseBatch memory world lookup progress (.done after) executed receipt member
          entries reachable references (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 (RegistryPublicSource.context ctx (job.slots.slot column)) parameters)
        radius world history)

variable (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (small : ∀ column : Fin (origin.ready.jobs.get index).tag.request.columns,
      3*radius < (ctx.registry.val.get (job.slots.slot column)).parameters.code.blocks.val-
        (ctx.registry.val.get (job.slots.slot column)).parameters.code.messageBlocks.val+1)
    (framing : ∀ receipt ∈ after.receipts, NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (responseFits : ∀ receipt ∈ after.receipts, (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)

include truthful observed small framing responseFits

theorem source_no_bad
    (wrong : ∃ column, (fun lane => goldValue (job.view.inputs column lane)) ≠
      (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ job.view.shape)
        (fun j => goldExtensionValue (job.view.point j))).query.fold (sources column))
    (noBad : ¬NativeRootFamilyLifetime.Bad dummy history) :
    Witness ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job entries reachable helperHandle references template assembled dummy history radius := by
  obtain ⟨column,different⟩ := wrong
  obtain ⟨receipt,member,parameters,root,_,_,pair,received,inserted,receivedAt,queryAt,rowAt,matched,_⟩ :=
    LookupSourceParameterAssociation.associated_no_bad ctx chooseHelper chooseBatch memory world lookup progress after executed
      (job.slots.slot column) (job.used column) dummy history truthful observed noBad
  obtain ⟨original,originalAt,rawEq⟩ := job.opening column
  have sameRow := Option.some.inj (originalAt.symm.trans receivedAt)
  have receivedEq : received.val = List.ofFn (job.view.inputs column) := sameRow ▸ rawEq
  have fields := (NativeGoldPcsClaim.equal_iff inserted.val received.val).mp matched
  have encoded : inserted.val.map goldValue = List.ofFn (fun lane => goldValue (job.view.inputs column lane)) := by
    simpa only [receivedEq,List.map_ofFn,Function.comp_def] using fields
  have mismatch : inserted.val.map goldValue ≠ List.ofFn
      ((ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ job.view.shape)
        (fun j => goldExtensionValue (job.view.point j))).query.fold (sources column)) := by
    intro equal
    exact different (List.ofFn_injective (encoded.symm.trans equal))
  refine ⟨column,receipt,member,parameters,?_⟩
  apply SourceOpeningObligationLifetime.witness ctx chooseHelper chooseBatch memory world lookup progress (.done after) executed receipt member
    dummy entries reachable references (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 (RegistryPublicSource.context ctx (job.slots.slot column)) parameters rfl radius
    (framing receipt member) (responseFits receipt member) history observed
  intro decoded parsed
  let owner := RegistryBatchCodeOrigin.ofReceipt ctx chooseHelper chooseBatch memory world lookup progress (.done after) executed receipt member
    entries reachable references (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1
  exact AllocatedSourceWrongObligation.wrong ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job
    entries reachable helperHandle references template assembled geometry dummy history radius column _ owner receipt.work
    (SourceOpeningObligationLifetime.preparation ctx chooseHelper chooseBatch memory world lookup progress (.done after) executed receipt member)
    parameters root (small column) (framing receipt member) (responseFits receipt member) decoded parsed pair inserted queryAt rowAt mismatch

theorem source_or_bad
    (wrong : ∃ column, (fun lane => goldValue (job.view.inputs column lane)) ≠
      (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ job.view.shape)
        (fun j => goldExtensionValue (job.view.point j))).query.fold (sources column)) :
    Witness ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job entries reachable helperHandle references template assembled dummy history radius ∨
      NativeRootFamilyLifetime.Bad dummy history := by
  by_cases bad : NativeRootFamilyLifetime.Bad dummy history
  · exact Or.inr bad
  · exact Or.inl (source_no_bad ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job entries reachable helperHandle
      references template assembled geometry dummy history radius truthful observed small framing responseFits wrong bad)

end
end FormalProof4FHE.HasteBoots.AllocatedSourceLifetime
