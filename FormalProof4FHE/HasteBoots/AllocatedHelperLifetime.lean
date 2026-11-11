module
public import FormalProof4FHE.HasteBoots.AllocatedHelperWrongObligation
@[expose] public section

/-! A wrong original helper fold supplies an actual single-opening lifetime
witness. The helper store entry, proof root, raw claim and accepted receipt
are recovered from the original allocated lookup and checked job ordinal. -/
namespace FormalProof4FHE.HasteBoots.AllocatedHelperLifetime
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
include executed

theorem witness (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (small : 3*radius < ctx.helper.code.blocks.val-ctx.helper.code.messageBlocks.val+1)
    (framing : ∀ receipt ∈ lookup.helpers.receipts,
      SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (responseFits : ∀ receipt ∈ lookup.helpers.receipts, (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (wrong : NativeHelperPacking.coefficients goldilocksBasis (3+AllocatedLookupTables.helperPadding (ctx := ctx))
        (goldExtensionValue job.view.checked.helper) ≠
      (ExtensionQuery.coefficientsQuery goldilocksBasis (fun j => goldExtensionValue (job.view.point j))).query.fold
        (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template assembled geometry dummy history radius)) :
    Nonempty (SingleOpeningLifetimeSoundness.Witness Memory dummy target radius world history) := by
  have prepared := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) executed).1
  have done := LookupHelperClaimMeaning.prepared_helpers ctx chooseHelper memory world lookup prepared
  obtain ⟨receipt,_,member,query,rawValues,rootAt,_,_,_⟩ := LookupHelperClaimMeaning.checked_receipt ctx chooseHelper memory world lookup.body lookup.plan
    lookup.helpers done job.view.checked (List.mem_of_getElem? job.view.checkedAt)
  rw [job.view.ordinalEq] at rootAt
  have root : receipt.call.root = ctx.proof.roots.val.get (AllocatedLookupTables.helperIndex origin index) := by
    simpa only [List.get_eq_getElem] using Option.some.inj
      (rootAt.symm.trans (List.getElem?_eq_getElem (AllocatedLookupTables.helperIndex origin index).isLt))
  let expected := NativeHelperPacking.coefficients goldilocksBasis ctx.helper.width.val (goldExtensionValue job.view.checked.helper)
  have encoded : receipt.call.values.val.map goldValue = List.ofFn expected := by
    rw [rawValues]
    change (NativeGoldHelper.vector ctx.helper.width.val job.view.checked.helper).map goldValue = _
    rw [NativeGoldHelper.vector_value]
    rfl
  have packedEncoded : receipt.call.values.val.map goldValue = List.ofFn
      (NativeHelperPacking.coefficients goldilocksBasis (3+AllocatedLookupTables.helperPadding (ctx := ctx))
        (goldExtensionValue job.view.checked.helper)) := by
    rw [encoded]
    unfold expected
    rw [AllocatedLookupTables.helperWidth origin]
  have different : receipt.call.values.val.map goldValue ≠ List.ofFn
      ((ExtensionQuery.coefficientsQuery goldilocksBasis (fun j => goldExtensionValue (job.view.point j))).query.fold
        (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template assembled geometry dummy history radius)) := by
    intro equal
    exact wrong (List.ofFn_injective (packedEncoded.symm.trans equal))
  have entry := AllocatedScalarHelper.entry_spec entries reachable helperHandle references template ctx assembled
  apply HelperOpeningObligationLifetime.witness ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers done dummy receipt member
    (framing receipt member) (responseFits receipt member) history ((NativeGoldLookupVerification.program_helpers ctx chooseHelper chooseBatch memory world).trans observed)
    entries reachable helperHandle (AllocatedScalarHelper.entry entries reachable helperHandle references template ctx assembled) entry.1 entry.2.2
    target parameters profile radius expected encoded
  intro sample sampler decoded parsed
  let owner := AllocatedSingleOpeningOrigin.helperReceipt entries reachable helperHandle
    (AllocatedScalarHelper.entry entries reachable helperHandle references template ctx assembled) entry.1 ctx entry.2.2 receipt
  exact AllocatedHelperWrongObligation.wrong ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job
    entries reachable helperHandle references template assembled geometry dummy history radius _ owner receipt.work
    (HelperOpeningObligationLifetime.prepared ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers done receipt member)
    (AllocatedHelperCube.parameters origin index entries reachable helperHandle references template assembled).symm root small
    (framing receipt member) (responseFits receipt member) sample sampler decoded parsed query expected encoded different

end
end FormalProof4FHE.HasteBoots.AllocatedHelperLifetime
