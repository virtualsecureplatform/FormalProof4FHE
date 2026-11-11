module
public import FormalProof4FHE.HasteBoots.AllocatedLookupTables
public import FormalProof4FHE.HasteBoots.LookupHelperClaimMeaning
@[expose] public section

/-! The original identity Wrong alternative reaches an actually accepted
source-batch pair or helper opening, retaining original addresses and raw
rows. Only field values are compared; native encodings are not rewritten. -/
namespace FormalProof4FHE.HasteBoots.LookupWrongReceipts
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeFieldRepresentation (goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeExtensionFields (goldilocksBasis)
open NativeScalarQueryShape (laneBits)
open InputIndexedOracle (World)
open OracleProgram (run)
open MatrixFold (Cube)
noncomputable section

variable {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : NativeDeferredBatchVerification.Progress Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)

variable (sources : Fin (origin.ready.jobs.get index).tag.request.columns → Cube lookup.body.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : Cube (laneBits (3+origin.padding)+lookup.body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)

def SourceFalse : Prop :=
  ∃ column : Fin (origin.ready.jobs.get index).tag.request.columns,
    ∃ receipt : NativeDeferredBatchVerification.Receipt Memory, receipt ∈ after.receipts ∧
      ∃ (pair : Fin receipt.work.binding.queries.val.length) (received inserted : NativeLookupRequestWire.Row),
        ctx.proof.sources.val[(job.slots.slot column).val]? = some received ∧
        receipt.work.binding.queries.val[pair.val]? = some lookup.query ∧
        receipt.work.binding.values.val[pair.val]? = some inserted ∧
        NativeGoldPcsClaim.equal inserted.val received.val = true ∧
        inserted.val.map goldValue ≠ List.ofFn
          ((ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ job.view.shape)
            (fun j => goldExtensionValue (job.view.point j))).query.fold (sources column)) ∧
        NativeDeferredBatchVerification.Checked ctx.tables ctx.fieldFuel chooseBatch ctx.workerFuel world receipt

def HelperFalse : Prop :=
  ∃ receipt : NativeGoldHelperVerification.Receipt Memory,
    lookup.helpers.receipts[index.val]? = some receipt ∧ receipt ∈ lookup.helpers.receipts ∧
      receipt.call.query = lookup.plan.query ∧
      receipt.call.values.val.map goldValue ≠ List.ofFn
        ((ExtensionQuery.coefficientsQuery goldilocksBasis (fun j => goldExtensionValue (job.view.point j))).query.fold helpers) ∧
      NativeGoldHelperVerification.Checked ctx.tables ctx.helper ctx.fieldFuel chooseHelper ctx.workerFuel world receipt

include executed

theorem wrong_source
    (wrong : ∃ column, (fun lane => goldValue (job.view.inputs column lane)) ≠
      (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ job.view.shape)
        (fun j => goldExtensionValue (job.view.point j))).query.fold (sources column)) :
    SourceFalse ctx chooseBatch world lookup after origin index job sources := by
  obtain ⟨column,different⟩ := wrong
  obtain ⟨original,originalAt,rawEq⟩ := job.opening column
  obtain ⟨receipt,member,pair,received,inserted,_,receivedAt,queryAt,valueAt,matched,sameFields,_,_,_,_,_,_,checked⟩ :=
    LookupSourceReceiptCoverage.source_receipt ctx chooseHelper chooseBatch memory world lookup progress after executed
      (job.slots.slot column) (job.used column)
  have sameRow := Option.some.inj (originalAt.symm.trans receivedAt)
  have receivedEq : received.val = List.ofFn (job.view.inputs column) := sameRow ▸ rawEq
  have values : inserted.val.map goldValue = List.ofFn (fun lane => goldValue (job.view.inputs column lane)) := by
    simpa only [receivedEq,List.map_ofFn,Function.comp_def] using sameFields
  refine ⟨column,receipt,member,pair,received,inserted,receivedAt,queryAt,valueAt,matched,?_,checked⟩
  intro equal
  exact different (List.ofFn_injective (values.symm.trans equal))

theorem wrong_helper
    (wrong : NativeHelperPacking.coefficients goldilocksBasis (3+AllocatedLookupTables.helperPadding (ctx := ctx))
        (goldExtensionValue job.view.checked.helper) ≠
      (ExtensionQuery.coefficientsQuery goldilocksBasis (fun j => goldExtensionValue (job.view.point j))).query.fold helpers) :
    HelperFalse ctx chooseHelper world lookup origin index job helpers := by
  have prepared := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) executed).1
  have done := LookupHelperClaimMeaning.prepared_helpers ctx chooseHelper memory world lookup prepared
  obtain ⟨receipt,atReceipt,member,query,rawValues,_,_,_,checked⟩ :=
    LookupHelperClaimMeaning.checked_receipt ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers done
      job.view.checked (List.mem_of_getElem? job.view.checkedAt)
  have values : receipt.call.values.val.map goldValue = List.ofFn
      (NativeHelperPacking.coefficients goldilocksBasis (3+AllocatedLookupTables.helperPadding (ctx := ctx))
        (goldExtensionValue job.view.checked.helper)) := by
    rw [rawValues]
    change (NativeGoldHelper.vector ctx.helper.width.val job.view.checked.helper).map goldValue = _
    rw [NativeGoldHelper.vector_value,AllocatedLookupTables.helperWidth origin]
    rfl
  rw [job.view.ordinalEq] at atReceipt
  refine ⟨receipt,atReceipt,member,query,?_,checked⟩
  intro equal
  exact wrong (List.ofFn_injective (values.symm.trans equal))

theorem wrong_receipt (wrong : LookupIdentityCausalReduction.Wrong job.view sources helpers) :
    SourceFalse ctx chooseBatch world lookup after origin index job sources ∨
      HelperFalse ctx chooseHelper world lookup origin index job helpers := by
  rcases wrong with source | helper
  · exact Or.inl (wrong_source ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job sources source)
  · exact Or.inr (wrong_helper ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job helpers helper)

end
end FormalProof4FHE.HasteBoots.LookupWrongReceipts
