module
public import FormalProof4FHE.HasteBoots.ProgramEqualityLookupFactors
@[expose] public section

/-! Successful original native execution supplies observed lookup receipt
outputs for both endpoint factors at an equality input. -/
namespace FormalProof4FHE.HasteBoots.LoggedEqualityLookupFactors
open InputIndexedOracle (World)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3)
open EqualityLookupFactorFixation (Scalar Side receiptAt)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}

theorem recover {A : Type} (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (program : OracleProgram.Program A)
    (success : (OracleProgram.run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1 = some (.bound body))
    (observed : (OracleProgram.run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.2.Sublist (OracleProgram.run program world).run.2)
    (view : EqualityLookupReceiptView.View)
    (groups : view.prelude.groups = (OriginalReceiptSegmentation.original origin rootsFit).groups) :
    ∃ compression offset : Scalar,
      compression.view = view ∧ offset.view = view ∧ compression.world = world ∧ offset.world = world ∧
      compression.ordinal = index.val ∧ offset.ordinal = index.val ∧
      compression.side = .compression ∧ offset.side = .offset ∧
      compression.word = (origin.ready.jobs.get index).output.y ∧ offset.word = (origin.ready.jobs.get index).output.r ∧
      ProgramEqualityLookupFactors.Observed program compression ∧ ProgramEqualityLookupFactors.Observed program offset := by
  obtain ⟨first,last,firstAt,lastAt,yDecode,rDecode⟩ := LookupProducedEndpoints.draws _ _ _ _ job.view.produced
  have getter := LookupProducerOrdinal.producer_at origin job
  have firstReceipt : receiptAt view index.val .compression = some (ReceiptFrameView.frame world first.coefficients.phase) := by
    unfold receiptAt
    rw [groups]
    change ((NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 ctx.lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule ctx.requests.property.le
        (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling))
        (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world)) world).1.completed.map
        (fun record => record.selection.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase)))[index.val]?.bind List.head? = _
    rw [List.getElem?_map,getter,Option.map_some,Option.bind_some,List.head?_map,firstAt,Option.map_some]
  have lastReceipt : receiptAt view index.val .offset = some (ReceiptFrameView.frame world last.coefficients.phase) := by
    unfold receiptAt
    rw [groups]
    change ((NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 ctx.lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule ctx.requests.property.le
        (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling))
        (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world)) world).1.completed.map
        (fun record => record.selection.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase)))[index.val]?.bind List.getLast? = _
    rw [List.getElem?_map,getter,Option.map_some,Option.bind_some,List.getLast?_map,lastAt,Option.map_some]
  have traces := LookupProducerConsumed.producer origin job
  let compression : Scalar := ⟨view,world,index.val,.compression,first.coefficients,
    traces.2 first (List.mem_of_mem_head? (by rw [firstAt]; rfl)),firstReceipt,_,yDecode⟩
  let offset : Scalar := ⟨view,world,index.val,.offset,last.coefficients,
    traces.2 last (List.mem_of_mem_getLast? (by rw [lastAt]; rfl)),lastReceipt,_,rDecode⟩
  have reads := LookupPreludeTrace.lookup_reads origin success job.view.producer job.producerMember
  exact ⟨compression,offset,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    observed.subset ((reads first (List.mem_of_mem_head? (by rw [firstAt]; rfl))).subset (LookupReceiptLogs.output_member world first.coefficients.phase)),
    observed.subset ((reads last (List.mem_of_mem_getLast? (by rw [lastAt]; rfl))).subset (LookupReceiptLogs.output_member world last.coefficients.phase))⟩

end
end FormalProof4FHE.HasteBoots.LoggedEqualityLookupFactors
