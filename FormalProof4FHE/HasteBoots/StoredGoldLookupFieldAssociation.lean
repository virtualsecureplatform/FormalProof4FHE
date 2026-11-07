module
public import FormalProof4FHE.HasteBoots.StoredGoldNativeFieldAssociation
public import FormalProof4FHE.HasteBoots.StoredGoldRegistryPacketAssociation
public import FormalProof4FHE.HasteBoots.NativeGoldLookupAvailability
@[expose] public section

/-! Field-key provenance from a receipt in the actual native lookup dispatcher.
The receipt's checked batch preparation supplies raw field identity; the native
first-original owner theorem supplies its context/root relation. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldLookupFieldAssociation
open InputIndexedOracle (Byte World)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldLookupVerification (Prepared program batchContext)
open NativeDeferredBatchVerification (Receipt Result)
open NativeTranscript (Observation)
open StoredSourceVectorReadCost (Sources view sourceView)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

private theorem get_same (left right : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source)
    (same : left = right) (i : Fin left.val.length) (j : Fin right.val.length) (index : i.val = j.val) :
    left.val.get i = right.val.get j := by
  subst right
  have equal : i = j := Fin.ext index
  rw [equal]

theorem receipt_field_slot {Memory : Type} (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (history : List Observation) (dummy : Vector Byte 64) (extractCtx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history
      (NativeGoldBatchReadExposure.phase (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work).pending.input
      dummy extractCtx radius).value = some output) :
    ∃ slot : Fin prepared.metadata.sources.val.length,
      slot.val = receipt.call.slot ∧ sourceView output.1.data.source = prepared.metadata.sources.val.get slot ∧
      output.1.data.queries = receipt.call.queries ∧ output.1.data.values = receipt.call.values ∧
      output.1.count = receipt.work.geometry.randomCount ∧
      ∀ earlier : Fin prepared.metadata.sources.val.length, earlier.val < slot.val →
        prepared.metadata.sources.val.get earlier ≠ prepared.metadata.sources.val.get slot := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress _ executed
  have checked := (NativeDeferredBatchVerification.program_receipts (batchContext ctx progress) chooseBatch
    prepared.helpers.memory world result origin.2.2.1 receipt member).1
  have native := NativeGoldBatchPcsProgram.completed_origin _ chooseBatch ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1
  obtain ⟨before,parent,valid,fits⟩ := framed
  obtain ⟨context,hashed,contextEq,rootEq,queries,values,count⟩ :=
    StoredGoldNativeFieldAssociation.extraction_prepared_field _ world receipt.work native.prepared before parent valid fits
      history dummy extractCtx radius output accepted
  obtain ⟨slot,position,_,computed,root,first⟩ := NativeGoldLookupAvailability.receipt_owner_key ctx chooseHelper chooseBatch memory world
    prepared progress result executed receipt member
  refine ⟨slot,position,?_,queries,values,count,first⟩
  apply Prod.ext
  · exact contextEq.trans (Option.some.inj (hashed.symm.trans computed))
  · exact rootEq.trans root

theorem receipt_stored_key {Memory : Type} (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (history : List Observation) (dummy : Vector Byte 64) (extractCtx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history
      (NativeGoldBatchReadExposure.phase (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work).pending.input
      dummy extractCtx radius).value = some output)
    (sources : Sources) (retained : view sources = prepared.metadata.sources) :
    ∃ index : Fin sources.val.length,
      index.val = receipt.call.slot ∧ output.1.data.source = sources.val.get index ∧
      (StoredRegistryOwnerCost.owner sources index).value = some index.val := by
  obtain ⟨slot,position,key,_,_,_,first⟩ := receipt_field_slot ctx chooseHelper chooseBatch memory world prepared progress result
    executed receipt member framed history dummy extractCtx radius output accepted
  have lengths : sources.val.length = prepared.metadata.sources.val.length := by
    have same := congrArg (fun values => values.val.length) retained
    simpa only [view,List.length_map] using same
  let index : Fin sources.val.length := ⟨slot.val,by have bound := slot.isLt; omega⟩
  have viewed : sourceView (sources.val.get index) = prepared.metadata.sources.val.get slot :=
    (StoredRegistryOwnerCost.view_get sources index).symm.trans
      (get_same (view sources) prepared.metadata.sources retained (StoredRegistryOwnerCost.position sources index) slot rfl)
  have earliest : ∀ i (before : i < index.val), sources.val[i]'(before.trans index.isLt) ≠ sources.val.get index := by
    intro i before same
    let earlier : Fin sources.val.length := ⟨i,before.trans index.isLt⟩
    let nativeEarlier : Fin prepared.metadata.sources.val.length := ⟨i,by have bound := earlier.isLt; omega⟩
    have earlierSame : prepared.metadata.sources.val.get nativeEarlier = sourceView (sources.val.get earlier) :=
      (get_same (view sources) prepared.metadata.sources retained
        (StoredRegistryOwnerCost.position sources earlier) nativeEarlier rfl).symm.trans
        (StoredRegistryOwnerCost.view_get sources earlier)
    apply first nativeEarlier before
    rw [earlierSame,← viewed]
    exact congrArg sourceView same
  refine ⟨index,position,StoredMetadataCost.sourceView_injective (key.trans viewed.symm),?_⟩
  have chosen := StoredRegistryOwnerCost.first_at (sources.val.get index) sources.val index.val index.isLt rfl earliest
  simp only [StoredRegistryOwnerCost.owner,StoredRegistryOwnerCost.readAt_value,List.getElem?_eq_getElem index.isLt]
  exact chosen

/-- Both stored-key premises come from the actual dispatcher: its retained
initializer parent packet and a receipt's native pending field input. -/
theorem receipt_packet_key {Memory : Type} (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (history : List Observation) (dummy : Vector Byte 64) (extractCtx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history
      (NativeGoldBatchReadExposure.phase (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work).pending.input
      dummy extractCtx radius).value = some output)
    (before : List TranscriptFrame.Frame)
    (parentBytes : (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1.input =
      TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (labelFits : NativeCanonicalLookupWire.registryLabel.length < TranscriptFrame.lengthLimit)
    (messageFits : (NativeCanonicalLookupWire.sourcesCodec.encode prepared.metadata.sources).length < TranscriptFrame.lengthLimit)
    (sources : Sources) (decoded : (StoredRegistryPacketCost.decode prepared.metadata.parent.input).value = some sources) :
    ∃ index : Fin sources.val.length,
      index.val = receipt.call.slot ∧ output.1.data.source = sources.val.get index ∧
      (StoredRegistryOwnerCost.owner sources index).value = some index.val := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress _ executed
  obtain ⟨geometry,registered⟩ := NativeGoldLookupVerification.prepared_metadata ctx chooseHelper memory world prepared origin.1
  have initialized := (NativeRegisteredLookup.prepare_origin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests
    world geometry prepared.metadata registered).1
  have retained := StoredGoldRegistryPacketAssociation.initialized_sources ctx.registry _ world prepared.metadata initialized
    before parentBytes valid labelFits messageFits sources decoded
  exact receipt_stored_key ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member framed
    history dummy extractCtx radius output accepted sources retained

end
end FormalProof4FHE.HasteBoots.StoredGoldLookupFieldAssociation
