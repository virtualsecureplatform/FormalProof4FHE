module
public import FormalProof4FHE.HasteBoots.StoredGoldLookupFieldAssociation
public import FormalProof4FHE.HasteBoots.NativeGoldLookupRegistryTrace
@[expose] public section

/-! Actual dispatcher receipts associate checked extraction with the first
original registry parameter object, outside the existing persistent bad event.
All logs belong to the same enclosing lookup and mixed causal history. Native
framing/allocation, full application soundness and physical refinement remain
separate obligations. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldLookupParameterAssociation
open InputIndexedOracle (Byte World)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldLookupVerification (Prepared program)
open NativeDeferredBatchVerification (Receipt Result)
open NativeTranscript (Observation)
open StoredSourceVectorReadCost (Sources)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem receipt_original {Memory : Type} (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (included : (run (program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (dummy : Vector Byte 64) (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history)
    (extractCtx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
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
    ∃ (index : Fin sources.val.length) (original : Fin ctx.registry.val.length),
      index.val = receipt.call.slot ∧ original.val = receipt.call.slot ∧
      output.1.data.source = sources.val.get index ∧
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧
      ctx.registry.val.get original = receipt.call.oracle ∧
      extractCtx.parameters = (ctx.registry.val.get original).parameters ∧
      (ctx.registry.val.get original).root = output.1.data.source.2.get := by
  obtain ⟨index,slot,key,owner⟩ := StoredGoldLookupFieldAssociation.receipt_packet_key ctx chooseHelper chooseBatch memory world
    prepared progress result executed receipt member framed history dummy extractCtx radius output accepted before parentBytes valid
    labelFits messageFits sources decoded
  obtain ⟨initialized,trace⟩ := NativeGoldLookupRegistryTrace.lookup_initializer ctx chooseHelper chooseBatch memory world
    prepared progress _ executed
  obtain ⟨original,selected,_,parameters,root⟩ := StoredGoldRegistryPacketAssociation.extraction_original ctx.registry _ world
    prepared.metadata initialized before parentBytes valid labelFits messageFits sources decoded index history (trace.trans included)
    _ dummy extractCtx radius output accepted key truthful safe
  have sameIndex : original.val = index.val := Option.some.inj (selected.symm.trans owner)
  have actualSlot : original.val = receipt.call.slot := sameIndex.trans slot
  obtain ⟨receiptSlot,receiptPosition,found,_,_,_⟩ := NativeGoldLookupAvailability.receipt_owner_key ctx chooseHelper chooseBatch memory world
    prepared progress result executed receipt member
  have oracle : ctx.registry.val.get original = receipt.call.oracle := by
    apply Option.some.inj
    have sameOption := congrArg (fun n => ctx.registry.val[n]?) (actualSlot.trans receiptPosition.symm)
    exact (List.getElem?_eq_getElem original.isLt).symm.trans (sameOption.trans found)
  exact ⟨index,original,slot,actualSlot,key,selected,oracle,parameters,root⟩

/-- The actual valid native registry packet produces its stored source vector;
no successful-decoder certificate or caller source vector is required. -/
theorem receipt_extracted {Memory : Type} (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (included : (run (program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (dummy : Vector Byte 64) (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history)
    (extractCtx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history
      (NativeGoldBatchReadExposure.phase (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work).pending.input
      dummy extractCtx radius).value = some output)
    (before : List TranscriptFrame.Frame)
    (parentBytes : (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1.input =
      TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (labelFits : NativeCanonicalLookupWire.registryLabel.length < TranscriptFrame.lengthLimit)
    (messageFits : (NativeCanonicalLookupWire.sourcesCodec.encode prepared.metadata.sources).length < TranscriptFrame.lengthLimit)
    : ∃ sources : Sources,
      (StoredRegistryPacketCost.decode prepared.metadata.parent.input).value = some sources ∧
    ∃ (index : Fin sources.val.length) (original : Fin ctx.registry.val.length),
      index.val = receipt.call.slot ∧ original.val = receipt.call.slot ∧
      output.1.data.source = sources.val.get index ∧
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧
      ctx.registry.val.get original = receipt.call.oracle ∧
      extractCtx.parameters = (ctx.registry.val.get original).parameters ∧
      (ctx.registry.val.get original).root = output.1.data.source.2.get := by
  obtain ⟨initialized,_⟩ := NativeGoldLookupRegistryTrace.lookup_initializer ctx chooseHelper chooseBatch memory world prepared progress _ executed
  let parent := (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1
  have origin := NativeSourceRegistry.initialized_origin NativeGoldBlockCode.description.row ctx.registry parent world prepared.metadata initialized
  have allValid : ∀ frame ∈ before ++ [⟨1,NativeCanonicalLookupWire.registryLabel,
      NativeCanonicalLookupWire.sourcesCodec.encode prepared.metadata.sources⟩], TranscriptFrame.Valid frame := by
    intro frame member
    rcases List.mem_append.mp member with old | added
    · exact valid frame old
    · obtain rfl := List.mem_singleton.mp added
      exact ⟨labelFits,messageFits⟩
  obtain ⟨sources,decoded,_⟩ := StoredRegistryPacketCost.decode_native_complete parent prepared.metadata.sources before parentBytes allValid
  rw [← origin.2.2.1] at decoded
  exact ⟨sources,decoded,receipt_original ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member framed
    history truthful included dummy safe extractCtx radius output accepted before parentBytes valid labelFits messageFits sources decoded⟩

end
end FormalProof4FHE.HasteBoots.StoredGoldLookupParameterAssociation
