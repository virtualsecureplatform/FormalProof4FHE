/-! Dispatcher receipts derive membership before reading the original extracted
Rust registry. Framing and native dispatcher refinement remain explicit. -/
namespace HasteBootsExtractedRegistryLookup
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open HasteBootsExtractedRegistryDecode (Source decode root)
open HasteBootsExtractedRegistry (registry registry_slot)
open HasteBootsExtractedParametersDecode (decodeParameters)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
open formalproof4fhe_native_registry_fixture (registry_get)
noncomputable section

theorem receipt_original_read {Memory : Type} (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (receipt : NativeDeferredBatchVerification.Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (included : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (dummy : _root_.Vector InputIndexedOracle.Byte 64) (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history)
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
    (source : Slice Source) (sourceDecoded : registry source = some ctx.registry)
    : ∃ (original : Fin ctx.registry.val.length) (word : Usize) (entry : Source),
      original.val = receipt.call.slot ∧ word.val = receipt.call.slot ∧
      registry_get source word = .ok (some (entry.parameters,entry.commitment.root)) ∧
      decode entry = some receipt.call.oracle ∧
      decodeParameters entry.parameters = some extractCtx.parameters ∧
      root entry.commitment.root = output.1.data.source.2.get := by
  obtain ⟨_,_,_,original,_,slot,_,_,oracle,parameters,rootEq⟩ :=
    StoredGoldLookupParameterAssociation.receipt_extracted ctx chooseHelper chooseBatch memory world prepared progress result
      executed receipt member framed history truthful included dummy safe extractCtx radius output accepted before parentBytes valid
      labelFits messageFits
  obtain ⟨word,entry,wordValue,read,entryDecoded⟩ := registry_slot source ctx.registry sourceDecoded original
  have fields := HasteBootsExtractedRegistryDecode.decode_fields entry (ctx.registry.val.get original) entryDecoded
  refine ⟨original,word,entry,slot,wordValue.trans slot,read,?_,?_,fields.2.symm.trans rootEq⟩
  · rw [← oracle]; exact entryDecoded
  · rw [parameters]; exact fields.1

theorem receipt_bad_or_original_read {Memory A : Type} (whole : OracleProgram.Program A) (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (receipt : NativeDeferredBatchVerification.Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (included : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist (run whole world).run.2)
    (dummy : _root_.Vector InputIndexedOracle.Byte 64)
    (extractCtx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run (run whole world).run.2
      (NativeGoldBatchReadExposure.phase (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work).pending.input
      dummy extractCtx radius).value = some output)
    (before : List TranscriptFrame.Frame)
    (parentBytes : (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1.input =
      TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (labelFits : NativeCanonicalLookupWire.registryLabel.length < TranscriptFrame.lengthLimit)
    (messageFits : (NativeCanonicalLookupWire.sourcesCodec.encode prepared.metadata.sources).length < TranscriptFrame.lengthLimit)
    (source : Slice Source) (sourceDecoded : registry source = some ctx.registry)
    : NativeRootFamilyLifetime.Bad dummy.get (run whole world).run.2 ∨
      (∃ (original : Fin ctx.registry.val.length) (word : Usize) (entry : Source),
      original.val = receipt.call.slot ∧ word.val = receipt.call.slot ∧
      registry_get source word = .ok (some (entry.parameters,entry.commitment.root)) ∧
      decode entry = some receipt.call.oracle ∧
      decodeParameters entry.parameters = some extractCtx.parameters ∧
      root entry.commitment.root = output.1.data.source.2.get) := by
  classical
  by_cases bad : NativeRootFamilyLifetime.Bad dummy.get (run whole world).run.2
  · exact Or.inl bad
  · exact Or.inr (receipt_original_read ctx chooseHelper chooseBatch memory world prepared progress result executed
      receipt member framed (run whole world).run.2 ((OracleProgram.run_replay whole).truthful world) included dummy bad
      extractCtx radius output accepted before parentBytes valid labelFits messageFits source sourceDecoded)

end
end HasteBootsExtractedRegistryLookup
