module
public import FormalProof4FHE.HasteBoots.AllocatedSourceClaimFraming
@[expose] public section

/-! Dynamic source-batch trace framing uses only the actual checked call,
collector group cardinality and original proof response bytes. Failed later
calls retain earlier receipt framing; future receipt certificates are absent. -/
namespace FormalProof4FHE.HasteBoots.CollectedBatchFramingRecovery
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeGoldBlockCode (Stored Tables)
open NativeDeferredBatchVerification (Call Progress Result Trace)
open NativeDeferredBatchFraming (ValidProgress)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem call_width (registry : Vector (Oracle Stored)) (small : AllocatedSourceClaimFraming.RegistrySmall registry)
    (state : NativeDeferredOpeningBatch.State) (group : Fin (NativeSourceRegistry.groupCount state.sources))
    (opening : NativeGoldBatchOpening.Opening) (planned : Call)
    (computed : NativeDeferredBatchVerification.call registry state group opening = some planned) :
    planned.oracle.parameters.width.val ≤ 4 := by
  have found := (NativeDeferredBatchVerification.call_spec registry state group opening planned computed).2.2.1
  obtain ⟨inside,same⟩ := List.getElem?_eq_some_iff.mp found
  simpa only [List.get_eq_getElem,same] using (small ⟨planned.slot,inside⟩).1

theorem trace_framed {Memory : Type} {tables : Tables} {registry : Vector (Oracle Stored)}
    {state : NativeDeferredOpeningBatch.State} {fieldFuel : ℕ} {choose : NativeGoldBatchPcsProgram.Scheduler Memory}
    {workerFuel : ℕ} {world : World} {groups : List (Fin (NativeSourceRegistry.groupCount state.sources))}
    {openings : List NativeGoldBatchOpening.Opening} {before : Progress Memory} {result : Result Memory}
    {log : List NativeTranscript.Observation}
    (trace : Trace tables registry state fieldFuel choose workerFuel world groups openings before result log)
    (small : AllocatedSourceClaimFraming.RegistrySmall registry)
    (singleton : ∀ group, (NativeDeferredOpeningBatch.groupClaims state group).length ≤ 1)
    (responses : ∀ opening ∈ openings, (NativeGoldBatchResponseBinding.payload opening).length < TranscriptFrame.lengthLimit)
    (valid : ValidProgress tables fieldFuel before) : ValidProgress tables fieldFuel result.progress := by
  revert responses valid
  induction trace with
  | done before => intro _ valid; exact valid
  | packets groups openings before mismatch => intro _ valid; exact valid
  | index group rest opening openings before missing => intro _ valid; exact valid
  | stopped group rest opening openings before planned outcome log computed executed failed => intro _ valid; exact valid
  | passed group rest opening openings before after planned outcome log result later computed executed advanced tail ih =>
    intro responses valid
    have spec := NativeDeferredBatchVerification.call_spec registry state group opening planned computed
    obtain ⟨work,completion,next,sameOutcome,accepted,sameAfter⟩ :=
      NativeDeferredBatchVerification.advance_spec before planned outcome after advanced
    have completed := (congrArg Prod.fst executed).trans sameOutcome
    have count : planned.queries.val.length ≤ 1 := by
      rw [spec.2.2.2.1]
      simpa only [NativeDeferredOpeningBatch.groupQueries,List.length_map] using singleton group
    have metadata := CheckedBatchMetadataSize.completed_fits (planned.context tables fieldFuel before.parent)
      choose workerFuel before.memory world work completion completed (call_width registry small state group opening planned computed) count
    have response : (NativeGoldBatchResponseBinding.payload planned.opening).length < TranscriptFrame.lengthLimit := by
      rw [spec.2.2.2.2.2]
      exact responses opening (by simp)
    have fits : NativeDeferredBatchFraming.CallFits planned := ⟨metadata,response⟩
    have extension := NativeGoldBatchTranscriptExtension.accepted (planned.context tables fieldFuel before.parent) choose workerFuel before.memory
      world work completion completed next accepted fits
    have validAfter : ValidProgress tables fieldFuel after := by
      rw [sameAfter]
      constructor
      · exact NativeTranscriptFraming.of_extension valid.1 extension
      · intro receipt member
        rcases List.mem_append.mp member with old | added
        · exact valid.2 receipt old
        · obtain rfl := List.mem_singleton.mp added
          exact NativeDeferredBatchFraming.call_framed tables fieldFuel before.parent planned valid.1 fits
    exact ih (fun opening member => responses opening (List.mem_cons_of_mem _ member)) validAfter

theorem program_framed {Memory : Type} (ctx : NativeDeferredBatchVerification.Context)
    (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World) (after : Progress Memory)
    (executed : (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.1 = .verification (.done after))
    (small : AllocatedSourceClaimFraming.RegistrySmall ctx.registry)
    (singleton : ∀ group, (NativeDeferredOpeningBatch.groupClaims ctx.state group).length ≤ 1)
    (responses : ∀ opening ∈ ctx.proof.val, (NativeGoldBatchResponseBinding.payload opening).length < TranscriptFrame.lengthLimit)
    (framed : NativeTranscriptFraming.Framed ctx.state.parent) : ValidProgress ctx.tables ctx.fieldFuel after := by
  have trace := (NativeDeferredBatchVerification.program_trace ctx choose memory world (.done after) executed).2
  exact trace_framed trace small singleton responses
    ⟨NativeTranscriptFraming.of_extension framed (NativeDeferredBatchFraming.seal_extension ctx.state ctx.proof.val.length),by simp⟩

open NativeGoldHelperVerification (Context)
open NativeGoldBatchOpening (Opening)

variable {Memory : Type} (ctx : Context (Vector Opening))
  (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
  (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
  (progress : NativeSharedSourceClaims.Progress) (after : Progress Memory)
  (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
    .batches lookup progress (.verification (.done after)))

include executed

theorem source_parent (helperWidth : ctx.helper.width.val ≤ 4) (sourceSmall : AllocatedSourceClaimFraming.RegistrySmall ctx.registry)
    (framed : NativeTranscriptFraming.Framed ctx.parent)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit)
    (proofDomain : SharedProofSerializationDomain.Domain ctx.proof) : NativeTranscriptFraming.Framed progress.state.parent := by
  have initial := (HelperReceiptFramingRecovery.receipts_framed ctx chooseHelper chooseBatch memory world lookup progress after executed
    helperWidth framed parentDomain registryFits proofDomain).1
  have extension := AllocatedSourceClaimFraming.program NativeGoldBlockCode.description.row ctx.registry sourceSmall ctx.requests lookup.query ctx.proof.sources
    (NativeGoldLookupVerification.initial lookup) world
  have collected := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress (.verification (.done after)) executed).2.1
  change NativeTranscriptExtension.Extends lookup.helpers.lastAccepted (run (NativeGoldLookupVerification.sourceProgram ctx lookup) world).run.1.progress.state.parent at extension
  rw [collected] at extension
  exact NativeTranscriptFraming.of_extension initial extension

theorem receipts_framed (helperWidth : ctx.helper.width.val ≤ 4) (sourceSmall : AllocatedSourceClaimFraming.RegistrySmall ctx.registry)
    (framed : NativeTranscriptFraming.Framed ctx.parent)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit)
    (proofDomain : SharedProofSerializationDomain.Domain ctx.proof) : ValidProgress ctx.tables ctx.fieldFuel after := by
  have batch := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) executed).2.2.1
  exact program_framed (NativeGoldLookupVerification.batchContext ctx progress) chooseBatch lookup.helpers.memory world after batch sourceSmall
    (SourceClaimGroupCardinality.collected_group_le_one ctx chooseHelper chooseBatch memory world lookup progress after executed)
    proofDomain.sourceResponses
    (source_parent ctx chooseHelper chooseBatch memory world lookup progress after executed helperWidth sourceSmall framed parentDomain registryFits proofDomain)

end
end FormalProof4FHE.HasteBoots.CollectedBatchFramingRecovery
