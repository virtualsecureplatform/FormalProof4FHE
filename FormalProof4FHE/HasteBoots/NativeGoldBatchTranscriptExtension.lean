module

public import FormalProof4FHE.HasteBoots.NativePrimeIndexExtension
public import FormalProof4FHE.HasteBoots.NativeGoldBatchReadExposure
import all Init.Data.String.Defs
@[expose] public section

/-! Actual successful batch PCS execution preserves valid append-only transcript ancestry. Domains bound the original serialized binding and response messages; prime and atomic sampler receipts are handled by their real transitions. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchTranscriptExtension
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler)
open NativeGoldBlockCode (description)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript utf8)
open NativeTranscriptExtension (Extends)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def PayloadFits (ctx : Context) : Prop :=
  128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
    (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit

def ResponsesFit (ctx : Context) : Prop :=
  (NativeLookupRequestWire.rowCodec.encode ctx.opening.test ++
    (NativePrefixCodec.vector NativeLookupRequestWire.rowCodec).encode ctx.opening.evaluations).length < TranscriptFrame.lengthLimit

def Domain (ctx : Context) : Prop := PayloadFits ctx ∧ ResponsesFit ctx

theorem bind_many (parent : Transcript) (context root : Digest)
    (queries : NativePrefixCodec.Vector NativeGoldPcsWire.Query) (values : NativePrefixCodec.Vector NativeLookupRequestWire.Row)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode values).length < TranscriptFrame.lengthLimit) :
    Extends parent (NativeGoldBatchBinding.appendBound parent context root queries values) := by
  apply NativeTranscriptExtension.absorb parent 1 (utf8 "mw batched row-code v1") _
  simpa only [NativeGoldBatchExposure.frame,← NativeGoldBatchRootMentions.payload_encode] using
    NativeGoldBatchReadExposure.frame_valid context root queries values fits

theorem bind_responses (parent : Transcript) (opening : NativeGoldBatchOpening.Opening)
    (fits : (NativeLookupRequestWire.rowCodec.encode opening.test ++
      (NativePrefixCodec.vector NativeLookupRequestWire.rowCodec).encode opening.evaluations).length < TranscriptFrame.lengthLimit) :
    Extends parent (NativeGoldBatchOpening.bindResponses parent opening) := by
  apply NativeTranscriptExtension.absorb parent 1 (utf8 "mw batch linear responses") _
  constructor
  · change (utf8 "mw batch linear responses").length < TranscriptFrame.lengthLimit
    decide +kernel
  · exact fits

/-- All byte receipts and atomic responses preserve the actual framed parent,
including arbitrary canonical-candidate rejection before this successful prefix. -/
theorem prepared (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (domain : Domain ctx) : Extends ctx.parent work.sample.transcript := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,_,drawn,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  obtain ⟨_,bound,_,sampled⟩ := NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude
  obtain ⟨_,context,_,same,_⟩ := NativeGoldBatchBinding.bound_origin description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound
  have bindingExt : Extends ctx.parent binding.parent := by
    rw [congrArg NativeGoldBatchBinding.Bound.parent same]
    exact bind_many ctx.parent context ctx.root ctx.queries ctx.values domain.1
  have fieldExt := NativePrimeIndexExtension.prime_finished NativeFields.goldilocksModulus ctx.fieldFuel binding.parent .vector
    NativeGoldBatchPrelude.randomLabel geometry.randomCount world (by decide +kernel) state next sampled
  have responseExt := bind_responses next ctx.opening domain.2
  have atomicExt := NativePrimeIndexExtension.index_accepted (NativeGoldBatchOpening.bindResponses next ctx.opening) NativeGoldBatchColumns.label
    (description.row.blocks ctx.parameters.code) ctx.parameters.queries world sample (by decide +kernel) drawn
  exact bindingExt.trans (fieldExt.trans (responseExt.trans atomicExt))

theorem accepted {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : Transcript) (success : completion.status = .accepted parent) (domain : Domain ctx) : Extends ctx.parent parent := by
  have origin := NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed
  rw [(NativeGoldBatchPcsProgram.accepted_flags ctx choose fuel memory world work completion executed parent success).2.2]
  exact prepared ctx world work origin.prepared domain
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchTranscriptExtension
