module

public import FormalProof4FHE.HasteBoots.NativePrimeIndexExtension
public import FormalProof4FHE.HasteBoots.NativeGoldPcsProgram
import all Init.Data.String.Defs
@[expose] public section

/-! Single-opening helper PCS framing follows its actual checked prefix,
completed field sampler, response binding and atomic index request. Bounds
mention only original serialized messages, not future oracle answers. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsTranscriptExtension
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (description)
open NativeTranscript (Transcript utf8)
open NativeTranscriptExtension (Extends)
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def Domain (ctx : Context) : Prop :=
  (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit ∧
  (NativeGoldPcsWire.responses ctx.opening.test ctx.opening.evaluation).length < TranscriptFrame.lengthLimit

theorem bind_opening (parent : Transcript) (context root : Digest)
    (query : NativeGoldPcsWire.Query) (values : NativeLookupRequestWire.Row)
    (fits : (NativeGoldPcsWire.opening root query values).length < TranscriptFrame.lengthLimit) :
    Extends parent (NativeGoldPcsBinding.appendBound parent context root query values) := by
  apply Extends.trans (NativeTranscriptExtension.absorb parent 1 (utf8 "mw brakedown row-code v2") (List.ofFn context)
    ⟨by change (utf8 "mw brakedown row-code v2").length < _; decide +kernel,by change (List.ofFn context).length < _; simp only [List.length_ofFn]; decide +kernel⟩)
  exact NativeTranscriptExtension.absorb _ 1 (utf8 "mw commitment and query") _ ⟨by change (utf8 "mw commitment and query").length < _; decide +kernel,fits⟩

theorem binding (ctx : Context) (world : World) (bound : Transcript)
    (executed : (run (NativeGoldPcsBinding.protocol description.row ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed) world).run.1 = some bound)
    (domain : Domain ctx) : Extends ctx.transcript bound := by
  simp only [NativeGoldPcsBinding.protocol] at executed
  split at executed
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind] at executed
    cases computed : (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 with
    | none => simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
    | some context =>
      simp only [computed,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed
      cases executed
      exact bind_opening ctx.transcript context ctx.root ctx.query ctx.claimed domain.1
  · contradiction

theorem bind_responses (parent : Transcript) (opening : NativeGoldPcsOpening.Opening)
    (fits : (NativeGoldPcsWire.responses opening.test opening.evaluation).length < TranscriptFrame.lengthLimit) :
    Extends parent (NativeGoldPcsWire.bindResponses parent opening.test opening.evaluation) :=
  NativeTranscriptExtension.absorb parent 1 (utf8 "mw linear responses") _ ⟨by change (utf8 "mw linear responses").length < _; decide +kernel,fits⟩

theorem prepared (ctx : Context) (world : World) (work : Prepared)
    (executed : (run ctx.prefix world).run.1 = .prepared work)
    (domain : Domain ctx) : Extends ctx.transcript work.transcript := by
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,_,rfl⟩ :=
    NativeGoldPcsWorkers.prepared_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel world work executed
  have original := (NativeGoldPcsEncoding.encoded_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel world geometry state weights sample planRoot test evaluation encoded).1
  obtain ⟨next,prior,_,drawn,_⟩ := NativeGoldPcsColumns.columns_origin description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel world geometry state weights sample original
  obtain ⟨_,_,bound,boundRead,sampled⟩ := NativeGoldPcsPrelude.sampling_origin description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel world geometry (.finished state next) prior
  have field := NativePrimeIndexExtension.prime_finished NativeFields.goldilocksModulus ctx.fieldFuel bound .vector
    NativeGoldPcsPrelude.randomLabel geometry.randomCount world (by decide +kernel) state next sampled
  have atomic := NativePrimeIndexExtension.index_accepted (NativeGoldPcsWire.bindResponses next ctx.opening.test ctx.opening.evaluation)
    NativeGoldPcsColumns.label (description.row.blocks ctx.parameters.code) ctx.parameters.queries world sample (by decide +kernel) drawn
  exact (binding ctx world bound boundRead domain).trans (field.trans ((bind_responses next ctx.opening domain.2).trans atomic))

theorem accepted {Memory : Type} (ctx : Context) (choose : NativeGoldPcsProgram.Scheduler Memory) (fuel : ℕ)
    (memory : Memory) (world : World) (work : Prepared)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (next : Transcript) (success : completion.status = .accepted next) (domain : Domain ctx) :
    Extends ctx.transcript next := by
  rw [(NativeGoldPcsProgram.accepted_flags ctx choose fuel memory world work completion executed next success).2.2]
  exact prepared ctx world work (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared domain
end
end FormalProof4FHE.HasteBoots.NativeGoldPcsTranscriptExtension
