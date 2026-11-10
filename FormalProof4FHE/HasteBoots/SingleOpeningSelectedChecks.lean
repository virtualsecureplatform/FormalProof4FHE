module
public import FormalProof4FHE.HasteBoots.SingleOpeningFixedSourceChecks
public import FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnChecks
@[expose] public section

/-! Actual accepted single-opening checks at the exact source selected by
an earlier field read. Context, log, and original ordered sampler receipt
are retained explicitly; no later existential source can replace them. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningSelectedChecks
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (shape)
open NativeGoldBatchFamilyAvailability (reconstructed)
open SingleOpeningFieldInputView (View)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem accepted_view {Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (origin : CacheBackedSingleOpening.Origin ctx) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (before after : List Observation) (field : View)
    (parsed : SingleOpeningFieldInputView.parse (SingleOpeningRandomLaw.phase receipt).pending.input = some field)
    (offset : ℕ) (values : Input) (positive : values ≠ [])
    (accepted : SingleOpeningAvailability.Accepted world
      (before++ .output (SingleOpeningRandomLaw.phase receipt).pending.input offset values :: after) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (before++ .output (SingleOpeningRandomLaw.phase receipt).pending.input offset values :: after))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape
      (reconstructed dummy (before++ .output (SingleOpeningRandomLaw.phase receipt).pending.input offset values :: after))) :
    ∃ view : SingleOpeningRectangularAcceptance.View dummy ctx world work
        (before++ .output (SingleOpeningRandomLaw.phase receipt).pending.input offset values :: after) origin,
      view.context = field.data.context ∧ view.log = SingleOpeningFirstFieldSource.selectedLog dummy before field ∧ view.sample = sample := by
  obtain ⟨requests,hashed,computed,snapshots,equations⟩ := SingleOpeningFirstFieldSource.accepted_selected dummy ctx world work receipt
    choose fuel memory before after field parsed offset values positive accepted truthful noDisagreement
  obtain ⟨_,completion,next,executed,status,_⟩ := accepted
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨actual,draw,sampled,jobs,typed,ordered,randomChecks,structuredChecks⟩ :=
    SingleOpeningFixedSourceChecks.checks dummy field.data.context ctx world work prepared origin requests computed
      (SingleOpeningFirstFieldSource.selectedLog dummy before field) (fun entry member => (equations entry member).2)
  have actualEq : actual = sample := by
    obtain ⟨state,columns,_,_⟩ := sampled
    have same := receipt.columns.symm.trans columns
    have result := congrArg (fun outcome => match outcome with
      | NativeGoldPcsColumns.Outcome.columns _ _ _ value => some value
      | _ => none) same
    exact (Option.some.inj result).symm
  subst actual
  refine ⟨⟨prepared,field.data.context,SingleOpeningFirstFieldSource.selectedLog dummy before field,sample,draw,
    hashed,snapshots,sampled,jobs,typed,ordered,randomChecks,structuredChecks,?_⟩,rfl,rfl,rfl⟩
  exact SingleOpeningRectangularData.accepted_claim ctx world work prepared choose fuel memory completion executed next status

/-- Recover the precise first-exposure log from the full history. Positive
reads at arbitrary offsets qualify; starts and empty reads do not. -/
theorem recovered_view {Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (origin : CacheBackedSingleOpening.Origin ctx) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (history : List Observation) (field : View)
    (parsed : SingleOpeningFieldInputView.parse (SingleOpeningRandomLaw.phase receipt).pending.input = some field)
    (sourceLog : NativeRootFamilySourceSelection.Log)
    (found : SingleOpeningFirstFieldSource.recover dummy history field = some sourceLog)
    (accepted : SingleOpeningAvailability.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history)
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy history)) :
    ∃ view : SingleOpeningRectangularAcceptance.View dummy ctx world work history origin,
      view.context = field.data.context ∧ view.log = sourceLog ∧ view.sample = sample := by
  have inputEq : SingleOpeningFirstFieldSource.input field = (SingleOpeningRandomLaw.phase receipt).pending.input := by
    have same := (SingleOpeningFieldInputView.parse_sound _ field parsed ctx.transcript.profile).1
    rw [SingleOpeningFieldInputView.phase_input] at same
    exact same
  obtain ⟨before,offset,values,after,_,positive,split,logEq⟩ :=
    SingleOpeningFirstFieldSource.recover_sound dummy history field sourceLog found
  rw [inputEq] at split
  subst history
  obtain ⟨view,context,sameLog,sameSample⟩ := accepted_view dummy receipt origin choose fuel memory
    before after field parsed offset values positive accepted truthful noDisagreement
  exact ⟨view,context,sameLog.trans logEq.symm,sameSample⟩

/-- The concrete parsed family uses the log recovered by the original
history and the actual ordered native sample, including repeated draws. -/
theorem recovered_checks {Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (origin : CacheBackedSingleOpening.Origin ctx) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (history : List Observation) (decoded : SingleOpeningChallengeLink.View)
    (sourceLog : NativeRootFamilySourceSelection.Log)
    (found : SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog)
    (accepted : SingleOpeningAvailability.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history)
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy history))
    (before : List TranscriptFrame.Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded) :
    ∃ draw : Fin ctx.parameters.queries.val → Fin (2^NativeGoldBlockCode.logSize ctx.parameters.code),
      NativeGoldPcsDraws.typed (NativeGoldBlockCode.logSize ctx.parameters.code) ctx.parameters.queries.val sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = sample.draws ∧
      ∀ test : SingleOpeningConcreteColumnFamily.Test ctx, ColumnOpening.Agrees
        (SingleOpeningConcreteColumnFamily.raw dummy ctx decoded sourceLog
          (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 test)
        (SingleOpeningConcreteColumnFamily.claim ctx origin.primitive decoded
          (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 test) draw := by
  have acceptedCopy := accepted
  obtain ⟨_,completion,_,executed,_,_⟩ := acceptedCopy
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have phaseEq := (SingleOpeningPreparedChallenge.parsed_origin receipt prepared before parent valid fits responseFits decoded parsed).2.1
  have fieldParsed := SingleOpeningFirstFieldSource.linked_field_parsed _ decoded parsed
  change SingleOpeningFieldInputView.parse (TranscriptFrame.encodeMany decoded.field.frames) = some decoded.field at fieldParsed
  rw [← SingleOpeningFieldInputView.phase_input decoded.field ctx.transcript.profile,phaseEq] at fieldParsed
  obtain ⟨view,_,sameLog,sameSample⟩ := recovered_view dummy receipt origin choose fuel memory history decoded.field
    fieldParsed sourceLog found accepted truthful noDisagreement
  have checks := SingleOpeningConcreteColumnChecks.accepted_checks view receipt before parent valid fits responseFits decoded parsed
  rw [sameLog] at checks
  exact ⟨view.draw,by simpa only [sameSample] using view.typed,by simpa only [sameSample] using view.ordered,checks⟩

end
end FormalProof4FHE.HasteBoots.SingleOpeningSelectedChecks
