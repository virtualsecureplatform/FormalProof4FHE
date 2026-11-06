module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchChallengeOrigin
import all Init.Data.String.Defs
@[expose] public section

/-! An actual successful native preparation supplies the parsed challenge
view and its exact collected state. Framing bounds are explicit encoder
obligations. Structural recovery alone does not assert past source ownership
or authentication, and is not a Rust decoder refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchPreparedChallenge
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBatchChallengeOrigin (view input)
open NativeGoldBatchColumnInputView (responseFrame)
open NativeGoldBatchChallengeLink (receiptFrame)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

theorem frames_valid (field : NativeGoldBatchFieldInputView.View) (opening : NativeGoldBatchOpening.Opening)
    (label : Input) (domain count : NativeUsizeMessage.Usize) (payload : Input)
    (fieldValid : ∀ frame ∈ field.frames, TranscriptFrame.Valid frame)
    (labelFits : label.length < TranscriptFrame.lengthLimit) (length : payload.length = 80)
    (responseFits : (NativeGoldBatchResponseBinding.payload opening).length < TranscriptFrame.lengthLimit) :
    ∀ frame ∈ (view field opening label domain count payload).column.index.frames, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [view,NativeIndexInputView.View.frames,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (member | rfl | rfl) | rfl | rfl
  · exact fieldValid frame member
  · constructor
    · change NativeGoldBatchPrelude.randomLabel.length < TranscriptFrame.lengthLimit
      decide +kernel
    · simpa only [receiptFrame,length] using (by decide +kernel : 80 < TranscriptFrame.lengthLimit)
  · refine ⟨?_,responseFits⟩
    change (NativeTranscript.utf8 "mw batch linear responses").length < TranscriptFrame.lengthLimit
    decide +kernel
  · constructor
    · change (NativeTranscript.utf8 "index domain").length < TranscriptFrame.lengthLimit
      decide +kernel
    · simp only [TranscriptFrame.littleEndian_length]
      decide +kernel
  · exact ⟨labelFits,by simp only [TranscriptFrame.littleEndian_length]; decide +kernel⟩

def recovered (ctx : Context) (world : World) (work : Prepared) (before : List Frame) (context : Digest) :=
  view ⟨before,⟨context,ctx.root,ctx.queries,ctx.values⟩,work.geometry.randomCount⟩ ctx.opening
    NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries
    (NativeTranscript.receipt world work.state.phase.consumed).run.1

/-- The decoded view comes from the actual native column input. Its phase
and coefficient count are derived from preparation rather than supplied as
freshness or sampler certificates. -/
theorem prepared_link (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit) :
    ∃ context : Digest,
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
      NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) =
        some (recovered ctx world work before context) ∧
      (recovered ctx world work before context).field.phase ctx.parent.profile = NativeGoldBatchRandomLaw.phase work ∧
      (NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel (recovered ctx world work before context) world).1 = work.state := by
  obtain ⟨context,hashed,phase,parsed⟩ := NativeGoldBatchFieldExposure.prepared_phase ctx world work prepared before parent valid fits
  let field : NativeGoldBatchFieldInputView.View := ⟨before,⟨context,ctx.root,ctx.queries,ctx.values⟩,work.geometry.randomCount⟩
  have fieldParsed : NativeGoldBatchFieldInputView.parse (field.phase ctx.parent.profile).pending.input = some field := by
    rw [phase]
    exact parsed
  have sound := NativeGoldBatchFieldInputView.parse_sound _ field fieldParsed ctx.parent.profile
  have native := NativeGoldBatchChallengeOrigin.parse_native field ctx.parent.profile ctx.opening NativeGoldBatchColumns.label
    ctx.parameters.code.blocks ctx.parameters.queries (NativeTranscript.receipt world work.state.phase.consumed).run.1
    (NativeTranscript.receipt_length world _) sound.2.1 (NativeGoldBatchColumnRequestLaw.prepared_check ctx world work prepared)
    (frames_valid field ctx.opening _ _ _ _ sound.2.2 (by decide +kernel) (NativeTranscript.receipt_length world _) responseFits)
  refine ⟨context,hashed,?_,phase,?_⟩
  · rw [NativeGoldBatchChallengeOrigin.prepared_input ctx world work prepared field phase]
    exact native
  · obtain ⟨log,collected⟩ := NativeGoldBatchChallengeOrigin.prepared_collector ctx world work prepared
    change (NativeFieldVector.execute NativeFields.goldilocksModulus ctx.fieldFuel
      (NativeFieldVector.initial (field.phase ctx.parent.profile) work.geometry.randomCount.val) world).1 = work.state
    rw [phase,collected]

/-- Any successful parsing of that actual input recovers the same field
state, true receipt, raw responses and original binding. This is pointwise
native execution recovery, not a claim that future work is past-measurable. -/
theorem parsed_origin (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded) :
    decoded.field.count = work.geometry.randomCount ∧
      decoded.field.phase ctx.parent.profile = NativeGoldBatchRandomLaw.phase work ∧
      (NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel decoded world).1 = work.state ∧
      decoded.receipt = (NativeTranscript.receipt world work.state.phase.consumed).run.1 ∧
      decoded.column.opening.test = ctx.opening.test ∧ decoded.column.opening.evaluations = ctx.opening.evaluations ∧
      decoded.field.data.root = ctx.root ∧ decoded.field.data.queries = ctx.queries ∧ decoded.field.data.values = ctx.values ∧
      decoded.column.index.domain = ctx.parameters.code.blocks ∧ decoded.column.index.count = ctx.parameters.queries ∧
      decoded.column.index.label = NativeGoldBatchColumns.label ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some decoded.field.data.context := by
  obtain ⟨context,hashed,native,phase,collected⟩ := prepared_link ctx world work prepared before parent valid fits responseFits
  have equal := Option.some.inj (parsed.symm.trans native)
  subst decoded
  exact ⟨rfl,phase,collected,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hashed⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchPreparedChallenge
