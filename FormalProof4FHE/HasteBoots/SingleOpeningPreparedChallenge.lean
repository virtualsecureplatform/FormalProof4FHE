module
public import FormalProof4FHE.HasteBoots.SingleOpeningChallengeLink
import all Init.Data.String.Defs
@[expose] public section

/-! The strict linked view is produced by an actual native single-opening
collector, true receipt and response-bound column request. Native framing
bounds remain explicit. Structural receipt quotes alone do not certify the
receipt, nor make future work measurable in an earlier history. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningPreparedChallenge
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open SingleOpeningSamplingReceipt (Receipt)
open SingleOpeningChallengeLink (receiptFrame)
open SingleOpeningColumnInputView (responses responseFrame)
open TranscriptFrame (Frame encodeMany)
open OracleProgram (run)
noncomputable section

/-- Authentication paths are later data and absent from the response nonce. -/
def view (field : SingleOpeningFieldInputView.View) (opening : NativeGoldPcsOpening.Opening)
    (label : Input) (domain count : NativeUsizeMessage.Usize) (payload : Input) : SingleOpeningChallengeLink.View :=
  ⟨⟨⟨field.frames++[receiptFrame payload,responseFrame opening],label,domain,count⟩,responses opening⟩,
    field,field.frames,payload⟩

def input (field : SingleOpeningFieldInputView.View) (profile : Digest) (opening : NativeGoldPcsOpening.Opening)
    (label : Input) (domain count : NativeUsizeMessage.Usize) (payload : Input) : Input :=
  SingleOpeningColumnLaw.boundInput ⟨encodeMany (field.frames++[receiptFrame payload]),profile⟩ label domain count opening

theorem parse_native (field : SingleOpeningFieldInputView.View) (profile : Digest)
    (opening : NativeGoldPcsOpening.Opening) (label : Input) (domain count : NativeUsizeMessage.Usize)
    (payload : Input) (length : payload.length = 80) (positive : 0 < field.count.val)
    (valid : NativeIndexRequest.check domain count = true)
    (framed : ∀ frame ∈ (view field opening label domain count payload).column.index.frames, TranscriptFrame.Valid frame) :
    SingleOpeningChallengeLink.parse (input field profile opening label domain count payload) = some (view field opening label domain count payload) := by
  have fieldValid : ∀ frame ∈ field.frames, TranscriptFrame.Valid frame := by
    intro frame member
    apply framed frame
    simp only [view,NativeIndexInputView.View.frames,List.mem_append,List.mem_cons,List.not_mem_nil]
    exact Or.inl (Or.inl member)
  have columnFramed : ∀ frame ∈ NativeIndexInputView.View.frames
      ⟨(field.frames++[receiptFrame payload])++[responseFrame opening],label,domain,count⟩, TranscriptFrame.Valid frame := by
    simpa only [view,List.append_assoc,List.cons_append,List.nil_append] using framed
  unfold SingleOpeningChallengeLink.parse input
  rw [SingleOpeningColumnInputView.parse_native (field.frames++[receiptFrame payload]) profile label domain count opening valid columnFramed,Option.bind_some]
  simpa only [view,List.append_assoc,List.cons_append,List.nil_append,responseFrame,responses,SingleOpeningColumnLaw.payload] using
    SingleOpeningChallengeLink.readColumn_native field (responses opening) label domain count payload length positive fieldValid

variable {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}

theorem prepared_collector (receipt : Receipt ctx world work sample) :
    ∃ log, NativeFieldVector.execute NativeFields.goldilocksModulus ctx.fieldFuel
      (NativeFieldVector.initial (SingleOpeningRandomLaw.phase receipt) work.geometry.randomCount.val) world = (receipt.state,log) := by
  obtain ⟨log,collected,_,_⟩ := NativeFieldReceipt.finished_origin NativeFields.goldilocksModulus ctx.fieldFuel work.geometry.randomCount.val
    (NativePrimeRequest.prepare receipt.bound .vector) NativeGoldPcsPrelude.randomLabel world receipt.state receipt.next receipt.field
  exact ⟨log,collected⟩

theorem prepared_header (receipt : Receipt ctx world work sample) :
    receipt.state.phase.pending = (SingleOpeningRandomLaw.phase receipt).pending ∧ receipt.state.phase.label = NativeGoldPcsPrelude.randomLabel := by
  obtain ⟨log,collected⟩ := prepared_collector receipt
  have header := NativeFieldVector.header_preserved NativeFields.goldilocksModulus ctx.fieldFuel
    (NativeFieldVector.initial (SingleOpeningRandomLaw.phase receipt) work.geometry.randomCount.val) world
  rw [collected] at header
  exact header

/-- The actual nonce includes the original true native receipt, with no new
nonwrapping premise on its fixed-width consumed-length header. -/
theorem prepared_input (receipt : Receipt ctx world work sample) (field : SingleOpeningFieldInputView.View)
    (phase : field.phase ctx.transcript.profile = SingleOpeningRandomLaw.phase receipt) :
    SingleOpeningColumnLaw.input receipt world = input field ctx.transcript.profile ctx.opening NativeGoldPcsColumns.label
      ctx.parameters.code.blocks ctx.parameters.queries (NativeTranscript.receipt world receipt.state.phase.consumed).run.1 := by
  have header := prepared_header receipt
  have fieldInput := SingleOpeningFieldInputView.phase_input field ctx.transcript.profile
  rw [phase] at fieldInput
  have parentInput : (receipt.parent world).input = encodeMany (field.frames++[receiptFrame (NativeTranscript.receipt world receipt.state.phase.consumed).run.1]) := by
    change receipt.state.phase.pending.input ++ TranscriptFrame.encode
      ⟨5,receipt.state.phase.label,(NativeTranscript.receipt world receipt.state.phase.consumed).run.1⟩ = _
    rw [header.1,header.2,fieldInput,SingleOpeningExposure.encodeMany_append]
    simp only [encodeMany,List.append_nil,receiptFrame]
  unfold SingleOpeningColumnLaw.input SingleOpeningColumnLaw.transcript input SingleOpeningColumnLaw.boundInput
    NativePrequeryIndexLaw.requestInput NativeIndexRequest.prepare NativeGoldPcsWire.bindResponses NativeTranscript.appendBytes NativeTranscript.absorb
  simp only [parentInput]

theorem frames_valid (field : SingleOpeningFieldInputView.View) (opening : NativeGoldPcsOpening.Opening)
    (label : Input) (domain count : NativeUsizeMessage.Usize) (payload : Input)
    (fieldValid : ∀ frame ∈ field.frames, TranscriptFrame.Valid frame)
    (labelFits : label.length < TranscriptFrame.lengthLimit) (length : payload.length = 80)
    (responseFits : (SingleOpeningColumnLaw.payload opening).length < TranscriptFrame.lengthLimit) :
    ∀ frame ∈ (view field opening label domain count payload).column.index.frames, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [view,NativeIndexInputView.View.frames,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (member | rfl | rfl) | rfl | rfl
  · exact fieldValid frame member
  · constructor
    · change NativeGoldPcsPrelude.randomLabel.length < TranscriptFrame.lengthLimit
      decide +kernel
    · simpa only [receiptFrame,length] using (by decide +kernel : 80 < TranscriptFrame.lengthLimit)
  · refine ⟨?_,responseFits⟩
    change (NativeTranscript.utf8 "mw linear responses").length < TranscriptFrame.lengthLimit
    decide +kernel
  · constructor
    · change (NativeTranscript.utf8 "index domain").length < TranscriptFrame.lengthLimit
      decide +kernel
    · simp only [TranscriptFrame.littleEndian_length]
      decide +kernel
  · exact ⟨labelFits,by simp only [TranscriptFrame.littleEndian_length]; decide +kernel⟩

def recovered (receipt : Receipt ctx world work sample) (before : List Frame) (context : Digest) :=
  view ⟨before,⟨context,ctx.root,ctx.query,ctx.claimed⟩,work.geometry.randomCount⟩ ctx.opening NativeGoldPcsColumns.label
    ctx.parameters.code.blocks ctx.parameters.queries (NativeTranscript.receipt world receipt.state.phase.consumed).run.1

def collected (profile : Digest) (fuel : ℕ) (decoded : SingleOpeningChallengeLink.View) (other : World) :=
  NativeFieldVector.execute NativeFields.goldilocksModulus fuel
    (NativeFieldVector.initial (decoded.field.phase profile) decoded.field.count.val) other

/-- Native preparation supplies the complete parse, exact original phase and
collector state. No receipt knowledge or first-read eligibility is assumed. -/
theorem prepared_link (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.transcript.input = encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit) :
    ∃ context : Digest,
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
      SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some (recovered receipt before context) ∧
      (recovered receipt before context).field.phase ctx.transcript.profile = SingleOpeningRandomLaw.phase receipt ∧
      (collected ctx.transcript.profile ctx.fieldFuel (recovered receipt before context) world).1 = receipt.state := by
  obtain ⟨context,hashed,parsed⟩ := SingleOpeningFieldInputView.receipt_parse receipt prepared before parent valid fits
  obtain ⟨other,otherHash,bound⟩ := SingleOpeningExposure.binding_origin ctx world receipt.bound receipt.binding
  have sameContext : other = context := Option.some.inj (otherHash.symm.trans hashed)
  subst other
  let field : SingleOpeningFieldInputView.View := ⟨before,⟨context,ctx.root,ctx.query,ctx.claimed⟩,work.geometry.randomCount⟩
  have original : (⟨encodeMany before,ctx.transcript.profile⟩ : NativeTranscript.Transcript) = ctx.transcript := by rw [← parent]
  have phase : field.phase ctx.transcript.profile = SingleOpeningRandomLaw.phase receipt := by
    change NativePrimeRequest.phase NativeFields.goldilocksModulus
      (NativeGoldPcsBinding.appendBound ⟨encodeMany before,ctx.transcript.profile⟩ context ctx.root ctx.query ctx.claimed)
      .vector NativeGoldPcsPrelude.randomLabel work.geometry.randomCount = _
    rw [original,← bound]
    rfl
  have fieldParsed : SingleOpeningFieldInputView.parse (field.phase ctx.transcript.profile).pending.input = some field := by
    rw [phase]
    exact parsed
  have sound := SingleOpeningFieldInputView.parse_sound _ field fieldParsed ctx.transcript.profile
  have native := parse_native field ctx.transcript.profile ctx.opening NativeGoldPcsColumns.label ctx.parameters.code.blocks ctx.parameters.queries
    (NativeTranscript.receipt world receipt.state.phase.consumed).run.1 (NativeTranscript.receipt_length world _) sound.2.1
    (SingleOpeningColumnLaw.prepared_check receipt)
    (frames_valid field ctx.opening _ _ _ _ sound.2.2 (by decide +kernel) (NativeTranscript.receipt_length world _) responseFits)
  refine ⟨context,hashed,?_,phase,?_⟩
  · rw [prepared_input receipt field phase]
    exact native
  · obtain ⟨log,collector⟩ := prepared_collector receipt
    change (NativeFieldVector.execute NativeFields.goldilocksModulus ctx.fieldFuel
      (NativeFieldVector.initial (field.phase ctx.transcript.profile) work.geometry.randomCount.val) world).1 = receipt.state
    rw [phase,collector]

/-- Any parse of that actual complete input recovers the same true receipt,
responses, original binding, phase and collector. This is pointwise recovery. -/
theorem parsed_origin (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.transcript.input = encodeMany before) (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View) (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded) :
    decoded.field.count = work.geometry.randomCount ∧ decoded.field.phase ctx.transcript.profile = SingleOpeningRandomLaw.phase receipt ∧
      (collected ctx.transcript.profile ctx.fieldFuel decoded world).1 = receipt.state ∧
      decoded.receipt = (NativeTranscript.receipt world receipt.state.phase.consumed).run.1 ∧
      decoded.column.opening.test = ctx.opening.test ∧ decoded.column.opening.evaluation = ctx.opening.evaluation ∧
      decoded.field.data.root = ctx.root ∧ decoded.field.data.query = ctx.query ∧ decoded.field.data.claimed = ctx.claimed ∧
      decoded.column.index.domain = ctx.parameters.code.blocks ∧ decoded.column.index.count = ctx.parameters.queries ∧
      decoded.column.index.label = NativeGoldPcsColumns.label ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some decoded.field.data.context := by
  obtain ⟨context,hashed,native,phase,collected⟩ := prepared_link receipt prepared before parent valid fits responseFits
  have equal := Option.some.inj (parsed.symm.trans native)
  subst decoded
  exact ⟨rfl,phase,collected,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hashed⟩

end
end FormalProof4FHE.HasteBoots.SingleOpeningPreparedChallenge
