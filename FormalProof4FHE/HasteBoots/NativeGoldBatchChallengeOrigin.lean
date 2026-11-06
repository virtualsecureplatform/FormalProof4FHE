module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFieldColumnLaw
public import FormalProof4FHE.HasteBoots.NativeGoldBatchColumnRequestLaw
@[expose] public section

/-! Recover the field collector and true receipt behind an actual native
column input. Encoding completeness retains explicit framing bounds. No
receipt knowledge, oracle freshness or future-source certificate is used. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchChallengeOrigin
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBatchChallengeLink (receiptFrame)
open NativeGoldBatchColumnInputView (responses responseFrame)
open TranscriptFrame (Frame encodeMany)
open OracleProgram (run)
noncomputable section

/-- All raw responses are recovered; later authentication columns are absent. -/
def view (field : NativeGoldBatchFieldInputView.View) (opening : NativeGoldBatchOpening.Opening)
    (label : Input) (domain count : NativeUsizeMessage.Usize) (payload : Input) : NativeGoldBatchChallengeLink.View :=
  ⟨⟨⟨field.frames++[receiptFrame payload,responseFrame opening],label,domain,count⟩,responses opening⟩,
    field,field.frames,payload⟩

def input (field : NativeGoldBatchFieldInputView.View) (profile : Digest) (opening : NativeGoldBatchOpening.Opening)
    (label : Input) (domain count : NativeUsizeMessage.Usize) (payload : Input) : Input :=
  NativeGoldBatchResponseBinding.input ⟨encodeMany (field.frames++[receiptFrame payload]),profile⟩ label domain count opening

theorem parse_native (field : NativeGoldBatchFieldInputView.View) (profile : Digest)
    (opening : NativeGoldBatchOpening.Opening) (label : Input) (domain count : NativeUsizeMessage.Usize)
    (payload : Input) (length : payload.length = 80) (positive : 0 < field.count.val)
    (valid : NativeIndexRequest.check domain count = true)
    (framed : ∀ frame ∈ (view field opening label domain count payload).column.index.frames, TranscriptFrame.Valid frame) :
    NativeGoldBatchChallengeLink.parse (input field profile opening label domain count payload) =
      some (view field opening label domain count payload) := by
  have fieldValid : ∀ frame ∈ field.frames, TranscriptFrame.Valid frame := by
    intro frame member
    apply framed frame
    simp only [view,NativeIndexInputView.View.frames,List.mem_append,List.mem_cons,List.not_mem_nil] 
    exact Or.inl (Or.inl member)
  have columnFramed : ∀ frame ∈ NativeIndexInputView.View.frames
      ⟨(field.frames++[receiptFrame payload])++[responseFrame opening],label,domain,count⟩, TranscriptFrame.Valid frame := by
    simpa only [view,List.append_assoc,List.cons_append,List.nil_append] using framed
  unfold NativeGoldBatchChallengeLink.parse input
  rw [NativeGoldBatchColumnInputView.parse_native (field.frames++[receiptFrame payload]) profile label domain count opening valid columnFramed,Option.bind_some]
  simpa only [view,List.append_assoc,List.cons_append,List.nil_append,responseFrame,responses,
    NativeGoldBatchResponseBinding.payload] using
    NativeGoldBatchChallengeLink.readColumn_native field (responses opening) label domain count payload length positive fieldValid

/-- Exact native execution, including all rejected candidate observations. -/
theorem prepared_collector (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    ∃ log, NativeFieldVector.execute NativeFields.goldilocksModulus ctx.fieldFuel
      (NativeFieldVector.initial (NativeGoldBatchRandomLaw.phase work) work.geometry.randomCount.val) world = (work.state,log) := by
  obtain ⟨next,finished⟩ := NativeGoldBatchRandomLaw.prepared_request ctx world work prepared
  obtain ⟨log,collected,_,_⟩ := NativeFieldReceipt.finished_origin NativeFields.goldilocksModulus ctx.fieldFuel
    work.geometry.randomCount.val (NativePrimeRequest.prepare work.binding.parent .vector)
    NativeGoldBatchPrelude.randomLabel world work.state next finished
  exact ⟨log,collected⟩

theorem prepared_header (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    work.state.phase.pending = (NativeGoldBatchRandomLaw.phase work).pending ∧
      work.state.phase.label = NativeGoldBatchPrelude.randomLabel := by
  obtain ⟨log,collected⟩ := prepared_collector ctx world work prepared
  have header := NativeFieldVector.header_preserved NativeFields.goldilocksModulus ctx.fieldFuel
    (NativeFieldVector.initial (NativeGoldBatchRandomLaw.phase work) work.geometry.randomCount.val) world
  rw [collected] at header
  exact header

private theorem encodeMany_append (first later : List Frame) :
    encodeMany (first++later) = encodeMany first ++ encodeMany later := by
  induction first with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append,encodeMany,ih,List.append_assoc]

/-- The actual complete column input is the recovered field prefix followed
by its true native receipt and every raw response. No nonwrapping premise
about the receipt's consumed-length header is introduced. -/
theorem prepared_input (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (field : NativeGoldBatchFieldInputView.View)
    (phase : field.phase ctx.parent.profile = NativeGoldBatchRandomLaw.phase work) :
    NativeGoldBatchColumnRequestLaw.input ctx work world = input field ctx.parent.profile ctx.opening
      NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries
      (NativeTranscript.receipt world work.state.phase.consumed).run.1 := by
  have header := prepared_header ctx world work prepared
  have fieldInput := NativeGoldBatchFieldInputView.phase_input field ctx.parent.profile
  rw [phase] at fieldInput
  have parentInput : (NativeGoldBatchColumnRequestLaw.parent work world).input =
      encodeMany (field.frames++[receiptFrame (NativeTranscript.receipt world work.state.phase.consumed).run.1]) := by
    change work.state.phase.pending.input ++ TranscriptFrame.encode
      ⟨5,work.state.phase.label,(NativeTranscript.receipt world work.state.phase.consumed).run.1⟩ = _
    rw [header.1,header.2,fieldInput,encodeMany_append]
    simp only [encodeMany,List.append_nil,receiptFrame]
  unfold NativeGoldBatchColumnRequestLaw.input NativeGoldBatchColumnRequestLaw.transcript input
    NativeGoldBatchResponseBinding.input NativePrequeryIndexLaw.requestInput NativeIndexRequest.prepare
    NativeGoldBatchOpening.bindResponses NativeTranscript.appendBytes NativeTranscript.absorb
  simp only [parentInput]
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchChallengeOrigin
