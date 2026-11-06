module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchOpening
public import FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw
@[expose] public section

/-! Exact raw response binding for the native batch column request. With the
same parent and request parameters, its complete SHAKE input determines the
test row and every response-group row. Authentication columns are selected
later and are intentionally outside this response commitment. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchResponseBinding
open InputIndexedOracle (Input)
open NativeGoldBatchOpening (Opening)
open NativeTranscript (Transcript)
open NativeUsizeMessage (Usize)
noncomputable section

def payload (opening : Opening) : Input :=
  NativeLookupRequestWire.rowCodec.encode opening.test ++
    (NativePrefixCodec.vector NativeLookupRequestWire.rowCodec).encode opening.evaluations

def input (parent : Transcript) (label : Input) (domain count : Usize) (opening : Opening) : Input :=
  NativePrequeryIndexLaw.requestInput (NativeGoldBatchOpening.bindResponses parent opening) label domain count

theorem input_eq (parent : Transcript) (label : Input) (domain count : Usize) (opening : Opening) :
    input parent label domain count opening = parent.input ++
      TranscriptFrame.encode ⟨1,NativeTranscript.utf8 "mw batch linear responses",payload opening⟩ ++
      TranscriptFrame.encode ⟨1,NativeTranscript.utf8 "index domain",TranscriptFrame.littleEndian 8 domain.val⟩ ++
      TranscriptFrame.encode ⟨2,label,TranscriptFrame.littleEndian 8 (count.val*8)⟩ := rfl

/-- A full frame with fixed kind and label determines its complete message.
This uses actual byte lengths, not injectivity of a wrapping length header. -/
theorem frame_message (kind : Fin 9) (label first second : Input)
    (same : TranscriptFrame.encode ⟨kind,label,first⟩ = TranscriptFrame.encode ⟨kind,label,second⟩) : first = second := by
  have lengths := congrArg List.length same
  simp only [TranscriptFrame.encode_length] at lengths
  have size : first.length = second.length := by omega
  have tail := (List.cons.inj same).2
  change TranscriptFrame.sized label ++ (TranscriptFrame.littleEndian 8 first.length ++ first) =
    TranscriptFrame.sized label ++ (TranscriptFrame.littleEndian 8 second.length ++ second) at tail
  rw [size] at tail
  exact List.append_cancel_left (List.append_cancel_left tail)

theorem payload_eq_iff (first second : Opening) : payload first = payload second ↔
    first.test = second.test ∧ first.evaluations = second.evaluations := by
  constructor
  · intro same
    change (NativePrefixCodec.product NativeLookupRequestWire.rowCodec (NativePrefixCodec.vector NativeLookupRequestWire.rowCodec)).encode (first.test,first.evaluations) =
      (NativePrefixCodec.product NativeLookupRequestWire.rowCodec (NativePrefixCodec.vector NativeLookupRequestWire.rowCodec)).encode (second.test,second.evaluations) at same
    have pair := (NativePrefixCodec.product NativeLookupRequestWire.rowCodec
      (NativePrefixCodec.vector NativeLookupRequestWire.rowCodec)).encode_injective same
    exact Prod.mk.inj pair
  · rintro ⟨test,evaluations⟩
    simp only [payload,test,evaluations]

/-- Every response group is pinned by the complete input, including groups
not chosen as a hypothetical false-query witness. Raw lazy words are kept. -/
theorem input_eq_iff (parent : Transcript) (label : Input) (domain count : Usize) (first second : Opening) :
    input parent label domain count first = input parent label domain count second ↔
      first.test = second.test ∧ first.evaluations = second.evaluations := by
  constructor
  · intro same
    rw [input_eq,input_eq] at same
    have frames := List.append_cancel_left (List.append_cancel_right (List.append_cancel_right same))
    exact (payload_eq_iff first second).mp (frame_message 1 _ _ _ frames)
  · intro same
    rw [input_eq,input_eq,(payload_eq_iff first second).mpr same]
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchResponseBinding
