module
import all FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery
import all Init.Data.String.Defs

namespace HasteBootsLookupCompressionReceiptSmoke
open FormalProof4FHE.HasteBoots
open NativeLookupChallenge (hashLabel reciprocalLabel)
noncomputable section

def prior : TranscriptFrame.Frame := ⟨5,hashLabel,[1]⟩
def current : TranscriptFrame.Frame := ⟨5,hashLabel,[2]⟩
def rejected : TranscriptFrame.Frame := ⟨5,reciprocalLabel,[3]⟩
def accepted : TranscriptFrame.Frame := ⟨5,reciprocalLabel,[4]⟩

theorem valid (frame : TranscriptFrame.Frame) (member : frame ∈ [prior,current,rejected,accepted]) : TranscriptFrame.Valid frame := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals
    first
    | (change hashLabel.length < _; unfold hashLabel NativeTranscript.utf8; decide +kernel)
    | (change reciprocalLabel.length < _; unfold reciprocalLabel NativeTranscript.utf8; decide +kernel)
    | decide +kernel

/-- A prior job and duplicate rejected offsets cannot replace the current
job's compression receipt. Messages remain ordered and distinct. -/
theorem latest_after_rejections :
    LookupCompressionReceipt.latest (TranscriptFrame.encodeMany [prior,current,rejected,rejected,accepted]) = some current := by
  have framed : ∀ frame ∈ [prior,current,rejected,rejected,accepted], TranscriptFrame.Valid frame := by
    intro frame member
    apply valid frame
    simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self_left] using member
  unfold LookupCompressionReceipt.latest ReceiptFrameView.frames
  rw [TranscriptFrame.decodeAll_encodeMany _ framed]
  unfold prior current rejected accepted hashLabel reciprocalLabel NativeTranscript.utf8
  decide +kernel

/-- Offset receipts alone do not invent a compression value. -/
theorem no_compression :
    LookupCompressionReceipt.latest (TranscriptFrame.encodeMany [rejected,accepted]) = none := by
  have framed : ∀ frame ∈ [rejected,accepted], TranscriptFrame.Valid frame := by
    intro frame member
    apply valid frame
    exact List.mem_append_right [prior,current] member
  unfold LookupCompressionReceipt.latest ReceiptFrameView.frames
  rw [TranscriptFrame.decodeAll_encodeMany _ framed]
  unfold rejected accepted hashLabel reciprocalLabel NativeTranscript.utf8
  decide +kernel

/-- Receipt query payloads cannot themselves be parsed as framed stream
inputs and substituted for the reciprocal stream that quotes the receipt. -/
theorem receipt_key_not_compression (raw : InputIndexedOracle.Input) :
    LookupCompressionReceipt.latest (NativeReceiptPrefixView.key raw) = none := by
  simp only [LookupCompressionReceipt.latest,ReceiptFrameView.frames,
    show NativeReceiptPrefixView.key raw = NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ raw from rfl,
    NativeTranscript.receipt_decode_rejected,Option.getD_none,List.filter_nil,List.getLast?_nil]

end
end HasteBootsLookupCompressionReceiptSmoke
