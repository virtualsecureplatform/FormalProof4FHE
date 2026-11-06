module

public import FormalProof4FHE.HasteBoots.NativeRootInputView
public import FormalProof4FHE.HasteBoots.NativeGoldBatchBinding
@[expose] public section

/-! Actual native bind_many payloads are recognized by the raw-input source
monitor. This includes raw/off-path framed requests, without assuming that
the verifier has already received or declared the root. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRootMentions
open NativeRootMessage (Digest)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)
open NativePrefixCodec (Vector)
open NativeTranscript (Transcript utf8)
noncomputable section

theorem payload_encode (context root : Digest) (queries : Vector Query) (values : Vector Row) :
    NativeGoldBatchBinding.payload context root queries values = NativeGoldBatchMessage.codec.encode ⟨context,root,queries,values⟩ := by
  rw [NativeGoldBatchMessage.encode]
  rfl

theorem frame_complete (context root : Digest) (queries : Vector Query) (values : Vector Row) :
    NativeRootInputView.frameSources ⟨1,utf8 "mw batched row-code v1",NativeGoldBatchBinding.payload context root queries values⟩ =
      some [(context,root)] := by
  rw [payload_encode]
  exact NativeRootInputView.batch_complete _

private theorem encodeMany_append (first last : List TranscriptFrame.Frame) :
    TranscriptFrame.encodeMany (first++last) = TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany last := by
  induction first with
  | nil => simp only [List.nil_append,TranscriptFrame.encodeMany]
  | cons frame rest ih => simp only [List.cons_append,TranscriptFrame.encodeMany,ih,List.append_assoc]

theorem frames (parent : Transcript) (before : List TranscriptFrame.Frame) (bytes : parent.input = TranscriptFrame.encodeMany before)
    (context root : Digest) (queries : Vector Query) (values : Vector Row) :
    (NativeGoldBatchBinding.appendBound parent context root queries values).input = TranscriptFrame.encodeMany
      (before++[⟨1,utf8 "mw batched row-code v1",NativeGoldBatchBinding.payload context root queries values⟩]) := by
  rw [NativeGoldBatchBinding.appendBound_input,bytes,encodeMany_append]
  simp only [TranscriptFrame.encodeMany,List.append_nil]

theorem raw_complete (parent : Transcript) (before : List TranscriptFrame.Frame) (bytes : parent.input = TranscriptFrame.encodeMany before)
    (context root : Digest) (queries : Vector Query) (values : Vector Row)
    (valid : ∀ frame ∈ before++[⟨1,utf8 "mw batched row-code v1",NativeGoldBatchBinding.payload context root queries values⟩], TranscriptFrame.Valid frame) :
    ∃ found, NativeRootInputView.raw (NativeGoldBatchBinding.appendBound parent context root queries values).input = some found ∧ (context,root) ∈ found := by
  rw [frames parent before bytes context root queries values]
  refine ⟨_,NativeRootInputView.raw_complete _ valid,?_⟩
  have included := NativeRootInputView.recognized_sources
    (before++[⟨1,utf8 "mw batched row-code v1",NativeGoldBatchBinding.payload context root queries values⟩])
    ⟨1,utf8 "mw batched row-code v1",NativeGoldBatchBinding.payload context root queries values⟩
    (by simp) [(context,root)] (frame_complete context root queries values)
  exact included.subset (List.mem_singleton_self _)
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRootMentions
