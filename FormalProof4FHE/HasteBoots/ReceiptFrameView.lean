module
public import FormalProof4FHE.HasteBoots.NativeTranscriptExtension
public import FormalProof4FHE.HasteBoots.SingleOpeningExposure
@[expose] public section

/-! Actual native field receipts as kind-5 frames in a structurally decoded
transcript. This view preserves labels and whole receipt messages; membership
alone does not assign an original job or draw ordinal. -/
namespace FormalProof4FHE.HasteBoots.ReceiptFrameView
open InputIndexedOracle (Input World)
open NativeTranscript (FieldPhase Transcript)
open TranscriptFrame (Frame encodeMany)
noncomputable section

def frame (world : World) (phase : FieldPhase) : Frame :=
  ⟨5,phase.label,(NativeTranscript.receipt world phase.consumed).run.1⟩

def frames (input : Input) : List Frame :=
  ((TranscriptFrame.decodeAll input).getD []).filter (fun entry => entry.kind = 5)

theorem quoted (world : World) (phase : FieldPhase) (target : Transcript) (earlier : List Frame)
    (decoded : TranscriptFrame.decodeAll phase.pending.input = some earlier)
    (labelFits : phase.label.length < TranscriptFrame.lengthLimit)
    (extension : NativeTranscriptExtension.Extends (NativeTranscript.finishField world phase).run.1 target) :
    ∃ later, TranscriptFrame.decodeAll target.input = some (earlier ++ frame world phase :: later) := by
  obtain ⟨valid,bytes⟩ := TranscriptFrame.decodeAll_sound _ _ decoded
  obtain ⟨later,laterValid,laterBytes,_⟩ := extension
  have finished : (NativeTranscript.finishField world phase).run.1.input = phase.pending.input ++ TranscriptFrame.encode (frame world phase) := rfl
  have frameValid : TranscriptFrame.Valid (frame world phase) :=
    ⟨labelFits,by rw [show (frame world phase).message.length = 80 from NativeTranscript.receipt_length world phase.consumed]; decide +kernel⟩
  have encoded : target.input = encodeMany (earlier ++ frame world phase :: later) := by
    rw [laterBytes,finished,bytes,SingleOpeningExposure.encodeMany_append]
    simp only [encodeMany,List.append_assoc]
  refine ⟨later,?_⟩
  rw [encoded]
  apply TranscriptFrame.decodeAll_encodeMany
  intro entry member
  rcases List.mem_append.mp member with old | added
  · exact valid entry old
  · rcases List.mem_cons.mp added with rfl | tail
    · exact frameValid
    · exact laterValid entry tail

theorem member (world : World) (phase : FieldPhase) (target : Transcript) (earlier : List Frame)
    (decoded : TranscriptFrame.decodeAll phase.pending.input = some earlier)
    (labelFits : phase.label.length < TranscriptFrame.lengthLimit)
    (extension : NativeTranscriptExtension.Extends (NativeTranscript.finishField world phase).run.1 target) :
    frame world phase ∈ frames target.input := by
  obtain ⟨later,whole⟩ := quoted world phase target earlier decoded labelFits extension
  simp only [frames,whole,Option.getD_some,List.mem_filter]
  exact ⟨List.mem_append_right _ List.mem_cons_self,rfl⟩

end
end FormalProof4FHE.HasteBoots.ReceiptFrameView
