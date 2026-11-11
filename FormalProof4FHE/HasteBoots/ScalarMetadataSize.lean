module
public import FormalProof4FHE.HasteBoots.ScalarRecoveredReplay
@[expose] public section

/-! Native variable-integer statement metadata occupies real bytes in every
successfully recovered scalar key. No fixed-width usize encoding is assumed. -/
namespace FormalProof4FHE.HasteBoots.ScalarMetadataSize
open InputIndexedOracle (Input)
open NativeScalarBatchWire (Info Statement)
open TranscriptFrame (Frame encodeMany)

theorem usize_positive (value : NativeUsizeMessage.Usize) : 1 ≤ (NativeUsizeMessage.encode value).length := by
  unfold NativeUsizeMessage.encode
  split_ifs <;> simp [TranscriptFrame.littleEndian_length]

theorem info_lower (info : Info) : 2 ≤ (NativeScalarBatchWire.infoCodec.encode info).length := by
  rw [NativeScalarBatchWire.info_encode,List.length_append]
  have left := usize_positive info.maxMultiplicands
  have right := usize_positive info.numVariables
  omega

theorem infos_lower (infos : List Info) : 2*infos.length ≤ (infos.flatMap NativeScalarBatchWire.infoCodec.encode).length := by
  induction infos with
  | nil => simp
  | cons info rest ih =>
    have head := info_lower info
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

theorem statement_lower (statement : Statement) : 2*statement.infos.val.length ≤ (NativeScalarBatchWire.statementCodec.encode statement).length := by
  have infos := infos_lower statement.infos.val
  rw [NativeScalarBatchWire.statement_encode,List.length_append,List.length_append,List.length_append]
  omega

theorem message_le (frames : List Frame) (frame : Frame) (member : frame ∈ frames) : frame.message.length ≤ (encodeMany frames).length := by
  induction frames with
  | nil => cases member
  | cons head rest ih =>
    rw [encodeMany,List.length_append,TranscriptFrame.encode_length]
    rcases List.mem_cons.mp member with equal | later
    · subst head; omega
    · have tail := ih later; omega

noncomputable section

theorem recovered_lower (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration) :
    2*configuration.view.history.statement.infos.val.length ≤ input.length := by
  have parsed := ScalarTranscriptPrefix.parse_sound input configuration.view (ScalarRecoveredReplay.recover_sound input configuration found).1
  let view : ScalarChallengeInputView.View := ⟨configuration.view.history.frames,configuration.view.packet⟩
  have bytes := (ScalarChallengeInputView.parse_sound input view parsed (fun _ => 0)).1
  rw [ScalarChallengeInputView.phase_input] at bytes
  have member : ScalarTranscriptPrefix.statementFrame configuration.view.history.statement ∈ view.frames := by
    simp [view,ScalarChallengeInputView.View.frames,ScalarTranscriptPrefix.History.frames]
  have bound := message_le view.frames _ member
  have count := statement_lower configuration.view.history.statement
  change (NativeScalarBatchWire.statementCodec.encode configuration.view.history.statement).length ≤ (encodeMany view.frames).length at bound
  rw [bytes] at bound
  exact count.trans bound

theorem recovered_count_le (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration) : configuration.view.history.statement.infos.val.length ≤ input.length := by
  have bound := recovered_lower input configuration found
  omega

end
end FormalProof4FHE.HasteBoots.ScalarMetadataSize
