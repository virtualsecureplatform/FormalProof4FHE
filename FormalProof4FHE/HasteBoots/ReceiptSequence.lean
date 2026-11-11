module
public import FormalProof4FHE.HasteBoots.ReceiptFrameView
import all FormalProof4FHE.HasteBoots.NativeTranscript
@[expose] public section

/-! Exact kind-5 frame projection under native transcript operations.
The sequence is a list: repeated receipt frames retain their multiplicity. -/
namespace FormalProof4FHE.HasteBoots.ReceiptSequence
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript FieldPhase utf8)
open TranscriptFrame (Frame encodeMany)
open ReceiptFrameView (frames)
noncomputable section

def Framed (state : Transcript) : Prop := ∃ entries, TranscriptFrame.decodeAll state.input = some entries

theorem append (before after : Transcript) (suffix : List Frame) (old : Framed before)
    (valid : ∀ entry ∈ suffix, TranscriptFrame.Valid entry)
    (bytes : after.input = before.input ++ encodeMany suffix) :
    Framed after ∧ frames after.input = frames before.input ++ suffix.filter (fun entry => entry.kind = 5) := by
  obtain ⟨earlier,decoded⟩ := old
  obtain ⟨earlierValid,earlierBytes⟩ := TranscriptFrame.decodeAll_sound _ _ decoded
  have encoded : after.input = encodeMany (earlier ++ suffix) := by
    rw [bytes,earlierBytes,SingleOpeningExposure.encodeMany_append]
  have whole : TranscriptFrame.decodeAll after.input = some (earlier ++ suffix) := by
    rw [encoded]
    apply TranscriptFrame.decodeAll_encodeMany
    intro entry member
    rcases List.mem_append.mp member with first | later
    · exact earlierValid entry first
    · exact valid entry later
  exact ⟨⟨_,whole⟩,by simp only [frames,whole,decoded,Option.getD_some,List.filter_append]⟩

theorem absorb (state : Transcript) (kind : Fin 9) (label message : Input) (old : Framed state)
    (valid : TranscriptFrame.Valid ⟨kind,label,message⟩) (other : kind ≠ 5) :
    Framed (NativeTranscript.absorb state kind label message) ∧
      frames (NativeTranscript.absorb state kind label message).input = frames state.input := by
  have added := append state (NativeTranscript.absorb state kind label message) [⟨kind,label,message⟩] old
    (by intro entry member; obtain rfl := List.mem_singleton.mp member; exact valid)
    (by simp only [NativeTranscript.absorb,encodeMany,List.append_nil])
  simpa only [List.filter_cons,other,decide_false,List.filter_nil,List.append_nil,Bool.false_eq_true,ite_false] using added

theorem prepare (state : Transcript) (kind : TypedFieldRequest.Kind) (degree w : ℕ) (old : Framed state)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Framed (NativeExtensionRequest.prepare (TypedFieldRequest.prepare state kind) degree w) ∧
      frames (NativeExtensionRequest.prepare (TypedFieldRequest.prepare state kind) degree w).input = frames state.input := by
  have typed := absorb state 1 (utf8 "typed request kind") (TypedFieldRequest.kindBytes kind) old
    ⟨by change (utf8 "typed request kind").length < _; unfold utf8; decide +kernel,by cases kind <;> change (utf8 _).length < _ <;> unfold utf8 <;> decide +kernel⟩ (by decide)
  have extension := absorb (TypedFieldRequest.prepare state kind) 1 (utf8 "field challenge kind") (utf8 "extension vector") typed.1
    ⟨by unfold utf8; decide +kernel,by unfold utf8; decide +kernel⟩ (by decide)
  have basis := absorb _ 1 (utf8 "extension basis") (NativeExtensionDescriptor.descriptor degree w) extension.1
    ⟨by change (utf8 "extension basis").length < _; unfold utf8; decide +kernel,descriptorFits⟩ (by decide)
  exact ⟨basis.1,basis.2.trans (extension.2.trans typed.2)⟩

theorem begin_field (state : Transcript) (label : Input) (p count : ℕ) (old : Framed state)
    (labelFits : label.length < TranscriptFrame.lengthLimit) :
    Framed (NativeTranscript.beginField state label p count).run.1.pending ∧
      frames (NativeTranscript.beginField state label p count).run.1.pending.input = frames state.input :=
  absorb state 4 label _ old ⟨labelFits,by simp only [List.length_append,TranscriptFrame.littleEndian_length]; decide +kernel⟩ (by decide)

theorem scalar_begin (state : Transcript) (label : Input) (p degree w : ℕ) (old : Framed state)
    (labelFits : label.length < TranscriptFrame.lengthLimit)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Framed (TypedFieldRequest.beginExecute p degree w state label).1.phase.pending ∧
      frames (TypedFieldRequest.beginExecute p degree w state label).1.phase.pending.input = frames state.input := by
  have prepared := prepare state .scalar degree w old descriptorFits
  have begun := begin_field _ label p degree prepared.1 labelFits
  exact ⟨begun.1,begun.2.trans prepared.2⟩

theorem vector_begin (state : Transcript) (label : Input) (p degree w count : ℕ) (old : Framed state)
    (labelFits : label.length < TranscriptFrame.lengthLimit)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Framed (TypedFieldVector.beginExecute p degree w count state label).1.phase.pending ∧
      frames (TypedFieldVector.beginExecute p degree w count state label).1.phase.pending.input = frames state.input := by
  have prepared := prepare state .vector degree w old descriptorFits
  have begun := begin_field _ label p (count*degree) prepared.1 labelFits
  exact ⟨begun.1,begun.2.trans prepared.2⟩

theorem finish (phase : FieldPhase) (world : World) (old : Framed phase.pending)
    (labelFits : phase.label.length < TranscriptFrame.lengthLimit) :
    Framed (NativeTranscript.finishField world phase).run.1 ∧
      frames (NativeTranscript.finishField world phase).run.1.input = frames phase.pending.input ++ [ReceiptFrameView.frame world phase] := by
  have added := append phase.pending (NativeTranscript.finishField world phase).run.1 [ReceiptFrameView.frame world phase] old
    (by intro entry member; obtain rfl := List.mem_singleton.mp member
        exact ⟨labelFits,by rw [show (ReceiptFrameView.frame world phase).message.length = 80 from NativeTranscript.receipt_length world phase.consumed]; decide +kernel⟩)
    (by change phase.pending.input ++ TranscriptFrame.encode (ReceiptFrameView.frame world phase) =
          phase.pending.input ++ encodeMany [ReceiptFrameView.frame world phase]
        simp only [encodeMany,List.append_nil])
  simpa only [List.filter_cons,ReceiptFrameView.frame,decide_true,Bool.true_eq,ite_true,List.filter_nil] using added

end
end FormalProof4FHE.HasteBoots.ReceiptSequence
