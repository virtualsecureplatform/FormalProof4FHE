module

public import FormalProof4FHE.HasteBoots.NativeTranscriptExtension
import all Init.Data.String.Defs
@[expose] public section

/-! Structural transcript framing is preserved by valid append-only native transitions. This is a proof invariant, not an added verifier check or a Rust decoder refinement claim. -/
namespace FormalProof4FHE.HasteBoots.NativeTranscriptFraming
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript utf8)
open NativeRootMessage (Digest)
open NativeTranscriptExtension (Extends)
noncomputable section

def Framed (state : Transcript) : Prop := ∃ frames : List TranscriptFrame.Frame,
  state.input = TranscriptFrame.encodeMany frames ∧ ∀ frame ∈ frames, TranscriptFrame.Valid frame

private theorem encodeMany_append (first later : List TranscriptFrame.Frame) :
    TranscriptFrame.encodeMany (first++later) = TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany later := by
  induction first with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append,TranscriptFrame.encodeMany,ih,List.append_assoc]

theorem of_decode (state : Transcript) (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll state.input = some frames) : Framed state := by
  have sound := TranscriptFrame.decodeAll_sound state.input frames decoded
  exact ⟨frames,sound.2,sound.1⟩

theorem framed_iff_decode (state : Transcript) : Framed state ↔ (TranscriptFrame.decodeAll state.input).isSome = true := by
  constructor
  · rintro ⟨frames,bytes,valid⟩
    rw [bytes,TranscriptFrame.decodeAll_encodeMany frames valid]
    rfl
  · intro parsed
    cases decoded : TranscriptFrame.decodeAll state.input with
    | none => rw [decoded] at parsed; contradiction
    | some frames => exact of_decode state frames decoded

theorem of_extension {before after : Transcript} (valid : Framed before) (extension : Extends before after) : Framed after := by
  obtain ⟨frames,bytes,framed⟩ := valid
  obtain ⟨suffix,valid,appended,_⟩ := extension
  refine ⟨frames++suffix,?_,?_⟩
  · rw [appended,bytes,encodeMany_append]
  · intro frame member
    rcases List.mem_append.mp member with old | added
    · exact framed frame old
    · exact valid frame added

theorem empty (profile : Digest) : Framed ⟨[],profile⟩ := ⟨[],rfl,by simp⟩

theorem absorb (state : Transcript) (valid : Framed state) (kind : Fin 9) (label message : Input)
    (fits : TranscriptFrame.Valid ⟨kind,label,message⟩) : Framed (NativeTranscript.absorb state kind label message) :=
  of_extension valid (NativeTranscriptExtension.absorb state kind label message fits)

theorem new (application : Input) (profile : Digest) (fits : application.length < TranscriptFrame.lengthLimit) :
    Framed (NativeTranscript.new application profile) := by
  apply absorb _ (absorb _ (absorb _ (empty profile) 0 (utf8 "protocol") (utf8 "HasteBoots framed SHAKE256 v1")
    (by unfold TranscriptFrame.Valid; decide +kernel)) 0 (utf8 "application") application
      ⟨by change (utf8 "application").length < TranscriptFrame.lengthLimit; decide +kernel,fits⟩) 0 (utf8 "trusted profile") (List.ofFn profile)
  exact ⟨by change (utf8 "trusted profile").length < TranscriptFrame.lengthLimit; decide +kernel,by simp only [List.length_ofFn]; decide +kernel⟩

theorem challenge_bytes (state : Transcript) (label : Input) (count : ℕ) (world : World)
    (labelFits : label.length < TranscriptFrame.lengthLimit) (countFits : count < TranscriptFrame.lengthLimit) :
    Extends state (NativeTranscript.challengeBytes world state label count).run.1.2 := by
  exact (NativeTranscriptExtension.absorb state 2 label (TranscriptFrame.littleEndian 8 count)
    ⟨labelFits,by rw [TranscriptFrame.littleEndian_length]; decide +kernel⟩).trans
    (NativeTranscriptExtension.absorb _ 3 label _ ⟨labelFits,by
      change (InputIndexedOracle.bytes world _ 0 count).length < _
      simpa only [InputIndexedOracle.bytes,List.length_ofFn] using countFits⟩)
end
end FormalProof4FHE.HasteBoots.NativeTranscriptFraming
