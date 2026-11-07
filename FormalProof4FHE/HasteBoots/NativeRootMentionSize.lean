module
public import FormalProof4FHE.HasteBoots.NativeParentLedgerPools
@[expose] public section

/-! Structural mention counts are paid by bytes in their actual canonical
analysis-parser inputs. These are not native deserializer refinement claims. -/
namespace FormalProof4FHE.HasteBoots.NativeRootMentionSize
open InputIndexedOracle (Input)
open NativePrefixCodec (Codec Vector)
open TranscriptFrame (Frame encodeMany)
noncomputable section
open scoped Classical

private theorem flatMap_size {A : Type} (encode : A → Input) (positive : ∀ value, 0 < (encode value).length)
    (values : List A) : values.length ≤ (values.flatMap encode).length := by
  induction values with
  | nil => exact le_rfl
  | cons value tail ih =>
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    have nonempty := positive value
    omega

theorem vector_size {A : Type} (codec : Codec A) (positive : ∀ value, 0 < (codec.encode value).length)
    (values : Vector A) : values.val.length ≤ ((NativePrefixCodec.vector codec).encode values).length := by
  change values.val.length ≤ (_ ++ values.val.flatMap codec.encode).length
  rw [List.length_append]
  exact (flatMap_size codec.encode positive values.val).trans (Nat.le_add_left _ _)

theorem source_vector_size (values : Vector NativeCanonicalLookupWire.Source) :
    values.val.length ≤ (NativeCanonicalLookupWire.sourcesCodec.encode values).length := by
  apply vector_size
  intro value
  change 0 < (List.ofFn value.1 ++ List.ofFn value.2).length
  simp only [List.length_append,List.length_ofFn]
  decide +kernel

theorem binding_size (binding : NativeCanonicalLookupWire.Binding) :
    binding.sources.val.length ≤ (NativeCanonicalLookupWire.payload binding).length := by
  have bound := source_vector_size binding.sources
  simp only [NativeCanonicalLookupWire.payload,List.length_append]
  omega

private theorem exact_list_size {A B : Type} (codec : Codec A) (view : A → List B)
    (bounded : ∀ value, (view value).length ≤ (codec.encode value).length)
    (input : Input) (values : List B) (parsed : (NativeExactCodec.read codec input).map view = some values) :
    values.length ≤ input.length := by
  obtain ⟨value,read,rfl⟩ := Option.map_eq_some_iff.mp parsed
  rw [← NativeExactCodec.read_sound codec input value read]
  exact bounded value

theorem frameSources_size (frame : Frame) (values : List NativeCanonicalLookupWire.Source)
    (parsed : NativeRootInputView.frameSources frame = some values) : values.length ≤ frame.message.length := by
  unfold NativeRootInputView.frameSources at parsed
  split at parsed
  · split at parsed
    · exact exact_list_size NativeCanonicalLookupWire.sourcesCodec (fun value => value.val) source_vector_size _ _ parsed
    · split at parsed
      · exact exact_list_size NativeRootInputView.bindingCodec (fun value => value.sources.val) binding_size _ _ parsed
      · split at parsed
        · apply exact_list_size NativeGoldBatchMessage.codec (fun value => [(value.context,value.root)]) _ _ _ parsed
          intro value
          rw [NativeGoldBatchMessage.encode]
          simp only [List.length_singleton,List.length_append,List.length_ofFn]
          omega
        · cases parsed
  · cases parsed

theorem frameSources_getD_size (frame : Frame) :
    ((NativeRootInputView.frameSources frame).getD []).length ≤ frame.message.length := by
  cases parsed : NativeRootInputView.frameSources frame with
  | none => exact Nat.zero_le _
  | some values => exact frameSources_size frame values parsed

theorem helperRoots_size (frame : Frame) (values : List NativeRootMessage.Digest)
    (parsed : NativeParentInputView.helperRoots frame = some values) : values.length ≤ frame.message.length := by
  unfold NativeParentInputView.helperRoots at parsed
  split at parsed
  · apply exact_list_size (NativePrefixCodec.vector NativeByteCodec.digest) (fun value => value.val) _ _ _ parsed
    intro value
    apply vector_size
    intro digest
    change 0 < (List.ofFn digest).length
    rw [List.length_ofFn]
    decide +kernel
  · cases parsed

theorem helperRoots_getD_size (frame : Frame) :
    ((NativeParentInputView.helperRoots frame).getD []).length ≤ frame.message.length := by
  cases parsed : NativeParentInputView.helperRoots frame with
  | none => exact Nat.zero_le _
  | some values => exact helperRoots_size frame values parsed

theorem mentions_size (frames : List Frame) :
    (NativeRootInputView.mentions frames).length ≤ (encodeMany frames).length := by
  induction frames with
  | nil => exact le_rfl
  | cons frame tail ih =>
    have bound := frameSources_getD_size frame
    cases tail with
    | nil =>
      simp only [NativeRootInputView.mentions,encodeMany,List.length_append,TranscriptFrame.encode_length,List.length_nil] at *
      omega
    | cons next rest =>
      have one : (NativeRootInputView.single frame next).toList.length ≤ 1 := by
        cases NativeRootInputView.single frame next <;>
          simp only [Option.toList,List.length_nil,List.length_cons] <;> omega
      simp only [NativeRootInputView.mentions,encodeMany,List.length_append,TranscriptFrame.encode_length] at *
      omega

theorem frames_size (frames : List Frame) : frames.length ≤ (encodeMany frames).length := by
  induction frames with
  | nil => exact le_rfl
  | cons frame tail ih =>
    simp only [List.length_cons,encodeMany,List.length_append,TranscriptFrame.encode_length] at *
    omega

theorem roots_size (frames : List Frame) :
    (frames.flatMap (fun frame => (NativeParentInputView.helperRoots frame).getD [])).length ≤ (encodeMany frames).length := by
  induction frames with
  | nil => exact le_rfl
  | cons frame tail ih =>
    have bound := helperRoots_getD_size frame
    simp only [List.flatMap_cons,List.length_append,encodeMany,TranscriptFrame.encode_length] at *
    omega

theorem direct_size (input : Input) : (NativeParentLedger.direct input).length ≤ input.length := by
  unfold NativeParentLedger.direct NativeRootInputView.raw
  cases parsed : TranscriptFrame.decodeAll input with
  | none => exact Nat.zero_le _
  | some frames =>
    simp only [Option.map_some,Option.getD_some]
    rw [(TranscriptFrame.decodeAll_sound input frames parsed).2]
    exact mentions_size frames

theorem decoded_frames_size (input : Input) : (NativeParentLedger.frames input).length ≤ input.length := by
  unfold NativeParentLedger.frames
  cases parsed : TranscriptFrame.decodeAll input with
  | none => exact Nat.zero_le _
  | some frames =>
    simp only [Option.getD_some]
    rw [(TranscriptFrame.decodeAll_sound input frames parsed).2]
    exact frames_size frames

theorem helpers_size (input : Input) : (NativeParentLedger.helpers input).length ≤ input.length :=
  (List.length_filterMap_le _ _).trans (decoded_frames_size input)

theorem input_roots_size (input : Input) : (NativeParentLedger.roots input).length ≤ input.length := by
  unfold NativeParentLedger.roots NativeParentLedger.frames
  cases parsed : TranscriptFrame.decodeAll input with
  | none => exact Nat.zero_le _
  | some frames =>
    simp only [Option.getD_some]
    rw [(TranscriptFrame.decodeAll_sound input frames parsed).2]
    exact roots_size frames

theorem local_contexts_size (input : Input) : (NativeParentLedgerPools.localPools input).contexts.card ≤ 2*input.length := by
  apply (List.toFinset_card_le _).trans
  simp only [List.length_append,List.length_map]
  have direct := direct_size input
  have helpers := helpers_size input
  omega

theorem local_roots_size (input : Input) : (NativeParentLedgerPools.localPools input).roots.card ≤ 2*input.length := by
  apply (List.toFinset_card_le _).trans
  simp only [List.length_append,List.length_map]
  have direct := direct_size input
  have roots := input_roots_size input
  omega
end
end FormalProof4FHE.HasteBoots.NativeRootMentionSize
