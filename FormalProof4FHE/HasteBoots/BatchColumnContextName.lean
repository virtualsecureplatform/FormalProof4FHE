module
public import FormalProof4FHE.HasteBoots.CalibratedAdaptiveSourceLedger
@[expose] public section

/-! A complete linked column input names the exact context/root in its
field-prefix batch bind. Receipt correctness is not needed for naming. -/
namespace FormalProof4FHE.HasteBoots.BatchColumnContextName
open InputIndexedOracle (Input)
open NativeGoldBatchChallengeLink (View)
noncomputable section

theorem index_frames (input : Input) (view : NativeIndexInputView.View)
    (parsed : NativeIndexInputView.parse input = some view) :
    TranscriptFrame.decodeAll input = some view.frames := by
  obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp parsed
  have suffix := NativeIndexInputView.readFrames_sound frames.reverse view read
  have equal : frames = view.frames := by
    have same := congrArg List.reverse suffix.1
    simpa only [List.reverse_reverse] using same
  rwa [equal] at decoded

theorem frames (input : Input) (view : View) (parsed : NativeGoldBatchChallengeLink.parse input = some view) :
    TranscriptFrame.decodeAll input = some view.column.index.frames ∧ view.fieldFrames = view.field.frames := by
  obtain ⟨column,columnParsed,link⟩ := Option.bind_eq_some_iff.mp parsed
  have linked := NativeGoldBatchChallengeLink.readColumn_sound column view link
  obtain ⟨index,indexParsed,columnRead⟩ := Option.bind_eq_some_iff.mp columnParsed
  have indexed := NativeGoldBatchColumnInputView.readIndex_sound index column columnRead
  have indexEq : index = view.column.index := indexed.1.symm.trans (congrArg (fun col => col.index) linked.1.symm)
  rw [indexEq] at indexParsed
  have decoded := index_frames input view.column.index indexParsed
  have valid := (TranscriptFrame.decodeAll_sound input _ decoded).1
  have beforeEq : view.column.index.before = view.fieldFrames ++
      [NativeGoldBatchChallengeLink.receiptFrame view.receipt,NativeGoldBatchColumnInputView.responseFrame view.column.opening] := by
    exact (congrArg (fun col => col.index.before) linked.1).trans linked.2.2.2
  have fieldValid : ∀ frame ∈ view.fieldFrames, TranscriptFrame.Valid frame := by
    intro frame member
    apply valid frame
    rw [NativeIndexInputView.View.frames,beforeEq]
    exact List.mem_append_left _ (List.mem_append_left _ member)
  have fieldRead := linked.2.2.1
  unfold NativeGoldBatchFieldInputView.parse at fieldRead
  rw [TranscriptFrame.decodeAll_encodeMany _ fieldValid,Option.bind_some] at fieldRead
  have suffix := NativeGoldBatchFieldInputView.readFrames_sound view.fieldFrames.reverse view.field fieldRead
  have fields : view.fieldFrames = view.field.frames := by
    have same := congrArg List.reverse suffix.1
    simpa only [List.reverse_reverse] using same
  exact ⟨decoded,fields⟩

theorem source (input : Input) (view : View) (parsed : NativeGoldBatchChallengeLink.parse input = some view) :
    (view.field.data.context,view.field.data.root) ∈ NativeParentLedger.direct input := by
  have decoded := frames input view parsed
  have sound := TranscriptFrame.decodeAll_sound input _ decoded.1
  have linked := NativeGoldBatchChallengeLink.parse_sound input view parsed (fun _ => 0)
  have member : NativeGoldBatchFieldInputView.batchFrame view.field.data ∈ view.column.index.frames := by
    rw [NativeIndexInputView.View.frames,linked.2.2.2.1,decoded.2]
    apply List.mem_append_left
    apply List.mem_append_left
    simp [NativeGoldBatchFieldInputView.View.frames]
  change _ ∈ (NativeRootInputView.raw input).getD []
  rw [sound.2,NativeRootInputView.raw_complete _ sound.1,Option.getD_some]
  have recognized := NativeRootInputView.recognized_sources view.column.index.frames _ member
    [(view.field.data.context,view.field.data.root)] (NativeRootInputView.batch_complete view.field.data)
  exact recognized.subset (List.mem_singleton_self _)

theorem context (input : Input) (view : View) (parsed : NativeGoldBatchChallengeLink.parse input = some view) :
    view.field.data.context ∈ ContextDigestTargets.fromInput input := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨(view.field.data.context,view.field.data.root),source input view parsed,rfl⟩

end
end FormalProof4FHE.HasteBoots.BatchColumnContextName
