module
public import FormalProof4FHE.HasteBoots.OriginalHelperJointProbability
@[expose] public section

/-! The immediate native batch frame names its literal context/root at the
field input. No arbitrary earlier label or matching registry slot is chosen. -/
namespace FormalProof4FHE.HasteBoots.BatchFieldContextName
open InputIndexedOracle (Input)
open NativeGoldBatchFieldInputView (View)
noncomputable section

theorem source (input : Input) (view : View) (parsed : NativeGoldBatchFieldInputView.parse input = some view) :
    (view.data.context,view.data.root) ∈ NativeParentLedger.direct input := by
  have sound := NativeGoldBatchFieldInputView.parse_sound input view parsed (fun _ => 0)
  have bytes := sound.1
  rw [NativeGoldBatchFieldInputView.phase_input] at bytes
  change _ ∈ (NativeRootInputView.raw input).getD []
  rw [← bytes,NativeRootInputView.raw_complete _ sound.2.2,Option.getD_some]
  have recognized := NativeRootInputView.recognized_sources view.frames (NativeGoldBatchFieldInputView.batchFrame view.data)
    (by simp [NativeGoldBatchFieldInputView.View.frames]) [(view.data.context,view.data.root)] (NativeRootInputView.batch_complete view.data)
  exact recognized.subset (List.mem_singleton_self _)

theorem context (input : Input) (view : View) (parsed : NativeGoldBatchFieldInputView.parse input = some view) :
    view.data.context ∈ ContextDigestTargets.fromInput input := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨(view.data.context,view.data.root),source input view parsed,rfl⟩

end
end FormalProof4FHE.HasteBoots.BatchFieldContextName
