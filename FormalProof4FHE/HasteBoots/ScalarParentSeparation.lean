module
public import FormalProof4FHE.HasteBoots.ParentSeedCompletion
public import FormalProof4FHE.HasteBoots.FactorFiberUniform
@[expose] public section

/-! Actual scalar challenge inputs end in the typed scalar field frame;
parent-seed requests end in a distinct seed-request frame. Completing every
recognized parent key therefore leaves the outer scalar stream unseen. -/
namespace FormalProof4FHE.HasteBoots.ScalarParentSeparation
open InputIndexedOracle (Input)
open LookupFactorFixation (Sample)
noncomputable section

theorem rejected (input : Input) (view : ScalarChallengeInputView.View)
    (parsed : ScalarChallengeInputView.parse input = some view) :
    NativeParentInputView.parseParent input = none := by
  obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp parsed
  have reversed := ScalarChallengeInputView.readFrames_sound frames.reverse view read
  unfold NativeParentInputView.parseParent
  rw [decoded,Option.bind_some]
  have apart : ¬NativeParentInputView.isSeedFrames frames := by
    simp only [NativeParentInputView.isSeedFrames,reversed,ScalarChallengeInputView.View.frames,
      List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
      ScalarChallengeInputView.fieldFrame]
    decide
  exact ite_eq_right apart

theorem sample_rejected (sample : Sample) :
    NativeParentInputView.parseParent sample.view.reader.entry.coefficients.phase.pending.input = none := by
  obtain ⟨configuration,recovered,_,_,_⟩ := ScalarParentRecovery.recover sample.view.reader
  exact rejected _ _ (ScalarTranscriptPrefix.parse_sound _ _ (ScalarRecoveredReplay.recover_sound _ _ recovered).1)

end
end FormalProof4FHE.HasteBoots.ScalarParentSeparation
