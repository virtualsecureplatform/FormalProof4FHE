module
public import FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder
public import FormalProof4FHE.HasteBoots.LookupBatchReceiptOrder
public import FormalProof4FHE.HasteBoots.LookupReceiptLabels
import all FormalProof4FHE.HasteBoots.NativeLookupBatch
@[expose] public section

/-! Original batch initialization carries each completed selection's literal
draw-prefix receipt order. No successful-draw or job reindexing is assumed. -/
namespace FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch
open InputIndexedOracle (World)
open ReceiptFrameView (frames)
open LookupReceiptBatchLineage (current)
noncomputable section

def Certificates {p : ℕ} {K : Type} (world : World) (machine : NativeLookupBatch.Machine p K) : Prop :=
  (match machine.control with
  | .sampling _ _ selection => ∃ earlier, LookupDrawReceiptOrder.Traced world earlier selection ∧ LookupReceiptLabels.Labels selection
  | _ => True) ∧
  ∀ completed ∈ machine.completed, ∃ earlier, LookupDrawReceiptOrder.Traced world earlier completed.selection ∧ LookupReceiptLabels.Labels completed.selection

theorem after_sample {p : ℕ} {K : Type} (world : World) (machine : NativeLookupBatch.Machine p K)
    (job : NativeLookupBatch.Job p) (todo : List (NativeLookupBatch.Action p)) (selection : NativeLookupChallenge.Machine K)
    (selected : ∃ earlier, LookupDrawReceiptOrder.Traced world earlier selection ∧ LookupReceiptLabels.Labels selection)
    (old : ∀ completed ∈ machine.completed, ∃ earlier, LookupDrawReceiptOrder.Traced world earlier completed.selection ∧ LookupReceiptLabels.Labels completed.selection) :
    Certificates world (NativeLookupBatch.afterSample machine job todo selection) := by
  cases control : selection.control <;> simp only [NativeLookupBatch.afterSample,control,Certificates]
  · exact ⟨selected,old⟩
  · exact ⟨selected,old⟩
  · refine ⟨True.intro,?_⟩
    intro completed member
    rcases List.mem_append.mp member with prior | added
    · exact old completed prior
    · obtain rfl := List.mem_singleton.mp added
      exact selected

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (ordered : LookupBatchReceiptOrder.Ordered world earlier machine) (valid : Certificates world machine) :
    Certificates world (NativeLookupBatch.tickExecute basis w machine world).1 := by
  cases control : machine.control with
  | finished transcript => simpa only [NativeLookupBatch.tickExecute,control] using valid
  | ready todo transcript =>
    have framed : ReceiptSequence.Framed transcript := by simpa only [current,control] using ordered.1
    cases todo with
    | nil => simpa only [NativeLookupBatch.tickExecute,control,Certificates] using And.intro True.intro valid.2
    | cons action todo =>
      cases action with
      | request ordinal => simpa only [NativeLookupBatch.tickExecute,control,Certificates] using And.intro True.intro valid.2
      | sample job =>
        simp only [NativeLookupBatch.tickExecute,control,Certificates]
        exact ⟨⟨_,⟨LookupDrawReceiptOrder.initial p degree w transcript world framed descriptorFits,LookupReceiptLabels.initial p degree w transcript⟩⟩,valid.2⟩
  | sampling job todo selection =>
    obtain ⟨before,selected⟩ := (show ∃ before, LookupDrawReceiptOrder.Traced world before selection ∧ LookupReceiptLabels.Labels selection from by simpa only [control] using valid.1)
    have next := LookupDrawReceiptOrder.tick basis w job.request.width job.request.rows selection world before descriptorFits selected.1
    simpa only [NativeLookupBatch.tickExecute,control] using after_sample world machine job todo _ ⟨before,next,LookupReceiptLabels.tick basis w job.request.width job.request.rows selection world selected.2⟩ valid.2

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (ordered : LookupBatchReceiptOrder.Ordered world earlier machine) (valid : Certificates world machine) :
    Certificates world (NativeLookupBatch.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih =>
    exact ih _ (LookupBatchReceiptOrder.tick basis w machine world earlier descriptorFits ordered)
      (tick basis w machine world earlier descriptorFits ordered valid)

theorem initialized (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (actions : List (NativeLookupBatch.Action p)) (transcript : NativeTranscript.Transcript) (world : World)
    (framed : ReceiptSequence.Framed transcript)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Certificates world (NativeLookupBatch.execute basis w fuel (NativeLookupBatch.initial actions transcript) world).1 := by
  exact execute basis w fuel _ world _ descriptorFits (LookupBatchReceiptOrder.initial actions transcript world framed)
    ⟨True.intro,by simp only [NativeLookupBatch.initial,List.not_mem_nil,false_implies,implies_true]⟩

end
end FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch
