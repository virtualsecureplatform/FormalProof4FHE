module
public import FormalProof4FHE.HasteBoots.LookupReceiptLineage
import all FormalProof4FHE.HasteBoots.NativeLookupChallenge
import all FormalProof4FHE.HasteBoots.NativeTranscript
@[expose] public section

/-! Completed lookup selections keep their finalized receipt ancestry through
later ordered jobs and the eventual batch transcript. -/
namespace FormalProof4FHE.HasteBoots.LookupReceiptBatchLineage
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeTranscriptExtension (Extends)
open LookupReceiptLineage (current Selection)
noncomputable section

def current {p : ℕ} {K : Type} (machine : NativeLookupBatch.Machine p K) : Transcript :=
  match machine.control with
  | .ready _ transcript | .finished transcript => transcript
  | .sampling _ _ selection => LookupReceiptLineage.current selection

def Batch (world : World) {p : ℕ} {K : Type} (machine : NativeLookupBatch.Machine p K) : Prop :=
  (match machine.control with
  | .sampling _ _ selection => Selection world selection
  | _ => True) ∧
  ∀ completed ∈ machine.completed, ∀ draw ∈ completed.selection.draws,
    Extends (NativeTranscript.finishField world draw.coefficients.phase).run.1 (current machine)

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem initial (actions : List (NativeLookupBatch.Action p)) (transcript : Transcript) (world : World) :
    Batch world (NativeLookupBatch.initial (K := K) actions transcript) := ⟨True.intro,by simp [NativeLookupBatch.initial]⟩

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem after_sample (machine : NativeLookupBatch.Machine p K) (job : NativeLookupBatch.Job p)
    (todo : List (NativeLookupBatch.Action p)) (selection : NativeLookupChallenge.Machine K) (world : World)
    (selected : Selection world selection)
    (earlier : ∀ completed ∈ machine.completed, ∀ draw ∈ completed.selection.draws,
      Extends (NativeTranscript.finishField world draw.coefficients.phase).run.1 (LookupReceiptLineage.current selection)) :
    Batch world (NativeLookupBatch.afterSample machine job todo selection) := by
  cases control : selection.control <;> simp only [NativeLookupBatch.afterSample,control,Batch,current]
  · exact ⟨selected,earlier⟩
  · exact ⟨selected,earlier⟩
  · refine ⟨True.intro,?_⟩
    intro completed member draw drawMember
    rcases List.mem_append.mp member with old | added
    · simpa only [LookupReceiptLineage.current,control] using earlier completed old draw drawMember
    · obtain rfl := List.mem_singleton.mp added
      simpa only [LookupReceiptLineage.current,control] using selected.2 draw drawMember

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Batch world machine) :
    Extends (current machine) (current (NativeLookupBatch.tickExecute basis w machine world).1) ∧
      Batch world (NativeLookupBatch.tickExecute basis w machine world).1 := by
  cases control : machine.control with
  | finished transcript =>
    simpa only [NativeLookupBatch.tickExecute,control] using And.intro (Extends.refl _) valid
  | ready todo transcript =>
    cases todo with
    | nil =>
      simpa only [NativeLookupBatch.tickExecute,control,current,Batch] using And.intro (Extends.refl transcript) (And.intro True.intro valid.2)
    | cons action todo =>
      cases action with
      | request ordinal =>
        have progress := NativeTranscriptExtension.absorb transcript 1 NativeLookupBatch.requestLabel (NativeUsizeMessage.encode ordinal)
          ⟨by change NativeLookupBatch.requestLabel.length < _; decide +kernel,
            lt_of_le_of_lt (NativeUsizeMessage.encode_length ordinal) (by decide +kernel)⟩
        simp only [NativeLookupBatch.tickExecute,control,current,Batch]
        exact ⟨by simpa only [NativeTranscript.appendBytes] using progress,True.intro,fun completed member draw drawMember =>
          (valid.2 completed member draw drawMember).trans (by simpa only [current,control,NativeTranscript.appendBytes] using progress)⟩
      | sample job =>
        have begun := NativeTranscriptExtension.scalar_begin p degree w transcript NativeLookupChallenge.hashLabel (by change (NativeTranscript.utf8 "extension tuple hash challenge").length < _; unfold NativeTranscript.utf8; decide +kernel) descriptorFits
        simp only [NativeLookupBatch.tickExecute,control,current,Batch]
        change Extends transcript (TypedFieldRequest.beginExecute p degree w transcript NativeLookupChallenge.hashLabel).1.phase.pending ∧ _
        exact ⟨begun.1,LookupReceiptLineage.initial p degree w transcript world,
          fun completed member draw drawMember => (valid.2 completed member draw drawMember).trans (by simpa only [current,control,LookupReceiptLineage.current,NativeLookupChallenge.initialExecute] using begun.1)⟩
  | sampling job todo selection =>
    have selected : Selection world selection := by simpa only [control] using valid.1
    have next := LookupReceiptLineage.tick basis w job.request.width job.request.rows selection world descriptorFits selected
    have earlier : ∀ completed ∈ machine.completed, ∀ draw ∈ completed.selection.draws,
        Extends (NativeTranscript.finishField world draw.coefficients.phase).run.1
          (LookupReceiptLineage.current (NativeLookupChallenge.tickExecute basis w job.request.width job.request.rows selection world).1) := by
      intro completed member draw drawMember
      exact (valid.2 completed member draw drawMember).trans (by simpa only [current,control] using next.1)
    have preserved := after_sample machine job todo _ world next.2 earlier
    have sameCurrent : current (NativeLookupBatch.tickExecute basis w machine world).1 =
        LookupReceiptLineage.current (NativeLookupChallenge.tickExecute basis w job.request.width job.request.rows selection world).1 := by
      simp only [NativeLookupBatch.tickExecute,control]
      cases resultControl : (NativeLookupChallenge.tickExecute basis w job.request.width job.request.rows selection world).1.control <;>
        simp only [NativeLookupBatch.afterSample,resultControl,current,LookupReceiptLineage.current]
    exact ⟨by rw [sameCurrent]; simpa only [current,control] using next.1,
      by simpa only [NativeLookupBatch.tickExecute,control] using preserved⟩

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Batch world machine) :
    Extends (current machine) (current (NativeLookupBatch.execute basis w fuel machine world).1) ∧
      Batch world (NativeLookupBatch.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact ⟨Extends.refl _,valid⟩
  | succ fuel ih =>
    have next := tick basis w machine world descriptorFits valid
    have later := ih _ next.2
    exact ⟨next.1.trans later.1,later.2⟩

end
end FormalProof4FHE.HasteBoots.LookupReceiptBatchLineage
