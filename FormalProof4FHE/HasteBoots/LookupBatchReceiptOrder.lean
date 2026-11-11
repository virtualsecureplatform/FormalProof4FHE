module
public import FormalProof4FHE.HasteBoots.LookupReceiptOrder
public import FormalProof4FHE.HasteBoots.LookupReceiptBatchLineage
import all FormalProof4FHE.HasteBoots.NativeLookupBatch
import all FormalProof4FHE.HasteBoots.NativeTranscript
@[expose] public section

/-! Exact receipt concatenation across actual ordered lookup jobs. Active
selections follow all completed jobs; no rejected or duplicate draw is erased. -/
namespace FormalProof4FHE.HasteBoots.LookupBatchReceiptOrder
open InputIndexedOracle (World)
open ReceiptSequence (Framed)
open ReceiptFrameView (frames frame)
open LookupReceiptBatchLineage (current)
noncomputable section

def completedFrames (world : World) {p : ℕ} {K : Type} (machine : NativeLookupBatch.Machine p K) : List TranscriptFrame.Frame :=
  machine.completed.flatMap (fun entry => entry.selection.draws.map (fun draw => frame world draw.coefficients.phase))

def activeFrames (world : World) {p : ℕ} {K : Type} (machine : NativeLookupBatch.Machine p K) : List TranscriptFrame.Frame :=
  match machine.control with
  | .sampling _ _ selection => selection.draws.map (fun draw => frame world draw.coefficients.phase)
  | _ => []

def Ordered (world : World) (earlier : List TranscriptFrame.Frame) {p : ℕ} {K : Type}
    (machine : NativeLookupBatch.Machine p K) : Prop :=
  Framed (current machine) ∧
  (match machine.control with
  | .sampling _ _ selection => LookupReceiptOrder.Ordered world (earlier ++ completedFrames world machine) selection
  | _ => True) ∧
  frames (current machine).input = (earlier ++ completedFrames world machine) ++ activeFrames world machine

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem initial (actions : List (NativeLookupBatch.Action p)) (transcript : NativeTranscript.Transcript) (world : World) (old : Framed transcript) :
    Ordered world (frames transcript.input) (NativeLookupBatch.initial (K := K) actions transcript) :=
  ⟨old,True.intro,by simp [NativeLookupBatch.initial,completedFrames,activeFrames,current]⟩

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem after_sample (machine : NativeLookupBatch.Machine p K) (job : NativeLookupBatch.Job p)
    (todo : List (NativeLookupBatch.Action p)) (selection : NativeLookupChallenge.Machine K) (world : World)
    (earlier : List TranscriptFrame.Frame)
    (selected : LookupReceiptOrder.Ordered world (earlier ++ completedFrames world machine) selection) :
    Ordered world earlier (NativeLookupBatch.afterSample machine job todo selection) := by
  cases control : selection.control <;>
    simp only [NativeLookupBatch.afterSample,control,Ordered,current,completedFrames,activeFrames]
  · exact ⟨selected.1,selected,selected.2.2⟩
  · exact ⟨selected.1,selected,selected.2.2⟩
  · refine ⟨?_,True.intro,?_⟩
    · simpa only [LookupReceiptLineage.current,control] using selected.1
    · simpa only [LookupReceiptLineage.current,control,completedFrames,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,List.append_assoc] using selected.2.2

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Ordered world earlier machine) : Ordered world earlier (NativeLookupBatch.tickExecute basis w machine world).1 := by
  cases control : machine.control with
  | finished transcript => simpa only [NativeLookupBatch.tickExecute,control] using valid
  | ready todo transcript =>
    have old : Framed transcript := by simpa only [current,control] using valid.1
    have sequence : frames transcript.input = earlier ++ completedFrames world machine := by
      simpa only [current,activeFrames,control,List.append_nil] using valid.2.2
    cases todo with
    | nil =>
      simpa only [NativeLookupBatch.tickExecute,control,Ordered,current,completedFrames,activeFrames,List.append_nil] using
        And.intro old (And.intro True.intro sequence)
    | cons action todo =>
      cases action with
      | request ordinal =>
        have added := ReceiptSequence.absorb transcript 1 NativeLookupBatch.requestLabel (NativeUsizeMessage.encode ordinal) old
          ⟨by change (NativeTranscript.utf8 "shared lookup challenge request").length < _; unfold NativeTranscript.utf8; decide +kernel,
            lt_of_le_of_lt (NativeUsizeMessage.encode_length ordinal) (by decide +kernel)⟩ (by decide)
        simp only [NativeLookupBatch.tickExecute,control,Ordered,current,completedFrames,activeFrames,List.append_nil]
        exact ⟨added.1,True.intro,added.2.trans sequence⟩
      | sample job =>
        have started := LookupReceiptOrder.initial (K := K) p degree w transcript world old descriptorFits
        rw [sequence] at started
        simp only [NativeLookupBatch.tickExecute,control,Ordered,current,completedFrames,activeFrames]
        exact ⟨started.1,started,started.2.2⟩
  | sampling job todo selection =>
    have selected : LookupReceiptOrder.Ordered world (earlier ++ completedFrames world machine) selection := by
      simpa only [control] using valid.2.1
    simpa only [NativeLookupBatch.tickExecute,control] using
      after_sample machine job todo _ world earlier (LookupReceiptOrder.tick basis w job.request.width job.request.rows selection world _ descriptorFits selected)

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Ordered world earlier machine) : Ordered world earlier (NativeLookupBatch.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick basis w machine world earlier descriptorFits valid)

end
end FormalProof4FHE.HasteBoots.LookupBatchReceiptOrder
