module
public import FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch
public import FormalProof4FHE.HasteBoots.LookupProducerOrdinal
import all FormalProof4FHE.HasteBoots.NativeLookupBatch
@[expose] public section

/-! Every completed original job retains the receipt prefix of exactly the
preceding completed jobs. Rejected offsets remain inside their original job. -/
namespace FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix
open InputIndexedOracle (World)
open ReceiptFrameView (frames frame)
open LookupReceiptBatchLineage (current)
noncomputable section

def emitted {p : ℕ} {K : Type} (world : World) (entries : List (NativeLookupBatch.Completed p K)) :=
  entries.flatMap (fun entry => entry.selection.draws.map (fun draw => frame world draw.coefficients.phase))

def Indexed {p : ℕ} {K : Type} (world : World) (earlier : List TranscriptFrame.Frame)
    (entries : List (NativeLookupBatch.Completed p K)) : Prop :=
  ∀ index entry, entries[index]? = some entry →
    LookupDrawReceiptOrder.Traced world (earlier ++ emitted world (entries.take index)) entry.selection

theorem append {p : ℕ} {K : Type} (world : World) (earlier : List TranscriptFrame.Frame)
    (entries : List (NativeLookupBatch.Completed p K)) (entry : NativeLookupBatch.Completed p K)
    (old : Indexed world earlier entries)
    (selected : LookupDrawReceiptOrder.Traced world (earlier ++ emitted world entries) entry.selection) :
    Indexed world earlier (entries ++ [entry]) := by
  intro index actual found
  by_cases inside : index < entries.length
  · have oldAt := found
    rw [List.getElem?_append_left inside] at oldAt
    simpa only [List.take_append,Nat.sub_eq_zero_of_le (Nat.le_of_lt inside),List.take_zero,List.append_nil] using old index actual oldAt
  · have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [List.length_append,List.length_singleton] at bound
    have indexEq : index = entries.length := by omega
    subst index
    have actualEq : entry = actual := by simpa using found
    subst actual
    simpa using selected

def Certificates {p : ℕ} {K : Type} (world : World) (earlier : List TranscriptFrame.Frame)
    (machine : NativeLookupBatch.Machine p K) : Prop :=
  (match machine.control with
  | .sampling _ _ selection => LookupDrawReceiptOrder.Traced world (earlier ++ emitted world machine.completed) selection
  | _ => True) ∧ Indexed world earlier machine.completed

theorem after_sample {p : ℕ} {K : Type} (world : World) (earlier : List TranscriptFrame.Frame)
    (machine : NativeLookupBatch.Machine p K) (job : NativeLookupBatch.Job p)
    (todo : List (NativeLookupBatch.Action p)) (selection : NativeLookupChallenge.Machine K)
    (selected : LookupDrawReceiptOrder.Traced world (earlier ++ emitted world machine.completed) selection)
    (old : Indexed world earlier machine.completed) : Certificates world earlier (NativeLookupBatch.afterSample machine job todo selection) := by
  cases control : selection.control <;> simp only [NativeLookupBatch.afterSample,control,Certificates]
  · exact ⟨selected,old⟩
  · exact ⟨selected,old⟩
  · exact ⟨True.intro,append world earlier _ _ old selected⟩

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (ordered : LookupBatchReceiptOrder.Ordered world earlier machine) (valid : Certificates world earlier machine) :
    Certificates world earlier (NativeLookupBatch.tickExecute basis w machine world).1 := by
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
        have selected := LookupDrawReceiptOrder.initial (K := K) p degree w transcript world framed descriptorFits
        have sequence : frames transcript.input = earlier ++ emitted world machine.completed := by
          simpa only [current,LookupBatchReceiptOrder.activeFrames,LookupBatchReceiptOrder.completedFrames,emitted,control,List.append_nil] using ordered.2.2
        rw [sequence] at selected
        simpa only [NativeLookupBatch.tickExecute,control,Certificates] using And.intro selected valid.2
  | sampling job todo selection =>
    have selected : LookupDrawReceiptOrder.Traced world (earlier ++ emitted world machine.completed) selection := by simpa only [control] using valid.1
    simpa only [NativeLookupBatch.tickExecute,control] using after_sample world earlier machine job todo _
      (LookupDrawReceiptOrder.tick basis w job.request.width job.request.rows selection world _ descriptorFits selected) valid.2

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (ordered : LookupBatchReceiptOrder.Ordered world earlier machine) (valid : Certificates world earlier machine) :
    Certificates world earlier (NativeLookupBatch.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih =>
    exact ih _ (LookupBatchReceiptOrder.tick basis w machine world earlier descriptorFits ordered)
      (tick basis w machine world earlier descriptorFits ordered valid)

theorem initialized (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (actions : List (NativeLookupBatch.Action p)) (transcript : NativeTranscript.Transcript) (world : World)
    (framed : ReceiptSequence.Framed transcript)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Certificates world (frames transcript.input) (NativeLookupBatch.execute basis w fuel (NativeLookupBatch.initial actions transcript) world).1 := by
  exact execute basis w fuel _ world _ descriptorFits (LookupBatchReceiptOrder.initial actions transcript world framed)
    ⟨True.intro,by intro index entry found; simp only [NativeLookupBatch.initial,List.getElem?_nil] at found; contradiction⟩

end
end FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix
