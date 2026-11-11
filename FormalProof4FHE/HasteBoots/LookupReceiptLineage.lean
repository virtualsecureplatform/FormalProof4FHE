module
public import FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension
import all FormalProof4FHE.HasteBoots.NativeLookupChallenge
import all FormalProof4FHE.HasteBoots.NativeTranscript
@[expose] public section

/-! Every retained native lookup draw has its actual finalized receipt in the
current transcript ancestry. Rejected draws remain in order; the sampler and
its transcript construction are unchanged. -/
namespace FormalProof4FHE.HasteBoots.LookupReceiptLineage
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeTranscriptExtension (Extends StateExtends)
noncomputable section

/-- A finished drive returns exactly the native finalization of its retained
state, rather than an independently supplied receipt transcript. -/
theorem drive_finished (p fuel : ℕ) (field next : NativeFieldVector.State) (world : World) (transcript : Transcript)
    (finished : (NativeFieldVector.driveExecute p fuel field world).1 = .finished next transcript) :
    transcript = (NativeTranscript.finishField world next.phase).run.1 := by
  change (NativeFieldVector.finishExecute world (NativeFieldVector.execute p fuel field world).1).1 = .finished next transcript at finished
  unfold NativeFieldVector.finishExecute at finished
  split at finished
  next complete =>
    obtain ⟨state,result⟩ := NativeFieldVector.Status.finished.inj finished
    rw [← state]
    exact result.symm
  next => contradiction

def current {K : Type} (machine : NativeLookupChallenge.Machine K) : Transcript :=
  match machine.control with
  | .compression field | .reciprocal _ _ _ field => field.phase.pending
  | .finished _ _ _ _ transcript => transcript

def Selection (world : World) {K : Type} (machine : NativeLookupChallenge.Machine K) : Prop :=
  (match machine.control with
  | .compression field | .reciprocal _ _ _ field => field.phase.label.length < TranscriptFrame.lengthLimit
  | .finished _ _ _ _ _ => True) ∧
  ∀ draw ∈ machine.draws, Extends (NativeTranscript.finishField world draw.coefficients.phase).run.1 (current machine)

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem initial (p degree w : ℕ) (transcript : Transcript) (world : World) :
    Selection world (NativeLookupChallenge.initialExecute (K := K) p degree w transcript).1 :=
  ⟨by change (NativeTranscript.utf8 "extension tuple hash challenge").length < _; unfold NativeTranscript.utf8; decide +kernel,
    by simp [NativeLookupChallenge.initialExecute]⟩

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Selection world machine) :
    Extends (current machine) (current (NativeLookupChallenge.tickExecute basis w width rows machine world).1) ∧
      Selection world (NativeLookupChallenge.tickExecute basis w width rows machine world).1 := by
  cases control : machine.control with
  | finished y r weights table transcript =>
    simpa only [NativeLookupChallenge.tickExecute,control] using And.intro (Extends.refl _) valid
  | compression field =>
    have label : field.phase.label.length < TranscriptFrame.lengthLimit := by simpa only [control] using valid.1
    have driven := NativeTranscriptExtension.drive_status field.phase.pending p 1 field world ⟨Extends.refl _,label⟩
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      simp only [result,NativeTranscriptExtension.StatusExtends] at driven
      have fields := NativeTranscriptExtension.execute_fields p 1 field world
      have sameState := congrArg NativeFieldVector.stateOf result
      rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at sameState
      change (NativeFieldVector.execute p 1 field world).1 = next at sameState
      rw [sameState] at fields
      have retained : current (NativeLookupChallenge.tickExecute basis w width rows machine world).1 = current machine := by
        simp only [NativeLookupChallenge.tickExecute,control,result,current,fields.1]
      refine ⟨by rw [retained]; exact Extends.refl _,?_⟩
      simpa only [Selection,NativeLookupChallenge.tickExecute,control,result,current,fields.1] using And.intro driven.2 valid.2
    | finished next transcript =>
      simp only [result,NativeTranscriptExtension.StatusExtends] at driven
      have begun := NativeTranscriptExtension.scalar_begin p degree w transcript NativeLookupChallenge.reciprocalLabel (by change (NativeTranscript.utf8 "extension tuple reciprocal challenge").length < _; unfold NativeTranscript.utf8; decide +kernel) descriptorFits
      have final := drive_finished p 1 field next world transcript result
      have progress := driven.2.trans begun.1
      refine ⟨?_,?_⟩
      · simpa only [current,control,NativeLookupChallenge.tickExecute,result] using progress
      · simp only [Selection,NativeLookupChallenge.tickExecute,control,result,current]
        refine ⟨begun.2,?_⟩
        intro draw member
        rcases List.mem_append.mp member with old | added
        · exact (valid.2 draw old).trans (by simpa only [current,control] using progress)
        · obtain rfl := List.mem_singleton.mp added
          rw [← final]
          exact begun.1
  | reciprocal y weights table field =>
    have label : field.phase.label.length < TranscriptFrame.lengthLimit := by simpa only [control] using valid.1
    have driven := NativeTranscriptExtension.drive_status field.phase.pending p 1 field world ⟨Extends.refl _,label⟩
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      simp only [result,NativeTranscriptExtension.StatusExtends] at driven
      have fields := NativeTranscriptExtension.execute_fields p 1 field world
      have sameState := congrArg NativeFieldVector.stateOf result
      rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at sameState
      change (NativeFieldVector.execute p 1 field world).1 = next at sameState
      rw [sameState] at fields
      have retained : current (NativeLookupChallenge.tickExecute basis w width rows machine world).1 = current machine := by
        simp only [NativeLookupChallenge.tickExecute,control,result,current,fields.1]
      refine ⟨by rw [retained]; exact Extends.refl _,?_⟩
      simpa only [Selection,NativeLookupChallenge.tickExecute,control,result,current,fields.1] using And.intro driven.2 valid.2
    | finished next transcript =>
      simp only [result,NativeTranscriptExtension.StatusExtends] at driven
      have final := drive_finished p 1 field next world transcript result
      have retained : ∀ draw ∈ machine.draws ++ [⟨TypedFieldRequest.scalarValue basis next.values,next⟩],
          Extends (NativeTranscript.finishField world draw.coefficients.phase).run.1 transcript := by
        intro draw member
        rcases List.mem_append.mp member with old | added
        · exact (valid.2 draw old).trans (by simpa only [current,control] using driven.2)
        · obtain rfl := List.mem_singleton.mp added
          rw [← final]
          exact Extends.refl _
      cases allowed : NativeLookupChallenge.allowed table (TypedFieldRequest.scalarValue basis next.values) with
      | true =>
        simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,ite_true,current,Selection] using
          And.intro driven.2 (And.intro True.intro retained)
      | false =>
        have begun := NativeTranscriptExtension.scalar_begin p degree w transcript NativeLookupChallenge.reciprocalLabel (by change (NativeTranscript.utf8 "extension tuple reciprocal challenge").length < _; unfold NativeTranscript.utf8; decide +kernel) descriptorFits
        simp only [NativeLookupChallenge.tickExecute,control,result,allowed,Bool.false_eq_true,ite_false,current,Selection]
        exact ⟨driven.2.trans begun.1,begun.2,fun draw member => (retained draw member).trans begun.1⟩

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Selection world machine) :
    Extends (current machine) (current (NativeLookupChallenge.execute basis w width rows fuel machine world).1) ∧
      Selection world (NativeLookupChallenge.execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact ⟨Extends.refl _,valid⟩
  | succ fuel ih =>
    have next := tick basis w width rows machine world descriptorFits valid
    have later := ih _ next.2
    exact ⟨next.1.trans later.1,later.2⟩

end
end FormalProof4FHE.HasteBoots.LookupReceiptLineage
