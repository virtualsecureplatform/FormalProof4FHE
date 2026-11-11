module
public import FormalProof4FHE.HasteBoots.ReceiptSequence
public import FormalProof4FHE.HasteBoots.LookupReceiptLineage
import all FormalProof4FHE.HasteBoots.NativeLookupChallenge
import all FormalProof4FHE.HasteBoots.NativeTranscript
@[expose] public section

/-! Exact chronological receipt sequence of the actual lookup reader, with
rejected offsets and duplicate frames preserved. -/
namespace FormalProof4FHE.HasteBoots.LookupReceiptOrder
open InputIndexedOracle (World)
open ReceiptSequence (Framed)
open ReceiptFrameView (frames frame)
open LookupReceiptLineage (current)
noncomputable section

def Ordered (world : World) (earlier : List TranscriptFrame.Frame) {K : Type}
    (machine : NativeLookupChallenge.Machine K) : Prop :=
  Framed (current machine) ∧ LookupReceiptLineage.Selection world machine ∧
    frames (current machine).input = earlier ++ machine.draws.map (fun draw => frame world draw.coefficients.phase)

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem initial (p degree w : ℕ) (transcript : NativeTranscript.Transcript) (world : World) (old : Framed transcript)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Ordered world (frames transcript.input) (NativeLookupChallenge.initialExecute (K := K) p degree w transcript).1 := by
  have begun := ReceiptSequence.scalar_begin transcript NativeLookupChallenge.hashLabel p degree w old
    (by change (NativeTranscript.utf8 "extension tuple hash challenge").length < _; unfold NativeTranscript.utf8; decide +kernel) descriptorFits
  exact ⟨begun.1,LookupReceiptLineage.initial p degree w transcript world,by simpa only [NativeLookupChallenge.initialExecute,List.map_nil,List.append_nil,current] using begun.2⟩

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Ordered world earlier machine) :
    Ordered world earlier (NativeLookupChallenge.tickExecute basis w width rows machine world).1 := by
  have lineage := (LookupReceiptLineage.tick basis w width rows machine world descriptorFits valid.2.1).2
  cases control : machine.control with
  | finished y r weights table transcript => simpa only [NativeLookupChallenge.tickExecute,control] using valid
  | compression field =>
    have label : field.phase.label.length < TranscriptFrame.lengthLimit := by simpa only [control] using valid.2.1.1
    have old : Framed field.phase.pending := by simpa only [current,control] using valid.1
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      have fields := NativeTranscriptExtension.execute_fields p 1 field world
      have retained := congrArg NativeFieldVector.stateOf result
      rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at retained
      change (NativeFieldVector.execute p 1 field world).1 = next at retained
      rw [retained] at fields
      refine ⟨?_,lineage,?_⟩
      · simpa only [NativeLookupChallenge.tickExecute,control,result,current,fields.1] using old
      · simpa only [NativeLookupChallenge.tickExecute,control,result,current,fields.1] using valid.2.2
    | finished next transcript =>
      have fields := NativeTranscriptExtension.execute_fields p 1 field world
      have retained := congrArg NativeFieldVector.stateOf result
      rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at retained
      change (NativeFieldVector.execute p 1 field world).1 = next at retained
      rw [retained] at fields
      have final := LookupReceiptLineage.drive_finished p 1 field next world transcript result
      have done := ReceiptSequence.finish next.phase world (by rw [fields.1]; exact old) (by rw [fields.2]; exact label)
      rw [← final] at done
      have begun := ReceiptSequence.scalar_begin transcript NativeLookupChallenge.reciprocalLabel p degree w done.1
        (by change (NativeTranscript.utf8 "extension tuple reciprocal challenge").length < _; unfold NativeTranscript.utf8; decide +kernel) descriptorFits
      refine ⟨?_,lineage,?_⟩
      · simpa only [NativeLookupChallenge.tickExecute,control,result,current] using begun.1
      · simp only [NativeLookupChallenge.tickExecute,control,result,current,List.map_append,List.map_singleton]
        rw [begun.2,done.2,fields.1]
        have sequence := valid.2.2
        simp only [current,control] at sequence
        rw [sequence,List.append_assoc]
  | reciprocal y weights table field =>
    have label : field.phase.label.length < TranscriptFrame.lengthLimit := by simpa only [control] using valid.2.1.1
    have old : Framed field.phase.pending := by simpa only [current,control] using valid.1
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      have fields := NativeTranscriptExtension.execute_fields p 1 field world
      have retained := congrArg NativeFieldVector.stateOf result
      rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at retained
      change (NativeFieldVector.execute p 1 field world).1 = next at retained
      rw [retained] at fields
      refine ⟨?_,lineage,?_⟩
      · simpa only [NativeLookupChallenge.tickExecute,control,result,current,fields.1] using old
      · simpa only [NativeLookupChallenge.tickExecute,control,result,current,fields.1] using valid.2.2
    | finished next transcript =>
      have fields := NativeTranscriptExtension.execute_fields p 1 field world
      have retained := congrArg NativeFieldVector.stateOf result
      rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at retained
      change (NativeFieldVector.execute p 1 field world).1 = next at retained
      rw [retained] at fields
      have final := LookupReceiptLineage.drive_finished p 1 field next world transcript result
      have done := ReceiptSequence.finish next.phase world (by rw [fields.1]; exact old) (by rw [fields.2]; exact label)
      rw [← final] at done
      have sequence : frames transcript.input = earlier ++
          (machine.draws ++ [(⟨TypedFieldRequest.scalarValue basis next.values,next⟩ : NativeLookupChallenge.Draw K)]).map (fun draw => frame world draw.coefficients.phase) := by
        rw [done.2,fields.1,List.map_append,List.map_singleton]
        have previous := valid.2.2
        simp only [current,control] at previous
        rw [previous,List.append_assoc]
      cases allowed : NativeLookupChallenge.allowed table (TypedFieldRequest.scalarValue basis next.values) with
      | true =>
        exact ⟨by simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,ite_true,current] using done.1,
          lineage,by simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,ite_true,current] using sequence⟩
      | false =>
        have begun := ReceiptSequence.scalar_begin transcript NativeLookupChallenge.reciprocalLabel p degree w done.1
          (by change (NativeTranscript.utf8 "extension tuple reciprocal challenge").length < _; unfold NativeTranscript.utf8; decide +kernel) descriptorFits
        refine ⟨?_,lineage,?_⟩
        · simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,Bool.false_eq_true,ite_false,current] using begun.1
        · simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,Bool.false_eq_true,ite_false,current,begun.2] using sequence

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Ordered world earlier machine) :
    Ordered world earlier (NativeLookupChallenge.execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick basis w width rows machine world earlier descriptorFits valid)

end
end FormalProof4FHE.HasteBoots.LookupReceiptOrder
