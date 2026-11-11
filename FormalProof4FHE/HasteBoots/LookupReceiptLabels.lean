module
public import FormalProof4FHE.HasteBoots.LookupReceiptLineage
public import FormalProof4FHE.HasteBoots.NativeLookupDrawHistory
import all FormalProof4FHE.HasteBoots.NativeLookupChallenge
@[expose] public section

/-! The actual retained lookup draws have one compression label followed by
reciprocal labels. This invariant includes every rejected offset. -/
namespace FormalProof4FHE.HasteBoots.LookupReceiptLabels
open InputIndexedOracle (World)
open NativeLookupChallenge (hashLabel reciprocalLabel)
noncomputable section

def Group {K : Type} (draws : List (NativeLookupChallenge.Draw K)) : Prop :=
  ∃ first rest, draws = first :: rest ∧ first.coefficients.phase.label = hashLabel ∧
    ∀ draw ∈ rest, draw.coefficients.phase.label = reciprocalLabel

def Labels {K : Type} (machine : NativeLookupChallenge.Machine K) : Prop :=
  match machine.control with
  | .compression field => field.phase.label = hashLabel ∧ machine.draws = []
  | .reciprocal _ _ _ field => field.phase.label = reciprocalLabel ∧ Group machine.draws
  | .finished _ _ _ _ _ => Group machine.draws

theorem append_group {K : Type} (draws : List (NativeLookupChallenge.Draw K)) (old : Group draws)
    (draw : NativeLookupChallenge.Draw K) (label : draw.coefficients.phase.label = reciprocalLabel) :
    Group (draws ++ [draw]) := by
  obtain ⟨first,rest,ordered,head,tail⟩ := old
  refine ⟨first,rest ++ [draw],by rw [ordered,List.cons_append],head,?_⟩
  intro entry member
  rcases List.mem_append.mp member with earlier | added
  · exact tail entry earlier
  · obtain rfl := List.mem_singleton.mp added
    exact label

theorem drive_label (p fuel : ℕ) (field : NativeFieldVector.State) (world : World) :
    (NativeFieldVector.stateOf (NativeFieldVector.driveExecute p fuel field world).1).phase.label = field.phase.label := by
  change (NativeFieldVector.stateOf (NativeFieldVector.finishExecute world (NativeFieldVector.execute p fuel field world).1).1).phase.label = _
  rw [NativeFieldVector.finish_state]
  exact (NativeTranscriptExtension.execute_fields p fuel field world).2

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem initial (p degree w : ℕ) (transcript : NativeTranscript.Transcript) :
    Labels (NativeLookupChallenge.initialExecute (K := K) p degree w transcript).1 := ⟨rfl,rfl⟩

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (valid : Labels machine) :
    Labels (NativeLookupChallenge.tickExecute basis w width rows machine world).1 := by
  cases control : machine.control with
  | finished y r weights table transcript => simpa only [NativeLookupChallenge.tickExecute,control] using valid
  | compression field =>
    have old : field.phase.label = hashLabel ∧ machine.draws = [] := by simpa only [Labels,control] using valid
    have label := drive_label p 1 field world
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      rw [result] at label
      simpa only [NativeLookupChallenge.tickExecute,control,result,Labels,NativeFieldVector.stateOf] using And.intro (label.trans old.1) old.2
    | finished next transcript =>
      rw [result] at label
      simp only [NativeLookupChallenge.tickExecute,control,result,Labels]
      refine ⟨rfl,?_⟩
      rw [old.2,List.nil_append]
      exact ⟨_,[],rfl,label.trans old.1,by simp⟩
  | reciprocal y weights table field =>
    have old : field.phase.label = reciprocalLabel ∧ Group machine.draws := by simpa only [Labels,control] using valid
    have label := drive_label p 1 field world
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      rw [result] at label
      simpa only [NativeLookupChallenge.tickExecute,control,result,Labels,NativeFieldVector.stateOf] using And.intro (label.trans old.1) old.2
    | finished next transcript =>
      rw [result] at label
      have added := append_group machine.draws old.2 ⟨TypedFieldRequest.scalarValue basis next.values,next⟩ (label.trans old.1)
      cases allowed : NativeLookupChallenge.allowed table (TypedFieldRequest.scalarValue basis next.values) with
      | true => simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,ite_true,Labels] using added
      | false =>
        simp only [NativeLookupChallenge.tickExecute,control,result,allowed,Bool.false_eq_true,ite_false,Labels]
        exact ⟨rfl,added⟩

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (valid : Labels machine) :
    Labels (NativeLookupChallenge.execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick basis w width rows machine world valid)

end
end FormalProof4FHE.HasteBoots.LookupReceiptLabels
