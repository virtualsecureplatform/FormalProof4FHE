module
public import FormalProof4FHE.HasteBoots.LookupReceiptOrder
import all FormalProof4FHE.HasteBoots.NativeLookupChallenge
@[expose] public section

/-! Each retained draw keeps the exact receipt prefix before that draw.
The draw's own receipt and all later rejected/accepted offsets are excluded. -/
namespace FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder
open InputIndexedOracle (World)
open ReceiptFrameView (frames frame)
open LookupReceiptLineage (current)
noncomputable section

def Before {K : Type} (world : World) (earlier : List TranscriptFrame.Frame)
    (draws : List (NativeLookupChallenge.Draw K)) : Prop :=
  ∀ index draw, draws[index]? = some draw →
    frames draw.coefficients.phase.pending.input = earlier ++ (draws.take index).map (fun prior => frame world prior.coefficients.phase)

theorem append {K : Type} (world : World) (earlier : List TranscriptFrame.Frame)
    (draws : List (NativeLookupChallenge.Draw K)) (draw : NativeLookupChallenge.Draw K)
    (old : Before world earlier draws)
    (atDraw : frames draw.coefficients.phase.pending.input = earlier ++ draws.map (fun prior => frame world prior.coefficients.phase)) :
    Before world earlier (draws ++ [draw]) := by
  intro index entry found
  by_cases inside : index < draws.length
  · have oldAt := found
    rw [List.getElem?_append_left inside] at oldAt
    rw [old index entry oldAt]
    simp only [List.take_append,Nat.sub_eq_zero_of_le (Nat.le_of_lt inside),List.take_zero,List.append_nil]
  · have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [List.length_append,List.length_singleton] at bound
    have indexEq : index = draws.length := by omega
    subst index
    have entryEq : draw = entry := by simpa using found
    subst entry
    simpa using atDraw

def Traced {K : Type} (world : World) (earlier : List TranscriptFrame.Frame)
    (machine : NativeLookupChallenge.Machine K) : Prop :=
  LookupReceiptOrder.Ordered world earlier machine ∧ Before world earlier machine.draws

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem initial (p degree w : ℕ) (transcript : NativeTranscript.Transcript) (world : World)
    (old : ReceiptSequence.Framed transcript)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Traced world (frames transcript.input) (NativeLookupChallenge.initialExecute (K := K) p degree w transcript).1 := by
  refine ⟨LookupReceiptOrder.initial p degree w transcript world old descriptorFits,?_⟩
  intro index draw found
  simp only [NativeLookupChallenge.initialExecute,List.getElem?_nil] at found
  contradiction

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Traced world earlier machine) :
    Traced world earlier (NativeLookupChallenge.tickExecute basis w width rows machine world).1 := by
  refine ⟨LookupReceiptOrder.tick basis w width rows machine world earlier descriptorFits valid.1,?_⟩
  cases control : machine.control with
  | finished y r weights table transcript => simpa only [NativeLookupChallenge.tickExecute,control] using valid.2
  | compression field | reciprocal y weights table field =>
    have fields := NativeTranscriptExtension.execute_fields p 1 field world
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next => simpa only [NativeLookupChallenge.tickExecute,control,result] using valid.2
    | finished next transcript =>
      have retained := congrArg NativeFieldVector.stateOf result
      rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at retained
      change (NativeFieldVector.execute p 1 field world).1 = next at retained
      rw [retained] at fields
      have atDraw : frames next.phase.pending.input = earlier ++ machine.draws.map (fun prior => frame world prior.coefficients.phase) := by
        rw [fields.1]
        simpa only [current,control] using valid.1.2.2
      have added := append world earlier machine.draws ⟨TypedFieldRequest.scalarValue basis next.values,next⟩ valid.2 atDraw
      all_goals simp only [NativeLookupChallenge.tickExecute,control,result]
      all_goals first | exact added | split <;> exact added

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Traced world earlier machine) :
    Traced world earlier (NativeLookupChallenge.execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick basis w width rows machine world earlier descriptorFits valid)

end
end FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder
