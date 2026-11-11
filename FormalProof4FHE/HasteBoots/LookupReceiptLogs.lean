module
public import FormalProof4FHE.HasteBoots.LookupReceiptLineage
public import FormalProof4FHE.HasteBoots.NativeFieldReceipt
@[expose] public section

/-! Every retained lookup draw has its actual native finalization observations
in the execution log, including rejected offsets and resumed readers. No
receipt observation, freshness or framed ancestry is supplied independently. -/
namespace FormalProof4FHE.HasteBoots.LookupReceiptLogs
open InputIndexedOracle (World)
open NativeTranscript (Observation)
noncomputable section

theorem drive_receipt (p fuel : ℕ) (field next : NativeFieldVector.State) (world : World) (transcript : NativeTranscript.Transcript)
    (finished : (NativeFieldVector.driveExecute p fuel field world).1 = .finished next transcript) :
    (NativeTranscript.finishField world next.phase).run.2.Sublist (NativeFieldVector.driveExecute p fuel field world).2 := by
  change (NativeFieldVector.finishExecute world (NativeFieldVector.execute p fuel field world).1).1 = .finished next transcript at finished
  unfold NativeFieldVector.finishExecute at finished
  split at finished
  next complete =>
    obtain ⟨sameState,_⟩ := NativeFieldVector.Status.finished.inj finished
    rw [← sameState]
    simp only [NativeFieldVector.driveExecute,NativeFieldVector.finishExecute,complete,ite_true]
    exact List.sublist_append_right _ _
  next => contradiction

theorem output_member (world : World) (phase : NativeTranscript.FieldPhase) :
    Observation.output (NativeFieldReceipt.input phase) 0 (InputIndexedOracle.bytes world (NativeFieldReceipt.input phase) 0 64) ∈
      (NativeTranscript.finishField world phase).run.2 := by
  change _ ∈ [Observation.start _,Observation.output _ _ _]
  exact List.mem_cons_of_mem _ List.mem_cons_self

def Reads {K : Type} (world : World) (draws : List (NativeLookupChallenge.Draw K)) (history : List Observation) : Prop :=
  ∀ draw ∈ draws, (NativeTranscript.finishField world draw.coefficients.phase).run.2.Sublist history

theorem mono {K : Type} (world : World) (draws : List (NativeLookupChallenge.Draw K))
    (earlier later : List Observation) (reads : Reads world draws earlier) (included : earlier.Sublist later) : Reads world draws later :=
  fun draw member => (reads draw member).trans included

theorem add {K : Type} (world : World) (draws : List (NativeLookupChallenge.Draw K)) (draw : NativeLookupChallenge.Draw K)
    (earlier later : List Observation) (reads : Reads world draws earlier)
    (receipt : (NativeTranscript.finishField world draw.coefficients.phase).run.2.Sublist later) :
    Reads world (draws ++ [draw]) (earlier ++ later) := by
  intro entry member
  rcases List.mem_append.mp member with old | added
  · exact (reads entry old).trans (List.sublist_append_left _ _)
  · obtain rfl := List.mem_singleton.mp added
    exact receipt.trans (List.sublist_append_right _ _)

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (history : List Observation) (reads : Reads world machine.draws history) :
    Reads world (NativeLookupChallenge.tickExecute basis w width rows machine world).1.draws
      (history ++ (NativeLookupChallenge.tickExecute basis w width rows machine world).2) := by
  cases control : machine.control with
  | finished y r weights table transcript => simpa only [NativeLookupChallenge.tickExecute,control,List.append_nil] using reads
  | compression field =>
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      simpa only [NativeLookupChallenge.tickExecute,control,result] using mono world machine.draws history _ reads (List.sublist_append_left _ _)
    | finished next transcript =>
      have logged := drive_receipt p 1 field next world transcript result
      simpa only [NativeLookupChallenge.tickExecute,control,result] using
        add world machine.draws ⟨TypedFieldRequest.scalarValue basis next.values,next⟩ history _ reads
          (logged.trans (List.sublist_append_left _ _))
  | reciprocal y weights table field =>
    cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      simpa only [NativeLookupChallenge.tickExecute,control,result] using mono world machine.draws history _ reads (List.sublist_append_left _ _)
    | finished next transcript =>
      have logged := drive_receipt p 1 field next world transcript result
      cases allowed : NativeLookupChallenge.allowed table (TypedFieldRequest.scalarValue basis next.values) with
      | true =>
        simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,ite_true] using
          add world machine.draws ⟨TypedFieldRequest.scalarValue basis next.values,next⟩ history _ reads logged
      | false =>
        simpa only [NativeLookupChallenge.tickExecute,control,result,allowed,Bool.false_eq_true,ite_false] using
          add world machine.draws ⟨TypedFieldRequest.scalarValue basis next.values,next⟩ history _ reads
            (logged.trans (List.sublist_append_left _ _))

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ) (rows : List (List (ZMod p)))
    (machine : NativeLookupChallenge.Machine K) (world : World) (history : List Observation) (reads : Reads world machine.draws history) :
    Reads world (NativeLookupChallenge.execute basis w width rows fuel machine world).1.draws
      (history ++ (NativeLookupChallenge.execute basis w width rows fuel machine world).2) := by
  induction fuel generalizing machine history with
  | zero => simpa only [NativeLookupChallenge.execute,List.append_nil] using reads
  | succ fuel ih =>
    have later := ih _ _ (tick basis w width rows machine world history reads)
    simpa only [NativeLookupChallenge.execute,List.append_assoc] using later

end
end FormalProof4FHE.HasteBoots.LookupReceiptLogs
