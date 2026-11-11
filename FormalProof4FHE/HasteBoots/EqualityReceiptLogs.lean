module
public import FormalProof4FHE.HasteBoots.LookupReceiptLogs
@[expose] public section

/-! Every actual retained EQ point has its finalization observations in the
native request log, across later points and arbitrary suspended prefixes. -/
namespace FormalProof4FHE.HasteBoots.EqualityReceiptLogs
open InputIndexedOracle (World)
open NativeTranscript (Observation)
noncomputable section

def Reads {count : ℕ} {K : Type} (world : World) (draws : List (NativeLookupEquality.Draw count K)) (history : List Observation) : Prop :=
  ∀ draw ∈ draws, (NativeTranscript.finishField world draw.coefficients.phase).run.2.Sublist history

variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K]

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World) (history : List Observation) (valid : Reads world machine.draws history) :
    Reads world (NativeLookupEquality.tickExecute basis w machine world).1.draws
      (history ++ (NativeLookupEquality.tickExecute basis w machine world).2) := by
  by_cases complete : machine.remaining = 0
  · simpa only [NativeLookupEquality.tickExecute,complete,ite_true,List.append_nil] using valid
  · cases active : machine.active with
    | none =>
      simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,Reads]
      exact fun draw member => (valid draw member).trans (List.sublist_append_left _ _)
    | some field =>
      cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
      | suspended next =>
        simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,result,Reads]
        exact fun draw member => (valid draw member).trans (List.sublist_append_left _ _)
      | finished next transcript =>
        have logged := LookupReceiptLogs.drive_receipt p 1 field next world transcript result
        simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,result,Reads]
        intro draw member
        rcases List.mem_append.mp member with old | added
        · exact (valid draw old).trans (List.sublist_append_left _ _)
        · obtain rfl := List.mem_singleton.mp added
          exact logged.trans (List.sublist_append_right _ _)

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World) (history : List Observation) (valid : Reads world machine.draws history) :
    Reads world (NativeLookupEquality.execute basis w fuel machine world).1.draws
      (history ++ (NativeLookupEquality.execute basis w fuel machine world).2) := by
  induction fuel generalizing machine history with
  | zero => simpa only [NativeLookupEquality.execute,List.append_nil] using valid
  | succ fuel ih =>
    have later := ih _ _ (tick basis w machine world history valid)
    simpa only [NativeLookupEquality.execute,List.append_assoc] using later

theorem request (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (transcript : NativeTranscript.Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64) (world : World) :
    Reads world (OracleProgram.run (NativeLookupEquality.request basis w count fuel transcript roots fits) world).run.1.draws
      (OracleProgram.run (NativeLookupEquality.request basis w count fuel transcript roots fits) world).run.2 := by
  rw [NativeLookupEquality.request,NativeLookupEquality.run_steps]
  simpa only [List.nil_append] using execute basis w fuel (NativeLookupEquality.initial count transcript roots fits) world [] (by simp [Reads,NativeLookupEquality.initial])

end
end FormalProof4FHE.HasteBoots.EqualityReceiptLogs
