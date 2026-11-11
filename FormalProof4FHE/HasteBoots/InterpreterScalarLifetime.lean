module
public import FormalProof4FHE.HasteBoots.CandidateContinuation
public import FormalProof4FHE.HasteBoots.ByteScalarLogWork
@[expose] public section

/-! Actual interpreter horizons compose with one shared lifetime bad ledger.
The event union is not charged once per horizon, and no event measurability,
termination, or finite expected work premise is imposed. -/
namespace FormalProof4FHE.HasteBoots.InterpreterScalarLifetime
open InputIndexedOracle (Input World law)
open OracleProgram (Program bind)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

theorem safe_union {A : Type} (programs : ℕ → Program A) (dummy : Digest) (radius : ℕ) (risk : ENNReal)
    (growing : Monotone (fun fuel => {world | ScalarLifetimeComposition.Event (programs fuel) dummy radius world}))
    (bounded : ∀ fuel, law {world | ScalarLifetimeComposition.Event (programs fuel) dummy radius world ∧
        ¬GlobalReferenceBad.Bad (programs fuel) dummy world} ≤ risk) :
    law {world | (∃ fuel, ScalarLifetimeComposition.Event (programs fuel) dummy radius world) ∧
        ¬∃ fuel, GlobalReferenceBad.Bad (programs fuel) dummy world} ≤ risk := by
  let events := fun fuel => {world | ScalarLifetimeComposition.Event (programs fuel) dummy radius world ∧
    ¬∃ horizon, GlobalReferenceBad.Bad (programs horizon) dummy world}
  have monotone : Monotone events := by
    intro first later ordered world occurred
    exact ⟨growing ordered occurred.1,occurred.2⟩
  have union : {world | (∃ fuel, ScalarLifetimeComposition.Event (programs fuel) dummy radius world) ∧
        ¬∃ fuel, GlobalReferenceBad.Bad (programs fuel) dummy world} = ⋃ fuel, events fuel := by
    ext world
    simp only [events,Set.mem_ofPred_eq,Set.mem_iUnion,exists_and_right]
  rw [union,monotone.measure_iUnion]
  apply iSup_le
  intro fuel
  apply (measure_mono (show events fuel ⊆ {world | ScalarLifetimeComposition.Event (programs fuel) dummy radius world ∧
      ¬GlobalReferenceBad.Bad (programs fuel) dummy world} from ?_)).trans (bounded fuel)
  intro world occurred
  exact ⟨occurred.1,fun bad => occurred.2 ⟨fuel,bad⟩⟩

def closed (code : List ClosedByteMachine.Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (fuel : ℕ) := ClosedByteMachine.take code publicData fuel (ClosedByteMachine.initialise code privateData)

theorem closed_monotone (code : List ClosedByteMachine.Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (radius : ℕ) :
    Monotone (fun fuel => {world | ScalarLifetimeComposition.Event (closed code publicData privateData fuel) dummy radius world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change ScalarLifetimeComposition.Event (closed code publicData privateData (first+extra)) dummy radius world
  unfold closed at occurred ⊢
  rw [ClosedByteMachine.take_resume]
  exact CandidateContinuation.lifetime_event _ dummy radius occurred

theorem closed_safe_bound (code : List ClosedByteMachine.Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (radius : ℕ) :
    law {world | (∃ fuel, ScalarLifetimeComposition.Event (closed code publicData privateData fuel) dummy radius world) ∧
        ¬∃ fuel, GlobalReferenceBad.Bad (closed code publicData privateData fuel) dummy world} ≤
      ClosedByteMachineWork.expectedWork code publicData privateData * ScalarEquationWork.rate :=
  safe_union _ dummy radius _ (closed_monotone code publicData privateData dummy radius)
    (fun fuel => ByteScalarLogWork.safe_probability code publicData privateData fuel dummy radius)

def privateProgram (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) :=
  PrivateCoinByteMachine.take code publicData tape fuel (PrivateCoinByteMachine.initialise code privateData)

theorem private_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (radius : ℕ) :
    Monotone (fun fuel => {world | ScalarLifetimeComposition.Event (privateProgram code publicData tape privateData fuel) dummy radius world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change ScalarLifetimeComposition.Event (privateProgram code publicData tape privateData (first+extra)) dummy radius world
  unfold privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact CandidateContinuation.lifetime_event _ dummy radius occurred

theorem private_safe_bound (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (radius : ℕ) :
    law {world | (∃ fuel, ScalarLifetimeComposition.Event (privateProgram code publicData tape privateData fuel) dummy radius world) ∧
        ¬∃ fuel, GlobalReferenceBad.Bad (privateProgram code publicData tape privateData fuel) dummy world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * ScalarEquationWork.rate :=
  safe_union _ dummy radius _ (private_monotone code publicData tape privateData dummy radius)
    (fun fuel => ByteScalarLogWork.private_safe_probability code publicData tape privateData fuel dummy radius)

theorem split_bad {A : Type} (programs : ℕ → Program A) (dummy : Digest) (radius : ℕ) :
    law {world | ∃ fuel, ScalarLifetimeComposition.Event (programs fuel) dummy radius world} ≤
      law {world | ∃ fuel, GlobalReferenceBad.Bad (programs fuel) dummy world} +
        law {world | (∃ fuel, ScalarLifetimeComposition.Event (programs fuel) dummy radius world) ∧
          ¬∃ fuel, GlobalReferenceBad.Bad (programs fuel) dummy world} := by
  apply (measure_mono (show {world | ∃ fuel, ScalarLifetimeComposition.Event (programs fuel) dummy radius world} ⊆
      {world | ∃ fuel, GlobalReferenceBad.Bad (programs fuel) dummy world} ∪
      {world | (∃ fuel, ScalarLifetimeComposition.Event (programs fuel) dummy radius world) ∧
        ¬∃ fuel, GlobalReferenceBad.Bad (programs fuel) dummy world} from ?_)).trans (measure_union_le _ _)
  intro world occurred
  by_cases bad : ∃ fuel, GlobalReferenceBad.Bad (programs fuel) dummy world
  · exact Or.inl bad
  · exact Or.inr ⟨occurred,bad⟩

theorem closed_bound (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (radius : ℕ) :
    law {world | ∃ fuel, ScalarLifetimeComposition.Event (closed code publicData privateData fuel) dummy radius world} ≤
      law {world | ∃ fuel, GlobalReferenceBad.Bad (closed code publicData privateData fuel) dummy world} +
        ClosedByteMachineWork.expectedWork code publicData privateData * ScalarEquationWork.rate :=
  (split_bad _ dummy radius).trans (add_le_add le_rfl (closed_safe_bound code publicData privateData dummy radius))

theorem private_bound (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (radius : ℕ) :
    law {world | ∃ fuel, ScalarLifetimeComposition.Event (privateProgram code publicData tape privateData fuel) dummy radius world} ≤
      law {world | ∃ fuel, GlobalReferenceBad.Bad (privateProgram code publicData tape privateData fuel) dummy world} +
        PrivateCoinByteFixed.expectedWork code publicData tape privateData * ScalarEquationWork.rate :=
  (split_bad _ dummy radius).trans (add_le_add le_rfl (private_safe_bound code publicData tape privateData dummy radius))

end
end FormalProof4FHE.HasteBoots.InterpreterScalarLifetime
