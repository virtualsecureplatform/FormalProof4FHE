module
public import FormalProof4FHE.HasteBoots.OffsetPositionContinuation
public import FormalProof4FHE.HasteBoots.OffsetDegreeBudget
public import FormalProof4FHE.HasteBoots.PrivateCoinProgramPrefix
public import FormalProof4FHE.HasteBoots.CountableCoinOuterBound
@[expose] public section

/-! All reciprocal classes at one first-read position retain their degree bound across
all original private tapes and instruction horizons. The global reference bad
event is excluded once. No union over positions or attacker-work bound is
asserted by this per-position theorem. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def Event (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (position budget : ℕ) (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  OffsetPositionKernel.Event (privateProgram code publicData execution.1 privateData fuel) position budget dummy execution.2

def Bad (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2

theorem prefix_safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (position budget : ℕ) (dummy : Digest) (fuel : ℕ) :
    (coins.prod law) {execution | Event code publicData privateData position budget dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} ≤
      coins Set.univ * ((budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  let sectionEvent := fun values : Fin fuel → InputIndexedOracle.Byte => {world |
    let program := privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel values) privateData fuel
    OffsetPositionKernel.BoundedEvent program position budget dummy world}
  have same (tape : Tape) : privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel
      (PrivateCoinProgramPrefix.select fuel tape)) privateData fuel = privateProgram code publicData tape privateData fuel :=
    PrivateCoinProgramPrefix.selected_program code publicData privateData fuel tape
  have equal : {execution | Event code publicData privateData position budget dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} =
      {execution : Tape × World | execution.2 ∈ sectionEvent (PrivateCoinProgramPrefix.select fuel execution.1)} := by
    ext execution
    simp only [sectionEvent,same,Event,Bad,OffsetPositionKernel.safe_iff,Set.mem_ofPred_eq]
  rw [equal]
  apply (CountableCoinOuterBound.bound coins _ (PrivateCoinProgramPrefix.select_measurable fuel) sectionEvent
    (fun _ => (budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) ?_).trans
  · simp only [lintegral_const,mul_comm,le_refl]
  · intro tape
    change law {world | OffsetPositionKernel.BoundedEvent _ position budget dummy world} ≤ _
    rw [same]
    exact OffsetPositionKernel.bound _ position budget dummy

theorem safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (position budget : ℕ) (dummy : Digest) :
    (coins.prod law) {execution | (∃ fuel, Event code publicData privateData position budget dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      coins Set.univ * ((budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  let events := fun fuel => {execution : Tape × World | Event code publicData privateData position budget dummy fuel execution ∧
    ¬∃ horizon, Bad code publicData privateData dummy horizon execution}
  have monotone : Monotone events := by
    intro first later ordered execution occurred
    exact ⟨OffsetPositionContinuation.private_monotone code publicData execution.1 privateData position budget dummy ordered occurred.1,occurred.2⟩
  have union : {execution | (∃ fuel, Event code publicData privateData position budget dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} = ⋃ fuel, events fuel := by
    ext execution
    simp only [events,Set.mem_ofPred_eq,Set.mem_iUnion,exists_and_right]
  rw [union,monotone.measure_iUnion]
  apply iSup_le
  intro fuel
  apply (measure_mono (show events fuel ⊆ {execution | Event code publicData privateData position budget dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} from ?_)).trans
    (prefix_safe_bound coins code publicData privateData position budget dummy fuel)
  intro execution occurred
  exact ⟨occurred.1,fun bad => occurred.2 ⟨fuel,bad⟩⟩

theorem bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (position budget : ℕ) (dummy : Digest) :
    (coins.prod law) {execution | ∃ fuel, Event code publicData privateData position budget dummy fuel execution} ≤
      (coins.prod law) {execution | ∃ fuel, Bad code publicData privateData dummy fuel execution} +
        coins Set.univ * ((budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  have included : {execution | ∃ fuel, Event code publicData privateData position budget dummy fuel execution} ⊆
      {execution | ∃ fuel, Bad code publicData privateData dummy fuel execution} ∪
      {execution | (∃ fuel, Event code publicData privateData position budget dummy fuel execution) ∧
        ¬∃ fuel, Bad code publicData privateData dummy fuel execution} := by
    intro execution occurred
    by_cases bad : ∃ fuel, Bad code publicData privateData dummy fuel execution
    · exact Or.inl bad
    · exact Or.inr ⟨occurred,bad⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (safe_bound coins code publicData privateData position budget dummy)))

def OriginalEvent (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (position : ℕ) (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  ∃ input ordinal cost, OffsetClassKernel.Event (privateProgram code publicData execution.1 privateData fuel)
    position input ordinal cost dummy execution.2

theorem original_iff (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (position : ℕ) (dummy : Digest) (fuel : ℕ) (execution : Tape × World) :
    OriginalEvent code publicData privateData position dummy fuel execution ↔
      Event code publicData privateData position OffsetDegreeBudget.budget dummy fuel execution :=
  OffsetDegreeBudget.event dummy

/-- Every attained input/job/degree class at this position is retained, over
all original tapes and horizons; the wire-domain budget is derived. -/
theorem original_safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (position : ℕ) (dummy : Digest) :
    (coins.prod law) {execution | (∃ fuel, OriginalEvent code publicData privateData position dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      coins Set.univ * ((OffsetDegreeBudget.budget : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  simpa only [original_iff] using safe_bound coins code publicData privateData position OffsetDegreeBudget.budget dummy

end
end FormalProof4FHE.HasteBoots.PrivateCoinOffsetPositionProbability
