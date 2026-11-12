module
public import FormalProof4FHE.HasteBoots.OffsetContinuation
public import FormalProof4FHE.HasteBoots.PrivateCoinProgramPrefix
public import FormalProof4FHE.HasteBoots.CountableCoinOuterBound
@[expose] public section

/-! One attained reciprocal class retains its exact complexity bound across
all original private tapes and instruction horizons. The global reference bad
event is excluded once. No union over all classes or attacker-work bound is
asserted by this per-class theorem. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinOffsetClassProbability
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def Event (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (position : ℕ) (input : Input) (ordinal cost : ℕ) (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  OffsetClassKernel.Event (privateProgram code publicData execution.1 privateData fuel) position input ordinal cost dummy execution.2

def Bad (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2

theorem prefix_safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (position : ℕ) (input : Input) (ordinal cost : ℕ) (dummy : Digest) (fuel : ℕ) :
    (coins.prod law) {execution | Event code publicData privateData position input ordinal cost dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} ≤
      coins Set.univ * ((cost : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  let sectionEvent := fun values : Fin fuel → InputIndexedOracle.Byte => {world |
    let program := privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel values) privateData fuel
    OffsetClassKernel.SafeEvent program position input ordinal cost dummy world}
  have same (tape : Tape) : privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel
      (PrivateCoinProgramPrefix.select fuel tape)) privateData fuel = privateProgram code publicData tape privateData fuel :=
    PrivateCoinProgramPrefix.selected_program code publicData privateData fuel tape
  have equal : {execution | Event code publicData privateData position input ordinal cost dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} =
      {execution : Tape × World | execution.2 ∈ sectionEvent (PrivateCoinProgramPrefix.select fuel execution.1)} := by
    ext execution
    simp only [sectionEvent,same,Event,Bad,OffsetClassKernel.SafeEvent,Set.mem_ofPred_eq]
  rw [equal]
  apply (CountableCoinOuterBound.bound coins _ (PrivateCoinProgramPrefix.select_measurable fuel) sectionEvent
    (fun _ => (cost : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) ?_).trans
  · simp only [lintegral_const,mul_comm,le_refl]
  · intro tape
    change law {world | OffsetClassKernel.SafeEvent _ position input ordinal cost dummy world} ≤ _
    rw [same]
    exact OffsetClassKernel.bound _ position input ordinal cost dummy

theorem safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (position : ℕ) (input : Input) (ordinal cost : ℕ) (dummy : Digest) :
    (coins.prod law) {execution | (∃ fuel, Event code publicData privateData position input ordinal cost dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      coins Set.univ * ((cost : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  let events := fun fuel => {execution : Tape × World | Event code publicData privateData position input ordinal cost dummy fuel execution ∧
    ¬∃ horizon, Bad code publicData privateData dummy horizon execution}
  have monotone : Monotone events := by
    intro first later ordered execution occurred
    exact ⟨OffsetContinuation.private_class_monotone code publicData execution.1 privateData position input ordinal cost dummy ordered occurred.1,occurred.2⟩
  have union : {execution | (∃ fuel, Event code publicData privateData position input ordinal cost dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} = ⋃ fuel, events fuel := by
    ext execution
    simp only [events,Set.mem_ofPred_eq,Set.mem_iUnion,exists_and_right]
  rw [union,monotone.measure_iUnion]
  apply iSup_le
  intro fuel
  apply (measure_mono (show events fuel ⊆ {execution | Event code publicData privateData position input ordinal cost dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} from ?_)).trans
    (prefix_safe_bound coins code publicData privateData position input ordinal cost dummy fuel)
  intro execution occurred
  exact ⟨occurred.1,fun bad => occurred.2 ⟨fuel,bad⟩⟩

theorem bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (position : ℕ) (input : Input) (ordinal cost : ℕ) (dummy : Digest) :
    (coins.prod law) {execution | ∃ fuel, Event code publicData privateData position input ordinal cost dummy fuel execution} ≤
      (coins.prod law) {execution | ∃ fuel, Bad code publicData privateData dummy fuel execution} +
        coins Set.univ * ((cost : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  have included : {execution | ∃ fuel, Event code publicData privateData position input ordinal cost dummy fuel execution} ⊆
      {execution | ∃ fuel, Bad code publicData privateData dummy fuel execution} ∪
      {execution | (∃ fuel, Event code publicData privateData position input ordinal cost dummy fuel execution) ∧
        ¬∃ fuel, Bad code publicData privateData dummy fuel execution} := by
    intro execution occurred
    by_cases bad : ∃ fuel, Bad code publicData privateData dummy fuel execution
    · exact Or.inl bad
    · exact Or.inr ⟨occurred,bad⟩
  exact (measure_mono included).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (safe_bound coins code publicData privateData position input ordinal cost dummy)))

end
end FormalProof4FHE.HasteBoots.PrivateCoinOffsetClassProbability
