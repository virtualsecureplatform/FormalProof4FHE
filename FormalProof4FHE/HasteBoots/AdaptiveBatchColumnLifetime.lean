module
public import FormalProof4FHE.HasteBoots.AdaptiveBatchColumnKernel
@[expose] public section

/-! Adaptive attained column families compose on the original joint runtime
execution with no index-count multiplier. The shared global bad union is
kept outside the whole lifetime; source witness coverage remains separate. -/
namespace FormalProof4FHE.HasteBoots.AdaptiveBatchColumnLifetime
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def Occurs (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (profile dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  ∃ position, AdaptiveBatchColumnKernel.Occurs (privateProgram code publicData execution.1 privateData fuel) position profile dummy execution.2

def Bad (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2

theorem prefix_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (profile dummy : Digest) (fuel : ℕ) :
    (coins.prod law) {execution | Occurs code publicData privateData profile dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * AdaptiveBatchColumnKernel.rate := by
  let event := fun values : Fin fuel → InputIndexedOracle.Byte => {world | ∃ position,
    AdaptiveBatchColumnKernel.Event (privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel values) privateData fuel) position profile dummy world}
  have same (tape : Tape) : privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel
      (PrivateCoinProgramPrefix.select fuel tape)) privateData fuel = privateProgram code publicData tape privateData fuel :=
    PrivateCoinProgramPrefix.selected_program code publicData privateData fuel tape
  have equal : {execution | Occurs code publicData privateData profile dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} =
      {execution : Tape × World | execution.2 ∈ event (PrivateCoinProgramPrefix.select fuel execution.1)} := by
    ext execution
    simp only [event,same,Occurs,Bad,AdaptiveBatchColumnKernel.Event,Set.mem_ofPred_eq,exists_and_right]
  rw [equal]
  apply (CountableCoinOuterBound.bound coins _ (PrivateCoinProgramPrefix.select_measurable fuel) event
    (fun tape => ∫⁻ world, PrivateCoinByteWork.lifetimeWork code publicData privateData (tape,world)*AdaptiveBatchColumnKernel.rate ∂law) ?_).trans
  · calc
      _ = ∫⁻ execution, PrivateCoinByteWork.lifetimeWork code publicData privateData execution*AdaptiveBatchColumnKernel.rate ∂coins.prod law :=
        (lintegral_prod _ ((PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData).mul_const AdaptiveBatchColumnKernel.rate).aemeasurable).symm
      _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * AdaptiveBatchColumnKernel.rate :=
        lintegral_mul_const AdaptiveBatchColumnKernel.rate (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData)
      _ ≤ _ := le_rfl
  · intro tape
    change law {world | ∃ position, AdaptiveBatchColumnKernel.Event _ position profile dummy world} ≤ _
    rw [same]
    change _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * AdaptiveBatchColumnKernel.rate ∂law
    rw [lintegral_mul_const AdaptiveBatchColumnKernel.rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)]
    exact AdaptiveBatchColumnKernel.private_prefix_bound code publicData tape privateData fuel profile dummy

theorem monotone (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (profile dummy : Digest) :
    Monotone (fun fuel => {execution | Occurs code publicData privateData profile dummy fuel execution}) := by
  intro first later ordered execution occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  obtain ⟨position,field⟩ := occurred
  refine ⟨position,?_⟩
  unfold privateProgram at field ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact AdaptiveBatchColumnKernel.occurs_extend _ _ position profile dummy execution.2 field

theorem safe_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (profile dummy : Digest) :
    (coins.prod law) {execution | (∃ fuel, Occurs code publicData privateData profile dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * AdaptiveBatchColumnKernel.rate := by
  let events := fun fuel => {execution : Tape × World | Occurs code publicData privateData profile dummy fuel execution ∧
    ¬∃ horizon, Bad code publicData privateData dummy horizon execution}
  have growing : Monotone events := by
    intro first later ordered execution occurred
    exact ⟨monotone code publicData privateData profile dummy ordered occurred.1,occurred.2⟩
  have union : {execution | (∃ fuel, Occurs code publicData privateData profile dummy fuel execution) ∧
      ¬∃ fuel, Bad code publicData privateData dummy fuel execution} = ⋃ fuel, events fuel := by
    ext execution
    simp only [events,Set.mem_ofPred_eq,Set.mem_iUnion,exists_and_right]
  rw [union,growing.measure_iUnion]
  apply iSup_le
  intro fuel
  apply (measure_mono (show events fuel ⊆ {execution | Occurs code publicData privateData profile dummy fuel execution ∧
      ¬Bad code publicData privateData dummy fuel execution} from ?_)).trans (prefix_bound coins code publicData privateData profile dummy fuel)
  intro execution occurred
  exact ⟨occurred.1,fun bad => occurred.2 ⟨fuel,bad⟩⟩

end
end FormalProof4FHE.HasteBoots.AdaptiveBatchColumnLifetime
