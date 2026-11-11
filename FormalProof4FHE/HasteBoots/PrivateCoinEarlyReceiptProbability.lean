module
public import FormalProof4FHE.HasteBoots.ProgramEarlyReceiptContinuation
@[expose] public section

/-! One joint early-receipt charge covers every raw observation position,
every instruction horizon and all native collector budgets. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinEarlyReceiptProbability
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
open MeasureTheory
noncomputable section

def rate (threshold : ℕ) : ENNReal := 1/(threshold : ENNReal)+PrivateCoinByteReceiptWork.rate threshold

def Occurs (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (profile : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  ProgramEarlyReceiptWork.Occurs (privateProgram code publicData execution.1 privateData fuel) profile execution.2

theorem prefix_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (profile : Digest) (fuel threshold : ℕ) (positive : 0 < threshold) :
    (coins.prod law) {execution | Occurs code publicData privateData profile fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate threshold := by
  let event := fun values : Fin fuel → InputIndexedOracle.Byte => {world | ProgramEarlyReceiptWork.Occurs
    (privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel values) privateData fuel) profile world}
  have same (tape : Tape) : privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel
      (PrivateCoinProgramPrefix.select fuel tape)) privateData fuel = privateProgram code publicData tape privateData fuel :=
    PrivateCoinProgramPrefix.selected_program code publicData privateData fuel tape
  have equal : {execution | Occurs code publicData privateData profile fuel execution} =
      {execution : Tape × World | execution.2 ∈ event (PrivateCoinProgramPrefix.select fuel execution.1)} := by
    ext execution
    simp only [Occurs,event,same,Set.mem_ofPred_eq]
  rw [equal]
  apply (CountableCoinOuterBound.bound coins _ (PrivateCoinProgramPrefix.select_measurable fuel) event
    (fun tape => ∫⁻ world, PrivateCoinByteWork.lifetimeWork code publicData privateData (tape,world)*rate threshold ∂law) ?_).trans
  · calc
      _ = ∫⁻ execution, PrivateCoinByteWork.lifetimeWork code publicData privateData execution*rate threshold ∂coins.prod law :=
        (lintegral_prod _ ((PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData).mul_const (rate threshold)).aemeasurable).symm
      _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * rate threshold :=
        lintegral_mul_const (rate threshold) (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData)
      _ ≤ _ := le_rfl
  · intro tape
    change law {world | ProgramEarlyReceiptWork.Occurs _ profile world} ≤ _
    rw [same]
    change _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * rate threshold ∂law
    rw [lintegral_mul_const (rate threshold) (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)]
    exact ProgramEarlyReceiptWork.private_bound code publicData tape privateData fuel threshold profile positive

theorem monotone (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (profile : Digest) :
    Monotone (fun fuel => {execution | Occurs code publicData privateData profile fuel execution}) := by
  intro first later ordered execution occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change ProgramEarlyReceiptWork.Occurs (privateProgram code publicData execution.1 privateData (first+extra)) profile execution.2
  unfold privateProgram
  rw [PrivateCoinByteMachine.take_resume]
  exact ProgramEarlyReceiptContinuation.occurs_extend _ _ profile execution.2 occurred

theorem lifetime_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (profile : Digest) (threshold : ℕ) (positive : 0 < threshold) :
    (coins.prod law) {execution | ∃ fuel, Occurs code publicData privateData profile fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate threshold := by
  have union : {execution | ∃ fuel, Occurs code publicData privateData profile fuel execution} =
      ⋃ fuel, {execution | Occurs code publicData privateData profile fuel execution} := by
    ext execution
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union,(monotone code publicData privateData profile).measure_iUnion]
  exact iSup_le (fun fuel => prefix_bound coins code publicData privateData profile fuel threshold positive)

theorem lifetime_le_255 (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (profile : Digest) :
    (coins.prod law) {execution | ∃ fuel, Occurs code publicData privateData profile fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^255) :=
  (lifetime_bound coins code publicData privateData profile (2^256) (by positivity)).trans
    (mul_le_mul' le_rfl PrivateCoinByteReceiptWork.rate_256)

end
end FormalProof4FHE.HasteBoots.PrivateCoinEarlyReceiptProbability
