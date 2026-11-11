module
public import FormalProof4FHE.HasteBoots.SeedOrderContinuation
@[expose] public section

/-! One joint specified-work bound covers bad seed order across every raw
position and runtime private-coin horizon. The infinite tape is retained. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinSeedOrderProbability
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open MeasureTheory
noncomputable section

def rate (threshold : ℕ) : ENNReal := 1/(threshold : ENNReal)+SeedOrderRiskBudget.rate threshold

def Bad (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (fuel : ℕ) (execution : Tape × World) : Prop :=
  SeedQuoteOrder.Bad OracleProgramMachine.step (privateProgram code publicData execution.1 privateData fuel) execution.2

theorem prefix_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (fuel threshold : ℕ) (positive : 0 < threshold) :
    (coins.prod law) {execution | Bad code publicData privateData fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate threshold := by
  let event := fun values : Fin fuel → InputIndexedOracle.Byte => {world | SeedQuoteOrder.Bad OracleProgramMachine.step
    (privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel values) privateData fuel) world}
  have same (tape : Tape) : privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel
      (PrivateCoinProgramPrefix.select fuel tape)) privateData fuel = privateProgram code publicData tape privateData fuel :=
    PrivateCoinProgramPrefix.selected_program code publicData privateData fuel tape
  have equal : {execution | Bad code publicData privateData fuel execution} =
      {execution : Tape × World | execution.2 ∈ event (PrivateCoinProgramPrefix.select fuel execution.1)} := by
    ext execution
    simp only [Bad,event,same,Set.mem_ofPred_eq]
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
    change law {world | SeedQuoteOrder.Bad OracleProgramMachine.step _ world} ≤ _
    rw [same]
    change _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * rate threshold ∂law
    rw [lintegral_mul_const (rate threshold) (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)]
    exact SeedOrderRiskBudget.private_bound code publicData tape privateData fuel threshold positive

theorem monotone (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) :
    Monotone (fun fuel => {execution | Bad code publicData privateData fuel execution}) := by
  intro first later ordered execution occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change SeedQuoteOrder.Bad OracleProgramMachine.step (privateProgram code publicData execution.1 privateData (first+extra)) execution.2
  unfold privateProgram
  rw [PrivateCoinByteMachine.take_resume]
  exact SeedOrderContinuation.bad _ _ execution.2 occurred

theorem lifetime_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (threshold : ℕ) (positive : 0 < threshold) :
    (coins.prod law) {execution | ∃ fuel, Bad code publicData privateData fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate threshold := by
  have union : {execution | ∃ fuel, Bad code publicData privateData fuel execution} =
      ⋃ fuel, {execution | Bad code publicData privateData fuel execution} := by
    ext execution
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union,(monotone code publicData privateData).measure_iUnion]
  exact iSup_le (fun fuel => prefix_bound coins code publicData privateData fuel threshold positive)

theorem rate_160 : rate (2^160) ≤ 1/(2 : ENNReal)^159 := by
  have raw : SeedOrderRiskBudget.rate (2^160) ≤ ReferenceRiskBudget.rate (2^160) := by
    unfold SeedOrderRiskBudget.rate ReferenceRiskBudget.rate
    apply ENNReal.div_le_div_right
    exact Nat.cast_le.mpr (by omega)
  exact (add_le_add le_rfl raw).trans PrivateCoinReferenceProbability.rate_160

theorem lifetime_le_159 (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) :
    (coins.prod law) {execution | ∃ fuel, Bad code publicData privateData fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^159) :=
  (lifetime_bound coins code publicData privateData (2^160) (by positivity)).trans (mul_le_mul' le_rfl rate_160)

end
end FormalProof4FHE.HasteBoots.PrivateCoinSeedOrderProbability
