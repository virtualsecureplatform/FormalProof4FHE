module
public import FormalProof4FHE.HasteBoots.ReferenceMaskedEvents
public import FormalProof4FHE.HasteBoots.InterpreterScalarLifetime
@[expose] public section

/-! Original non-root reference failures on low-work executions are covered
by masked prefix events. Completed posterior queries create no work charge. -/
namespace FormalProof4FHE.HasteBoots.ReferenceLowProbability
open InputIndexedOracle (Input World law)
open OracleProgram (Program run runPrefix)
open MeasureTheory
noncomputable section

def Low {A : Type} (program : Program A) (threshold : ℕ) (world : World) : Prop :=
  ∃ position, ReferenceMaskedEvents.small threshold (runPrefix position program world).run ∧
    ReferenceMaskedEvents.event OracleProgramMachine.step (runPrefix position program world).run world

theorem bound {A : Type} (program : Program A) (threshold : ℕ) :
    law {world | Low program threshold world} ≤ ∫⁻ world, ReferenceRiskBudget.totalLowCharge program threshold world ∂law := by
  have union : {world | Low program threshold world} = ⋃ position : ℕ,
      {world | ReferenceMaskedEvents.small threshold (runPrefix position program world).run ∧
        ReferenceMaskedEvents.event OracleProgramMachine.step (runPrefix position program world).run world} := by
    ext world
    simp only [Low,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  calc
    _ ≤ ∑' position : ℕ, law {world | ReferenceMaskedEvents.small threshold (runPrefix position program world).run ∧
        ReferenceMaskedEvents.event OracleProgramMachine.step (runPrefix position program world).run world} := measure_iUnion_le _
    _ ≤ ∑' position : ℕ, ∫⁻ world, ReferenceRiskBudget.lowRisk OracleProgramMachine.step threshold (runPrefix position program world).run ∂law :=
      ENNReal.tsum_le_tsum (fun position => ReferenceMaskedEvents.bound OracleProgramMachine.step (OracleProgram.prefix_replay position program) threshold)
    _ = _ := (lintegral_tsum (fun position => (OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program)
      (ReferenceRiskBudget.lowRisk OracleProgramMachine.step threshold)).aemeasurable)).symm

theorem other_iff {A : Type} (program : Program A) (world : World) :
    GlobalReferenceBad.OtherBad program world ↔ ∃ position, ReferenceMaskedEvents.event OracleProgramMachine.step
      (runPrefix position program world).run world := by
  simp only [GlobalReferenceBad.OtherBad,ProgramParentSeedCollision.Bad,ProgramContextTarget.Bad,
    ProgramReceiptCoverage.Bad,ProgramReceiptCollision.Bad,ReferenceMaskedEvents.event,exists_or]

theorem inputWork_mono {left right : List NativeTranscript.Observation} (included : left.IsPrefix right) :
    ClosedByteMachineRootBudget.inputWork left ≤ ClosedByteMachineRootBudget.inputWork right := by
  obtain ⟨tail,rfl⟩ := included
  rw [ClosedByteMachineRootBudget.inputWork_append]
  omega

theorem private_covered (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (fuel threshold : ℕ) (world : World)
    (bad : GlobalReferenceBad.OtherBad (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) world)
    (small : PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world < (threshold : ENNReal)) :
    Low (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) threshold world := by
  let program := InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel
  obtain ⟨position,occurred⟩ := (other_iff program world).mp bad
  have growing := OracleProgramMachine.log_prefix_run position program world
  rw [OracleProgramMachine.take_run] at growing
  have bytes := (inputWork_mono growing).trans (PrivateCoinByteRootBudget.take_inputWork_le code publicData tape fuel _ world)
  have entries := growing.length_le.trans (PrivateCoinByteLogWork.log_le_work code publicData tape fuel _ world)
  have work : ((run program world).run.1.work : ENNReal) < (threshold : ENNReal) :=
    lt_of_le_of_lt (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel) small
  have below : (run program world).run.1.work < threshold := Nat.cast_lt.mp work
  exact ⟨position,⟨lt_of_le_of_lt entries below,lt_of_le_of_lt bytes below⟩,occurred⟩

theorem private_bound (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (fuel threshold : ℕ) (positive : 0 < threshold) :
    law {world | GlobalReferenceBad.OtherBad (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * (1/(threshold : ENNReal)+ReferenceRiskBudget.rate threshold) := by
  let program := InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel
  have included : {world | GlobalReferenceBad.OtherBad program world} ⊆
      {world | (threshold : ENNReal) ≤ PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world} ∪
      {world | Low program threshold world} := by
    intro world bad
    by_cases high : (threshold : ENNReal) ≤ PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world
    · exact Or.inl high
    · exact Or.inr (private_covered code publicData tape privateData fuel threshold world bad (lt_of_not_ge high))
  have high := meas_ge_le_lintegral_div (μ := law)
    (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData).aemeasurable
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive) : (threshold : ENNReal) ≠ 0) (ENNReal.natCast_ne_top threshold)
  have low : law {world | Low program threshold world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * ReferenceRiskBudget.rate threshold := by
    apply (bound program threshold).trans
    calc
      _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * ReferenceRiskBudget.rate threshold ∂law := by
        apply lintegral_mono
        intro world
        exact (ReferenceRiskBudget.private_charge _ _ _ _ _ _ _).trans
          (mul_le_mul' (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel) le_rfl)
      _ = _ := lintegral_mul_const (ReferenceRiskBudget.rate threshold) (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)
  apply (measure_mono included).trans
  calc
    _ ≤ PrivateCoinByteFixed.expectedWork code publicData tape privateData/(threshold : ENNReal) +
        PrivateCoinByteFixed.expectedWork code publicData tape privateData * ReferenceRiskBudget.rate threshold :=
      (measure_union_le _ _).trans (add_le_add high low)
    _ = _ := by rw [mul_add,one_div,div_eq_mul_inv]

end
end FormalProof4FHE.HasteBoots.ReferenceLowProbability
