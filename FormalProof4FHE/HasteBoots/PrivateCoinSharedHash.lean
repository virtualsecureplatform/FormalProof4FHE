module
public import FormalProof4FHE.HasteBoots.PrivateCoinScalarProbability
public import FormalProof4FHE.HasteBoots.PrivateCoinByteRootWork
@[expose] public section

/-! One joint runtime hash ledger is priced by the existing specified-work
bound and shared with scalar reference failures and original PCS witnesses. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinSharedHash
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
noncomputable section

def rate : ENNReal := 1/(2 : ENNReal)^159

def Root (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (fuel : ℕ) (execution : Tape × World) : Prop :=
  NativeRootFamilyLifetime.Bad dummy (OracleProgram.run (privateProgram code publicData execution.1 privateData fuel) execution.2).run.2

theorem prefix_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (fuel : ℕ) :
    (coins.prod law) {execution | Root code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  let event := fun values : Fin fuel → InputIndexedOracle.Byte => {world |
    NativeRootFamilyLifetime.Bad dummy (OracleProgram.run (privateProgram code publicData
      (PrivateCoinProgramPrefix.restore fuel values) privateData fuel) world).run.2}
  have same (tape : Tape) : privateProgram code publicData (PrivateCoinProgramPrefix.restore fuel
      (PrivateCoinProgramPrefix.select fuel tape)) privateData fuel = privateProgram code publicData tape privateData fuel :=
    PrivateCoinProgramPrefix.selected_program code publicData privateData fuel tape
  have equal : {execution | Root code publicData privateData dummy fuel execution} =
      {execution : Tape × World | execution.2 ∈ event (PrivateCoinProgramPrefix.select fuel execution.1)} := by
    ext execution
    simp only [event,same,Root,Set.mem_ofPred_eq]
  rw [equal]
  apply (CountableCoinOuterBound.bound coins _ (PrivateCoinProgramPrefix.select_measurable fuel) event
    (fun tape => ∫⁻ world, PrivateCoinByteWork.lifetimeWork code publicData privateData (tape,world)*rate ∂law) ?_).trans
  · calc
      _ = ∫⁻ execution, PrivateCoinByteWork.lifetimeWork code publicData privateData execution*rate ∂coins.prod law :=
        (lintegral_prod _ ((PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData).mul_const rate).aemeasurable).symm
      _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * rate :=
        lintegral_mul_const rate (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData)
      _ ≤ _ := le_rfl
  · intro tape
    change law {world | NativeRootFamilyLifetime.Bad dummy (OracleProgram.run _ world).run.2} ≤ _
    rw [same]
    have covered : {world | NativeRootFamilyLifetime.Bad dummy (OracleProgram.run (privateProgram code publicData tape privateData fuel) world).run.2} ⊆
        {world | ∃ horizon, NativeRootFamilyLifetime.Bad dummy (PrivateCoinByteFixed.history code publicData tape privateData horizon world).run.2} := by
      intro world bad
      refine ⟨fuel,?_⟩
      rw [PrivateCoinByteFixed.history_run]
      exact bad
    have bounded := (measure_mono covered).trans (PrivateCoinByteRootWork.lifetime_le_159 code publicData tape dummy privateData)
    change _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * rate ∂law
    rw [lintegral_mul_const rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)]
    simpa only [rate,mul_comm,PrivateCoinByteFixed.expectedWork] using bounded

theorem root_monotone (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) : Monotone (fun fuel => {execution | Root code publicData privateData dummy fuel execution}) := by
  intro first later ordered execution bad
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  have included : (OracleProgram.run (privateProgram code publicData execution.1 privateData first) execution.2).run.2.IsPrefix
      (OracleProgram.run (privateProgram code publicData execution.1 privateData (first+extra)) execution.2).run.2 := by
    unfold privateProgram
    rw [PrivateCoinByteMachine.take_resume,OracleProgram.run_bind,ObservationReplay.run_bind]
    exact ⟨_,rfl⟩
  exact NativeRootFamilyAudit.bad_persistent dummy execution.2 _ _
    ((OracleProgram.run_replay (privateProgram code publicData execution.1 privateData (first+extra))).truthful execution.2) included bad

theorem lifetime_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    (coins.prod law) {execution | ∃ fuel, Root code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  have union : {execution | ∃ fuel, Root code publicData privateData dummy fuel execution} =
      ⋃ fuel, {execution | Root code publicData privateData dummy fuel execution} := by ext execution; simp
  rw [union,(root_monotone code publicData privateData dummy).measure_iUnion]
  exact iSup_le (prefix_bound coins code publicData privateData dummy)

theorem source_bad_iff {A : Type} (program : OracleProgram.Program A) (dummy : Digest) (world : World) :
    SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world ↔
      NativeRootFamilyLifetime.Bad dummy (OracleProgram.run program world).run.2 := by
  constructor
  · rintro ⟨fuel,bad⟩
    rw [ProgramOpeningLifetime.history_log] at bad
    have included := OracleProgramMachine.log_prefix_run fuel program world
    rw [OracleProgramMachine.take_run] at included
    exact NativeRootFamilyAudit.bad_persistent dummy world _ _ ((OracleProgram.run_replay program).truthful world) included bad
  · exact ProgramOpeningLifetime.root_bad program world dummy

def Other (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (execution : Tape × World) : Prop :=
  ∃ fuel, GlobalReferenceBad.OtherBad (privateProgram code publicData execution.1 privateData fuel) execution.2

theorem bad_split (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (execution : Tape × World) :
    (∃ fuel, PrivateCoinScalarProbability.Bad code publicData privateData dummy fuel execution) ↔
      (∃ fuel, Root code publicData privateData dummy fuel execution) ∨ Other code publicData privateData execution := by
  simp only [PrivateCoinScalarProbability.Bad,GlobalReferenceBad.Bad,Root,Other,exists_or]

theorem scalar_bound (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (radius : ℕ) :
    (coins.prod law) {execution | ∃ fuel, PrivateCoinScalarProbability.Event code publicData privateData dummy radius fuel execution} ≤
      (coins.prod law) {execution | Other code publicData privateData execution} +
        PrivateCoinByteWork.expectedWork coins code publicData privateData * (rate+ScalarEquationWork.rate) := by
  have bad_bound : (coins.prod law) {execution | ∃ fuel, PrivateCoinScalarProbability.Bad code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate + (coins.prod law) {execution | Other code publicData privateData execution} := by
    simp only [bad_split,Set.ofPred_or]
    exact (measure_union_le _ _).trans (add_le_add (lifetime_bound coins code publicData privateData dummy) le_rfl)
  apply (PrivateCoinScalarProbability.bound coins code publicData privateData dummy radius).trans
  calc
    _ ≤ (PrivateCoinByteWork.expectedWork coins code publicData privateData * rate +
        (coins.prod law) {execution | Other code publicData privateData execution}) +
        PrivateCoinByteWork.expectedWork coins code publicData privateData * ScalarEquationWork.rate := add_le_add bad_bound le_rfl
    _ = _ := by rw [mul_add]; ac_rfl

theorem combined_rate_le : rate+ScalarEquationWork.rate ≤ 1/(2 : ENNReal)^158 := by
  have bound : (1 : NNReal)/2^159 + 4/((NativeFields.goldilocksModulus^3 : ℕ) : NNReal) ≤ 1/2^158 := by
    rw [← NNReal.coe_le_coe]
    norm_num [NativeFields.goldilocksModulus]
  have nonzero : (2 : NNReal) ≠ 0 := by norm_num
  have modulus : ((NativeFields.goldilocksModulus^3 : ℕ) : NNReal) ≠ 0 := by norm_num [NativeFields.goldilocksModulus]
  have cast := ENNReal.coe_le_coe.mpr bound
  simpa only [rate,ScalarEquationWork.rate,ENNReal.coe_add,ENNReal.coe_div (pow_ne_zero 159 nonzero),
    ENNReal.coe_div (pow_ne_zero 158 nonzero),ENNReal.coe_div modulus,ENNReal.coe_pow,
    ENNReal.coe_one,ENNReal.coe_ofNat,ENNReal.coe_natCast] using cast

end
end FormalProof4FHE.HasteBoots.PrivateCoinSharedHash
