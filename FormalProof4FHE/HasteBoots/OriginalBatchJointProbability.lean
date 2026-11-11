module
public import FormalProof4FHE.HasteBoots.OriginalBatchInstructionCoverage
@[expose] public section

/-! Joint work bounds for one original source parameter/profile family.
Accepted native witnesses are realized on original instruction logs, whose
finite certificates establish joint measurability without a tape support cap. -/
namespace FormalProof4FHE.HasteBoots.OriginalBatchJointProbability
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction initialise take)
open InterpreterScalarLifetime (privateProgram)
open PrivateCoinByteLineage (history)
open PrivateCoinByteRequest (command)
open NativeGoldBatchPcsProgram (Context)
open NativeRootMessage (Digest)
noncomputable section

def rate : ENNReal := (17 : ENNReal)/2^141+1/(2 : ENNReal)^255

def ActualFailure (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (ctx : Context) (radius : ℕ) (execution : Tape × World) : Prop :=
  ∃ index, Nonempty (NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius execution.2
    (history code publicData privateData execution.1 index execution.2).run.2)

theorem actual_measurable (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (ctx : Context) (radius : ℕ) :
    MeasurableSet {execution | ActualFailure Memory code publicData privateData dummy ctx radius execution} := by
  have equal : {execution | ActualFailure Memory code publicData privateData dummy ctx radius execution} =
      ⋃ index : ℕ, {execution : Tape × World | NativeGoldBatchLifetimeMeasurable.HistoryFailure Memory dummy ctx radius
        (history code publicData privateData execution.1 index execution.2).run.2} := by
    ext execution
    simp only [ActualFailure,Set.mem_ofPred_eq,Set.mem_iUnion]
    exact exists_congr (fun index => NativeGoldBatchLifetimeMeasurable.witness_iff_history Memory dummy ctx radius _ _
      ((PrivateCoinByteLineage.history_replay code publicData privateData execution.1 index).truthful execution.2))
  rw [equal]
  apply MeasurableSet.iUnion
  intro index
  have measurable := PrivateCoinScores.event_measurable (fun tape => OracleProgram.run_replay (take code publicData tape index (initialise code privateData)))
    (PrivateCoinByteMachine.take_finiteResult code publicData index (initialise code privateData))
    (fun result => NativeGoldBatchLifetimeMeasurable.HistoryFailure Memory dummy ctx radius result.2)
  simpa only [PrivateCoinByteLineage.history_run,PrivateCoinByteLineage.packet] using measurable

theorem root_measurable (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) :
    MeasurableSet {execution | ∃ index, PrivateCoinSharedHash.Root code publicData privateData dummy index execution} := by
  have equal : {execution | ∃ index, PrivateCoinSharedHash.Root code publicData privateData dummy index execution} =
      ⋃ index : ℕ, {execution | PrivateCoinSharedHash.Root code publicData privateData dummy index execution} := by ext execution; simp
  rw [equal]
  exact MeasurableSet.iUnion (fun index => PrivateCoinScores.event_measurable
    (fun tape => OracleProgram.run_replay (take code publicData tape index (initialise code privateData)))
    (PrivateCoinByteMachine.take_finiteResult code publicData index (initialise code privateData))
    (fun result => NativeRootFamilyLifetime.Bad dummy result.2))

theorem section_bound (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (dummy : Digest) (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (role : NativeBrakedownCalibration.Role) (compatible : NativeGoldBatchCalibration.Matches ctx role) (width : 3 ≤ ctx.parameters.width.val) :
    law {world | ActualFailure Memory code publicData privateData dummy ctx (NativeBrakedownCalibration.radius .goldilocks role) (tape,world) ∧
      ¬∃ index, PrivateCoinSharedHash.Root code publicData privateData dummy index (tape,world)} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * rate := by
  have included : {world | ActualFailure Memory code publicData privateData dummy ctx (NativeBrakedownCalibration.radius .goldilocks role) (tape,world) ∧
      ¬∃ index, PrivateCoinSharedHash.Root code publicData privateData dummy index (tape,world)} ⊆
      {world | ∃ index, PrivateCoinByteGoldRisk.event code publicData tape dummy ctx (origin.primitiveAt ctx rfl) role ctx.parent.profile
        (PrivateCoinByteFixed.history code publicData tape privateData index world).run world ∨
        NativeEarlyReceiptBound.event ctx.parent.profile (command code publicData tape)
          (PrivateCoinByteFixed.history code publicData tape privateData index world).run world} := by
    rintro world ⟨⟨index,⟨witness⟩⟩,safe⟩
    rcases OriginalBatchInstructionCoverage.witness_covered Memory code publicData privateData tape index world dummy ctx origin _ width safe witness with
      ⟨earlier,early⟩ | ⟨earlier,field⟩ | ⟨earlier,column⟩
    · exact ⟨earlier,Or.inr early⟩
    · exact ⟨earlier,Or.inl (Or.inl field)⟩
    · exact ⟨earlier,Or.inl (Or.inr column)⟩
  have bounded := (measure_mono included).trans (PrivateCoinByteReceiptWork.gold_exposure_lifetime_le_work code publicData tape dummy ctx
    origin.tables origin.request.message origin.request.block origin.request.blowup (origin.constructedAt ctx rfl)
    (origin.primitiveAt ctx rfl) role compatible ctx.parent.profile privateData)
  simpa only [rate,mul_comm] using bounded

theorem joint_bound (Memory : Type) (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (role : NativeBrakedownCalibration.Role) (compatible : NativeGoldBatchCalibration.Matches ctx role) (width : 3 ≤ ctx.parameters.width.val) :
    (coins.prod law) {execution | ActualFailure Memory code publicData privateData dummy ctx (NativeBrakedownCalibration.radius .goldilocks role) execution ∧
      ¬∃ index, PrivateCoinSharedHash.Root code publicData privateData dummy index execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  have measurable := (actual_measurable Memory code publicData privateData dummy ctx (NativeBrakedownCalibration.radius .goldilocks role)).inter
    (root_measurable code publicData privateData dummy).compl
  apply (PrivateCoinLifetime.independent_work_bound coins _ measurable
    (fun execution => PrivateCoinByteWork.lifetimeWork code publicData privateData execution * rate)
    ((PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData).mul_const rate).aemeasurable ?_).trans
  · exact le_of_eq (lintegral_mul_const rate (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData))
  · intro tape
    change _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * rate ∂law
    rw [lintegral_mul_const rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)]
    exact section_bound Memory code publicData privateData tape dummy ctx origin role compatible width

theorem original_bound (Memory : Type) (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (role : NativeBrakedownCalibration.Role) (compatible : NativeGoldBatchCalibration.Matches ctx role) (width : 3 ≤ ctx.parameters.width.val) :
    (coins.prod law) {execution : Tape × World | (∃ fuel, CacheBackedBatchLifetimeSoundness.Failure Memory dummy ctx origin (NativeBrakedownCalibration.radius .goldilocks role)
      (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData execution.1 privateData fuel)) id OracleProgramMachine.step execution.2) ∧
      ¬∃ index, PrivateCoinSharedHash.Root code publicData privateData dummy index execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  apply (measure_mono (show {execution : Tape × World | (∃ fuel, CacheBackedBatchLifetimeSoundness.Failure Memory dummy ctx origin (NativeBrakedownCalibration.radius .goldilocks role)
      (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData execution.1 privateData fuel)) id OracleProgramMachine.step execution.2) ∧
      ¬∃ index, PrivateCoinSharedHash.Root code publicData privateData dummy index execution} ⊆
      {execution | ActualFailure Memory code publicData privateData dummy ctx (NativeBrakedownCalibration.radius .goldilocks role) execution ∧
        ¬∃ index, PrivateCoinSharedHash.Root code publicData privateData dummy index execution} from ?_)).trans
    (joint_bound Memory coins code publicData privateData dummy ctx origin role compatible width)
  rintro execution ⟨⟨fuel,failed⟩,safe⟩
  obtain ⟨index,_,witness⟩ := PrivateCoinOpeningWitness.cached_source Memory code publicData privateData execution.1 fuel execution.2 dummy ctx origin _ failed
  exact ⟨⟨index,witness⟩,safe⟩

end
end FormalProof4FHE.HasteBoots.OriginalBatchJointProbability
