module
public import FormalProof4FHE.HasteBoots.PrivateCoinInitialisation
public import FormalProof4FHE.HasteBoots.ClosedByteMachineExecutableSoundness
@[expose] public section

/-! Executable common-source extraction soundness under private random
initialization, including the existing root/source and early receipt hazards.
Prices are specified interpreter work. PBS semantics and physical refinement
are not established here. A target certificate does not prove registry trust. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinExecutableSoundness
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (logSize Tables)
open NativeBrakedownCalibration (Role)
noncomputable section

structure Target where
  ctx : Context
  role : Role
  tables : Tables
  message : NativeUsizeMessage.Usize
  block : NativeUsizeMessage.Usize
  blowup : NativeUsizeMessage.Usize
  constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code
  primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
    (2^(logSize ctx.parameters.code+1))
  compatible : NativeGoldBatchCalibration.Matches ctx role

def Failure (Memory : Type) (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target)
    (execution : Tape × World) : Prop :=
  ClosedByteMachineExecutableSoundness.Failure Memory code publicData (privateData execution.1)
    dummy target.ctx target.role execution.2

theorem failure_measurable (Memory : Type) (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) (dummy : Digest) (target : Target) :
    MeasurableSet {execution | Failure Memory code publicData privateData dummy target execution} :=
  PrivateCoinInitialisation.event_measurable privateData finiteData _ (fun data =>
    ClosedByteMachineExecutableSoundness.failure_measurable Memory code publicData data dummy target.ctx target.role
      target.tables target.message target.block target.blowup target.constructed target.compatible)

/-- All source/hash, early receipt and field/column exceptions are covered on
this same execution. No separate hazard coverage premise is supplied. -/
theorem failure_covered (Memory : Type) (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target)
    (execution : Tape × World) (failed : Failure Memory code publicData privateData dummy target execution) :
    ClosedByteMachineGoldAllRisk.Failure code publicData dummy target.ctx target.primitive target.role
      target.ctx.parent.profile (privateData execution.1) execution.2 :=
  ClosedByteMachineNativeSoundness.failure_covered Memory code publicData (privateData execution.1)
    dummy target.ctx target.role target.tables target.message target.block target.blowup target.constructed
    target.primitive target.compatible execution.2
    ((ClosedByteMachineExecutableSoundness.failure_iff_analysis Memory code publicData (privateData execution.1)
      dummy target.ctx target.role target.tables target.message target.block target.blowup target.constructed
      target.compatible execution.2).mp failed)

theorem lifetime_le_work (coins : Measure Tape) (Memory : Type) (code : List ClosedByteMachine.Instruction)
    (publicData : Input) (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) (dummy : Digest) (target : Target) :
    (coins.prod law) {execution | Failure Memory code publicData privateData dummy target execution} ≤
      ClosedByteMachineGoldAllRisk.rate * PrivateCoinClosedWork.expectedWork coins code publicData privateData := by
  simpa only [one_mul, Failure] using PrivateCoinInitialisation.scaled_bound coins code publicData privateData finiteData _
    (fun data => ClosedByteMachineExecutableSoundness.failure_measurable Memory code publicData data dummy target.ctx target.role
      target.tables target.message target.block target.blowup target.constructed target.compatible)
    1 (by simp) ClosedByteMachineGoldAllRisk.rate
    (fun data => by
      simpa only [one_mul] using
        (ClosedByteMachineExecutableSoundness.lifetime_le_work Memory code publicData data dummy target.ctx target.role
          target.tables target.message target.block target.blowup target.constructed target.primitive target.compatible))

theorem scaled_lifetime_le_work (coins : Measure Tape) (Memory : Type) (code : List ClosedByteMachine.Instruction)
    (publicData : Input) (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) (dummy : Digest) (target : Target) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | Failure Memory code publicData privateData dummy target execution} ≤
        (9/4096 : ENNReal) * PrivateCoinClosedWork.expectedWork coins code publicData privateData :=
  PrivateCoinInitialisation.scaled_bound coins code publicData privateData finiteData _
    (fun data => ClosedByteMachineExecutableSoundness.failure_measurable Memory code publicData data dummy target.ctx target.role
      target.tables target.message target.block target.blowup target.constructed target.compatible)
    ((2 : ENNReal)^128) (by simp) (9/4096)
    (fun data => ClosedByteMachineExecutableSoundness.scaled_lifetime_le_work Memory code publicData data dummy
      target.ctx target.role target.tables target.message target.block target.blowup target.constructed
      target.primitive target.compatible)
end
end FormalProof4FHE.HasteBoots.PrivateCoinExecutableSoundness
