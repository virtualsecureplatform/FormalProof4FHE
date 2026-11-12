module
public import FormalProof4FHE.HasteBoots.CallerPairedPreparation
public import FormalProof4FHE.HasteBoots.SequencedInputIdentityWork
@[expose] public section

/-! Both original scalar equations inherit the 128-bit work bound from one
sequenced caller/proof-input realization. Framing, statement bounds and
seed-order safety are derived or charged, not new witness certificates. -/
namespace FormalProof4FHE.HasteBoots.SequencedInputPairedWork
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open OracleProgram (Program)
open AllocatedFamilyFunctions (Allocation)
open InterpreterScalarLifetime (privateProgram)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

structure Witness {Memory A : Type} (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
    (program : Program A) (dummy : Digest) (world : World) where
  data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world
  inputs : SequencedCallerInputs.Inputs data
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  initial : (ScalarChainHealing.value (2*data.index.val) data.origin.ready.statement.claims.val ≠
    some (CallerPairedPreparation.sumTruth data dummy)) ∨
    (ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
      some (CallerFramedAllocatedJob.truth data dummy))

def toSeedOrder {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4) :
    SeedOrderPairedWork.Witness (Memory := Memory) ctx allocation program dummy world :=
  let decoded := EqualityFramingRecovery.ready_decoded witness.data
  ⟨CallerPairedPreparation.toCanonical witness.data witness.inputs helperWidth sourceWidths ⟨witness.before,witness.bytes,witness.valid⟩,
    (CallerFramedAllocatedJob.domain witness.data).rootsFit,decoded.choose,decoded.choose_spec,
    CheckedScalarStatementSize.retained_fits witness.data,CallerPairedPreparation.round_domain witness.data,
    CallerPairedPreparation.framing witness.data witness.inputs helperWidth sourceWidths witness.before witness.bytes witness.valid,
    witness.before,witness.bytes,witness.valid,witness.inputs.parent_domain,witness.initial⟩

def ofIdentity {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : SequencedInputIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,witness.inputs,witness.before,witness.bytes,witness.valid,Or.inr witness.initial⟩

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem identity_included (execution : Tape × World)
    (failed : SequencedInputIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution) :
    Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  exact ⟨fuel,⟨ofIdentity witness⟩⟩

theorem covered (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (execution : Tape × World) (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    SeedOrderPairedWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  exact ⟨fuel,⟨toSeedOrder witness helperWidth sourceWidths⟩⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have helperWidth : ctx.helper.width.val ≤ 4 := by
    rw [parameters,helperAdmitted.width]
    cases helperRole <;> decide +kernel
  have sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4 := by
    intro slot
    have compatible := (sourceAdmitted slot).width
    change (ctx.registry.val.get slot).parameters.width.val = NativeBrakedownCalibration.testWidth .goldilocks (sourceRole slot) at compatible
    rw [compatible]
    cases sourceRole slot <;> decide +kernel
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | SeedOrderPairedWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy helperWidth sourceWidths execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (SeedOrderPairedWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted coins)

end
end FormalProof4FHE.HasteBoots.SequencedInputPairedWork
