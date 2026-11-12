module
public import FormalProof4FHE.HasteBoots.SequencedCallerInputs
@[expose] public section

/-! All proof and caller-message reads are observed in one successful heap
operation sequence from empty memory. Whole Rust execution, application
acceptance and physical-work refinements remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.SequencedInputIdentityWork
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
  initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
    some (CallerFramedAllocatedJob.truth data dummy)

def toResident {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    ResidentCallerIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,witness.inputs.buffers,witness.before,witness.bytes,witness.valid,witness.initial⟩

def ofResident {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : ResidentCallerIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world)
    (inputs : SequencedCallerInputs.Inputs witness.data) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,inputs,witness.before,witness.bytes,witness.valid,witness.initial⟩

def toHeap {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    HeapProofIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world :=
  HeapProofIdentityWork.ofResident (toResident witness) witness.inputs.proofSource

theorem truth_toHeap {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    ResidentDecodedAllocatedJob.truth (toHeap witness).data dummy = CallerFramedAllocatedJob.truth witness.data dummy := rfl

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem covered (execution : Tape × World)
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    HeapProofIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel, ⟨witness⟩⟩ := failed
  exact ⟨fuel, ⟨toHeap witness⟩⟩

theorem failure_iff (execution : Tape × World) :
    Failure Memory ctx allocation code publicData privateData dummy execution ↔
      ∃ fuel, ∃ witness : ResidentCallerIdentityWork.Witness (Memory := Memory) ctx allocation
        (privateProgram code publicData execution.1 privateData fuel) dummy execution.2,
          Nonempty (SequencedCallerInputs.Inputs witness.data) := by
  constructor
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,toResident witness,⟨witness.inputs⟩⟩
  · rintro ⟨fuel,witness,⟨inputs⟩⟩
    exact ⟨fuel,⟨ofResident witness inputs⟩⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | HeapProofIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (HeapProofIdentityWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted coins)

end
end FormalProof4FHE.HasteBoots.SequencedInputIdentityWork
