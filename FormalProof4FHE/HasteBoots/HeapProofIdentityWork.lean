module
public import FormalProof4FHE.HasteBoots.ResidentDecodedAllocatedJob
@[expose] public section

/-! The proof object used by the original native caller comes from the exact
bytes of a checked heap-read/decode operation. Whole Rust decoding, heap
execution and physical-work correspondence remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.HeapProofIdentityWork
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
  data : ResidentDecodedAllocatedJob.Job (Memory := Memory) ctx allocation program world
  buffers : CallerSerializationOrigin.Buffers (ResidentDecodedAllocatedJob.toCaller data)
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
    some (ResidentDecodedAllocatedJob.truth data dummy)

def toResident {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    ResidentCallerIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨ResidentDecodedAllocatedJob.toCaller witness.data,witness.buffers,witness.before,witness.bytes,witness.valid,witness.initial⟩

def ofResident {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : ResidentCallerIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world)
    (buffer : ResidentMessageBounds.Buffer witness.data.proofBytes.val) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨ResidentDecodedAllocatedJob.ofCaller witness.data buffer,
    by rw [ResidentDecodedAllocatedJob.toCaller_ofCaller]; exact witness.buffers,
    witness.before,witness.bytes,witness.valid,witness.initial⟩

theorem truth_toResident {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    CallerFramedAllocatedJob.truth (toResident witness).data dummy = ResidentDecodedAllocatedJob.truth witness.data dummy := rfl

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem covered (execution : Tape × World)
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    ResidentCallerIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel, ⟨witness⟩⟩ := failed
  exact ⟨fuel, ⟨toResident witness⟩⟩

theorem failure_iff (execution : Tape × World) :
    Failure Memory ctx allocation code publicData privateData dummy execution ↔
      ∃ fuel, ∃ witness : ResidentCallerIdentityWork.Witness (Memory := Memory) ctx allocation
        (privateProgram code publicData execution.1 privateData fuel) dummy execution.2,
          Nonempty (ResidentMessageBounds.Buffer witness.data.proofBytes.val) := by
  constructor
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,toResident witness,⟨⟨witness.data.proofMemory,witness.data.proofPointer,witness.data.proofLayout,
      ResidentDecodedAllocatedJob.original_read witness.data⟩⟩⟩
  · rintro ⟨fuel,witness,⟨buffer⟩⟩
    exact ⟨fuel,⟨ofResident witness buffer⟩⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | ResidentCallerIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (ResidentCallerIdentityWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted coins)

end
end FormalProof4FHE.HasteBoots.HeapProofIdentityWork
