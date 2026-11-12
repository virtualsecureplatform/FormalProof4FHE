module
public import FormalProof4FHE.HasteBoots.CallerSerializationOrigin
@[expose] public section

/-! Original checked message-buffer reads replace abstract parent/registry
size domains. Realization of these buffers by Rust serialization remains an
explicit implementation boundary, not an assumed physical-work theorem. -/
namespace FormalProof4FHE.HasteBoots.ResidentCallerIdentityWork
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
  buffers : CallerSerializationOrigin.Buffers data
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
    some (CallerFramedAllocatedJob.truth data dummy)

def toStatement {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    StatementDerivedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,CallerSerializationOrigin.registry_fits witness.data witness.buffers,
    witness.before,witness.bytes,witness.valid,
    CallerSerializationOrigin.parent_domain witness.data witness.buffers,witness.initial⟩

def ofStatement {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : StatementDerivedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world)
    (buffers : CallerSerializationOrigin.Buffers witness.data) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,buffers,witness.before,witness.bytes,witness.valid,witness.initial⟩

theorem ofStatement_toStatement {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    ofStatement (toStatement witness) witness.buffers = witness := rfl

theorem toStatement_ofStatement {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : StatementDerivedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world)
    (buffers : CallerSerializationOrigin.Buffers witness.data) :
    toStatement (ofStatement witness buffers) = witness := rfl

theorem data_toStatement {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    (toStatement witness).data = witness.data := rfl

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem covered (execution : Tape × World)
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    StatementDerivedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel, ⟨witness⟩⟩ := failed
  exact ⟨fuel, ⟨toStatement witness⟩⟩

theorem failure_iff (execution : Tape × World) :
    Failure Memory ctx allocation code publicData privateData dummy execution ↔
      ∃ fuel, ∃ witness : StatementDerivedIdentityWork.Witness (Memory := Memory) ctx allocation
        (privateProgram code publicData execution.1 privateData fuel) dummy execution.2,
          Nonempty (CallerSerializationOrigin.Buffers witness.data) := by
  constructor
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,toStatement witness,⟨witness.buffers⟩⟩
  · rintro ⟨fuel,witness,⟨buffers⟩⟩
    exact ⟨fuel,⟨ofStatement witness buffers⟩⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | StatementDerivedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (StatementDerivedIdentityWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted coins)

end
end FormalProof4FHE.HasteBoots.ResidentCallerIdentityWork
