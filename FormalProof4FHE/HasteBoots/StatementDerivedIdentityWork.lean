module
public import FormalProof4FHE.HasteBoots.CheckedScalarStatementSize
@[expose] public section

/-! Executed statement construction and original allocated helper parameters
supply scalar statement framing. No statement-size or future-transcript
certificate is stored in the caller witness. -/
namespace FormalProof4FHE.HasteBoots.StatementDerivedIdentityWork
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
  registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
    (OracleProgram.run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
      (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests
  initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
    some (CallerFramedAllocatedJob.truth data dummy)

def toExecution {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    ExecutionDerivedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,CheckedScalarStatementSize.retained_fits witness.data,
    witness.registryFits,witness.before,witness.bytes,witness.valid,witness.parentDomain,witness.initial⟩

def ofExecution {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : ExecutionDerivedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,witness.registryFits,witness.before,witness.bytes,witness.valid,
    witness.parentDomain,witness.initial⟩

theorem ofExecution_toExecution {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    ofExecution (toExecution witness) = witness := rfl

theorem data_toExecution {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    (toExecution witness).data = witness.data := rfl

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem covered (execution : Tape × World)
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    ExecutionDerivedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel, ⟨witness⟩⟩ := failed
  exact ⟨fuel, ⟨toExecution witness⟩⟩

theorem failure_iff (execution : Tape × World) :
    Failure Memory ctx allocation code publicData privateData dummy execution ↔
      ExecutionDerivedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  constructor
  · exact covered Memory ctx allocation code publicData privateData dummy execution
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,⟨ofExecution witness⟩⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | ExecutionDerivedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (ExecutionDerivedIdentityWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted coins)

end
end FormalProof4FHE.HasteBoots.StatementDerivedIdentityWork
