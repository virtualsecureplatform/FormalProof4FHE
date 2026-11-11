module
public import FormalProof4FHE.HasteBoots.ParentFramedAllocatedJob
@[expose] public section

/-! Original parent framing and checked admitted helper metadata derive
helper receipt framing. No helper receipt framing certificate is supplied;
the previous failure event is preserved on the admitted width domain. -/
namespace FormalProof4FHE.HasteBoots.ParentDerivedIdentityWork
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
  data : ParentFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world
  frames : List TranscriptFrame.Frame
  decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames
  statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit
  registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
    (OracleProgram.run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
      (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests
  initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
    some (ParentFramedAllocatedJob.truth data dummy)

def toReceipt {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) (width : ctx.helper.width.val ≤ 4) :
    ReceiptDerivedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨ParentFramedAllocatedJob.toDecoded witness.data width ⟨witness.before,witness.bytes,witness.valid⟩ witness.parentDomain witness.registryFits,
    witness.frames,witness.decoded,witness.statementFits,witness.registryFits,witness.before,witness.bytes,witness.valid,
    witness.parentDomain,witness.initial⟩

def ofReceipt {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : ReceiptDerivedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨ParentFramedAllocatedJob.ofDecoded witness.data,witness.frames,witness.decoded,witness.statementFits,witness.registryFits,
    witness.before,witness.bytes,witness.valid,witness.parentDomain,witness.initial⟩

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem covered (width : ctx.helper.width.val ≤ 4) (execution : Tape × World)
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    ReceiptDerivedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel, ⟨witness⟩⟩ := failed
  exact ⟨fuel, ⟨toReceipt witness width⟩⟩

theorem failure_iff (width : ctx.helper.width.val ≤ 4) (execution : Tape × World) :
    Failure Memory ctx allocation code publicData privateData dummy execution ↔
      ReceiptDerivedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  constructor
  · exact covered Memory ctx allocation code publicData privateData dummy width execution
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,⟨ofReceipt witness⟩⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have width : ctx.helper.width.val ≤ 4 := by
    rw [parameters,helperAdmitted.width]
    cases helperRole <;> decide +kernel
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | ReceiptDerivedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy width execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (ReceiptDerivedIdentityWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted coins)

end
end FormalProof4FHE.HasteBoots.ParentDerivedIdentityWork
