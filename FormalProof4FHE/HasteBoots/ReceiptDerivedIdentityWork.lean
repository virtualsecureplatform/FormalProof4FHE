module
public import FormalProof4FHE.HasteBoots.DecodedAllocatedJob
@[expose] public section

/-! Original receipt positions and a decoded proof buffer supply the source
and helper response-size domains. The failure event and security rate are
preserved without independent response-size certificates. -/
namespace FormalProof4FHE.HasteBoots.ReceiptDerivedIdentityWork
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
  data : DecodedAllocatedJob.Job (Memory := Memory) ctx allocation program world
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
    some (CanonicalAllocatedIdentity.truth (DecodedAllocatedJob.toCanonical data) dummy)

def toDecoded {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    DecodedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨(DecodedAllocatedJob.toCanonical witness.data),witness.frames,witness.decoded,witness.statementFits,witness.data.proofBytes,witness.data.rest,
    witness.data.parsedProof,witness.registryFits,witness.before,witness.bytes,witness.valid,witness.parentDomain,witness.initial⟩

def ofDecoded {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : DecodedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨DecodedAllocatedJob.ofCanonical witness.data witness.proofBytes witness.rest witness.parsedProof,
    witness.frames,witness.decoded,witness.statementFits,witness.registryFits,witness.before,witness.bytes,witness.valid,
    witness.parentDomain,witness.initial⟩

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem covered (execution : Tape × World)
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    DecodedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel, ⟨witness⟩⟩ := failed
  exact ⟨fuel, ⟨toDecoded witness⟩⟩

theorem failure_iff (execution : Tape × World) :
    Failure Memory ctx allocation code publicData privateData dummy execution ↔
      DecodedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  constructor
  · exact covered Memory ctx allocation code publicData privateData dummy execution
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,⟨ofDecoded witness⟩⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | DecodedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (DecodedIdentityWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted coins)

end
end FormalProof4FHE.HasteBoots.ReceiptDerivedIdentityWork
