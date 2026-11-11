module
public import FormalProof4FHE.HasteBoots.SharedProofReadSize
@[expose] public section

/-! Bounded structural proof buffers supply the canonical serialization
obligations even with wider varints and trailing bytes. Rust refinement and
actual attacker-work correspondence remain separate. -/
namespace FormalProof4FHE.HasteBoots.DecodedIdentityWork
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
  data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world
  frames : List TranscriptFrame.Frame
  decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames
  statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit
  proofBytes : Vector InputIndexedOracle.Byte
  rest : Input
  parsedProof : SharedProofByteCodec.codec.read proofBytes.val = some (ctx.proof,rest)
  registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
    (OracleProgram.run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
      (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests
  initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
    some (CanonicalAllocatedIdentity.truth data dummy)

def toSerialized {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    SerializedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world := by
  let available := SharedProofReadSize.canonical_source witness.proofBytes ctx.proof witness.rest witness.parsedProof
  let canonical := Classical.choose available
  have parsed := Classical.choose_spec available
  exact ⟨witness.data,witness.frames,witness.decoded,witness.statementFits,canonical,parsed,witness.registryFits,
    witness.before,witness.bytes,witness.valid,witness.parentDomain,witness.initial⟩

def ofSerialized {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : SerializedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world) :
    Witness (Memory := Memory) ctx allocation program dummy world := by
  have bytes := NativeExactCodec.read_sound SharedProofByteCodec.codec witness.proofBytes.val ctx.proof witness.parsedProof
  have parsed : SharedProofByteCodec.codec.read witness.proofBytes.val = some (ctx.proof,[]) := by
    rw [← bytes]
    simpa only [List.append_nil] using SharedProofByteCodec.read_prefix ctx.proof []
  exact ⟨witness.data,witness.frames,witness.decoded,witness.statementFits,witness.proofBytes,[],parsed,witness.registryFits,
    witness.before,witness.bytes,witness.valid,witness.parentDomain,witness.initial⟩

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem covered (execution : Tape × World)
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    SerializedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel, ⟨witness⟩⟩ := failed
  exact ⟨fuel, ⟨toSerialized witness⟩⟩

theorem failure_iff (execution : Tape × World) :
    Failure Memory ctx allocation code publicData privateData dummy execution ↔
      SerializedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  constructor
  · exact covered Memory ctx allocation code publicData privateData dummy execution
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,⟨ofSerialized witness⟩⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | SerializedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (SerializedIdentityWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted coins)

end
end FormalProof4FHE.HasteBoots.DecodedIdentityWork
