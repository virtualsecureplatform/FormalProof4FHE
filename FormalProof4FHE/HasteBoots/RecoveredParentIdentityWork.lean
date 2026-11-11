module
public import FormalProof4FHE.HasteBoots.LookupFramingRecovery
@[expose] public section

/-! Native parent completion supplies parent frame lists and helper binding for
the false-identity endpoint. Byte allocation domains and Rust refinement remain. -/
namespace FormalProof4FHE.HasteBoots.RecoveredParentIdentityWork
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
  rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit
  frames : List TranscriptFrame.Frame
  decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames
  statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit
  proofBytes : Vector InputIndexedOracle.Byte
  parsedProof : NativeExactCodec.read ScalarProofFraming.proofCodec proofBytes.val = some ctx.proof.algebra
  registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
    (OracleProgram.run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
      (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit
  groupedFits : (NativeLookupMultiplicityWire.grouped ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit
  flatFits : (NativeLookupMultiplicityWire.flattened ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests
  initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
    some (CanonicalAllocatedIdentity.truth data dummy)

def toFramed {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : Witness (Memory := Memory) ctx allocation program dummy world) :
    FramedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world := by
  let framing := Classical.choice (LookupFramingRecovery.job_framing witness.data witness.before witness.bytes
    witness.valid witness.parentDomain witness.registryFits witness.groupedFits witness.flatFits)
  exact ⟨witness.data,witness.rootsFit,witness.frames,witness.decoded,witness.statementFits,witness.proofBytes,
    witness.parsedProof,framing,witness.before,witness.bytes,witness.valid,witness.parentDomain,witness.initial⟩

/-- Previous framing witnesses already contain exactly the retained size domains. -/
def ofFramed {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : FramedIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,witness.rootsFit,witness.frames,witness.decoded,witness.statementFits,witness.proofBytes,
    witness.parsedProof,witness.framing.registryFits,witness.framing.groupedFits,witness.framing.flatFits,
    witness.before,witness.bytes,witness.valid,witness.parentDomain,witness.initial⟩

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem covered (execution : Tape × World)
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    FramedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel, ⟨witness⟩⟩ := failed
  exact ⟨fuel, ⟨toFramed witness⟩⟩

/-- Recovering the parent certificates preserves the entire previous failure event. -/
theorem failure_iff (execution : Tape × World) :
    Failure Memory ctx allocation code publicData privateData dummy execution ↔
      FramedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  constructor
  · exact covered Memory ctx allocation code publicData privateData dummy execution
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,⟨ofFramed witness⟩⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | FramedIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (FramedIdentityWork.work_128 Memory ctx allocation code publicData privateData dummy target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted coins)

end
end FormalProof4FHE.HasteBoots.RecoveredParentIdentityWork
