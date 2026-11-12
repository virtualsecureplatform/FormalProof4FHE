module
public import FormalProof4FHE.HasteBoots.CanonicalIdentityWork
public import FormalProof4FHE.HasteBoots.CanonicalNativeHealingCoverage
public import FormalProof4FHE.HasteBoots.CanonicalNativeSumCoverage
public import FormalProof4FHE.HasteBoots.CanonicalPairedJointWorkBound
@[expose] public section

/-! Initially false native sum or identity equations inherit a joint
128-bit specified-work bound. Original framing/seed-order premises remain
explicit; whole public modified-PBS initial falsity is not asserted. -/
namespace FormalProof4FHE.HasteBoots.CanonicalPairedIdentityWork
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
  domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra
  framing : AllocatedLookupReadStability.Framing ctx world
  seedOrder : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests
  initial : (ScalarChainHealing.value (2*data.index.val) data.origin.ready.statement.claims.val ≠
    some (AllocatedSumAlternatives.truth data dummy)) ∨
    (ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
      some (CanonicalAllocatedIdentity.truth data dummy))

def ofIdentity {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World}
    (witness : CanonicalIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world) :
    Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,witness.rootsFit,witness.frames,witness.decoded,witness.statementFits,witness.domain,witness.framing,
    witness.seedOrder,witness.before,witness.bytes,witness.valid,witness.parentDomain,Or.inr witness.initial⟩

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

theorem identity_included (execution : Tape × World)
    (failed : CanonicalIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution) :
    Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  exact ⟨fuel,⟨ofIdentity witness⟩⟩

theorem covered (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (execution : Tape × World) (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    (∃ fuel, PrivateCoinPairedScalarProbability.Event code publicData privateData dummy fuel execution) ∨
    PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (RegistryPublicSource.context ctx)
      (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
        (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1)
      (NativeBrakedownCalibration.radius .goldilocks helperRole)
      (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) execution := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  rcases witness.initial with sumFalse | identityFalse
  · rcases CanonicalNativeSumCoverage.false_sum_covered witness.data dummy witness.rootsFit witness.frames witness.decoded witness.statementFits
      witness.domain witness.framing witness.seedOrder witness.before witness.bytes witness.valid witness.parentDomain target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted sumFalse with healing | bad | pcs
    · exact Or.inl ⟨fuel,Or.inr healing⟩
    · exact Or.inr ⟨fuel,Or.inl bad⟩
    · exact Or.inr ⟨fuel,Or.inr pcs⟩
  · rcases CanonicalNativeHealingCoverage.false_identity_covered witness.data dummy witness.rootsFit witness.frames witness.decoded witness.statementFits
      witness.domain witness.framing witness.seedOrder witness.before witness.bytes witness.valid witness.parentDomain target parameters profile
      helperRole helperAdmitted sourceRole sourceAdmitted identityFalse with healing | bad | pcs
    · exact Or.inl ⟨fuel,Or.inl healing⟩
    · exact Or.inr ⟨fuel,Or.inl bad⟩
    · exact Or.inr ⟨fuel,Or.inr pcs⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  let helperOrigin := AllocatedOpeningLifetimeBound.helperOrigin ctx allocation.entries allocation.reachable allocation.helperHandle allocation.references
    allocation.template allocation.assembled target parameters
  let sourceOrigin := RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
    (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1
  have width : 3 ≤ target.parameters.width.val := by
    rw [helperAdmitted.width]
    cases helperRole <;> decide +kernel
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | (∃ fuel, PrivateCoinPairedScalarProbability.Event code publicData privateData dummy fuel execution) ∨
        PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (RegistryPublicSource.context ctx) sourceOrigin
          (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted execution failed
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (CanonicalPairedJointWorkBound.work_128 Memory Memory code publicData privateData dummy ctx.parent.profile target helperOrigin helperRole helperAdmitted width
      (RegistryPublicSource.context ctx) sourceOrigin sourceRole sourceAdmitted (IndexedSourceFieldReduction.registry_profiles ctx) coins)

end
end FormalProof4FHE.HasteBoots.CanonicalPairedIdentityWork
