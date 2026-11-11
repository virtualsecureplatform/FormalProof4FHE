module
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedJob
@[expose] public section

/-! False original identity claims, interpreted with independent original
source/helper decoding radii, yield native healing or calibrated PCS failure.
Recovering this canonical healing into a priced scalar candidate is separate. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedIdentity
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open OracleProgram (Program)
open AllocatedFamilyFunctions (Allocation)
open CanonicalAllocatedJob (Job sources helpers)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx} {program : Program A} {world : World}

def truth (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :=
  AllocatedIdentityAlternatives.truth data.origin data.index data.job (sources data dummy) (helpers data dummy)

def Healing (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) : Prop :=
  AllocatedHealingWitness.Event data.origin data.index data.job (sources data dummy) (helpers data dummy)

theorem false_identity (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠ some (truth data dummy)) :
    Healing data dummy ∨
    SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world ∨
    OpeningLifetimeFamily.Failure Memory Memory dummy target (RegistryPublicSource.context ctx)
      (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
        (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1)
      (NativeBrakedownCalibration.radius .goldilocks helperRole)
      (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) program OracleProgramMachine.step world := by
  by_cases branch : (data.origin.ready.jobs.get data.index).tag.request.terminal.logicalLength.val = 2^data.origin.geometry.geometry.1.val
  · have falseFull := initial
    simp only [truth,AllocatedIdentityAlternatives.truth,branch,ite_true] at falseFull
    rcases data.job.full_event_or_wrong (sources data dummy) (helpers data dummy) frames decoded statementFits domain branch falseFull with healing | wrong
    · exact Or.inl (AllocatedHealingWitness.full_event data.origin data.index data.job _ _ branch healing)
    · exact Or.inr (CanonicalAllocatedJob.wrong_covered data dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted wrong)
  · have falsePartial := initial
    simp only [truth,AllocatedIdentityAlternatives.truth,branch,ite_false] at falsePartial
    rcases data.job.partial_event_or_wrong (sources data dummy) (helpers data dummy) frames decoded statementFits domain branch falsePartial with healing | wrong
    · exact Or.inl (AllocatedHealingWitness.partial_event data.origin data.index data.job _ _ branch healing)
    · exact Or.inr (CanonicalAllocatedJob.wrong_covered data dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted wrong)

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedIdentity
