module
public import FormalProof4FHE.HasteBoots.LookupViewSumReduction
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedIdentity
@[expose] public section

/-! The original even-slot sum equation yields actual scalar healing or a
wrong original helper opening, at the independently calibrated helper radius.
Pricing its healing event and whole-lookup initial falsity remain separate. -/
namespace FormalProof4FHE.HasteBoots.AllocatedSumAlternatives
open NativeGoldHelperVerification (Context)
open NativeGoldBatchOpening (Opening)
open NativePrefixCodec (Vector)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open OracleProgram (Program)
open CanonicalAllocatedJob (Job helpers sources)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

def truth (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :=
  ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient
    ScalarLookupExpression.sumIndices (NativeScalarQueryShape.laneBits (3+data.origin.padding)+data.lookup.body.sourceVariables)
    (LookupViewSumReduction.tables (helpers data dummy)) []

def Healing (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) : Prop :=
  ScalarFinishedSourceEvent.Event data.origin.ready.equality.transcript data.origin.ready.statement ctx.proof.algebra ctx.scalarFuel world
    ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
    (NativeScalarQueryShape.laneBits (3+data.origin.padding)+data.lookup.body.sourceVariables)
    (LookupViewSumReduction.tables (helpers data dummy)) (2*data.index.val) (LookupScalarGrammar.sumInfo data.origin.geometry.geometry.1)

theorem false_sum_or_wrong (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (initial : ScalarChainHealing.value (2*data.index.val) data.origin.ready.statement.claims.val ≠ some (truth data dummy)) :
    Healing data dummy ∨ LookupViewSumReduction.Wrong data.job.view (helpers data dummy) := by
  have pair := LookupScalarGrammar.protocol_pair ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    data.origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property
    7 ctx.lookupFuel ctx.equalityFuel _ world data.origin.ready data.origin.prepared data.index.val data.index.isLt
  have guard := NativeSharedLookupGuard.guard_spec _ _ _ _ _ data.origin.guarded
  have evidence := guard.checked data.job.view.checked (List.mem_of_getElem? data.job.view.checkedAt)
  have sumAt := evidence.sum
  rw [data.job.view.ordinalEq] at sumAt
  exact LookupViewSumReduction.event_or_wrong data.job.view _ frames _ _ decoded statementFits domain ctx.scalarFuel world data.origin.scalar
    pair.1 sumAt evidence.matched (helpers data dummy) initial

theorem false_sum_helper (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (initial : ScalarChainHealing.value (2*data.index.val) data.origin.ready.statement.claims.val ≠ some (truth data dummy)) :
    Healing data dummy ∨ SingleOpeningLifetimeSoundness.Failure Memory dummy target
      (NativeBrakedownCalibration.radius .goldilocks helperRole) (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world := by
  rcases false_sum_or_wrong data dummy frames decoded statementFits domain initial with healing | wrong
  · exact Or.inl healing
  · right
    exact CanonicalAllocatedHelperCoverage.helper ctx data.chooseHelper data.chooseBatch data.memory world data.lookup data.progress data.after
      data.executed data.origin data.index data.job allocation data.geometry dummy program target parameters profile helperRole helperAdmitted
      data.observed data.helperFraming data.helperResponseFits wrong

theorem false_sum (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (initial : ScalarChainHealing.value (2*data.index.val) data.origin.ready.statement.claims.val ≠ some (truth data dummy)) :
    Healing data dummy ∨
    SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world ∨
    OpeningLifetimeFamily.Failure Memory Memory dummy target (RegistryPublicSource.context ctx)
      (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
        (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1)
      (NativeBrakedownCalibration.radius .goldilocks helperRole)
      (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) program OracleProgramMachine.step world := by
  rcases false_sum_or_wrong data dummy frames decoded statementFits domain initial with healing | wrong
  · exact Or.inl healing
  · exact Or.inr (CanonicalAllocatedJob.wrong_covered data dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted (Or.inr wrong))

theorem false_pair (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (initial : (ScalarChainHealing.value (2*data.index.val) data.origin.ready.statement.claims.val ≠ some (truth data dummy)) ∨
      (ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠ some (CanonicalAllocatedIdentity.truth data dummy))) :
    Healing data dummy ∨ CanonicalAllocatedIdentity.Healing data dummy ∨
    SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world ∨
    OpeningLifetimeFamily.Failure Memory Memory dummy target (RegistryPublicSource.context ctx)
      (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
        (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1)
      (NativeBrakedownCalibration.radius .goldilocks helperRole)
      (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) program OracleProgramMachine.step world := by
  rcases initial with sumFalse | identityFalse
  · rcases false_sum data dummy frames decoded statementFits domain target parameters profile helperRole helperAdmitted
        sourceRole sourceAdmitted sumFalse with healing | bad | pcs
    · exact Or.inl healing
    · exact Or.inr (Or.inr (Or.inl bad))
    · exact Or.inr (Or.inr (Or.inr pcs))
  · rcases CanonicalAllocatedIdentity.false_identity data dummy frames decoded statementFits domain target parameters profile
        helperRole helperAdmitted sourceRole sourceAdmitted identityFalse with healing | bad | pcs
    · exact Or.inr (Or.inl healing)
    · exact Or.inr (Or.inr (Or.inl bad))
    · exact Or.inr (Or.inr (Or.inr pcs))

end
end FormalProof4FHE.HasteBoots.AllocatedSumAlternatives
