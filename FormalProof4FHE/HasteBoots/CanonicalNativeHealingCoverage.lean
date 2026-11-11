module
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedHealing
public import FormalProof4FHE.HasteBoots.CanonicalScalarLifetime
@[expose] public section

/-! Retained native jobs reconstruct their actual allocated execution.
Canonical healing is recovered from that same enclosing program history. -/
namespace FormalProof4FHE.HasteBoots.CanonicalNativeHealingCoverage
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open OracleProgram (Program run)
open AllocatedFamilyFunctions (Allocation)
open CanonicalAllocatedJob (Job)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx} {program : Program A} {world : World}

theorem allocated_packet (data : Job (Memory := Memory) ctx allocation program world) :
    (run (AllocatedLookupExecution.program allocation.entries allocation.helperHandle allocation.references allocation.template
      data.chooseHelper data.chooseBatch data.memory) world).run =
      (.verification ctx (run (NativeGoldLookupVerification.program ctx data.chooseHelper data.chooseBatch data.memory) world).run.1,
        (run (NativeGoldLookupVerification.program ctx data.chooseHelper data.chooseBatch data.memory) world).run.2) := by
  rw [AllocatedLookupExecution.program,allocation.assembled,OracleProgram.run_bind,ObservationReplay.run_bind]
  change (_, _ ++ []) = (_, _)
  rw [List.append_nil]
  rfl

theorem recover (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (healing : CanonicalAllocatedIdentity.Healing data dummy) :
    (∃ position input, CanonicalAttainableEvent.Event program position input data.index.val dummy world) ∨
      NativeRootFamilyLifetime.Bad dummy (run program world).run.2 := by
  have packet := allocated_packet data
  have executed := congrArg Prod.fst packet
  have observed : (run (AllocatedLookupExecution.program allocation.entries allocation.helperHandle allocation.references allocation.template
      data.chooseHelper data.chooseBatch data.memory) world).run.2.Sublist (run program world).run.2 := by
    rw [packet]
    exact data.observed
  exact CanonicalAllocatedHealing.recover allocation.entries allocation.reachable allocation.helperHandle allocation.references allocation.template
    data.chooseHelper data.chooseBatch data.memory _ executed data.lookup data.progress data.after data.executed data.origin rootsFit statementFits domain
    program observed framing safe before bytes valid parentDomain data.index data.job data.geometry dummy healing

theorem false_identity_covered (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
      some (CanonicalAllocatedIdentity.truth data dummy)) :
    CanonicalScalarLifetime.Event program dummy world ∨
    SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world ∨
    OpeningLifetimeFamily.Failure Memory Memory dummy target (RegistryPublicSource.context ctx)
      (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
        (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1)
      (NativeBrakedownCalibration.radius .goldilocks helperRole)
      (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) program OracleProgramMachine.step world := by
  rcases CanonicalAllocatedIdentity.false_identity data dummy frames decoded statementFits domain target parameters profile helperRole helperAdmitted
      sourceRole sourceAdmitted initial with healing | bad | pcs
  · rcases recover data dummy rootsFit statementFits domain framing safe before bytes valid parentDomain healing with attained | bad
    · obtain ⟨position,input,event⟩ := attained
      exact Or.inl ⟨position,input,data.index.val,event⟩
    · exact Or.inr (Or.inl (ProgramOpeningLifetime.root_bad program world dummy bad))
  · exact Or.inr (Or.inl bad)
  · exact Or.inr (Or.inr pcs)

end
end FormalProof4FHE.HasteBoots.CanonicalNativeHealingCoverage
