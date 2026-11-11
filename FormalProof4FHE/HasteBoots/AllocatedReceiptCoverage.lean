module
public import FormalProof4FHE.HasteBoots.ProgramReceiptCoverage
public import FormalProof4FHE.HasteBoots.AllocatedScalarExposure
@[expose] public section

/-! The actual allocated execution supplies the enclosing-log inclusion and
outer scalar first read. Outside one program-wide fresh-receipt ledger, all
three original lookup factor samples have named raw payloads at that read. -/
namespace FormalProof4FHE.HasteBoots.AllocatedReceiptCoverage
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
open LookupFactorFixation (Sample Scalar Point)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

theorem samples_named {Memory A : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) {index : Fin origin.ready.jobs.length}
    (job : LookupExecutionJob.Job origin index)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed)
    (program : Program A)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (run program world).run.2)
    (safe : ¬ ProgramReceiptCoverage.Bad program world) :
    ∃ first : ProgramFirstStreamRead.First program world entry.coefficients.phase.pending.input,
      ∃ compression offset : Scalar, ∃ point : Point,
        compression.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member ∧
        offset.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member ∧
        point.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member ∧
        compression.position = .compression index.val ∧ offset.position = .offset index.val ∧ point.position = .equalityPoint index.val ∧
        compression.word = (origin.ready.jobs.get index).output.y ∧ offset.word = (origin.ready.jobs.get index).output.r ∧
        point.point = List.ofFn job.view.eqPoint ∧
        compression.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix first.position program world).run.2 ∧
        offset.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix first.position program world).run.2 ∧
        point.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix first.position program world).run.2 := by
  have native := AllocatedRegistrySeed.native_execution entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase
  have captured := AllocatedScalarExposure.captured entries helperHandle references template chooseHelper chooseBatch memory result executed lookup progress after phase origin
    (run program world).run.2 observed
  obtain ⟨first⟩ := AllocatedScalarExposure.first_read origin program captured entry member
  obtain ⟨compression,offset,compressionView,offsetView,compressionAt,offsetAt,y,r,compressionLog,offsetLog⟩ :=
    LoggedLookupFactorSamples.scalars origin native.1 job rootsFit statementFits domain entry member
  obtain ⟨point,pointView,pointAt,pointValue,pointLog⟩ :=
    LoggedLookupFactorSamples.point origin native.1 job rootsFit statementFits domain entry member
  have named (sample : Sample)
      (view : sample.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
      (logged : LoggedLookupFactorSamples.Logged (row := NativeGoldBlockCode.description.row) (registry := ctx.registry)
        (helper := ctx.helper) (parent := ctx.parent) (requests := ctx.requests) (proof := ctx.proof)
        (lookupFuel := ctx.lookupFuel) (equalityFuel := ctx.equalityFuel) (scalarFuel := ctx.scalarFuel) sample) :
      sample.state.phase.consumed ∈ ReceiptPayloadView.payloads (runPrefix first.position program world).run.2 := by
    have sameWorld : sample.view.reader.world = world := by rw [view]; rfl
    have sameInput : sample.view.reader.entry.coefficients.phase.pending.input = entry.coefficients.phase.pending.input := by rw [view]; rfl
    have loggedWorld := logged
    unfold LoggedLookupFactorSamples.Logged at loggedWorld
    rw [sameWorld] at loggedWorld
    exact ProgramReceiptCoverage.named_at sample program first sameWorld sameInput
      ((native.2.trans observed).subset loggedWorld) safe

  exact ⟨first,compression,offset,point,compressionView,offsetView,pointView,compressionAt,offsetAt,pointAt,y,r,pointValue,
    named compression.toSample compressionView compressionLog,named offset.toSample offsetView offsetLog,named point.toSample pointView pointLog⟩

end
end FormalProof4FHE.HasteBoots.AllocatedReceiptCoverage
