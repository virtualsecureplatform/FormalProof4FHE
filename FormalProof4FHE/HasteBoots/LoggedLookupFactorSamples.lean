module
public import FormalProof4FHE.HasteBoots.LookupFactorFixation
public import FormalProof4FHE.HasteBoots.LookupPreludeTrace
public import FormalProof4FHE.HasteBoots.ReceiptFirstReadCoverage
@[expose] public section

/-! Original factor samples with actual receipt observations in the native
caller log. Raw states are recovered from actual draws, never from digest
or frame equality. -/
namespace FormalProof4FHE.HasteBoots.LoggedLookupFactorSamples
open InputIndexedOracle (World)
open LookupFactorFixation (Sample Scalar Point)
noncomputable section
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open LookupExecutionOrigin (Origin childStart)
variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : NativeTranscript.Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : NativeSharedLookupBody.Bound}


/-- The native full receipt output occurs in the original caller log. -/
def Logged (sample : Sample) : Prop :=
  NativeTranscript.Observation.output (NativeReceiptPrefixView.key sample.state.phase.consumed) 0
    (InputIndexedOracle.bytes sample.view.reader.world (NativeReceiptPrefixView.key sample.state.phase.consumed) 0 64) ∈
      (OracleProgram.run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) sample.view.reader.world).run.2

theorem scalars (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (success : (OracleProgram.run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result))
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ∃ compression offset : Scalar,
      compression.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member ∧
      offset.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member ∧
      compression.position = .compression index.val ∧ offset.position = .offset index.val ∧
      compression.word = (origin.ready.jobs.get index).output.y ∧ offset.word = (origin.ready.jobs.get index).output.r ∧
      Logged (row := row) (registry := registry) (helper := helper) (parent := parent) (requests := requests) (proof := proof)
        (lookupFuel := lookupFuel) (equalityFuel := equalityFuel) (scalarFuel := scalarFuel) compression.toSample ∧
      Logged (row := row) (registry := registry) (helper := helper) (parent := parent) (requests := requests) (proof := proof)
        (lookupFuel := lookupFuel) (equalityFuel := equalityFuel) (scalarFuel := scalarFuel) offset.toSample := by
  obtain ⟨first,last,firstAt,lastAt,yDecode,rDecode⟩ := LookupProducedEndpoints.draws _ _ _ _ job.view.produced
  have positions := IndexedScalarReceiptPosition.producer_at origin job rootsFit statementFits domain entry member first last firstAt lastAt
  have traces := LookupProducerConsumed.producer origin job
  have firstMem := List.mem_of_mem_head? (by rw [firstAt]; rfl)
  have lastMem := List.mem_of_mem_getLast? (by rw [lastAt]; rfl)
  have firstTrace := traces.2 first firstMem
  have lastTrace := traces.2 last lastMem
  have reads := LookupPreludeTrace.lookup_reads origin success job.view.producer job.producerMember
  let view := ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member
  let firstSample : Sample := ⟨view,.compression index.val,first.coefficients,firstTrace,positions.1⟩
  let lastSample : Sample := ⟨view,.offset index.val,last.coefficients,lastTrace,positions.2⟩
  exact ⟨⟨firstSample,(origin.ready.jobs.get index).output.y,yDecode⟩,
    ⟨lastSample,(origin.ready.jobs.get index).output.r,rDecode⟩,rfl,rfl,rfl,rfl,rfl,rfl,
      (reads first firstMem).subset (LookupReceiptLogs.output_member world first.coefficients.phase),
      (reads last lastMem).subset (LookupReceiptLogs.output_member world last.coefficients.phase)⟩

theorem point (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (success : (OracleProgram.run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result))
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ∃ sample : Point,
      sample.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member ∧
      sample.position = .equalityPoint index.val ∧ sample.point = List.ofFn job.view.eqPoint ∧
      Logged (row := row) (registry := registry) (helper := helper) (parent := parent) (requests := requests) (proof := proof)
        (lookupFuel := lookupFuel) (equalityFuel := equalityFuel) (scalarFuel := scalarFuel) sample.toSample := by
  obtain ⟨draw,found,evidence⟩ := job.equality
  have present := List.mem_of_getElem? found
  have contract := NativeSharedLookupPrelude.protocol_contract requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared
  obtain ⟨transcript,_,machine,_⟩ := contract.lookup
  have traces := LookupConsumedTrace.equality_request NativeExtensionFields.goldilocksBasis 7 origin.geometry.geometry.1.val equalityFuel transcript
    proof.values.roots proof.roots.property world
  have valid := NativeLookupEquality.request_valid NativeExtensionFields.goldilocksBasis 7 origin.geometry.geometry.1.val equalityFuel transcript
    proof.values.roots proof.roots.property world
  rw [← machine] at traces valid
  have atReceipt : ScalarReceiptMatching.receiptAt (ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
      (.equalityPoint index.val) = some (ReceiptFrameView.frame world draw.coefficients.phase) := by
    change (origin.ready.machine.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase))[index.val]? = _
    rw [List.getElem?_map,found,Option.map_some]
  let sampled : Sample := ⟨ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member,
    .equalityPoint index.val,draw.coefficients,traces.2 draw present,atReceipt⟩
  exact ⟨⟨sampled,origin.geometry.geometry.1.val,List.ofFn job.view.eqPoint,(valid.2 draw present).1,evidence.raw⟩,rfl,rfl,rfl,
    (LookupPreludeTrace.equality_reads origin success draw present).subset (LookupReceiptLogs.output_member world draw.coefficients.phase)⟩

/-- Embed the actual native receipt observation in an enclosing adversarial
program and select the fresh first receipt read whenever its payload was not
yet named at the outer scalar first read. -/
theorem Logged.covered {sample : Sample}
    (logged : Logged (row := row) (registry := registry) (helper := helper) (parent := parent) (requests := requests) (proof := proof)
      (lookupFuel := lookupFuel) (equalityFuel := equalityFuel) (scalarFuel := scalarFuel) sample)
    {A : Type} (program : OracleProgram.Program A)
    (included : (OracleProgram.run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel)
      sample.view.reader.world).run.2.Sublist (OracleProgram.run program sample.view.reader.world).run.2)
    (outer : ProgramFirstStreamRead.First program sample.view.reader.world sample.view.reader.entry.coefficients.phase.pending.input) :
    sample.state.phase.consumed ∈ ReceiptPayloadView.payloads (OracleProgram.runPrefix outer.position program sample.view.reader.world).run.2 ∨
      ∃ first : ProgramFirstStreamRead.First program sample.view.reader.world (NativeReceiptPrefixView.key sample.state.phase.consumed),
        outer.position < first.position ∧ FreshReceiptTargetRisk.event OracleProgramMachine.step
          (OracleProgram.runPrefix first.position program sample.view.reader.world).run sample.view.reader.world :=
  ReceiptFirstReadCoverage.named_or_event sample program outer (included.subset logged)

end
end FormalProof4FHE.HasteBoots.LoggedLookupFactorSamples
