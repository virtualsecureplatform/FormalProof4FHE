module
public import FormalProof4FHE.HasteBoots.SourceOpeningLifetimeWitness
public import FormalProof4FHE.HasteBoots.BatchOpeningNativeObligation
@[expose] public section

/-! Wrong original source-batch obligations on the common extracted cube
enter the joint opening lifetime event. Allocation provenance, actual accepted
receipts, original query indices, parsed data and profile lineage are retained. -/
namespace FormalProof4FHE.HasteBoots.SourceOpeningObligationLifetime
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldParameterStore (Entry Reference)
open NativeDeferredBatchVerification (Receipt Result)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

variable {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification result)) (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)

include executed member

theorem preparation :
    (run (NativeGoldBatchPcsProgram.prepareProgram (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)) world).run.1 = .prepared receipt.work := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress (.verification result) executed
  have checked := (NativeDeferredBatchVerification.program_receipts (NativeGoldLookupVerification.batchContext ctx progress) chooseBatch lookup.helpers.memory
    world result origin.2.2.1 receipt member).1
  exact (NativeGoldBatchPcsProgram.completed_origin _ chooseBatch ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1).prepared

theorem witness (dummy : Digest) (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (collected : NativeGoldParameterStore.registry entries references = some ctx.registry)
    (target : NativeGoldBatchPcsProgram.Context) (parameters : receipt.call.oracle.parameters = target.parameters)
    (profile : ctx.parent.profile = target.parent.profile) (radius : ℕ)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (responseFits : (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (wrong : ∀ decoded, NativeGoldBatchChallengeLink.parse
        (NativeGoldBatchColumnRequestLaw.input (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work world) = some decoded →
      BatchOpeningNativeObligation.Wrong dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
        ((SourceOpeningLifetimeWitness.origin ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member entries reachable references collected target parameters).primitiveAt _ parameters)
        ((SourceOpeningLifetimeWitness.origin ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member entries reachable references collected target parameters).capacityAt _ parameters)
        world receipt.work (preparation ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member) decoded history radius) :
    Nonempty (CacheBackedBatchLifetimeSoundness.Witness Memory dummy target
      (SourceOpeningLifetimeWitness.origin ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member entries reachable references collected target parameters)
      radius world history) := by
  apply SourceOpeningLifetimeWitness.witness ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member
    dummy entries reachable references collected target parameters profile radius framed responseFits history observed
  intro decoded parsed
  exact (BatchOpeningNativeObligation.false_claim_iff dummy _ _ _ world receipt.work
    (preparation ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member) decoded history radius framed responseFits parsed).mpr
      (wrong decoded parsed)

/-- A wrong particular original row suffices, even when it shares a left
response group with other original queries. -/
theorem at_witness (dummy : Digest) (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (collected : NativeGoldParameterStore.registry entries references = some ctx.registry)
    (target : NativeGoldBatchPcsProgram.Context) (parameters : receipt.call.oracle.parameters = target.parameters)
    (profile : ctx.parent.profile = target.parent.profile) (radius : ℕ)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (responseFits : (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (index : NativeGoldBatchRectangularData.Query receipt.work) (row : NativeLookupRequestWire.Row)
    (foundRow : receipt.work.binding.values.val[index.val]? = some row)
    (expected : Fin receipt.call.oracle.parameters.width.val → NativeFields.Goldilocks)
    (encoded : row.val.map NativeFieldRepresentation.goldValue = List.ofFn expected)
    (wrong : ∀ decoded, NativeGoldBatchChallengeLink.parse
        (NativeGoldBatchColumnRequestLaw.input (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work world) = some decoded →
      BatchOpeningNativeObligation.WrongAt dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
        ((SourceOpeningLifetimeWitness.origin ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member entries reachable references collected target parameters).primitiveAt _ parameters)
        ((SourceOpeningLifetimeWitness.origin ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member entries reachable references collected target parameters).capacityAt _ parameters)
        world receipt.work (preparation ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member) decoded history radius index expected) :
    Nonempty (CacheBackedBatchLifetimeSoundness.Witness Memory dummy target
      (SourceOpeningLifetimeWitness.origin ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member entries reachable references collected target parameters)
      radius world history) := by
  apply witness ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member
    dummy entries reachable references collected target parameters profile radius framed responseFits history observed
  intro decoded parsed
  exact BatchOpeningNativeObligation.wrong_of_at dummy _ _ _ world receipt.work
    (preparation ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member) decoded history radius
    index row foundRow expected encoded (wrong decoded parsed)

/-- The same source branch enters the joint lifetime event with the existing
complete history and single shared hash charge. -/
theorem at_joint_failure (dummy : Digest) (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (collected : NativeGoldParameterStore.registry entries references = some ctx.registry)
    (target : NativeGoldBatchPcsProgram.Context) (parameters : receipt.call.oracle.parameters = target.parameters)
    (profile : ctx.parent.profile = target.parent.profile) (radius : ℕ)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (responseFits : (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (index : NativeGoldBatchRectangularData.Query receipt.work) (row : NativeLookupRequestWire.Row)
    (foundRow : receipt.work.binding.values.val[index.val]? = some row)
    (expected : Fin receipt.call.oracle.parameters.width.val → NativeFields.Goldilocks)
    (encoded : row.val.map NativeFieldRepresentation.goldValue = List.ofFn expected)
    (wrong : ∀ decoded, NativeGoldBatchChallengeLink.parse
        (NativeGoldBatchColumnRequestLaw.input (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work world) = some decoded →
      BatchOpeningNativeObligation.WrongAt dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
        ((SourceOpeningLifetimeWitness.origin ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member entries reachable references collected target parameters).primitiveAt _ parameters)
        ((SourceOpeningLifetimeWitness.origin ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member entries reachable references collected target parameters).capacityAt _ parameters)
        world receipt.work (preparation ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member) decoded history radius index expected)
    {P S A HelperMemory : Type} (past : World → NativeTranscript.Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ)
    (historyEq : history = (CausalExposureLifetime.history past initial step fuel world).run.2)
    (helper : NativeGoldPcsExecution.Context) (helperRadius : ℕ)
    (referenceOrigin : CacheBackedCodeOrigin.Origin target) :
    SharedNativeOpeningLifetime.Failure HelperMemory Memory dummy helper target referenceOrigin helperRadius radius past initial step world := by
  obtain ⟨nativeWitness⟩ := at_witness ctx chooseHelper chooseBatch memory world lookup progress result executed receipt member
    dummy entries reachable references collected target parameters profile radius framed responseFits history observed index row foundRow expected encoded wrong
  apply Or.inr
  refine ⟨fuel,?_⟩
  rw [← historyEq]
  exact ⟨CacheBackedBatchLifetimeSoundness.ofNative referenceOrigin (CacheBackedBatchLifetimeSoundness.toNative nativeWitness)⟩

end
end FormalProof4FHE.HasteBoots.SourceOpeningObligationLifetime
