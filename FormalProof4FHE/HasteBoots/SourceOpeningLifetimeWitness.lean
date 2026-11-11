module
public import FormalProof4FHE.HasteBoots.RegistryBatchCodeOrigin
public import FormalProof4FHE.HasteBoots.CacheBackedBatchLifetimeSoundness
public import FormalProof4FHE.HasteBoots.DeferredBatchProfileLineage
public import FormalProof4FHE.HasteBoots.SharedNativeOpeningLifetime
@[expose] public section

/-! Actual whole-lookup source receipts produce lifetime witnesses with the
selected original allocation's constructor provenance. Only full-parameter /
reference-parent association, framing and parsed-claim falsity are inputs. -/
namespace FormalProof4FHE.HasteBoots.SourceOpeningLifetimeWitness
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

/-- Retargeting retains the actual constructor request and execution, rather
than choosing a new constructor that happens to produce equal code. -/
def retarget {ctx : NativeGoldBatchPcsProgram.Context} (origin : CacheBackedCodeOrigin.Origin ctx)
    (target : NativeGoldBatchPcsProgram.Context) (same : ctx.parameters = target.parameters) :
    CacheBackedCodeOrigin.Origin target :=
  ⟨origin.request,origin.config,origin.reachable,origin.result,origin.finished,
    origin.retained.trans (congrArg (fun parameters => parameters.code) same)⟩

theorem retarget_data {ctx : NativeGoldBatchPcsProgram.Context} (origin : CacheBackedCodeOrigin.Origin ctx)
    (target : NativeGoldBatchPcsProgram.Context) (same : ctx.parameters = target.parameters) :
    (retarget origin target same).request = origin.request ∧ (retarget origin target same).config = origin.config := ⟨rfl,rfl⟩

variable {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches prepared progress (.verification result)) (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)

include executed member

theorem accepted (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (history : List Observation)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history) :
    NativeGoldBatchAnySourceRisk.Accepted world history (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
      chooseBatch ctx.workerFuel receipt.memory receipt.work := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  exact NativeDeferredBatchAvailability.receipt_accepted (NativeGoldLookupVerification.batchContext ctx progress) chooseBatch prepared.helpers.memory world
    result origin.2.2.1 history ((NativeGoldLookupAvailability.batch_log_sublist ctx chooseHelper chooseBatch memory world prepared progress _ executed).trans observed)
    receipt member framed

/-- The first-original registry owner supplies its completed allocated backend
also when a later batch stops. Reference contexts may have different call data. -/
def origin (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (references : Vector Reference)
    (collected : NativeGoldParameterStore.registry entries references = some ctx.registry)
    (target : NativeGoldBatchPcsProgram.Context) (parameters : receipt.call.oracle.parameters = target.parameters) :
    CacheBackedCodeOrigin.Origin target :=
  retarget (RegistryBatchCodeOrigin.ofReceipt ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member
    entries reachable references collected) target parameters

theorem witness (dummy : Digest) (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (collected : NativeGoldParameterStore.registry entries references = some ctx.registry)
    (target : NativeGoldBatchPcsProgram.Context) (parameters : receipt.call.oracle.parameters = target.parameters)
    (profile : ctx.parent.profile = target.parent.profile) (radius : ℕ)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (responseFits : (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (falseClaim : ∀ decoded, NativeGoldBatchChallengeLink.parse
        (NativeGoldBatchColumnRequestLaw.input (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work world) = some decoded →
      NativeGoldBatchCausalCoverage.FalseClaim dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
        ((origin ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member entries reachable references collected target parameters).primitiveAt _ parameters)
        receipt.work decoded history
        ((origin ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member entries reachable references collected target parameters).capacityAt _ parameters) radius) :
    Nonempty (CacheBackedBatchLifetimeSoundness.Witness Memory dummy target
      (origin ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member entries reachable references collected target parameters)
      radius world history) := by
  have nativeAccepted := accepted ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member framed history observed
  obtain ⟨completion,next,callExecuted,_,_⟩ := nativeAccepted.2
  have preparation := (NativeGoldBatchPcsProgram.completed_origin _ chooseBatch ctx.workerFuel receipt.memory world receipt.work
    completion callExecuted).prepared
  obtain ⟨before,parent,valid,fits⟩ := framed
  obtain ⟨context,_,parsed,_,_⟩ := NativeGoldBatchPreparedChallenge.prepared_link _ world receipt.work preparation before parent valid fits responseFits
  have receiptProfile := (DeferredBatchProfileLineage.lookup_profiles ctx chooseHelper chooseBatch memory world prepared progress result executed).2 receipt member
  exact ⟨{
    candidate := receipt.call.context ctx.tables ctx.fieldFuel receipt.before
    sameParameters := parameters
    sameProfile := receiptProfile.1.trans profile
    choose := chooseBatch
    verifierFuel := ctx.workerFuel
    memory := receipt.memory
    work := receipt.work
    decoded := NativeGoldBatchPreparedChallenge.recovered _ world receipt.work before context
    parsed := parsed
    responseFits := responseFits
    accepted := nativeAccepted
    falseClaim := falseClaim _ parsed }⟩

/-- An actual false source receipt in any machine prefix enters the same joint
helper/source failure event, with no new hash charge or separate history. -/
theorem joint_failure (dummy : Digest) (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (collected : NativeGoldParameterStore.registry entries references = some ctx.registry)
    (target : NativeGoldBatchPcsProgram.Context) (parameters : receipt.call.oracle.parameters = target.parameters)
    (profile : ctx.parent.profile = target.parent.profile) (radius : ℕ)
    (framed : NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (responseFits : (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (falseClaim : ∀ decoded, NativeGoldBatchChallengeLink.parse
        (NativeGoldBatchColumnRequestLaw.input (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work world) = some decoded →
      NativeGoldBatchCausalCoverage.FalseClaim dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
        ((origin ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member entries reachable references collected target parameters).primitiveAt _ parameters)
        receipt.work decoded history
        ((origin ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member entries reachable references collected target parameters).capacityAt _ parameters) radius)
    {P S A HelperMemory : Type} (past : World → NativeTranscript.Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ)
    (historyEq : history = (CausalExposureLifetime.history past initial step fuel world).run.2)
    (helper : NativeGoldPcsExecution.Context) (helperRadius : ℕ)
    (referenceOrigin : CacheBackedCodeOrigin.Origin target) :
    SharedNativeOpeningLifetime.Failure HelperMemory Memory dummy helper target referenceOrigin helperRadius radius past initial step world := by
  obtain ⟨nativeWitness⟩ := witness ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member
    dummy entries reachable references collected target parameters profile radius framed responseFits history observed falseClaim
  apply Or.inr
  refine ⟨fuel,?_⟩
  rw [← historyEq]
  exact ⟨CacheBackedBatchLifetimeSoundness.ofNative referenceOrigin (CacheBackedBatchLifetimeSoundness.toNative nativeWitness)⟩

end
end FormalProof4FHE.HasteBoots.SourceOpeningLifetimeWitness
