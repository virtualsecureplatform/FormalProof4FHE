module
public import FormalProof4FHE.HasteBoots.AllocatedSingleOpeningOrigin
public import FormalProof4FHE.HasteBoots.HelperProfileLineage
public import FormalProof4FHE.HasteBoots.SharedNativeOpeningLifetime
@[expose] public section

/-! Actual ordered helper receipts yield the accepted call, native sampling
receipt and parsed single-opening data used by lifetime soundness. Logical
allocation-handle/parameter and reference-parent association remain explicit;
physical pointer and outer application falsity are not assumed proved. -/
namespace FormalProof4FHE.HasteBoots.HelperOpeningLifetimeWitness
open NativeGoldHelperVerification (Context Receipt)
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open NativeGoldParameterStore (Entry)
open NativeRootMessage (Digest)
open OracleProgram (run)
noncomputable section

theorem accepted {B Memory : Type} (ctx : Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (bound : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (status : NativeGoldHelperVerification.Result Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers bound plan status)
    (receipt : Receipt Memory) (member : receipt ∈ status.progress.receipts)
    (framed : SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (history : List Observation) (observed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.2.Sublist history) :
    SingleOpeningAvailability.Accepted world history
      (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call)
      choose ctx.workerFuel receipt.memory receipt.work := by
  obtain ⟨checked,trace⟩ := NativeGoldHelperVerification.helpers_receipts ctx choose memory world bound plan status executed receipt member
  exact ⟨framed,receipt.completion,receipt.after,checked.1,checked.2,trace.trans observed⟩

theorem lookup_accepted {Memory : Type} (ctx : Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (choose : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (bound : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (status : NativeGoldHelperVerification.Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx choose chooseBatch memory) world).run.1.helpers.1 = .helpers bound plan status)
    (receipt : Receipt Memory) (member : receipt ∈ status.progress.receipts)
    (framed : SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (history : List Observation) (observed : (run (NativeGoldLookupVerification.program ctx choose chooseBatch memory) world).run.2.Sublist history) :
    SingleOpeningAvailability.Accepted world history
      (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call)
      choose ctx.workerFuel receipt.memory receipt.work := by
  have helperRun := (NativeGoldLookupVerification.program_helpers_value ctx choose chooseBatch memory world).symm.trans executed
  exact accepted ctx choose memory world bound plan status helperRun receipt member framed history
    ((NativeGoldLookupVerification.program_helpers ctx choose chooseBatch memory world).trans observed)

/-- Existing receipts remain covered even if a later helper stopped. The
only falsity premise refers to the actual parsed native claim/source. -/
theorem witness {B Memory : Type} (dummy : Digest) (ctx : Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (bound : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (status : NativeGoldHelperVerification.Result Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers bound plan status)
    (receipt : Receipt Memory) (member : receipt ∈ status.progress.receipts)
    (framed : SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (responseFits : (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation) (observed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.2.Sublist history)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (handle : ℕ) (entry : Entry)
    (found : entries[handle]? = some entry) (same : ctx.helper = entry.initialized.parameters)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (radius : ℕ)
    (falseClaim : ∀ sample, ∀ sampler : SingleOpeningSamplingReceipt.Receipt
        (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) world receipt.work sample,
      ∀ decoded, SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded →
        SingleOpeningCausalCoverage.FalseClaim dummy _ (AllocatedSingleOpeningOrigin.helperReceipt entries reachable handle entry found ctx same receipt)
          decoded history radius) : Nonempty (SingleOpeningLifetimeSoundness.Witness Memory dummy target radius world history) := by
  have nativeAccepted := accepted ctx choose memory world bound plan status executed receipt member framed history observed
  have checked := (NativeGoldHelperVerification.helpers_receipts ctx choose memory world bound plan status executed receipt member).1
  have prepared := (NativeGoldPcsProgram.completed_origin _ choose ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1).prepared
  obtain ⟨sample,⟨sampler⟩⟩ := SingleOpeningSamplingReceipt.ofPreparation _ world receipt.work prepared
  obtain ⟨before,parent,valid,fits⟩ := framed
  obtain ⟨context,_,parsed,_,_⟩ := SingleOpeningPreparedChallenge.prepared_link sampler prepared before parent valid fits responseFits
  exact ⟨{
    candidate := NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call
    sameParameters := parameters
    sameProfile := (HelperProfileLineage.receipt_profiles ctx choose memory world bound plan status executed receipt member).1.trans profile
    origin := AllocatedSingleOpeningOrigin.helperReceipt entries reachable handle entry found ctx same receipt
    choose := choose
    verifierFuel := ctx.workerFuel
    memory := receipt.memory
    work := receipt.work
    sample := sample
    receipt := sampler
    decoded := SingleOpeningPreparedChallenge.recovered sampler before context
    parsed := parsed
    responseFits := responseFits
    accepted := nativeAccepted
    falseClaim := falseClaim sample sampler _ parsed }⟩

/-- A false accepted helper receipt at any machine prefix is covered by the
joint event sharing the source batches' complete-history hash charge. -/
theorem joint_failure {B Memory : Type} (dummy : Digest) (ctx : Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (bound : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (status : NativeGoldHelperVerification.Result Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers bound plan status)
    (receipt : Receipt Memory) (member : receipt ∈ status.progress.receipts)
    (framed : SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (responseFits : (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation) (observed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.2.Sublist history)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (handle : ℕ) (entry : Entry)
    (found : entries[handle]? = some entry) (same : ctx.helper = entry.initialized.parameters)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (radius : ℕ)
    (falseClaim : ∀ sample, ∀ sampler : SingleOpeningSamplingReceipt.Receipt
        (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) world receipt.work sample,
      ∀ decoded, SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded →
        SingleOpeningCausalCoverage.FalseClaim dummy _ (AllocatedSingleOpeningOrigin.helperReceipt entries reachable handle entry found ctx same receipt)
          decoded history radius)
    {P S A SourceMemory : Type} (past : World → NativeTranscript.Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ)
    (historyEq : history = (CausalExposureLifetime.history past initial step fuel world).run.2)
    (source : NativeGoldBatchPcsProgram.Context) (sourceOrigin : CacheBackedCodeOrigin.Origin source) (sourceRadius : ℕ) :
    SharedNativeOpeningLifetime.Failure Memory SourceMemory dummy target source sourceOrigin radius sourceRadius past initial step world := by
  obtain ⟨nativeWitness⟩ := witness dummy ctx choose memory world bound plan status executed receipt member framed responseFits history observed
    entries reachable handle entry found same target parameters profile radius falseClaim
  exact Or.inl ⟨fuel,by rw [← historyEq]; exact ⟨nativeWitness⟩⟩

end
end FormalProof4FHE.HasteBoots.HelperOpeningLifetimeWitness
