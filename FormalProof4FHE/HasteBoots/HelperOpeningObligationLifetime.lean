module
public import FormalProof4FHE.HasteBoots.HelperOpeningLifetimeWitness
public import FormalProof4FHE.HasteBoots.LookupHelperClaimMeaning
public import FormalProof4FHE.HasteBoots.SingleOpeningNativeObligation
@[expose] public section

/-! Checked outer helper obligations enter native opening lifetime soundness.
Original receipt, parsed claim, query and dimensions are derived; remaining
falsity is against the same common-source cube at its exact recovered log. -/
namespace FormalProof4FHE.HasteBoots.HelperOpeningObligationLifetime
open NativeGoldHelperVerification (Context Receipt Progress)
open NativeGoldParameterStore (Entry)
open NativeRootMessage (Digest)
open NativeFields (Goldilocks)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

variable {B Memory : Type} (ctx : Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (body : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (after : Progress Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers body plan (.done after))

include executed

theorem prepared (receipt : Receipt Memory) (member : receipt ∈ after.receipts) :
    (run (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call).prefix world).run.1 = .prepared receipt.work := by
  have checked := (NativeGoldHelperVerification.helpers_receipts ctx choose memory world body plan (.done after) executed receipt member).1
  exact (NativeGoldPcsProgram.completed_origin _ choose ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1).prepared

theorem witness (dummy : Digest) (receipt : Receipt Memory) (member : receipt ∈ after.receipts)
    (framed : SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (responseFits : (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation) (observed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.2.Sublist history)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (handle : ℕ) (entry : Entry)
    (found : entries[handle]? = some entry) (same : ctx.helper = entry.initialized.parameters)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (radius : ℕ)
    (expected : Fin ctx.helper.width.val → Goldilocks)
    (encoded : receipt.call.values.val.map NativeFieldRepresentation.goldValue = List.ofFn expected)
    (wrong : ∀ sample, ∀ sampler : SingleOpeningSamplingReceipt.Receipt
        (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) world receipt.work sample,
      ∀ decoded, SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded →
        SingleOpeningNativeObligation.Wrong dummy _ (AllocatedSingleOpeningOrigin.helperReceipt entries reachable handle entry found ctx same receipt)
          world receipt.work (prepared ctx choose memory world body plan after executed receipt member) decoded history radius expected) :
    Nonempty (SingleOpeningLifetimeSoundness.Witness Memory dummy target radius world history) := by
  apply HelperOpeningLifetimeWitness.witness dummy ctx choose memory world body plan (.done after) executed receipt member framed responseFits history observed
    entries reachable handle entry found same target parameters profile radius
  intro sample sampler decoded parsed
  exact (SingleOpeningNativeObligation.false_claim_iff sampler (prepared ctx choose memory world body plan after executed receipt member)
    framed responseFits dummy _ decoded parsed history radius expected encoded).mpr (wrong sample sampler decoded parsed)

/-- The checked guard and original helper order select the receipt and derive
its expected field vector. No independent native false-claim premise is input. -/
theorem checked_witness (dummy : Digest) (checked : NativeSharedLookupGuard.Checked) (checkedMember : checked ∈ body.terminal.checked)
    (framed : ∀ receipt ∈ after.receipts,
      SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) ∧
        (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation) (observed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.2.Sublist history)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (handle : ℕ) (entry : Entry)
    (found : entries[handle]? = some entry) (same : ctx.helper = entry.initialized.parameters)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (radius : ℕ)
    (wrong : ∀ receipt, ∀ member : receipt ∈ after.receipts, after.receipts[checked.ordinal]? = some receipt →
      ∀ sample, ∀ sampler : SingleOpeningSamplingReceipt.Receipt
        (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) world receipt.work sample,
      ∀ decoded, SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded →
        SingleOpeningNativeObligation.Wrong dummy _ (AllocatedSingleOpeningOrigin.helperReceipt entries reachable handle entry found ctx same receipt)
          world receipt.work (prepared ctx choose memory world body plan after executed receipt member) decoded history radius
          (NativeHelperPacking.coefficients NativeExtensionFields.goldilocksBasis ctx.helper.width.val
            (NativeFieldWire.goldExtensionValue checked.sumClaim.expected))) :
    Nonempty (SingleOpeningLifetimeSoundness.Witness Memory dummy target radius world history) := by
  obtain ⟨receipt,atReceipt,member,_,_,_,_,value,_⟩ := LookupHelperClaimMeaning.checked_receipt
    ctx choose memory world body plan after executed checked checkedMember
  have encoded : receipt.call.values.val.map NativeFieldRepresentation.goldValue = List.ofFn
      (NativeHelperPacking.coefficients NativeExtensionFields.goldilocksBasis ctx.helper.width.val
        (NativeFieldWire.goldExtensionValue checked.sumClaim.expected)) := by
    rw [value,NativeGoldHelper.vector_value]
    rfl
  exact witness ctx choose memory world body plan after executed dummy receipt member (framed receipt member).1 (framed receipt member).2
    history observed entries reachable handle entry found same target parameters profile radius _ encoded (wrong receipt member atReceipt)

/-- The outer helper branch reaches the same joint lifetime event with the
original history and its single shared hash charge. -/
theorem checked_joint_failure (dummy : Digest) (checked : NativeSharedLookupGuard.Checked) (checkedMember : checked ∈ body.terminal.checked)
    (framed : ∀ receipt ∈ after.receipts,
      SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) ∧
        (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (history : List Observation) (observed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.2.Sublist history)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (handle : ℕ) (entry : Entry)
    (found : entries[handle]? = some entry) (same : ctx.helper = entry.initialized.parameters)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (radius : ℕ)
    (wrong : ∀ receipt, ∀ member : receipt ∈ after.receipts, after.receipts[checked.ordinal]? = some receipt →
      ∀ sample, ∀ sampler : SingleOpeningSamplingReceipt.Receipt
        (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) world receipt.work sample,
      ∀ decoded, SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded →
        SingleOpeningNativeObligation.Wrong dummy _ (AllocatedSingleOpeningOrigin.helperReceipt entries reachable handle entry found ctx same receipt)
          world receipt.work (prepared ctx choose memory world body plan after executed receipt member) decoded history radius
          (NativeHelperPacking.coefficients NativeExtensionFields.goldilocksBasis ctx.helper.width.val
            (NativeFieldWire.goldExtensionValue checked.sumClaim.expected)))
    {P S A SourceMemory : Type} (past : World → NativeTranscript.Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ)
    (historyEq : history = (CausalExposureLifetime.history past initial step fuel world).run.2)
    (source : NativeGoldBatchPcsProgram.Context) (sourceOrigin : CacheBackedCodeOrigin.Origin source) (sourceRadius : ℕ) :
    SharedNativeOpeningLifetime.Failure Memory SourceMemory dummy target source sourceOrigin radius sourceRadius past initial step world := by
  obtain ⟨nativeWitness⟩ := checked_witness ctx choose memory world body plan after executed dummy checked checkedMember framed history observed
    entries reachable handle entry found same target parameters profile radius wrong
  exact Or.inl ⟨fuel,by rw [← historyEq]; exact ⟨nativeWitness⟩⟩

end
end FormalProof4FHE.HasteBoots.HelperOpeningObligationLifetime
