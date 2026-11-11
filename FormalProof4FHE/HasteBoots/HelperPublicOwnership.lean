module
public import FormalProof4FHE.HasteBoots.HelperPublicSource
public import FormalProof4FHE.HasteBoots.HelperOpeningObligationLifetime
@[expose] public section

/-! Actual checked helper ordinals select the original proof root, opening,
query and matched sum value. Successful borrowing of the original helper
allocation supplies its complete parameter association and code provenance. -/
namespace FormalProof4FHE.HasteBoots.HelperPublicOwnership
open NativeGoldHelperVerification (Context Receipt Progress)
open NativeGoldParameterStore (Entry)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

variable {B Memory : Type} (ctx : Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (body : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (after : Progress Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers body plan (.done after))
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (handle : ℕ)
    (template : Context B) (borrowed : AllocatedHelperContext.borrow entries handle template = some ctx)
    (dummy : Digest) (history : List Observation)

/-- Original checked proof ownership and public-table compatibility are tied
to one accepted receipt at its actual ordinal. The parameter-store handle is
retained rather than recovered by equality-search over completed codes. -/
def Owned (checked : NativeSharedLookupGuard.Checked) : Prop :=
  ∃ (entry : Entry) (found : entries[handle]? = some entry) (good : NativeGoldParameterStore.GoodEntry entry)
    (parameters : ctx.helper = entry.initialized.parameters) (receipt : Receipt Memory) (member : receipt ∈ after.receipts),
    after.receipts[checked.ordinal]? = some receipt ∧
    receipt.call.query = plan.query ∧ ctx.proof.roots.val[checked.ordinal]? = some receipt.call.root ∧
    ctx.proof.helperOpenings.val[checked.ordinal]? = some receipt.call.opening ∧
    receipt.call.values.val.map NativeFieldRepresentation.goldValue = List.ofFn
      (NativeHelperPacking.coefficients NativeExtensionFields.goldilocksBasis ctx.helper.width.val
        (NativeFieldWire.goldExtensionValue checked.sumClaim.expected)) ∧
    let candidate := NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call
    let original := HelperPublicSource.context ctx entry receipt.call.root
    let candidateOrigin := AllocatedSingleOpeningOrigin.helperReceipt entries reachable handle entry found ctx parameters receipt
    let prepared := HelperOpeningObligationLifetime.prepared ctx choose memory world body plan after executed receipt member
    ∃ sizes : GoldHistorySourceTable.Geometry original.parameters,
      HelperPublicSource.Compatible candidate original candidateOrigin (HelperPublicSource.origin ctx entry good receipt.call.root)
        world receipt.work prepared dummy history sizes

include executed borrowed

theorem checked_owned (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ body.terminal.checked) :
    Owned ctx choose memory world body plan after executed entries reachable handle dummy history checked := by
  obtain ⟨entry,found,good,parameters⟩ := AllocatedHelperContext.helper_parameters entries reachable handle template ctx borrowed
  obtain ⟨receipt,atReceipt,receiptMember,query,_,root,opening,value,_⟩ :=
    LookupHelperClaimMeaning.checked_receipt ctx choose memory world body plan after executed checked member
  have encoded : receipt.call.values.val.map NativeFieldRepresentation.goldValue = List.ofFn
      (NativeHelperPacking.coefficients NativeExtensionFields.goldilocksBasis ctx.helper.width.val
        (NativeFieldWire.goldExtensionValue checked.sumClaim.expected)) := by
    rw [value,NativeGoldHelper.vector_value]
    rfl
  refine ⟨entry,found,good,parameters,receipt,receiptMember,atReceipt,query,root,opening,encoded,?_⟩
  let candidate := NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call
  let original := HelperPublicSource.context ctx entry receipt.call.root
  have same : candidate.parameters = original.parameters := parameters
  let prepared := HelperOpeningObligationLifetime.prepared ctx choose memory world body plan after executed receipt receiptMember
  exact ⟨HelperPublicSource.geometry candidate original same world receipt.work prepared,
    HelperPublicSource.compatible candidate original _ _ same rfl world receipt.work prepared dummy history⟩

theorem all_checked_owned : ∀ checked ∈ body.terminal.checked,
    Owned ctx choose memory world body plan after executed entries reachable handle dummy history checked :=
  fun checked member => checked_owned ctx choose memory world body plan after executed entries reachable handle template borrowed dummy history checked member

end
end FormalProof4FHE.HasteBoots.HelperPublicOwnership
