module
public import FormalProof4FHE.HasteBoots.SingleHelperNativeValue
public import FormalProof4FHE.HasteBoots.NativeGoldLookupSourceInvariant
@[expose] public section

/-! Each checked outer sum obligation is tied to the accepted single-opening
helper receipt at its original ordinal. Field equality is used only for the
claim interpretation; original raw vectors, roots and openings are retained. -/
namespace FormalProof4FHE.HasteBoots.LookupHelperClaimMeaning
open NativeGoldHelperVerification (Context Receipt Progress)
open NativeFieldRepresentation (goldValue)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def point (body : NativeSharedLookupBody.Bound) (index : Fin body.terminal.point.length) :=
  body.terminal.point[index.val]

theorem point_list (body : NativeSharedLookupBody.Bound) : List.ofFn (point body) = body.terminal.point := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro index inside other
    simp only [List.getElem_ofFn,point]

variable {B Memory : Type} (ctx : Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (body : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (after : Progress Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers body plan (.done after))

include executed

theorem native_body : (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1 = some (.bound body) := by
  have origin := (NativeGoldHelperVerification.helpers_origin ctx choose memory world body plan (.done after) executed).native
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] at origin
  exact congrArg Prod.fst origin

theorem checked_helper (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ body.terminal.checked) :
    ctx.proof.helpers.val[checked.ordinal]? = some checked.helper ∧
      NativeGoldInterpolation.equal checked.sumClaim.expected checked.helper = true := by
  have native := native_body ctx choose memory world body plan after executed
  obtain ⟨geometry,launched,_,_,_,bodyRun⟩ := NativeSharedLookupExecution.bound_origin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world body native
  have contract := (NativeSharedLookupBody.body_bound (NativeSharedLookupParent.models ctx.requests) (ctx.registry.val.map NativeSharedLookupParent.Oracle.geometry)
    geometry.geometry.2.val launched.1 launched.2 ctx.proof ctx.scalarFuel world body bodyRun).2
  have evidence := (NativeSharedLookupGuard.guard_spec _ _ _ _ _ contract.guarded).checked checked member
  exact ⟨evidence.helper,evidence.matched⟩

/-- Acceptance supplies all getter bounds and the original receipt ordinal;
no independently supplied helper/root/opening association is needed. -/
theorem checked_receipt (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ body.terminal.checked) :
    ∃ receipt : Receipt Memory, after.receipts[checked.ordinal]? = some receipt ∧ receipt ∈ after.receipts ∧
      receipt.call.query = plan.query ∧ receipt.call.values = NativeSharedLookupHelpers.vector ctx.helper.width checked.helper ∧
      ctx.proof.roots.val[checked.ordinal]? = some receipt.call.root ∧
      ctx.proof.helperOpenings.val[checked.ordinal]? = some receipt.call.opening ∧
      receipt.call.values.val.map goldValue = (NativeGoldHelper.vector ctx.helper.width.val checked.sumClaim.expected).map goldValue ∧
      NativeGoldHelperVerification.Checked ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel world receipt := by
  have origin := NativeGoldHelperVerification.helpers_origin ctx choose memory world body plan (.done after) executed
  have native := native_body ctx choose memory world body plan after executed
  have geometry := NativeSharedLookupHelpers.completed_geometry NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world body native
  have helper := checked_helper ctx choose memory world body plan after executed checked member
  have helperBound := (List.getElem?_eq_some_iff.mp helper.1).1
  have rootBound : checked.ordinal < ctx.proof.roots.val.length := by rw [← geometry.2.2.2.1]; exact helperBound
  have openingBound : checked.ordinal < ctx.proof.helperOpenings.val.length := by rw [geometry.2.2.2.2]; exact rootBound
  let root := ctx.proof.roots.val[checked.ordinal]'rootBound
  let opening := ctx.proof.helperOpenings.val[checked.ordinal]'openingBound
  have rootAt : ctx.proof.roots.val[checked.ordinal]? = some root := List.getElem?_eq_getElem rootBound
  have openingAt : ctx.proof.helperOpenings.val[checked.ordinal]? = some opening := List.getElem?_eq_getElem openingBound
  have valueAt : plan.values.val[checked.ordinal]? = some (NativeSharedLookupHelpers.vector ctx.helper.width checked.helper) := by
    rw [origin.spec.vectors]
    simp only [NativeSharedLookupHelpers.values,List.getElem?_map,helper.1,Option.map_some]
  have callAt : plan.calls[checked.ordinal]? = some ⟨root,plan.query,NativeSharedLookupHelpers.vector ctx.helper.width checked.helper,opening⟩ := by
    rw [origin.spec.ordered]
    exact NativeSharedLookupHelpers.calls_get _ _ _ _ _ _ _ _ rootAt valueAt openingAt
  have ordered := (NativeGoldHelperVerification.helpers_order ctx choose memory world body plan after executed).1
  have mapped : (after.receipts[checked.ordinal]?).map Receipt.call =
      some ⟨root,plan.query,NativeSharedLookupHelpers.vector ctx.helper.width checked.helper,opening⟩ := by
    rw [← List.getElem?_map,ordered]
    exact callAt
  obtain ⟨receipt,receiptAt,callEq⟩ := Option.map_eq_some_iff.mp mapped
  have receiptMember := List.mem_of_getElem? receiptAt
  refine ⟨receipt,receiptAt,receiptMember,congrArg (fun call => call.query) callEq,
    congrArg (fun call => call.values) callEq,?_,?_,?_,?_⟩
  · rw [congrArg (fun call => call.root) callEq]; exact rootAt
  · rw [congrArg (fun call => call.opening) callEq]; exact openingAt
  · rw [congrArg (fun call => call.values) callEq]
    exact (SingleHelperNativeValue.matched_vector ctx.helper.width.val _ _ helper.2).symm
  · exact (NativeGoldHelperVerification.helpers_receipts ctx choose memory world body plan (.done after) executed receipt receiptMember).1

theorem query_models : plan.query.models = (NativeGoldCoefficientsQuery.built ctx.helper.width.val body.terminal.point).pairs := by
  have native := native_body ctx choose memory world body plan after executed
  have geometry := NativeSharedLookupHelpers.completed_geometry NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world body native
  have origin := NativeGoldHelperVerification.helpers_origin ctx choose memory world body plan (.done after) executed
  exact NativeGoldPcsWire.coefficientsQuery_models _ _ _ geometry.1 origin.spec.packed

/-- The nonempty native helper point has no post-map; its interpreted query
is exactly the abstract coefficient query at that original common point. -/
theorem query_meaning (padding : ℕ) (width : ctx.helper.width.val = 3 + padding) :
    NativeGoldCoefficientsQuery.interpret (3 + padding) body.terminal.point.length ⟨plan.query.models,none⟩ =
      some (ExtensionQuery.coefficientsQuery (padding := padding) NativeExtensionFields.goldilocksBasis
        (fun index => NativeFieldWire.goldExtensionValue (point body index))) := by
  have native := native_body ctx choose memory world body plan after executed
  have geometry := NativeSharedLookupHelpers.completed_geometry NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world body native
  have payload : (⟨plan.query.models,none⟩ : NativeGoldCoefficientsQuery.Query) =
      NativeGoldCoefficientsQuery.built ctx.helper.width.val body.terminal.point := by
    rw [query_models ctx choose memory world body plan after executed]
    cases points : body.terminal.point with
    | nil => have positive := geometry.2.2.1; simp only [points,List.length_nil,ne_eq,not_true_eq_false] at positive
    | cons head tail => rfl
  rw [payload,width]
  have shape : NativeGoldProjection.dimensions (3 + padding) = true := width ▸ geometry.1
  simpa only [point_list] using NativeGoldCoefficientsQuery.interpret_built (point body) shape

/-- The actual raw claim has the padded field value of the checked outer sum.
Canonical field aliases are never used to rewrite its native bytes. -/
theorem checked_padded (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ body.terminal.checked)
    (padding : ℕ) (width : ctx.helper.width.val = 3 + padding) :
    ∃ receipt : Receipt Memory, after.receipts[checked.ordinal]? = some receipt ∧ receipt ∈ after.receipts ∧
      receipt.call.query = plan.query ∧
      receipt.call.values.val.map goldValue = List.ofFn (PaddedExtension.encode (padding := padding)
        NativeExtensionFields.goldilocksBasis (NativeFieldWire.goldExtensionValue checked.sumClaim.expected)) ∧
      NativeGoldHelperVerification.Checked ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel world receipt := by
  obtain ⟨receipt,atReceipt,receiptMember,query,_,_,_,value,accepted⟩ :=
    checked_receipt ctx choose memory world body plan after executed checked member
  refine ⟨receipt,atReceipt,receiptMember,query,?_,accepted⟩
  rw [value,width,NativeGoldHelper.vector_value,NativeHelperPacking.vector,NativeHelperPacking.coefficients_padded]

/-- A wrong helper obligation from the outer terminal reduction is a wrong
field claim in the accepted original single-opening receipt at the same index. -/
theorem wrong_helper (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ body.terminal.checked)
    (padding : ℕ) (width : ctx.helper.width.val = 3 + padding)
    (table : MatrixFold.Cube body.terminal.point.length → Fin (3 + padding) → NativeFields.Goldilocks)
    (wrong : PaddedExtension.encode (padding := padding) NativeExtensionFields.goldilocksBasis
        (NativeFieldWire.goldExtensionValue checked.sumClaim.expected) ≠
      (ExtensionQuery.coefficientsQuery (padding := padding) NativeExtensionFields.goldilocksBasis
        (fun index => NativeFieldWire.goldExtensionValue (point body index))).query.fold table) :
    ∃ receipt : Receipt Memory, after.receipts[checked.ordinal]? = some receipt ∧ receipt ∈ after.receipts ∧
      receipt.call.query = plan.query ∧
      receipt.call.values.val.map goldValue ≠ List.ofFn
        ((ExtensionQuery.coefficientsQuery (padding := padding) NativeExtensionFields.goldilocksBasis
          (fun index => NativeFieldWire.goldExtensionValue (point body index))).query.fold table) ∧
      NativeGoldHelperVerification.Checked ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel world receipt := by
  obtain ⟨receipt,atReceipt,receiptMember,query,value,accepted⟩ := checked_padded ctx choose memory world body plan after executed checked member padding width
  refine ⟨receipt,atReceipt,receiptMember,query,?_,accepted⟩
  rw [value]
  exact fun same => wrong (List.ofFn_injective same)

end
noncomputable section

theorem prepared_helpers {Memory : Type}
    (ctx : Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (prepared : NativeGoldLookupVerification.Prepared Memory)
    (success : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared) :
    (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 =
      .helpers prepared.body prepared.plan (.done prepared.helpers) := by
  have erased : (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1.1 =
      (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 :=
    congrArg Prod.fst (NativeRegisteredLookup.helpers_erasure ctx choose memory world)
  have selected : (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1.1 =
      .helpers prepared.body prepared.plan (.done prepared.helpers) :=
    congrArg Prod.fst (NativeGoldLookupVerification.prepare_spec _ prepared success).1
  exact erased.symm.trans selected

/-- Direct bridge from the enclosing registered lookup's actual preparation.
The root and raw opening packet remain indexed by the checked job ordinal. -/
theorem lookup_checked_receipt {Memory : Type}
    (ctx : Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (prepared : NativeGoldLookupVerification.Prepared Memory)
    (success : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared)
    (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ prepared.body.terminal.checked) :
    ∃ receipt : Receipt Memory, prepared.helpers.receipts[checked.ordinal]? = some receipt ∧ receipt ∈ prepared.helpers.receipts ∧
      receipt.call.query = prepared.plan.query ∧ receipt.call.values = NativeSharedLookupHelpers.vector ctx.helper.width checked.helper ∧
      ctx.proof.roots.val[checked.ordinal]? = some receipt.call.root ∧
      ctx.proof.helperOpenings.val[checked.ordinal]? = some receipt.call.opening ∧
      receipt.call.values.val.map goldValue = (NativeGoldHelper.vector ctx.helper.width.val checked.sumClaim.expected).map goldValue ∧
      NativeGoldHelperVerification.Checked ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel world receipt :=
  checked_receipt ctx choose memory world prepared.body prepared.plan prepared.helpers
    (prepared_helpers ctx choose memory world prepared success) checked member

/-- The helper branch of the abstract terminal reduction reaches an actual
accepted helper receipt from the original enclosing lookup preparation. -/
theorem lookup_wrong_helper {Memory : Type}
    (ctx : Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (prepared : NativeGoldLookupVerification.Prepared Memory)
    (success : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared)
    (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ prepared.body.terminal.checked)
    (padding : ℕ) (width : ctx.helper.width.val = 3 + padding)
    (table : MatrixFold.Cube prepared.body.terminal.point.length → Fin (3 + padding) → NativeFields.Goldilocks)
    (wrong : PaddedExtension.encode (padding := padding) NativeExtensionFields.goldilocksBasis
        (NativeFieldWire.goldExtensionValue checked.sumClaim.expected) ≠
      (ExtensionQuery.coefficientsQuery (padding := padding) NativeExtensionFields.goldilocksBasis
        (fun index => NativeFieldWire.goldExtensionValue (point prepared.body index))).query.fold table) :
    ∃ receipt : Receipt Memory, prepared.helpers.receipts[checked.ordinal]? = some receipt ∧ receipt ∈ prepared.helpers.receipts ∧
      receipt.call.query = prepared.plan.query ∧
      receipt.call.values.val.map goldValue ≠ List.ofFn
        ((ExtensionQuery.coefficientsQuery (padding := padding) NativeExtensionFields.goldilocksBasis
          (fun index => NativeFieldWire.goldExtensionValue (point prepared.body index))).query.fold table) ∧
      NativeGoldHelperVerification.Checked ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel world receipt :=
  wrong_helper ctx choose memory world prepared.body prepared.plan prepared.helpers
    (prepared_helpers ctx choose memory world prepared success) checked member padding width table wrong

end
end FormalProof4FHE.HasteBoots.LookupHelperClaimMeaning
