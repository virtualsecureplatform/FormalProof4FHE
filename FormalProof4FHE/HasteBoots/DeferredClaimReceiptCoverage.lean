module
public import FormalProof4FHE.HasteBoots.NativeDeferredBatchAvailability
@[expose] public section

/-! A completely accepted deferred dispatcher authenticates every original
inserted query/value pair in its actual canonical group. Query and value
getters use one batch index; no independent receipt/index association is input. -/
namespace FormalProof4FHE.HasteBoots.DeferredClaimReceiptCoverage
open NativeDeferredOpeningBatch (Claim State groupClaims usedGroups)
open NativeDeferredBatchVerification (Context Receipt Progress)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem claim_group (state : State) (claim : Claim state.sources) (member : claim ∈ state.claims.val) :
    claim ∈ groupClaims state (NativeSourceRegistry.group state.sources claim.slot) := by
  apply List.mem_filter.mpr
  exact ⟨member,by simp⟩

theorem claim_used (state : State) (claim : Claim state.sources) (member : claim ∈ state.claims.val) :
    NativeSourceRegistry.group state.sources claim.slot ∈ usedGroups state := by
  have grouped := claim_group state claim member
  have nonempty : (groupClaims state (NativeSourceRegistry.group state.sources claim.slot)).isEmpty = false := by
    cases entries : groupClaims state (NativeSourceRegistry.group state.sources claim.slot) with
    | nil => rw [entries] at grouped; cases grouped
    | cons head tail => rfl
  apply List.mem_filter.mpr
  exact ⟨List.mem_finRange _,by rw [nonempty]; rfl⟩

theorem group_receipt {Memory : Type} (ctx : Context) (choose : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (after : Progress Memory)
    (executed : (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.1 = .verification (.done after))
    (group : Fin (NativeSourceRegistry.groupCount ctx.state.sources)) (used : group ∈ usedGroups ctx.state) :
    ∃ receipt : Receipt Memory, receipt ∈ after.receipts ∧ receipt.call.group = group.val := by
  have count := (NativeDeferredOpeningBatch.seal_spec ctx.state ctx.proof.val.length
    (NativeDeferredBatchVerification.program_trace ctx choose memory world (.done after) executed).1).1
  obtain ⟨position,atGroup⟩ := List.mem_iff_get.mp used
  have openingBound : position.val < ctx.proof.val.length := by rw [count]; exact position.isLt
  let opening := ctx.proof.val[position.val]'openingBound
  have zipBound : position.val < (((usedGroups ctx.state).map Fin.val).zip ctx.proof.val).length := by
    rw [List.length_zip,List.length_map,count,Nat.min_self]
    exact position.isLt
  have pairAt : (((usedGroups ctx.state).map Fin.val).zip ctx.proof.val)[position.val]? = some (group.val,opening) := by
    rw [List.getElem?_eq_getElem zipBound,List.getElem_zip,List.getElem_map]
    change some (((usedGroups ctx.state).get position).val,opening) = _
    rw [atGroup]
  have pairMember := List.mem_of_getElem? pairAt
  rw [← NativeDeferredBatchVerification.program_order ctx choose memory world after executed] at pairMember
  obtain ⟨receipt,member,same⟩ := List.mem_map.mp pairMember
  exact ⟨receipt,member,congrArg Prod.fst same⟩

/-- Both raw fields come from one original grouped claim and one native batch
index, including repeated queries and aliases of a registry source. -/
theorem claim_receipt {Memory : Type} (ctx : Context) (choose : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (after : Progress Memory)
    (executed : (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.1 = .verification (.done after))
    (claim : Claim ctx.state.sources) (member : claim ∈ ctx.state.claims.val) :
    ∃ receipt : Receipt Memory, receipt ∈ after.receipts ∧
      receipt.call.group = (NativeSourceRegistry.group ctx.state.sources claim.slot).val ∧
      receipt.call.slot = (NativeSourceRegistry.representative ctx.state.sources (NativeSourceRegistry.group ctx.state.sources claim.slot)).val ∧
      ctx.registry.val[receipt.call.slot]? = some receipt.call.oracle ∧
      ∃ index : Fin receipt.work.binding.queries.val.length,
        receipt.work.binding.queries.val[index.val]? = some claim.query ∧
        receipt.work.binding.values.val[index.val]? = some claim.values ∧
        NativeDeferredBatchVerification.Checked ctx.tables ctx.fieldFuel choose ctx.workerFuel world receipt := by
  let group := NativeSourceRegistry.group ctx.state.sources claim.slot
  obtain ⟨receipt,receiptMember,groupEq⟩ := group_receipt ctx choose memory world after executed group (claim_used ctx.state claim member)
  have owned := NativeDeferredBatchOwnership.program_owners ctx choose memory world (.done after) executed receipt receiptMember
  obtain ⟨actual,actualGroup,slot,found,queries,values,_⟩ := NativeDeferredBatchOwnership.original_spec ctx.registry ctx.state receipt.call owned
  have sameGroup : actual = group := Fin.ext (actualGroup.symm.trans groupEq)
  subst actual
  have grouped := claim_group ctx.state claim member
  obtain ⟨position,atClaim⟩ := List.mem_iff_get.mp grouped
  have groupedAt : (groupClaims ctx.state group)[position.val]? = some claim := by
    exact (List.getElem?_eq_getElem position.isLt).trans (congrArg some atClaim)
  have queryAt : receipt.call.queries.val[position.val]? = some claim.query := by
    rw [queries]
    simp only [NativeDeferredOpeningBatch.groupQueries,List.getElem?_map,groupedAt,Option.map_some]
  have valueAt : receipt.call.values.val[position.val]? = some claim.values := by
    rw [values]
    simp only [NativeDeferredOpeningBatch.groupValues,List.getElem?_map,groupedAt,Option.map_some]
  have checked := (NativeDeferredBatchVerification.program_receipts ctx choose memory world (.done after) executed receipt receiptMember).1
  have prepared := (NativeGoldBatchPcsProgram.completed_origin _ choose ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1).prepared
  have binding := NativeGoldBatchPcsProgram.prepared_binding _ world receipt.work prepared
  have workQuery : receipt.work.binding.queries.val[position.val]? = some claim.query := by rw [binding.2.2.1]; exact queryAt
  have workValue : receipt.work.binding.values.val[position.val]? = some claim.values := by rw [binding.2.2.2]; exact valueAt
  exact ⟨receipt,receiptMember,groupEq,slot,found,⟨position.val,(List.getElem?_eq_some_iff.mp workQuery).1⟩,workQuery,workValue,checked⟩

end
end FormalProof4FHE.HasteBoots.DeferredClaimReceiptCoverage
