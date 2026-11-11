module
public import FormalProof4FHE.HasteBoots.AllocatedScalarFamily
@[expose] public section

/-! Original request/repetition tags and source selectors at a native job
ordinal are determined by the original request vector. Actual producer values
do not choose a replacement request or permute duplicate source addresses. -/
namespace FormalProof4FHE.HasteBoots.OriginalJobOrdinal
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
noncomputable section

def requestTags (requests : Vector Request) : List NativeSharedLookupStatement.Tagged :=
  NativeSharedLookupStatement.tags requests.property.le (NativeSharedLookupParent.models requests)

theorem tags {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) :
    origin.ready.jobs.map NativeSharedLookupStatement.Prepared.tag = requestTags ctx.requests := by
  have contract := NativeSharedLookupPrelude.protocol_contract ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property 7 ctx.lookupFuel ctx.equalityFuel
    (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world)
    world origin.ready origin.prepared
  exact (NativeSharedLookupPrepared.prepare_spec _ _ _ contract.prepared).1

variable {leftCtx rightCtx : Context (Vector Opening)} {world other : World}
    {leftBody rightBody : NativeSharedLookupBody.Bound}
    (left : AllocatedLookupIdentity.NativeOrigin leftCtx world leftBody)
    (right : AllocatedLookupIdentity.NativeOrigin rightCtx other rightBody)

theorem tag_lists (requests : leftCtx.requests = rightCtx.requests) :
    left.ready.jobs.map NativeSharedLookupStatement.Prepared.tag = right.ready.jobs.map NativeSharedLookupStatement.Prepared.tag :=
  (tags left).trans ((congrArg requestTags requests).trans (tags right).symm)

theorem count (requests : leftCtx.requests = rightCtx.requests) : left.ready.jobs.length = right.ready.jobs.length := by
  have length := congrArg List.length (tag_lists left right requests)
  simpa only [List.length_map] using length

theorem tag (requests : leftCtx.requests = rightCtx.requests)
    (leftIndex : Fin left.ready.jobs.length) (rightIndex : Fin right.ready.jobs.length) (ordinal : leftIndex.val = rightIndex.val) :
    (left.ready.jobs.get leftIndex).tag = (right.ready.jobs.get rightIndex).tag := by
  have atLeft : (left.ready.jobs.map NativeSharedLookupStatement.Prepared.tag)[leftIndex.val]? = some (left.ready.jobs.get leftIndex).tag := by
    rw [List.getElem?_map,List.getElem?_eq_getElem leftIndex.isLt]
    rfl
  have atRight : (right.ready.jobs.map NativeSharedLookupStatement.Prepared.tag)[rightIndex.val]? = some (right.ready.jobs.get rightIndex).tag := by
    rw [List.getElem?_map,List.getElem?_eq_getElem rightIndex.isLt]
    rfl
  have selected := congrArg (fun jobs : List NativeSharedLookupStatement.Tagged => jobs[leftIndex.val]?) (tag_lists left right requests)
  rw [atLeft,ordinal,atRight] at selected
  exact Option.some.inj selected

theorem request (requests : leftCtx.requests = rightCtx.requests)
    (leftIndex : Fin left.ready.jobs.length) (rightIndex : Fin right.ready.jobs.length) (ordinal : leftIndex.val = rightIndex.val) :
    (left.ready.jobs.get leftIndex).tag.request = (right.ready.jobs.get rightIndex).tag.request :=
  congrArg NativeSharedLookupStatement.Tagged.request (tag left right requests leftIndex rightIndex ordinal)

/-- The original registry fixes source row dimension and packing width for
both complete native executions, even before selecting a used column. -/
theorem dimensions (registry : leftCtx.registry = rightCtx.registry) :
    leftBody.sourceVariables = rightBody.sourceVariables ∧ left.padding = right.padding := by
  obtain ⟨first,head,_⟩ := left.source
  have nonempty : leftCtx.registry.val ≠ [] := by
    intro empty
    rw [empty,List.map_nil] at head
    contradiction
  have positive : 0 < leftCtx.registry.val.length := List.length_pos_iff.mpr nonempty
  have rightPositive : 0 < rightCtx.registry.val.length := by rw [← registry]; exact positive
  have entry := OriginalPackedFamily.entry_eq leftCtx.registry rightCtx.registry registry ⟨0,positive⟩ ⟨0,rightPositive⟩ rfl
  have leftDimensions := left.registry_dimensions ⟨0,positive⟩
  have rightDimensions := right.registry_dimensions ⟨0,rightPositive⟩
  have sourceRows := congrArg (fun entry => entry.parameters.numVariables.val) entry
  have width := congrArg (fun entry => entry.parameters.width.val) entry
  rw [leftDimensions.1,rightDimensions.1] at sourceRows
  rw [leftDimensions.2,rightDimensions.2] at width
  exact ⟨sourceRows,by omega⟩

theorem selectors (requests : leftCtx.requests = rightCtx.requests) (registry : leftCtx.registry = rightCtx.registry)
    (leftIndex : Fin left.ready.jobs.length) (rightIndex : Fin right.ready.jobs.length) (ordinal : leftIndex.val = rightIndex.val)
    (leftJob : LookupExecutionJob.Job left leftIndex) (rightJob : LookupExecutionJob.Job right rightIndex) :
    HEq leftJob.slots.slot rightJob.slots.slot :=
  OriginalPackedFamily.slots (congrArg (fun registry => registry.val.length) registry)
    (request left right requests leftIndex rightIndex ordinal) leftJob.slots rightJob.slots


theorem slot_ordinal {leftCount rightCount : ℕ} {leftRequest rightRequest : NativeSharedLookupStatement.Request}
    (count : leftCount = rightCount) (request : leftRequest = rightRequest)
    (left : LookupOriginalSlots.Slots leftCount leftRequest) (right : LookupOriginalSlots.Slots rightCount rightRequest)
    (leftColumn : Fin leftRequest.columns) (rightColumn : Fin rightRequest.columns) (column : leftColumn.val = rightColumn.val) :
    (left.slot leftColumn).val = (right.slot rightColumn).val := by
  subst rightCount
  subst rightRequest
  have same : left.slot = right.slot := eq_of_heq (OriginalPackedFamily.slots rfl rfl left right)
  have index : leftColumn = rightColumn := Fin.ext column
  rw [index,same]

end
end FormalProof4FHE.HasteBoots.OriginalJobOrdinal
