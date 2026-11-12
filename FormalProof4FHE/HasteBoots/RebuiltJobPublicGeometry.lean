module
public import FormalProof4FHE.HasteBoots.RebuiltLookupExecution
public import FormalProof4FHE.HasteBoots.LookupValidatedPublicTable
@[expose] public section

/-! The original rebuilt execution supplies the public geometry of the
actual selected native job. Multiplicity shape follows independently from
its native proof checks and original request ordinal, never a reordered list. -/
namespace FormalProof4FHE.HasteBoots.RebuiltJobPublicGeometry
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeSharedLookupValues (Policy)
open NativeGoldHelperVerification (Context)
open NativeGoldBatchOpening (Opening)
open NativeFieldRepresentation (GoldWord)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

variable {Memory : Type} {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (policy : Policy) (requests : Vector Request) (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (RebuiltLookupExecution.program policy requests entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 =
      .allocated (.verification ctx result))
include executed

theorem selected (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) :
    NativeTupleLookupConfig.Spec (origin.ready.jobs.get index).tag.request.terminal.logicalLength
      (origin.ready.jobs.get index).tag.request.repetitions (origin.ready.jobs.get index).tag.request.table ∧
      (origin.ready.jobs.get index).tag.request.columns = NativeTupleLookupConfig.columns (origin.ready.jobs.get index).tag.request.table := by
  obtain ⟨_,_,_,_,valid,_⟩ := RebuiltLookupExecution.verification_origin policy requests entries helperHandle references template
    chooseHelper chooseBatch memory world ctx result executed
  have original := job.original
  rw [NativeSharedLookupParent.models_list] at original
  exact valid _ original

theorem rectangular (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) :
    ∀ row ∈ (origin.ready.jobs.get index).tag.request.table, row.length = (origin.ready.jobs.get index).tag.request.columns := by
  have spec := selected policy requests entries helperHandle references template chooseHelper chooseBatch memory result executed origin index job
  intro row member
  rw [spec.2]
  exact spec.1.rectangular row member

theorem logical_lt_characteristic (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) :
    (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val < NativeFields.goldilocksModulus :=
  NativeTupleLookupConfig.logical_lt_characteristic _ _ _
    (selected policy requests entries helperHandle references template chooseHelper chooseBatch memory result executed origin index job).1

theorem reciprocal_domain_positive (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) :
    0 < NativeFields.goldilocksModulus-(origin.ready.jobs.get index).tag.request.table.length-1 :=
  NativeTupleLookupConfig.reciprocal_domain_positive _ _ _
    (selected policy requests entries helperHandle references template chooseHelper chooseBatch memory result executed origin index job).1

omit executed in
theorem counts (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length) :
    ∃ counts, ctx.proof.values.multiplicities[(origin.ready.jobs.get index).tag.ordinal.val]? = some counts ∧
      counts.length = (origin.ready.jobs.get index).tag.request.table.length := by
  have contract := NativeSharedLookupPrelude.protocol_contract ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property
    7 ctx.lookupFuel ctx.equalityFuel _ world origin.ready origin.prepared
  have tagged : (origin.ready.jobs.get index).tag ∈ NativeSharedLookupStatement.tags ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests) := by
    rw [← (NativeSharedLookupPrepared.prepare_spec _ _ _ contract.prepared).1]
    exact List.mem_map.mpr ⟨origin.ready.jobs.get index,List.get_mem _ _,rfl⟩
  have requestAt := (NativeSharedLookupProofShape.tag_request ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests) _ tagged).2
  obtain ⟨counts,atCounts⟩ := NativeSharedLookupProofShape.multiplicity_getters ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    _ _ _ _ origin.shape _ _ contract.prepared _ (List.get_mem _ index)
  have shape := NativeSharedLookupProofShape.check_spec _ _ _ _ _ origin.shape
  obtain ⟨countsBound,countsValue⟩ := List.getElem?_eq_some_iff.mp atCounts
  obtain ⟨requestBound,requestValue⟩ := List.getElem?_eq_some_iff.mp requestAt
  have aligned := shape.multiplicities.get countsBound requestBound
  exact ⟨counts,atCounts,(congrArg List.length countsValue).symm.trans
    (aligned.trans (congrArg (fun request : NativeSharedLookupStatement.Request => request.table.length) requestValue))⟩

omit executed in
theorem counts_vector (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length) :
    ∃ counts : Fin (origin.ready.jobs.get index).tag.request.table.length → GoldWord,
      ctx.proof.values.multiplicities[(origin.ready.jobs.get index).tag.ordinal.val]? = some (List.ofFn counts) := by
  obtain ⟨values,atValues,length⟩ := counts origin index
  let vector : Fin (origin.ready.jobs.get index).tag.request.table.length → GoldWord := fun i => values[i.val]'(by rw [length]; exact i.isLt)
  have restored : List.ofFn vector = values := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using length.symm)
    intro i leftBound rightBound
    rw [List.getElem_ofFn]
  exact ⟨vector,by rw [restored]; exact atValues⟩

end
end FormalProof4FHE.HasteBoots.RebuiltJobPublicGeometry
