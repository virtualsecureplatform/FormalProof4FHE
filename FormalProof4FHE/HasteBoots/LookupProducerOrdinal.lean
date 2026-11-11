module
public import FormalProof4FHE.HasteBoots.LookupExecutionJob
public import FormalProof4FHE.HasteBoots.LookupScheduleKeys
@[expose] public section

/-! The retained original producer occupies exactly its prepared-job ordinal.
Native completion ordering and unique request/repetition keys discharge the
index association without an independent producer-position certificate. -/
namespace FormalProof4FHE.HasteBoots.LookupProducerOrdinal
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeSharedLookupBody (Bound)
open LookupExecutionOrigin (Origin childStart)
noncomputable section

variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : Bound}


theorem producer_at (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index) :
    (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
        (childStart row registry helper parent requests proof world)) world).1.completed[index.val]? = some job.view.producer := by
  have contract := NativeSharedLookupPrelude.protocol_contract requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared
  obtain ⟨transcript,finished,_,_⟩ := contract.lookup
  have ordered := NativeSharedLookupStatement.finished_jobs requests.property.le (models requests) 7 lookupFuel
    (childStart row registry helper parent requests proof world) world transcript finished
  have prepared := (NativeSharedLookupPrepared.prepare_spec _ _ _ contract.prepared).1
  have mapped := congrArg (List.map LookupScheduleKeys.jobKey) ordered
  simp only [List.map_map,Function.comp_def] at mapped
  have keysEqual :
      ((NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
          (childStart row registry helper parent requests proof world)) world).1.completed.map
            (fun entry => LookupScheduleKeys.jobKey entry.job)) =
        origin.ready.jobs.map (fun entry => LookupScheduleKeys.tagKey entry.tag) := by
    rw [mapped,← prepared,List.map_map]
    rfl
  apply LookupScheduleKeys.get_of_key _ (fun entry => LookupScheduleKeys.jobKey entry.job)
    (LookupScheduleKeys.completed_nodup requests.property.le (models requests) 7 lookupFuel
      (childStart row registry helper parent requests proof world) world transcript finished) index.val _ job.producerMember
  rw [keysEqual,List.getElem?_map,List.getElem?_eq_getElem index.isLt,Option.map_some]
  rw [job.producerJob]
  rfl

end
end FormalProof4FHE.HasteBoots.LookupProducerOrdinal
