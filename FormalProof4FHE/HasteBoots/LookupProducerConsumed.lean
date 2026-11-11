module
public import FormalProof4FHE.HasteBoots.LookupExecutionJob
public import FormalProof4FHE.HasteBoots.LookupConsumedBatch
@[expose] public section

namespace FormalProof4FHE.HasteBoots.LookupProducerConsumed
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

theorem producer (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index) :
    LookupConsumedTrace.Lookup NativeFields.goldilocksModulus job.view.producer.selection := by
  exact LookupConsumedBatch.completed NativeExtensionFields.goldilocksBasis 7 lookupFuel _ _ world _ job.producerMember

end
end FormalProof4FHE.HasteBoots.LookupProducerConsumed
