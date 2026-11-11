module
public import FormalProof4FHE.HasteBoots.ParameterDecodingRadius
@[expose] public section

/-! Original public source/helper tables decoded at their own retained
parameter radii. Original slot addresses, geometry and padding are retained. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedTables
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open AllocatedFamilyFunctions (Allocation)
noncomputable section

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}

def sourceRadius (ctx : Context (Vector Opening)) (slot : Fin ctx.registry.val.length) : ℕ :=
  ParameterDecodingRadius.ofParameters (ctx.registry.val.get slot).parameters

def helperRadius (ctx : Context (Vector Opening)) : ℕ := ParameterDecodingRadius.ofParameters ctx.helper

def sourceAt (allocation : Allocation ctx) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (dummy : Digest) (history : List Observation) (slot : Fin ctx.registry.val.length)
    (sizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters) :=
  AllocatedFamilyFunctions.sourceAt allocation origin dummy history (sourceRadius ctx slot) slot sizes

def sources (allocation : Allocation ctx) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation) :=
  fun column => sourceAt allocation origin dummy history (job.slots.slot column) (geometry.source column)

def helpers (allocation : Allocation ctx) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation) :=
  AllocatedFamilyFunctions.helpers allocation origin index job geometry dummy history (helperRadius ctx)

theorem source_at_radius (allocation : Allocation ctx) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation)
    (column : Fin (origin.ready.jobs.get index).tag.request.columns) :
    sources allocation origin index job geometry dummy history column =
      AllocatedLookupTables.sources origin index job allocation.entries allocation.reachable allocation.helperHandle allocation.references
        allocation.template allocation.assembled geometry dummy history (sourceRadius ctx (job.slots.slot column)) column := rfl

theorem sources_alias (allocation : Allocation ctx) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation)
    (left right : Fin (origin.ready.jobs.get index).tag.request.columns) (same : job.slots.slot left = job.slots.slot right) :
    sources allocation origin index job geometry dummy history left = sources allocation origin index job geometry dummy history right := by
  have radii := congrArg (sourceRadius ctx) same
  simp only [source_at_radius]
  rw [← radii]
  exact AllocatedLookupTables.sources_alias origin index job allocation.entries allocation.reachable allocation.helperHandle allocation.references
    allocation.template allocation.assembled geometry dummy history (sourceRadius ctx (job.slots.slot left)) left right same

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedTables
