module
public import FormalProof4FHE.HasteBoots.CollectedBatchFramingRecovery
@[expose] public section

/-! Caller framing and actual native collection/verification derive both
source and helper receipt framing. No receipt framing certificate is stored
in this retained decoded job. -/
namespace FormalProof4FHE.HasteBoots.CallerFramedAllocatedJob
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open OracleProgram (Program run)
open AllocatedFamilyFunctions (Allocation)
noncomputable section

structure Job {Memory A : Type} (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
    (program : Program A) (world : World) where
  chooseHelper : NativeGoldPcsProgram.Scheduler Memory
  chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory
  memory : Memory
  lookup : NativeGoldLookupVerification.Prepared Memory
  progress : NativeSharedSourceClaims.Progress
  after : NativeDeferredBatchVerification.Progress Memory
  executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
    .batches lookup progress (.verification (.done after))
  origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body
  index : Fin origin.ready.jobs.length
  job : LookupExecutionJob.Job origin index
  geometry : AllocatedLookupTables.Geometry origin index job
  observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist (run program world).run.2
  proofBytes : Vector InputIndexedOracle.Byte
  rest : InputIndexedOracle.Input
  parsedProof : SharedProofByteCodec.codec.read proofBytes.val = some (ctx.proof,rest)
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx} {program : Program A} {world : World}

theorem roots_nonempty (data : Job (Memory := Memory) ctx allocation program world) : ctx.proof.roots.val ≠ [] := by
  have contract := NativeSharedLookupPrelude.protocol_contract ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    data.origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property
    7 ctx.lookupFuel ctx.equalityFuel _ world data.origin.ready data.origin.prepared
  have count := contract.rootCount
  change ctx.proof.roots.val.length = data.origin.ready.jobs.length at count
  intro empty
  rw [empty,List.length_nil] at count
  have inside := data.index.isLt
  omega

theorem domain (data : Job (Memory := Memory) ctx allocation program world) : SharedProofSerializationDomain.Domain ctx.proof :=
  SharedProofSerializationDomain.of_length ctx.proof (roots_nonempty data)
    (SharedProofReadSize.canonical_fits data.proofBytes ctx.proof data.rest data.parsedProof)

def truth (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :=
  AllocatedIdentityAlternatives.truth data.origin data.index data.job
    (CanonicalAllocatedTables.sources allocation data.origin data.index data.job data.geometry dummy (run program world).run.2)
    (CanonicalAllocatedTables.helpers allocation data.origin data.index data.job data.geometry dummy (run program world).run.2)

def toParent (data : Job (Memory := Memory) ctx allocation program world) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (framed : NativeTranscriptFraming.Framed ctx.parent)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit) :
    ParentFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world :=
  ⟨data.chooseHelper,data.chooseBatch,data.memory,data.lookup,data.progress,data.after,data.executed,
    data.origin,data.index,data.job,data.geometry,data.observed,
    (CollectedBatchFramingRecovery.receipts_framed ctx data.chooseHelper data.chooseBatch data.memory world data.lookup data.progress data.after
      data.executed helperWidth (AllocatedSourceClaimFraming.allocated_small allocation sourceWidths) framed parentDomain registryFits (domain data)).2,
    data.proofBytes,data.rest,data.parsedProof⟩

def ofParent (data : ParentFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    Job (Memory := Memory) ctx allocation program world :=
  ⟨data.chooseHelper,data.chooseBatch,data.memory,data.lookup,data.progress,data.after,data.executed,
    data.origin,data.index,data.job,data.geometry,data.observed,data.proofBytes,data.rest,data.parsedProof⟩

variable (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (framed : NativeTranscriptFraming.Framed ctx.parent)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit)

theorem toParent_ofParent (data : ParentFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    toParent (ofParent data) helperWidth sourceWidths framed parentDomain registryFits = data := rfl

theorem ofParent_toParent (data : Job (Memory := Memory) ctx allocation program world) :
    ofParent (toParent data helperWidth sourceWidths framed parentDomain registryFits) = data := rfl

theorem truth_toParent (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :
    ParentFramedAllocatedJob.truth (toParent data helperWidth sourceWidths framed parentDomain registryFits) dummy = truth data dummy := rfl

end
end FormalProof4FHE.HasteBoots.CallerFramedAllocatedJob
