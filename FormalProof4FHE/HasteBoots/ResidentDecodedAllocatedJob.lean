module
public import FormalProof4FHE.HasteBoots.ResidentProofDecode
@[expose] public section

/-! Retain the original native job and a successful checked heap-read/decode
operation. The proof source is recovered from that operation, rather than
supplied as a separate byte vector. -/
namespace FormalProof4FHE.HasteBoots.ResidentDecodedAllocatedJob
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
  proofMemory : NativeByteMemory.State
  proofPointer : NativePointerStorage.Pointer
  proofLayout : NativeByteMemory.Layout
  rest : InputIndexedOracle.Input
  readProof : ResidentProofDecode.read proofMemory proofPointer proofLayout = some (ctx.proof,rest)
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx} {program : Program A} {world : World}

def source (data : Job (Memory := Memory) ctx allocation program world) :=
  ResidentProofDecode.recover data.proofMemory data.proofPointer data.proofLayout ctx.proof data.rest data.readProof

def toCaller (data : Job (Memory := Memory) ctx allocation program world) :
    CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world :=
  ⟨data.chooseHelper,data.chooseBatch,data.memory,data.lookup,data.progress,data.after,data.executed,
    data.origin,data.index,data.job,data.geometry,data.observed,(source data).vector,data.rest,(source data).parsed⟩

def ofCaller (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (buffer : ResidentMessageBounds.Buffer data.proofBytes.val) : Job (Memory := Memory) ctx allocation program world :=
  ⟨data.chooseHelper,data.chooseBatch,data.memory,data.lookup,data.progress,data.after,data.executed,
    data.origin,data.index,data.job,data.geometry,data.observed,buffer.memory,buffer.pointer,buffer.layout,data.rest,
    (ResidentProofDecode.read_iff _ _ _ _ _).mpr ⟨data.proofBytes.val,buffer.loaded,data.parsedProof⟩⟩

theorem original_read (data : Job (Memory := Memory) ctx allocation program world) :
    NativeByteRange.loadRange data.proofMemory data.proofPointer data.proofLayout = some (toCaller data).proofBytes.val :=
  (source data).loaded

theorem bytes_ofCaller (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (buffer : ResidentMessageBounds.Buffer data.proofBytes.val) :
    (toCaller (ofCaller data buffer)).proofBytes = data.proofBytes := by
  apply Subtype.ext
  exact (source (ofCaller data buffer)).original_bytes _ buffer.loaded

theorem toCaller_ofCaller (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (buffer : ResidentMessageBounds.Buffer data.proofBytes.val) :
    toCaller (ofCaller data buffer) = data := by
  have same := bytes_ofCaller data buffer
  cases data
  unfold toCaller ofCaller at same ⊢
  congr 1

theorem consumed_bound (data : Job (Memory := Memory) ctx allocation program world) :
    (SharedProofByteCodec.codec.encode ctx.proof).length + data.rest.length ≤ data.proofLayout.size :=
  (source data).consumed_bound

theorem domain (data : Job (Memory := Memory) ctx allocation program world) : SharedProofSerializationDomain.Domain ctx.proof :=
  CallerFramedAllocatedJob.domain (toCaller data)

def truth (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :=
  AllocatedIdentityAlternatives.truth data.origin data.index data.job
    (CanonicalAllocatedTables.sources allocation data.origin data.index data.job data.geometry dummy (run program world).run.2)
    (CanonicalAllocatedTables.helpers allocation data.origin data.index data.job data.geometry dummy (run program world).run.2)

theorem truth_toCaller (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :
    CallerFramedAllocatedJob.truth (toCaller data) dummy = truth data dummy := rfl

theorem truth_ofCaller (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (buffer : ResidentMessageBounds.Buffer data.proofBytes.val) (dummy : Digest) :
    truth (ofCaller data buffer) dummy = CallerFramedAllocatedJob.truth data dummy := rfl

end
end FormalProof4FHE.HasteBoots.ResidentDecodedAllocatedJob
