module
public import FormalProof4FHE.HasteBoots.OpeningReceiptProofSource
@[expose] public section

/-! The actual retained native job carries its decoded proof buffer.
Response-size bounds follow from original receipt positions and that buffer;
no independent source/helper response-size certificates are supplied. -/
namespace FormalProof4FHE.HasteBoots.DecodedAllocatedJob
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
  sourceFraming : ∀ receipt ∈ after.receipts, NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
  helperFraming : ∀ receipt ∈ lookup.helpers.receipts,
    SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call)
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

def toCanonical (data : Job (Memory := Memory) ctx allocation program world) :
    CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world :=
  ⟨data.chooseHelper,data.chooseBatch,data.memory,data.lookup,data.progress,data.after,data.executed,
    data.origin,data.index,data.job,data.geometry,data.observed,data.sourceFraming,
    OpeningReceiptProofSource.source_response_fits ctx data.chooseHelper data.chooseBatch data.memory world data.lookup data.progress data.after data.executed (domain data),
    data.helperFraming,
    OpeningReceiptProofSource.helper_response_fits ctx data.chooseHelper data.chooseBatch data.memory world data.lookup data.progress data.after data.executed (domain data)⟩

def ofCanonical (data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (proofBytes : Vector InputIndexedOracle.Byte) (rest : InputIndexedOracle.Input)
    (parsed : SharedProofByteCodec.codec.read proofBytes.val = some (ctx.proof,rest)) :
    Job (Memory := Memory) ctx allocation program world :=
  ⟨data.chooseHelper,data.chooseBatch,data.memory,data.lookup,data.progress,data.after,data.executed,
    data.origin,data.index,data.job,data.geometry,data.observed,data.sourceFraming,data.helperFraming,proofBytes,rest,parsed⟩

/-- Erasing redundant size proofs preserves every original canonical job field. -/
theorem toCanonical_ofCanonical (data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (proofBytes : Vector InputIndexedOracle.Byte) (rest : InputIndexedOracle.Input)
    (parsed : SharedProofByteCodec.codec.read proofBytes.val = some (ctx.proof,rest)) :
    toCanonical (ofCanonical data proofBytes rest parsed) = data := rfl

theorem ofCanonical_toCanonical (data : Job (Memory := Memory) ctx allocation program world) :
    ofCanonical (toCanonical data) data.proofBytes data.rest data.parsedProof = data := rfl

end
end FormalProof4FHE.HasteBoots.DecodedAllocatedJob
