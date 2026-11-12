module
public import FormalProof4FHE.HasteBoots.HeapReadExecution
@[expose] public section

/-! One complete reference-machine execution supplies all original serialized
caller messages and proof input. No independently selected heap states remain
in this input realization interface. Rust execution correspondence is separate. -/
namespace FormalProof4FHE.HasteBoots.SequencedCallerInputs
open NativeGoldHelperVerification (Context)
open NativeGoldBatchOpening (Opening)
open NativePrefixCodec (Vector)
open InputIndexedOracle (World)
open HeapReadExecution (Execution Observation)
noncomputable section

variable {Memory A : Type} {ctx : Context (Vector Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A} {world : World}

structure Inputs (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) where
  execution : Execution
  requests : Observation execution (NativeLookupRequestWire.requestsCodec.encode ctx.requests)
  bindings : ∀ binding ∈ CallerSerializationOrigin.bindings data,
    Nonempty (Observation execution (NativeCanonicalLookupWire.payload binding))
  registry : Observation execution (NativeCanonicalLookupWire.sourcesCodec.encode (CallerSerializationOrigin.sources data))
  proof : Observation execution data.proofBytes.val

def Inputs.buffers {data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world} (inputs : Inputs data) :
    CallerSerializationOrigin.Buffers data :=
  ⟨inputs.requests.buffer,fun binding member =>
    ⟨(Classical.choice (inputs.bindings binding member)).buffer⟩,inputs.registry.buffer⟩

def Inputs.proofSource {data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world} (inputs : Inputs data) :
    ResidentMessageBounds.Buffer data.proofBytes.val := inputs.proof.buffer

theorem Inputs.proof_decoded {data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world} (inputs : Inputs data) :
    ResidentProofDecode.read inputs.proofSource.memory inputs.proofSource.pointer inputs.proofSource.layout = some (ctx.proof,data.rest) :=
  (ResidentProofDecode.read_iff _ _ _ _ _).mpr ⟨data.proofBytes.val,inputs.proofSource.loaded,data.parsedProof⟩

theorem Inputs.parent_domain {data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world} (inputs : Inputs data) :
    NativeLookupParentFraming.Domain ctx.registry.val ctx.requests :=
  CallerSerializationOrigin.parent_domain data inputs.buffers

end
end FormalProof4FHE.HasteBoots.SequencedCallerInputs
