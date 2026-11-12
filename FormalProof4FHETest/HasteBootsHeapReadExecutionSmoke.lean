module
import all FormalProof4FHE.HasteBoots.SequencedInputIdentityWork
import all FormalProof4FHETest.HasteBootsResidentMessageBoundsSmoke
import all FormalProof4FHETest.HasteBootsProofReadSizeSmoke

namespace HasteBootsHeapReadExecutionSmoke
open FormalProof4FHE.HasteBoots
open NativeReferenceMachine (Op)
open HeapReadExecution (Execution Observation)
open HasteBootsResidentMessageBoundsSmoke (binding)
open HasteBootsSharedProofBytesSmoke (proof)
open HasteBootsProofReadSizeSmoke (wider wider_with_suffix)

def proofBytes := wider ++ [99,100]
def bindingBytes := NativeCanonicalLookupWire.payload binding
def registryBytes := NativeCanonicalLookupWire.sourcesCodec.encode binding.sources

def proofSetup : List Op := [.raw (.allocate 64 ⟨proofBytes.length,1⟩),.raw (.writeBytes 0 1 proofBytes),.borrow 0 .shared ⟨proofBytes.length,1⟩]
def bindingSetup : List Op := [.raw (.allocate 1024 ⟨bindingBytes.length,1⟩),.raw (.writeBytes 0 1 bindingBytes),.borrow 0 .shared ⟨bindingBytes.length,1⟩]
def registrySetup : List Op := [.raw (.allocate 2048 ⟨registryBytes.length,1⟩),.raw (.writeBytes 0 1 registryBytes),.borrow 0 .shared ⟨registryBytes.length,1⟩]
def proofRead : Op := .access 0 0 (.read proofBytes.length 1)
def bindingRead : Op := .access 0 0 (.read bindingBytes.length 1)
def registryRead : Op := .access 0 0 (.read registryBytes.length 1)
def operations := proofSetup ++ [proofRead] ++ bindingSetup ++ [bindingRead] ++ registrySetup ++ [registryRead]
def result := NativeReferenceMachine.run NativeReferenceMachine.empty operations

theorem executed : result.isSome = true := by decide +kernel

def execution : Execution := ⟨operations,result.get executed,(Option.some_get executed).symm⟩

def proofObservation : Observation execution proofBytes :=
  ⟨proofSetup,bindingSetup++[bindingRead]++registrySetup++[registryRead],0,0,proofBytes.length,1,
    by simp only [execution,operations,List.append_assoc,List.singleton_append]; rfl,by decide +kernel⟩

def bindingObservation : Observation execution bindingBytes :=
  ⟨proofSetup++[proofRead]++bindingSetup,registrySetup++[registryRead],0,0,bindingBytes.length,1,
    by simp only [execution,operations,List.append_assoc,List.singleton_append]; rfl,by decide +kernel⟩

def registryObservation : Observation execution registryBytes :=
  ⟨proofSetup++[proofRead]++bindingSetup++[bindingRead]++registrySetup,[],0,0,registryBytes.length,1,rfl,by decide +kernel⟩

noncomputable def proofBuffer := proofObservation.buffer

theorem proof_from_actual_read : ResidentProofDecode.read proofBuffer.memory proofBuffer.pointer proofBuffer.layout = some (proof,[99,100]) :=
  (ResidentProofDecode.read_iff _ _ _ _ _).mpr ⟨proofBytes,proofBuffer.loaded,wider_with_suffix⟩

theorem binding_frame_fits : (NativeCanonicalLookupWire.payload binding).length < TranscriptFrame.lengthLimit :=
  bindingObservation.fits

theorem registry_frame_fits : registryBytes.length < TranscriptFrame.lengthLimit := registryObservation.fits

theorem original_read_size : proofBytes.length = proofObservation.size := proofObservation.length_eq

theorem source_prefix_reachable : ∃ before,
    NativeReferenceMachine.run NativeReferenceMachine.empty proofObservation.earlierOps = some before ∧
      NativeReferenceMachine.Reachable before := proofObservation.prefix_reachable

theorem all_read_outputs : execution.finalState.outputs = [registryBytes,bindingBytes,proofBytes] := by decide +kernel

theorem later_output_not_proof : execution.finalState.outputs.head? ≠ some proofBytes := by decide +kernel

theorem revoked_read_rejected : NativeReferenceMachine.run NativeReferenceMachine.empty
    (operations++[.endBorrow 2,.access 2 0 (.read proofBytes.length 1)]) = none := by decide +kernel

end HasteBootsHeapReadExecutionSmoke
