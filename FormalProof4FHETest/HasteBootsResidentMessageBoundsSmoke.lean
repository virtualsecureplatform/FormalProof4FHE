module
import all FormalProof4FHE.HasteBoots.ResidentCallerIdentityWork
import all FormalProof4FHE.HasteBoots.NativeByteRangeWrite
import all FormalProof4FHETest.HasteBootsRegistryAncestrySmoke

namespace HasteBootsResidentMessageBoundsSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input)
open NativePointerStorage (Pointer)
open NativeByteMemory (State)
open HasteBootsRegistryAncestrySmoke

/-- Use the actual checked allocation and bulk-write primitives. -/
def allocateWrite (message : Input) : Option (Pointer × State) := do
  let (pointer,allocated) ← NativeByteMemory.allocate NativeByteMemory.empty ⟨64,by decide⟩ ⟨message.length,1⟩
  let initialized ← NativeByteRangeWrite.storeRange allocated pointer 1 message
  pure (pointer,initialized)

def buffer (message : Input) (present : (allocateWrite message).isSome = true) : ResidentMessageBounds.Buffer message :=
  let pair := (allocateWrite message).get present
  ⟨pair.2,pair.1,⟨message.length,1⟩,by
    have executed := (Option.some_get present).symm
    change allocateWrite message = some pair at executed
    obtain ⟨⟨pointer,allocated⟩,_,later⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨initialized,stored,returned⟩ := Option.bind_eq_some_iff.mp later
    have same : (pointer,initialized) = pair := Option.some.inj returned
    rw [← same]
    exact NativeByteRangeWrite.storeRange_then_load allocated pointer 1 message initialized stored⟩

def binding : NativeCanonicalLookupWire.Binding := ⟨config,digest 0,⟨[(digest 0,root)],by decide⟩⟩

theorem requests_allocated : (allocateWrite (NativeLookupRequestWire.requestsCodec.encode requests)).isSome = true := by decide +kernel

theorem binding_allocated : (allocateWrite (NativeCanonicalLookupWire.payload binding)).isSome = true := by decide +kernel

theorem registry_allocated : (allocateWrite (NativeCanonicalLookupWire.sourcesCodec.encode expected)).isSome = true := by decide +kernel

def requestBuffer := buffer _ requests_allocated
def bindingBuffer := buffer _ binding_allocated
def registryBuffer := buffer _ registry_allocated

theorem original_binding : ParentBindingTrace.ForRequest description registry.val helper world request binding := by
  exact ⟨[⟨sourceA,root⟩],rfl,rfl,by decide +kernel,by decide +kernel⟩

theorem parent_domain : NativeLookupParentFraming.Domain registry.val requests := by
  refine ⟨ResidentMessageBounds.fits requestBuffer,?_⟩
  apply ResidentMessageBounds.calls_fit description registry.val helper world requests.val [binding]
  · exact .cons original_binding .nil
  · intro actual member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨bindingBuffer⟩

theorem complete_registry_fits : (NativeCanonicalLookupWire.sourcesCodec.encode expected).length < TranscriptFrame.lengthLimit :=
  ResidentMessageBounds.fits registryBuffer

theorem aliases_and_unused_slots_retained : expected.val.length = 3 ∧ expected.val[0]? = expected.val[1]? ∧
    expected.val[0]?.map Prod.fst ≠ expected.val[2]?.map Prod.fst := by decide +kernel

theorem oversized_layout_rejected : NativeByteRange.loadRange NativeByteMemory.empty ⟨⟨64,by decide⟩,none⟩ ⟨2^63,1⟩ = none := by decide +kernel

theorem byte_mutation_not_original :
    NativeByteRange.loadRange bindingBuffer.memory bindingBuffer.pointer bindingBuffer.layout ≠
      some (NativeCanonicalLookupWire.payload binding ++ [0]) := by
  rw [bindingBuffer.loaded]
  intro same
  have length := congrArg List.length (Option.some.inj same)
  simp only [List.length_append,List.length_cons,List.length_nil] at length
  omega

theorem lost_provenance_rejected :
    NativeByteRange.loadRange bindingBuffer.memory ⟨bindingBuffer.pointer.address,none⟩ bindingBuffer.layout = none :=
  NativeByteRange.positive_without_origin _ _ _ (by decide +kernel) rfl

def alteredBinding := {binding with helper := digest 1}

theorem altered_same_length : (NativeCanonicalLookupWire.payload alteredBinding).length =
    (NativeCanonicalLookupWire.payload binding).length := by decide +kernel

theorem altered_helper_not_original :
    NativeByteRange.loadRange bindingBuffer.memory bindingBuffer.pointer bindingBuffer.layout ≠
      some (NativeCanonicalLookupWire.payload alteredBinding) := by
  rw [bindingBuffer.loaded]
  intro equal
  have same := NativeCanonicalLookupWire.payload_injective binding alteredBinding (Option.some.inj equal)
  have value := congrArg (fun actual => actual.helper (0 : Fin 64)) same
  change (0 : InputIndexedOracle.Byte) = 1 at value
  contradiction

end HasteBootsResidentMessageBoundsSmoke
