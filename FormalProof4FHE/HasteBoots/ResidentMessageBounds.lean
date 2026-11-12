module
public import FormalProof4FHE.HasteBoots.StatementDerivedIdentityWork
public import FormalProof4FHE.HasteBoots.NativeByteRange
@[expose] public section

/-! Exact serialized-message reads supply frame allocation bounds. These
records expose original checked heap operands, not Rust serializer refinement. -/
namespace FormalProof4FHE.HasteBoots.ResidentMessageBounds
open InputIndexedOracle (Input)
open NativeCanonicalLookupWire (Source Binding)
open NativePrefixCodec (Vector)

structure Buffer (message : Input) where
  memory : NativeByteMemory.State
  pointer : NativePointerStorage.Pointer
  layout : NativeByteMemory.Layout
  loaded : NativeByteRange.loadRange memory pointer layout = some message

theorem length_le {message : Input} (buffer : Buffer message) : message.length ≤ 2^63-1 := by
  have length := NativeByteRange.loadRange_length buffer.memory buffer.pointer buffer.layout message buffer.loaded
  have bound := NativeByteRange.range_size_bound buffer.memory buffer.pointer buffer.layout message buffer.loaded
  omega

theorem fits {message : Input} (buffer : Buffer message) : message.length < TranscriptFrame.lengthLimit := by
  have bound := length_le buffer
  norm_num [TranscriptFrame.lengthLimit]
  omega

theorem sources_body_length (sources : Vector Source) :
    (sources.val.flatMap (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2)).length = 128*sources.val.length := by
  induction sources.val with
  | nil => rfl
  | cons entry tail ih => simp only [List.flatMap_cons,List.length_append,List.length_ofFn,List.length_cons,ih]; omega

theorem frame_budget (binding : Binding) :
    (NativeLookupRequestWire.configCodec.encode binding.config).length + 65 + (9+128*binding.sources.val.length) ≤
      (NativeCanonicalLookupWire.payload binding).length + 9 := by
  rw [NativeCanonicalLookupWire.payload]
  simp only [List.length_append,NativeByteCodec.digest_encode,List.length_ofFn]
  rw [NativeCanonicalLookupWire.sources_encode,List.length_append,sources_body_length]
  have degree : (NativeUsizeMessage.encode ⟨3,by decide⟩).length = 1 := rfl
  omega

theorem binding_fits (binding : Binding) (buffer : Buffer (NativeCanonicalLookupWire.payload binding)) :
    (NativeLookupRequestWire.configCodec.encode binding.config).length + 65 + (9+128*binding.sources.val.length) <
      TranscriptFrame.lengthLimit := by
  have budget := frame_budget binding
  have size := length_le buffer
  norm_num [TranscriptFrame.lengthLimit]
  omega

theorem calls_fit {C : Type} (row : NativeBrakedownContext.RowDescription C)
    (registry : List (NativeSharedLookupParent.Oracle C)) (helper : NativeBrakedownContext.Parameters C)
    (world : InputIndexedOracle.World) (requests : List NativeLookupRequestWire.Request)
    (bindings : List Binding)
    (related : List.Forall₂ (ParentBindingTrace.ForRequest row registry helper world) requests bindings)
    (buffers : ∀ binding ∈ bindings, Nonempty (Buffer (NativeCanonicalLookupWire.payload binding))) :
    NativeLookupParentFraming.CallsFit registry requests := by
  induction related with
  | nil => intro request member; cases member
  | @cons request binding requests bindings first rest ih =>
    intro actual member selected gathered
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨original,chosen,config,_,computed⟩ := first
      have same : original = selected := Option.some.inj (chosen.symm.trans gathered)
      subst original
      obtain ⟨buffer⟩ := buffers binding List.mem_cons_self
      have bound := binding_fits binding buffer
      rw [config,NativeCanonicalMessageBounds.contexts_length row selected world binding.sources.val computed] at bound
      exact bound
    · exact ih (fun binding member => buffers binding (List.mem_cons_of_mem _ member)) actual later selected gathered

end FormalProof4FHE.HasteBoots.ResidentMessageBounds
