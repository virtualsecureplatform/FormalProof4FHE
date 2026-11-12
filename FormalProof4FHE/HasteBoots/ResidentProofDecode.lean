module
public import FormalProof4FHE.HasteBoots.ResidentCallerIdentityWork
@[expose] public section

/-! Shared-proof decoding consumes the exact bytes returned by a checked
heap read. This is the specified structural codec, not a Rust decoder proof. -/
namespace FormalProof4FHE.HasteBoots.ResidentProofDecode
open NativeByteMemory (State Layout)
open NativePointerStorage (Pointer)
open SharedProofByteCodec (Proof codec)
open InputIndexedOracle (Input Byte)
open NativePrefixCodec (Vector)

def read (memory : State) (pointer : Pointer) (layout : Layout) : Option (Proof × Input) :=
  (NativeByteRange.loadRange memory pointer layout).bind codec.read

theorem read_iff (memory : State) (pointer : Pointer) (layout : Layout) (proof : Proof) (rest : Input) :
    read memory pointer layout = some (proof,rest) ↔
      ∃ bytes, NativeByteRange.loadRange memory pointer layout = some bytes ∧ codec.read bytes = some (proof,rest) :=
  Option.bind_eq_some_iff

structure Source (memory : State) (pointer : Pointer) (layout : Layout) (proof : Proof) (rest : Input) where
  bytes : Input
  loaded : NativeByteRange.loadRange memory pointer layout = some bytes
  parsed : codec.read bytes = some (proof,rest)

theorem source_exists (memory : State) (pointer : Pointer) (layout : Layout) (proof : Proof) (rest : Input)
    (success : read memory pointer layout = some (proof,rest)) : Nonempty (Source memory pointer layout proof rest) := by
  obtain ⟨bytes,loaded,parsed⟩ := (read_iff memory pointer layout proof rest).mp success
  exact ⟨⟨bytes,loaded,parsed⟩⟩

noncomputable def recover (memory : State) (pointer : Pointer) (layout : Layout) (proof : Proof) (rest : Input)
    (success : read memory pointer layout = some (proof,rest)) : Source memory pointer layout proof rest :=
  Classical.choice (source_exists memory pointer layout proof rest success)

variable {memory : State} {pointer : Pointer} {layout : Layout} {proof : Proof} {rest : Input}

theorem Source.length_le (source : Source memory pointer layout proof rest) : source.bytes.length ≤ 2^63-1 :=
  ResidentMessageBounds.length_le ⟨memory,pointer,layout,source.loaded⟩

def Source.vector (source : Source memory pointer layout proof rest) : Vector Byte :=
  ⟨source.bytes,by have bound := source.length_le; norm_num at bound ⊢; omega⟩

theorem Source.consumed_bound (source : Source memory pointer layout proof rest) :
    (codec.encode proof).length + rest.length ≤ layout.size := by
  have bound := SharedProofReadSize.proof source.bytes proof rest source.parsed
  rw [NativeByteRange.loadRange_length memory pointer layout source.bytes source.loaded] at bound
  exact bound

theorem Source.original_bytes (source : Source memory pointer layout proof rest) (bytes : Input)
    (loaded : NativeByteRange.loadRange memory pointer layout = some bytes) : source.bytes = bytes :=
  Option.some.inj (source.loaded.symm.trans loaded)

theorem failed_load (memory : State) (pointer : Pointer) (layout : Layout)
    (failed : NativeByteRange.loadRange memory pointer layout = none) : read memory pointer layout = none := by
  rw [read,failed,Option.bind_none]

theorem failed_parse (memory : State) (pointer : Pointer) (layout : Layout) (bytes : Input)
    (loaded : NativeByteRange.loadRange memory pointer layout = some bytes) (failed : codec.read bytes = none) :
    read memory pointer layout = none := by
  rw [read,loaded,Option.bind_some,failed]

end FormalProof4FHE.HasteBoots.ResidentProofDecode
