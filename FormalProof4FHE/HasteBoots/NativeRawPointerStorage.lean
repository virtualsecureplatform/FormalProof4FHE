module
public import FormalProof4FHE.HasteBoots.NativePointerStorage
@[expose] public section

/-! Raw-pointer casts preserve the existing generation-aware logical registry.
This is not a Rust dereference, memory-layout or allocator refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeRawPointerStorage
open NativePointerStorage
open NativeRawPointer

def read {Value Pointee : Type} {mutable : Bool} (heap : List (Cell Value))
    (pointer : RawPtr Pointee mutable) : Option Value :=
  NativePointerStorage.read heap pointer.storage

theorem cast_read {Value Pointee : Type} {mutable : Bool} (heap : List (Cell Value))
    (Target : Type) (newMutable : Bool) (pointer : RawPtr Pointee mutable) :
    read heap (cast Target newMutable pointer) = read heap pointer := rfl

theorem read_without_origin {Value Pointee : Type} {mutable : Bool}
    (heap : List (Cell Value)) (pointer : RawPtr Pointee mutable)
    (absent : pointer.storage.provenance = none) : read heap pointer = none :=
  read_without_provenance heap pointer.storage absent

theorem read_zero {Value Pointee : Type} {mutable : Bool}
    (heap : List (Cell Value)) (pointer : RawPtr Pointee mutable)
    (zero : pointer.storage.address.val = 0) : read heap pointer = none :=
  read_null heap pointer.storage zero

theorem read_retired_origin {Value Pointee : Type} {mutable : Bool}
    (heap : List (Cell Value)) (origin : Origin) (pointer : RawPtr Pointee mutable)
    (same : pointer.storage.provenance = some origin) : read (retire heap origin) pointer = none :=
  read_retired heap origin pointer.storage same

end FormalProof4FHE.HasteBoots.NativeRawPointerStorage
