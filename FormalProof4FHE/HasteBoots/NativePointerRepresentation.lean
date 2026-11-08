module
public import Init
@[expose] public section

/-! Shared pointer data without a pointee-value surrogate. Provenance is ghost
allocation identity; metadata records thin/slice/vtable shape. This file provides
no allocation, dereference, borrow or Rust-validity theorem. -/
namespace FormalProof4FHE.HasteBoots.NativePointerStorage

abbrev Address := Fin (2 ^ 64)

structure Origin where
  allocation : Nat
  generation : Nat
  deriving DecidableEq

structure Pointer where
  address : Address
  provenance : Option Origin
  deriving DecidableEq

end FormalProof4FHE.HasteBoots.NativePointerStorage

namespace FormalProof4FHE.HasteBoots.NativeRawPointer
open NativePointerStorage (Address Pointer)

inductive Metadata where
  | thin
  | slice (length : Address)
  | vtable (pointer : Pointer)
  deriving DecidableEq

structure RawPtr (Pointee : Type) (mutable : Bool) where
  storage : Pointer
  metadata : Metadata
  deriving DecidableEq

def metadataWord : Metadata → Option Address
  | .thin => none
  | .slice length => some length
  | .vtable pointer => some pointer.address

/-- Rust pointer equality observes address/metadata bits, not ghost provenance. -/
def equal {Pointee : Type} {mutable : Bool} (left right : RawPtr Pointee mutable) : Bool :=
  decide (left.storage.address = right.storage.address ∧
    metadataWord left.metadata = metadataWord right.metadata)

def different {Pointee : Type} {mutable : Bool} (left right : RawPtr Pointee mutable) : Bool :=
  !equal left right

theorem equal_iff {Pointee : Type} {mutable : Bool} (left right : RawPtr Pointee mutable) :
    equal left right = true ↔ left.storage.address = right.storage.address ∧
      metadataWord left.metadata = metadataWord right.metadata := by
  simp only [equal, decide_eq_true_eq]


def cast {Pointee : Type} {mutable : Bool} (Target : Type) (newMutable : Bool)
    (pointer : RawPtr Pointee mutable) : RawPtr Target newMutable :=
  ⟨pointer.storage, pointer.metadata⟩

theorem cast_storage {Pointee : Type} {mutable : Bool} (Target : Type) (newMutable : Bool)
    (pointer : RawPtr Pointee mutable) :
    (cast Target newMutable pointer).storage = pointer.storage := rfl

theorem cast_metadata {Pointee : Type} {mutable : Bool} (Target : Type) (newMutable : Bool)
    (pointer : RawPtr Pointee mutable) :
    (cast Target newMutable pointer).metadata = pointer.metadata := rfl

theorem cast_identity {Pointee : Type} {mutable : Bool} (pointer : RawPtr Pointee mutable) :
    cast Pointee mutable pointer = pointer := by
  cases pointer
  rfl

theorem cast_compose {Pointee : Type} {mutable : Bool} (Middle Target : Type)
    (middleMutable newMutable : Bool) (pointer : RawPtr Pointee mutable) :
    cast Target newMutable (cast Middle middleMutable pointer) = cast Target newMutable pointer := rfl

theorem cast_injective {Pointee : Type} {mutable : Bool} (Target : Type) (newMutable : Bool) :
    Function.Injective (@cast Pointee mutable Target newMutable) := by
  intro left right same
  cases left
  cases right
  cases same
  rfl

end FormalProof4FHE.HasteBoots.NativeRawPointer
