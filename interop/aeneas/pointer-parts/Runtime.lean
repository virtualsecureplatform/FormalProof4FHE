/-! Raw pointer construction from address/provenance and checked metadata kinds.
These operations provide no allocation, borrow, dereference or physical-work rule. -/
namespace HasteBootsPointerPartsRuntime
open Aeneas Aeneas.Std
open FormalProof4FHE.HasteBoots.NativeRawPointer (RawPtr)

def from_thin_const (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (_metadata : Unit) : RawPtr Target false :=
  ⟨pointer.storage, .thin⟩

def from_thin_mut (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (_metadata : Unit) : RawPtr Target true :=
  ⟨pointer.storage, .thin⟩

def from_slice_const (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (length : U64) : RawPtr Target false :=
  ⟨pointer.storage, .slice length.bv.toFin⟩

def from_slice_mut (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (length : U64) : RawPtr Target true :=
  ⟨pointer.storage, .slice length.bv.toFin⟩

theorem thin_const_storage (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (metadata : Unit) :
    (from_thin_const Target pointer metadata).storage = pointer.storage := rfl

theorem thin_mut_storage (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (metadata : Unit) :
    (from_thin_mut Target pointer metadata).storage = pointer.storage := rfl

theorem slice_const_storage (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (length : U64) :
    (from_slice_const Target pointer length).storage = pointer.storage := rfl

theorem slice_mut_storage (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (length : U64) :
    (from_slice_mut Target pointer length).storage = pointer.storage := rfl

theorem slice_const_metadata (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (length : U64) :
    (from_slice_const Target pointer length).metadata = .slice length.bv.toFin := rfl

theorem slice_mut_metadata (Target : Type) {Data : Type} {mutable : Bool}
    (pointer : RawPtr Data mutable) (length : U64) :
    (from_slice_mut Target pointer length).metadata = .slice length.bv.toFin := rfl

theorem length_address_value (length : U64) : length.bv.toFin.val = length.val := rfl

theorem length_roundtrip (length : U64) : (⟨BitVec.ofFin length.bv.toFin⟩ : U64) = length := by
  cases length
  rfl

end HasteBootsPointerPartsRuntime
