import Aeneas.Std
import FormalProof4FHE.HasteBoots.NativePointerRepresentation

/-! Address/provenance/metadata preserving raw casts. No allocator, dereference,
nonnull constructor, exposed-provenance recovery or work charge is supplied. -/
namespace HasteBootsPointerRuntime
open Aeneas Aeneas.Std
abbrev RawPtr := FormalProof4FHE.HasteBoots.NativeRawPointer.RawPtr
abbrev MutRawPtr (T : Type) := RawPtr T true
abbrev ConstRawPtr (T : Type) := RawPtr T false

abbrev equal := @FormalProof4FHE.HasteBoots.NativeRawPointer.equal
abbrev different := @FormalProof4FHE.HasteBoots.NativeRawPointer.different

def mutableFlag : Mutability → Bool
  | .Mut => true
  | .Const => false

def cast_scalar {T : Type} {mutable : Bool} (Target : Type) (targetMutability : Mutability)
    (pointer : RawPtr T mutable) : Result (RawPtr Target (mutableFlag targetMutability)) :=
  .ok (FormalProof4FHE.HasteBoots.NativeRawPointer.cast Target (mutableFlag targetMutability) pointer)

theorem cast_result {T : Type} {mutable : Bool} (Target : Type) (targetMutability : Mutability)
    (pointer : RawPtr T mutable) : cast_scalar Target targetMutability pointer =
      .ok ⟨pointer.storage, pointer.metadata⟩ := rfl

theorem cast_address {T : Type} {mutable : Bool} (Target : Type) (targetMutability : Mutability)
    (pointer : RawPtr T mutable) :
    (do let result ← cast_scalar Target targetMutability pointer; pure result.storage.address) =
      Result.ok pointer.storage.address := rfl

theorem cast_provenance {T : Type} {mutable : Bool} (Target : Type) (targetMutability : Mutability)
    (pointer : RawPtr T mutable) :
    (do let result ← cast_scalar Target targetMutability pointer; pure result.storage.provenance) =
      Result.ok pointer.storage.provenance := rfl

theorem cast_metadata {T : Type} {mutable : Bool} (Target : Type) (targetMutability : Mutability)
    (pointer : RawPtr T mutable) :
    (do let result ← cast_scalar Target targetMutability pointer; pure result.metadata) =
      Result.ok pointer.metadata := rfl

end HasteBootsPointerRuntime
