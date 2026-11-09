module
public import FormalProof4FHE.HasteBoots.NativeRawVecFields
@[expose] public section

-- Retained storage metadata bound to checked reads; no Rust body translation.
namespace HasteBootsRawVecFields
open FormalProof4FHE.HasteBoots
def sourceSize : Nat := 16
def sourceAlignment : Nat := 8
def capacityOffset : Nat := 0
def pointerOffset : Nat := 8
def capacityRead := NativeRawVecFields.capacity
def pointerRead := NativeRawVecFields.pointer
end HasteBootsRawVecFields
