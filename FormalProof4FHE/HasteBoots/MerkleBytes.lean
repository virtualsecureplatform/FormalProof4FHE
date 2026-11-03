module

public import FormalProof4FHE.HasteBoots.MerkleOracle
public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
# Native Merkle byte-query framing

Internal nodes concatenate two fixed-width raw digest byte arrays, without a
tag or length prefix. Whole-column leaf inputs prepend the native ASCII domain
string to the serialized column. Node injectivity is proved here; leaf
injectivity reduces to the still-explicit column serializer contract.
The two byte-input roles need not have disjoint images.
-/

namespace FormalProof4FHE.HasteBoots.MerkleBytes

abbrev Digest (bytes : ℕ) := Fin bytes → UInt8

/-- Exactly the leaf domain string used by native `hash_column`. -/
def columnTag : List UInt8 := "HasteBoots/mw-column/v1".toUTF8.data.toList

def leafInput {Payload : Type} (serialize : Payload → List UInt8) (payload : Payload) : List UInt8 :=
  columnTag ++ serialize payload

/-- Raw, ordered digest concatenation, as in native `MerkleTree::check`. -/
def nodeInput {bytes : ℕ} (children : Digest bytes × Digest bytes) : List UInt8 :=
  List.ofFn children.1 ++ List.ofFn children.2

theorem nodeInput_length {bytes : ℕ} (children : Digest bytes × Digest bytes) :
    (nodeInput children).length = 2 * bytes := by
  simp only [nodeInput, List.length_append, List.length_ofFn, two_mul]

/-- Fixed digest widths make ordered node concatenation unambiguous. -/
theorem nodeInput_injective (bytes : ℕ) : Function.Injective (@nodeInput bytes) := by
  intro first second equal
  have parts := List.append_inj equal (by simp only [List.length_ofFn])
  exact Prod.ext (List.ofFn_injective parts.1) (List.ofFn_injective parts.2)

/-- The native fixed leaf prefix preserves serializer injectivity. -/
theorem leafInput_injective {Payload : Type} (serialize : Payload → List UInt8)
    (injective : Function.Injective serialize) : Function.Injective (leafInput serialize) := by
  intro first second equal
  exact injective (List.append_cancel_left equal)

/-- Native shared byte domain, with no artificial node tag or role separation. -/
def encoding {Payload : Type} (bytes : ℕ) (serialize : Payload → List UInt8)
    (injective : Function.Injective serialize) :
    MerkleOracle.Encoding (List UInt8) (Digest bytes) Payload where
  leaf _ := leafInput serialize
  node _ := nodeInput
  leaf_injective _ := leafInput_injective serialize injective
  node_injective _ := nodeInput_injective bytes

end FormalProof4FHE.HasteBoots.MerkleBytes
