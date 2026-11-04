module

public import FormalProof4FHE.HasteBoots.NativeLookupMultiplicityWire

@[expose] public section

/-!
# One typed shared proof source and its terminal-value payload

These fields mirror the canonical shared Proof. Backend opening objects
remain opaque here and are not authenticated by this module. Constructed
native vectors retain encoding domains; strict proof-byte decoding remains
open. Initializer, validators and terminal binding project the same data.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupProofData

open NativePrefixCodec (Codec product vector)
open NativeLookupRequestWire (Table tableCodec)
open NativeLookupMultiplicityWire (Packet)
open NativeFieldWire (GoldExtension)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)

structure Proof (Single Batch : Type) where
  multiplicities : Packet
  roots : NativePrefixCodec.Vector Digest
  algebra : NativeScalarBatchPreflight.Proof
  sources : Table
  helpers : NativePrefixCodec.Vector GoldExtension
  sourceOpening : Batch
  helperOpenings : NativePrefixCodec.Vector Single

def Proof.values {S B : Type} (proof : Proof S B) : NativeSharedLookupProofShape.Values :=
  ⟨proof.multiplicities.groups.values,proof.roots.val,proof.helpers.val,proof.sources.values⟩

def terminalCodec : Codec (Table × NativePrefixCodec.Vector GoldExtension) :=
  product tableCodec (vector NativeScalarBatchWire.goldCodec)

def terminal {S B : Type} (proof : Proof S B) : Input := terminalCodec.encode (proof.sources,proof.helpers)

theorem terminal_encode {S B : Type} (proof : Proof S B) : terminal proof =
    tableCodec.encode proof.sources ++
      NativeUsizeMessage.encode ⟨proof.helpers.val.length,proof.helpers.property⟩ ++
      proof.helpers.val.flatMap NativeFieldWire.goldExtension := by
  change tableCodec.encode proof.sources ++
    (NativeUsizeMessage.encode ⟨proof.helpers.val.length,proof.helpers.property⟩ ++
      proof.helpers.val.flatMap NativeFieldWire.goldExtension) = _
  exact (List.append_assoc _ _ _).symm

theorem terminal_prefix {S B : Type} (proof : Proof S B) (suffix : Input) :
    terminalCodec.read (terminal proof ++ suffix) = some ((proof.sources,proof.helpers),suffix) := terminalCodec.read_encode _ _

theorem terminal_injective {S B T C : Type} (left : Proof S B) (right : Proof T C) (same : terminal left = terminal right) :
    left.sources = right.sources ∧ left.helpers = right.helpers :=
  Prod.mk.inj (terminalCodec.encode_injective same)

theorem multiplicities_raw {S B : Type} (proof : Proof S B) : proof.values.multiplicities = proof.multiplicities.groups.values := rfl

theorem opening_count_fits {S B : Type} (proof : Proof S B) : proof.helperOpenings.val.length < 2^64 := proof.helperOpenings.property

end FormalProof4FHE.HasteBoots.NativeSharedLookupProofData
