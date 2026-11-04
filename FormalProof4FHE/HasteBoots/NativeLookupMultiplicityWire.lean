module

public import FormalProof4FHE.HasteBoots.NativeLookupRequestWire

@[expose] public section

/-!
# Grouped and flattened native multiplicity payloads

The two native messages retain their own vector headers. Flattening keeps
original row/entry order and raw lazy words. Checked packing exposes native
Vec allocation/encoding domains; it does not bound sampler retries or
attacker work. No independent flattened-vector certificate is accepted.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupMultiplicityWire

open NativeFieldRepresentation (GoldWord)
open NativeLookupRequestWire (Row Table rowCodec tableCodec)
open InputIndexedOracle (Input)

def group (values : List (List GoldWord)) (outer : values.length < 2^64)
    (inner : ∀ row ∈ values, row.length < 2^64) : Table :=
  ⟨values.attach.map (fun row => ⟨row.val,inner row.val row.property⟩),by
    rw [List.length_map,List.length_attach]; exact outer⟩

theorem group_values (values : List (List GoldWord)) (outer : values.length < 2^64)
    (inner : ∀ row ∈ values, row.length < 2^64) : (group values outer inner).values = values := by
  simp only [group,NativeLookupRequestWire.Table.values,List.map_map,Function.comp_def,List.attach_map_subtype_val]

structure Packet where
  groups : Table
  flatFits : groups.values.flatten.length < 2^64

def Packet.flat (packet : Packet) : Row := ⟨packet.groups.values.flatten,packet.flatFits⟩

def pack (values : List (List GoldWord)) : Option Packet :=
  if outer : values.length < 2^64 then
    if inner : ∀ row ∈ values, row.length < 2^64 then
      if flat : values.flatten.length < 2^64 then
        some ⟨group values outer inner,by rw [group_values]; exact flat⟩
      else none
    else none
  else none

def grouped (packet : Packet) : Input := tableCodec.encode packet.groups
def flattened (packet : Packet) : Input := rowCodec.encode packet.flat

theorem pack_spec (values : List (List GoldWord)) (packet : Packet) (success : pack values = some packet) :
    packet.groups.values = values ∧ packet.flat.val = values.flatten := by
  unfold pack at success
  split at success
  next outer =>
    split at success
    next inner =>
      split at success
      next flat =>
        have same := Option.some.inj success
        subst packet
        exact ⟨group_values values outer inner,congrArg List.flatten (group_values values outer inner)⟩
      next rejected => contradiction
    next rejected => contradiction
  next rejected => contradiction

theorem pack_complete (values : List (List GoldWord)) (outer : values.length < 2^64)
    (inner : ∀ row ∈ values, row.length < 2^64) (flat : values.flatten.length < 2^64) : ∃ packet, pack values = some packet := by
  unfold pack
  rw [dite_eq_left outer,dite_eq_left inner,dite_eq_left flat]
  exact ⟨_,rfl⟩

theorem grouped_encode (packet : Packet) : grouped packet =
    NativeUsizeMessage.encode ⟨packet.groups.val.length,packet.groups.property⟩ ++
      packet.groups.val.flatMap (fun row => NativeFieldWire.goldColumn row.val row.property) := rfl

theorem flattened_encode (packet : Packet) : flattened packet = NativeFieldWire.goldColumn packet.flat.val packet.flat.property := rfl

theorem grouped_prefix (packet : Packet) (suffix : Input) :
    tableCodec.read (grouped packet ++ suffix) = some (packet.groups,suffix) := tableCodec.read_encode _ _

theorem flattened_prefix (packet : Packet) (suffix : Input) :
    rowCodec.read (flattened packet ++ suffix) = some (packet.flat,suffix) := rowCodec.read_encode _ _

/-- The complete grouped payload identifies every original multiplicity row;
flattening alone deliberately forgets row boundaries. -/
theorem grouped_injective (left right : Packet) (same : grouped left = grouped right) : left.groups.values = right.groups.values := by
  have groups := tableCodec.encode_injective same
  rw [groups]

end FormalProof4FHE.HasteBoots.NativeLookupMultiplicityWire
