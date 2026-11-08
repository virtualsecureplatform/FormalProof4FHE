module
public import FormalProof4FHE.HasteBoots.NativeSliceLLBC
@[expose] public section

/-! Select an existing shared zero-byte reference. No tag, pointer origin or
extent is accepted from the caller, and no loan is minted by this decoder. -/
namespace FormalProof4FHE.HasteBoots.NativeZstReference
open NativeReferenceMachine (State Reference)
open NativeSliceLLBC (Value)

def decode (world : State) (index : Nat) : Option Value :=
  world.references[index]?.bind (fun reference =>
    (NativeByteBorrow.lookup world.leases reference.tag).bind (fun lease =>
      if lease.mode = .shared ∧ lease.layout = ⟨0,1⟩ then
        some (.reference false reference ⟨0,by decide⟩)
      else none))

theorem decode_success (world : State) (index : Nat) (value : Value)
    (decoded : decode world index = some value) :
    ∃ reference lease, world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      lease.mode = .shared ∧ lease.layout = ⟨0,1⟩ ∧
      value = .reference false reference ⟨0,by decide⟩ := by
  simp only [decode, Option.bind_eq_some_iff] at decoded
  obtain ⟨reference, selected, lease, found, actual⟩ := decoded
  split at actual
  next valid => cases actual; exact ⟨reference,lease,selected,found,valid.1,valid.2,rfl⟩
  next => cases actual

theorem decode_complete (world : State) (index : Nat) (reference : Reference) (lease : NativeByteBorrow.Lease)
    (selected : world.references[index]? = some reference)
    (found : NativeByteBorrow.lookup world.leases reference.tag = some lease)
    (shared : lease.mode = .shared) (empty : lease.layout = ⟨0,1⟩) :
    decode world index = some (.reference false reference ⟨0,by decide⟩) := by
  simp only [decode, selected, Option.bind_some, found, shared, empty, and_self, ite_true]

theorem decode_registered (world : State) (index : Nat) (value : Value)
    (decoded : decode world index = some value) :
    ∃ reference, reference ∈ world.references ∧ value = .reference false reference ⟨0,by decide⟩ := by
  obtain ⟨reference,lease,selected,_,_,_,same⟩ := decode_success world index value decoded
  exact ⟨reference,List.mem_of_getElem? selected,same⟩

end FormalProof4FHE.HasteBoots.NativeZstReference
