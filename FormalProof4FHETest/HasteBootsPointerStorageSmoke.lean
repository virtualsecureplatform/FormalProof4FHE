module
import all FormalProof4FHE.HasteBoots.NativePointerStorage

namespace HasteBootsPointerStorageSmoke
open FormalProof4FHE.HasteBoots.NativePointerStorage

private def old : Cell ℕ := ⟨⟨9, 0⟩, ⟨64, by decide⟩, by decide, 11⟩
private def fresh : Cell ℕ := ⟨⟨9, 1⟩, ⟨64, by decide⟩, by decide, 29⟩

example : read [old] (pointer old) = some 11 := by rfl

example : old.address = fresh.address ∧ old.origin ≠ fresh.origin := by decide

example : read (fresh :: retire [old] old.origin) (pointer old) = none :=
  reused_address_stale [old] old fresh (by decide)

example : read (fresh :: retire [old] old.origin) (pointer fresh) = some 29 :=
  reused_address_fresh [old] old fresh

example : NonNull ⟨old.address, none⟩ ∧ read [old] ⟨old.address, none⟩ = none :=
  ⟨old.nonzero, read_without_provenance [old] _ rfl⟩

example : read [old] (readdress (pointer old) ⟨128, by decide⟩) = none := by rfl

example : read [old] (readdress (pointer old) ⟨0, by decide⟩) = none := by rfl

example : read (retire [old, fresh] old.origin) (pointer fresh) = some 29 :=
  read_retire_other [old, fresh] old.origin (pointer fresh) (by decide)

end HasteBootsPointerStorageSmoke
