namespace HasteBootsPointerStorageProof
open Aeneas Aeneas.Std Result
open hasteboots_pointer_storage
open FormalProof4FHE.HasteBoots
open NativePointerStorage (Address Origin Pointer)
open NativeRawPointer (Metadata)

theorem mutable_identity_exact (p : HasteBootsPointerRuntime.MutRawPtr U8) : mutable_identity p = ok p := rfl

theorem constant_identity_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) : constant_identity p = ok p := rfl

theorem to_constant_exact (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    to_constant p = ok ⟨p.storage, p.metadata⟩ := rfl

theorem to_mutable_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) :
    to_mutable p = ok ⟨p.storage, p.metadata⟩ := rfl

theorem to_word_exact (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    to_word p = ok ⟨p.storage, p.metadata⟩ := rfl

theorem same_exact (p q : HasteBootsPointerRuntime.ConstRawPtr U8) :
    same p q = ok (NativeRawPointer.equal p q) := rfl

theorem different_exact (p q : HasteBootsPointerRuntime.ConstRawPtr U8) :
    different p q = ok (!NativeRawPointer.equal p q) := rfl

theorem slice_same_exact (p q : HasteBootsPointerRuntime.ConstRawPtr (Slice U8)) :
    slice_same p q = ok (NativeRawPointer.equal p q) := rfl

theorem word_cast_address (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    (do let q ← to_word p; pure q.storage.address) = Result.ok p.storage.address := rfl

theorem word_cast_origin (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    (do let q ← to_word p; pure q.storage.provenance) = Result.ok p.storage.provenance := rfl

theorem word_cast_metadata (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    (do let q ← to_word p; pure q.metadata) = Result.ok p.metadata := rfl

theorem comparison_fields (p q : HasteBootsPointerRuntime.ConstRawPtr U8) :
    same p q = ok true ↔ p.storage.address = q.storage.address ∧
      NativeRawPointer.metadataWord p.metadata = NativeRawPointer.metadataWord q.metadata := by
  change Result.ok (NativeRawPointer.equal p q) = Result.ok true ↔ _
  rw [Result.ok.injEq]
  exact NativeRawPointer.equal_iff p q

theorem comparison_ignores_origin (address : Address) (left right : Option Origin) :
    same ⟨⟨address, left⟩, .thin⟩ ⟨⟨address, right⟩, .thin⟩ = ok true := by
  apply (comparison_fields _ _).mpr
  exact ⟨rfl, rfl⟩

theorem different_addresses :
    same ⟨⟨⟨1, by decide⟩, none⟩, .thin⟩ ⟨⟨⟨2, by decide⟩, none⟩, .thin⟩ = ok false := rfl

theorem different_slice_lengths :
    slice_same ⟨⟨⟨1, by decide⟩, none⟩, .slice ⟨1, by decide⟩⟩
      ⟨⟨⟨1, by decide⟩, none⟩, .slice ⟨2, by decide⟩⟩ = ok false := rfl

theorem null_cast :
    to_constant ⟨⟨⟨0, by decide⟩, none⟩, .thin⟩ = ok ⟨⟨⟨0, by decide⟩, none⟩, .thin⟩ := rfl

theorem unaligned_word_cast :
    to_word ⟨⟨⟨1, by decide⟩, none⟩, .thin⟩ = ok ⟨⟨⟨1, by decide⟩, none⟩, .thin⟩ := rfl

end HasteBootsPointerStorageProof
