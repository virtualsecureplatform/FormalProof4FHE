namespace HasteBootsNonNullProof
open Aeneas Aeneas.Std Result
open hasteboots_nonnull_pointers
open FormalProof4FHE.HasteBoots
open NativePointerStorage (Address Origin)
open NativeRawPointer (Metadata)

abbrev NonNull := core.ptr.non_null.NonNull.mono_4b0391425e41366dde58d897537529df
abbrev Valid (T : Type) (mutable : Bool) :=
  { pointer : HasteBootsPointerRuntime.RawPtr T mutable // pointer.storage.address ≠ 0 }

theorem unwrap_const_exact (p : Valid U8 false) : unwrap_const p = ok p.val := rfl

theorem unwrap_mut_exact (p : Valid U8 true) : unwrap_mut p = ok p.val := rfl

theorem unwrap_slice_exact (p : Valid (Slice U8) false) : unwrap_slice p = ok p.val := rfl

theorem wrap_const_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) :
    wrap_const p = HasteBootsPointerRuntime.check_nonnull p := rfl

theorem wrap_mut_exact (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    wrap_mut p = HasteBootsPointerRuntime.check_nonnull p := rfl

theorem wrap_slice_exact (p : HasteBootsPointerRuntime.ConstRawPtr (Slice U8)) :
    wrap_slice p = HasteBootsPointerRuntime.check_nonnull p := rfl

theorem original_identity_exact (p : NonNull) : original_identity p = ok p := rfl

theorem original_as_ptr_exact (p : NonNull) :
    core.ptr.non_null.NonNull.as_ptr.mono_0c7d35cf3ad45800040d946380aa402c p =
      ok ⟨p.pointer.val.storage, p.pointer.val.metadata⟩ := rfl

theorem original_get_exact (p : NonNull) :
    original_get p = ok ⟨p.pointer.val.storage, p.pointer.val.metadata⟩ := rfl

theorem original_get_address (p : NonNull) :
    (do let q ← original_get p; pure q.storage.address) = ok p.pointer.val.storage.address := rfl

theorem original_get_origin (p : NonNull) :
    (do let q ← original_get p; pure q.storage.provenance) = ok p.pointer.val.storage.provenance := rfl

theorem original_get_metadata (p : NonNull) :
    (do let q ← original_get p; pure q.metadata) = ok p.pointer.val.metadata := rfl

theorem wrap_const_valid (p : HasteBootsPointerRuntime.ConstRawPtr U8)
    (valid : p.storage.address ≠ 0) : wrap_const p = ok ⟨p, valid⟩ :=
  HasteBootsPointerRuntime.check_nonnull_valid p valid

theorem wrap_mut_zero (p : HasteBootsPointerRuntime.MutRawPtr U8)
    (zero : p.storage.address = 0) : wrap_mut p = fail .undef :=
  HasteBootsPointerRuntime.check_nonnull_zero p zero

theorem wrap_slice_zero (p : HasteBootsPointerRuntime.ConstRawPtr (Slice U8))
    (zero : p.storage.address = 0) : wrap_slice p = fail .undef :=
  HasteBootsPointerRuntime.check_nonnull_zero p zero

theorem wrap_slice_valid (p : HasteBootsPointerRuntime.ConstRawPtr (Slice U8))
    (valid : p.storage.address ≠ 0) : wrap_slice p = ok ⟨p, valid⟩ :=
  HasteBootsPointerRuntime.check_nonnull_valid p valid

theorem const_roundtrip (p : Valid U8 false) :
    (do let raw ← unwrap_const p; wrap_const raw) = ok p :=
  HasteBootsPointerRuntime.check_nonnull_roundtrip p

theorem no_zero_original (p : NonNull) : p.pointer.val.storage.address ≠ 0 := p.pointer.property

end HasteBootsNonNullProof
