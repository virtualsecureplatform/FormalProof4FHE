namespace HasteBootsPointerPartsProof
open Aeneas Aeneas.Std Result
open hasteboots_pointer_parts
open FormalProof4FHE.HasteBoots
open NativePointerStorage (Address Origin)
open NativeRawPointer (Metadata)

theorem original_slice_const_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) (n : U64) :
    core.ptr.metadata.from_raw_parts.mono_422d76a278de43af91049b4bc99c6b4f p n =
      ok ⟨p.storage, .slice n.bv.toFin⟩ := rfl

theorem original_slice_mut_exact (p : HasteBootsPointerRuntime.MutRawPtr U8) (n : U64) :
    core.ptr.metadata.from_raw_parts_mut.mono_22ec1cc9473a101a472accb7192baec7 p n =
      ok ⟨p.storage, .slice n.bv.toFin⟩ := rfl

theorem original_thin_const_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) (empty : Unit) :
    core.ptr.metadata.from_raw_parts.mono_c981721880349b620e923f1ce62a5cc2 p empty =
      ok ⟨p.storage, .thin⟩ := rfl

theorem original_thin_mut_exact (p : HasteBootsPointerRuntime.MutRawPtr U8) (empty : Unit) :
    core.ptr.metadata.from_raw_parts_mut.mono_fefbca34f3928b7a21bda4668ad6a3cc p empty =
      ok ⟨p.storage, .thin⟩ := rfl

theorem original_str_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) (n : U64) :
    core.ptr.metadata.from_raw_parts.mono_e6501eb599e0382376ed88b3574f490f p n =
      ok ⟨p.storage, .slice n.bv.toFin⟩ := rfl

theorem slice_const_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) (n : U64) :
    slice_const p n = ok ⟨p.storage, .slice n.bv.toFin⟩ := rfl

theorem slice_mut_exact (p : HasteBootsPointerRuntime.MutRawPtr U8) (n : U64) :
    slice_mut p n = ok ⟨p.storage, .slice n.bv.toFin⟩ := rfl

theorem slice_const_from_mut_exact (p : HasteBootsPointerRuntime.MutRawPtr U8) (n : U64) :
    slice_const_from_mut p n = ok ⟨p.storage, .slice n.bv.toFin⟩ := rfl

theorem thin_const_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) :
    thin_const p = ok ⟨p.storage, .thin⟩ := rfl

theorem thin_mut_exact (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    thin_mut p = ok ⟨p.storage, .thin⟩ := rfl

theorem str_const_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) (n : U64) :
    str_const p n = ok ⟨p.storage, .slice n.bv.toFin⟩ := rfl

theorem slice_address (p : HasteBootsPointerRuntime.MutRawPtr U8) (n : U64) :
    (do let q ← slice_mut p n; pure q.storage.address) = ok p.storage.address := rfl

theorem slice_origin (p : HasteBootsPointerRuntime.MutRawPtr U8) (n : U64) :
    (do let q ← slice_mut p n; pure q.storage.provenance) = ok p.storage.provenance := rfl

theorem slice_length (p : HasteBootsPointerRuntime.MutRawPtr U8) (n : U64) :
    (do let q ← slice_mut p n; pure q.metadata) = ok (.slice n.bv.toFin) := rfl

theorem thin_metadata (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    (do let q ← thin_mut p; pure q.metadata) = ok Metadata.thin := rfl

theorem zero_address_allowed (origin : Option Origin) (n : U64) :
    slice_mut ⟨⟨0, origin⟩, .thin⟩ n = ok ⟨⟨0, origin⟩, .slice n.bv.toFin⟩ := rfl

theorem empty_slice_keeps_address (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    slice_mut p 0#u64 = ok ⟨p.storage, .slice 0⟩ := rfl

theorem maximum_length_kept (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    slice_mut p 18446744073709551615#u64 =
      ok ⟨p.storage, .slice ⟨18446744073709551615, by decide⟩⟩ := rfl

theorem new_metadata_replaces_old (address : Address) (origin : Option Origin)
    (left right : Metadata) (n : U64) :
    slice_const ⟨⟨address, origin⟩, left⟩ n = slice_const ⟨⟨address, origin⟩, right⟩ n := rfl

theorem thin_origin (p : HasteBootsPointerRuntime.MutRawPtr U8) :
    (do let q ← thin_mut p; pure q.storage.provenance) = ok p.storage.provenance := rfl

theorem original_pair_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) (empty : Unit) :
    core.ptr.metadata.from_raw_parts.mono_9d0463365bb2f74af857d38c1abbfaec p empty =
      ok ⟨p.storage, .thin⟩ := rfl

theorem pair_const_exact (p : HasteBootsPointerRuntime.ConstRawPtr U8) :
    pair_const p = ok ⟨p.storage, .thin⟩ := rfl

end HasteBootsPointerPartsProof
