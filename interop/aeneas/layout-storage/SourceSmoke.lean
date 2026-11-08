namespace HasteBootsLayoutStorageSourceSmoke
open Aeneas Aeneas.Std
open FormalProof4FHE.HasteBoots
private def value : HasteBootsLayoutStorage.Source.Layout := ⟨24#u64,⟨._Align1Shl3⟩⟩

example : NativeLayoutBytes.encode (HasteBootsLayoutStorage.Source.words value) =
    [8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0] := by decide

example : (HasteBootsLayoutStorage.Source.words ⟨18446744073709551615#u64,⟨._Align1Shl63⟩⟩).size.val =
    18446744073709551615 := by decide

example : NativeLayoutBytes.decode
    (NativeLayoutBytes.encode (HasteBootsLayoutStorage.Source.words ⟨0#u64,⟨._Align1Shl63⟩⟩)) =
    some ⟨⟨0,by decide⟩,⟨2^63,by decide⟩⟩ := by decide

end HasteBootsLayoutStorageSourceSmoke
