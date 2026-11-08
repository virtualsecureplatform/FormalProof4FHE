module
import all FormalProof4FHE.HasteBoots.NativeGoldPointerRegistry

open FormalProof4FHE.HasteBoots
open NativeGoldPointerRegistry

private def old : NativePointerStorage.Cell ℕ := ⟨⟨9,0⟩,⟨64,by decide⟩,by decide,7⟩
private def fresh : NativePointerStorage.Cell ℕ := ⟨⟨9,1⟩,⟨64,by decide⟩,by decide,8⟩
private def root : NativeRootMessage.Digest := fun _ => ⟨0,by decide⟩
private def borrowed : Borrow := ⟨NativePointerStorage.pointer old,root⟩

example : resolve [old] [borrowed,borrowed] = some [⟨7,root⟩,⟨7,root⟩] := rfl
example : resolve [fresh] [borrowed] = none := rfl
example : resolve [old] [borrowed,⟨NativePointerStorage.pointer fresh,root⟩] = none := rfl
example : resolve [old] [] = some [] := rfl
example : resolve [fresh] [⟨NativePointerStorage.pointer fresh,root⟩] = some [⟨8,root⟩] := rfl
example : resolve [old] [⟨⟨⟨64,by decide⟩,none⟩,root⟩] = none := rfl
