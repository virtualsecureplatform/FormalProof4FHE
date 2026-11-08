module
import all FormalProof4FHE.HasteBoots.NativeRawByteRange
import all FormalProof4FHE.HasteBoots.NativePointerShadow

namespace HasteBootsRawByteRangeSmoke
open FormalProof4FHE.HasteBoots
open NativeByteMemory (State)
open NativePointerStorage (Pointer Origin)

private def allocated : Option (Pointer × State) :=
  NativeByteMemory.allocate NativeByteMemory.empty ⟨64, by decide⟩ ⟨16, 8⟩
private def mixed : List NativeRawByteRange.Cell := [some 1, none, some 3, some 4]

example : (do
    let (p, state) ← allocated
    NativeRawByteRange.loadRange state p ⟨4, 1⟩) = some [none, none, none, none] := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeRawByteRange.storeRange state p 1 mixed
    NativeByteRange.loadRange state p ⟨4, 1⟩) = none := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeRawByteRange.storeRange state p 1 mixed
    let q ← NativeByteRange.pointerAt p 2
    let state ← NativeRawByteRange.copy state p q 4 1
    NativeRawByteRange.loadRange state p ⟨6, 1⟩) =
    some [some 1, none, some 1, none, some 3, some 4] := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeRawByteRange.storeRange state p 1 mixed
    let q ← NativeByteRange.pointerAt p 2
    NativeRawByteRange.copyNonoverlapping state p q 4 1) = none := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeRawByteRange.storeRange state p 1 mixed
    let q ← NativeByteRange.pointerAt p 8
    let state ← NativeRawByteRange.copyNonoverlapping state p q 4 1
    NativeRawByteRange.loadRange state q ⟨4, 1⟩) = some mixed := by decide
example : (do
    let (p, state) ← allocated
    let q ← NativeByteRange.pointerAt p 14
    NativeRawByteRange.copy state p q 4 1) = none := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeByteMemory.deallocate state p ⟨16, 8⟩
    let (_, state) ← NativeByteMemory.allocate state ⟨64, by decide⟩ ⟨16, 8⟩
    NativeRawByteRange.loadRange state p ⟨4, 1⟩) = none := by decide
private def null : Pointer := ⟨⟨0, by decide⟩, none⟩
example : NativeRawByteRange.copy NativeByteMemory.empty null null 0 8 = some NativeByteMemory.empty := by decide
example : NativeRawByteRange.copy NativeByteMemory.empty null null 1 1 = none := by decide
example : NativeRawByteRange.copy NativeByteMemory.empty null null 0 3 = none := by decide

private def owner : Origin := ⟨64, 0⟩
private def target : Origin := ⟨128, 1⟩
private def other : Origin := ⟨128, 2⟩
private def shadow : List NativePointerShadow.Cell :=
  NativePointerShadow.replace [] owner 64 (List.replicate 8 (some target))
example : NativePointerShadow.uniform shadow owner 64 8 = some (some target) := by decide
example : NativePointerShadow.uniform shadow ⟨64, 1⟩ 64 8 = some none := by decide
example : NativePointerShadow.uniform (NativePointerShadow.clear shadow owner 64 8) owner 64 8 = some none := by decide
example : NativePointerShadow.uniform (NativePointerShadow.clear shadow owner 66 1) owner 64 8 = none := by decide
example : NativePointerShadow.uniform (NativePointerShadow.replace shadow owner 66 [some other]) owner 64 8 = none := by decide
example : NativePointerShadow.uniform (NativePointerShadow.replace shadow owner 72
    (NativePointerShadow.snapshot shadow owner 64 8)) owner 72 8 = some (some target) := by decide
example : NativePointerShadow.uniform (NativePointerShadow.replace shadow owner 66
    (NativePointerShadow.snapshot shadow owner 64 8)) owner 66 8 = some (some target) := by decide
example : NativePointerShadow.lookup (NativePointerShadow.clear shadow owner 72 8) owner 64 = some target := by decide
end HasteBootsRawByteRangeSmoke
