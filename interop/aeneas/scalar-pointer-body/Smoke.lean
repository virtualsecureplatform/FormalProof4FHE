namespace HasteBootsScalarPointerBodySmoke
open FormalProof4FHE.HasteBoots
open NativeScalarLLBC
open HasteBootsScalarPointerBody

private def p : NativePointerStorage.Pointer := ⟨⟨64, by decide⟩, some ⟨64, 0⟩⟩
private def q : NativePointerStorage.Pointer := ⟨⟨128, by decide⟩, some ⟨128, 1⟩⟩
private def allocated : NativePointerByteMemory.State :=
  ⟨⟨2, [⟨⟨64,0⟩, ⟨64, by decide⟩, ⟨16,8⟩, List.replicate 16 none⟩,
    ⟨⟨128,1⟩, ⟨128, by decide⟩, ⟨8,8⟩, List.replicate 8 none⟩]⟩, []⟩
example : invoke f0 allocated [.pointer p] = .invalid allocated := by decide
example : (match invoke f1 allocated [.pointer p, .word ⟨77, by decide⟩] with
    | .returned .unit heap => invoke f0 heap [.pointer p]
    | _ => .invalid allocated) = .returned (.word ⟨77, by decide⟩) (invoke f1 allocated [.pointer p, .word ⟨77, by decide⟩]).heap := by decide
example : (match invoke f4 allocated [.pointer p, .pointer q] with
    | .returned .unit heap => invoke f3 heap [.pointer p]
    | _ => .invalid allocated) = .returned (.pointer q) (invoke f4 allocated [.pointer p, .pointer q]).heap := by decide
example : (match invoke f4 allocated [.pointer p, .pointer q] with
    | .returned .unit heap => invoke f1 heap [.pointer p, .word q.address]
    | _ => .invalid allocated).heap.shadow = [] := by decide
example : (match invoke f4 allocated [.pointer p, .pointer q] with
    | .returned .unit heap => invoke f1 heap [.pointer p, .word q.address]
    | _ => .invalid allocated).heap.memory.blocks[0]?.map (fun block => block.bytes.take 8) =
      some [some 128, some 0, some 0, some 0, some 0, some 0, some 0, some 0] := by decide
example : invoke f1 allocated [.pointer ⟨⟨65, by decide⟩, p.provenance⟩, .word ⟨1, by decide⟩] = .invalid allocated := by decide
example : invoke f3 allocated [.pointer ⟨p.address, none⟩] = .invalid allocated := by decide
example : (match invoke f1 allocated [.pointer p, .word ⟨7, by decide⟩] with
    | .returned .unit heap => invoke f2 heap [.pointer p, .word ⟨99, by decide⟩]
    | _ => .invalid allocated) = .returned (.word ⟨7, by decide⟩)
      (invoke f1 allocated [.pointer p, .word ⟨99, by decide⟩]).heap := by decide
end HasteBootsScalarPointerBodySmoke
