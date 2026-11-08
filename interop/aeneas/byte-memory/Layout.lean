namespace HasteBootsByteMemoryLayout
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
abbrev SourceLayout := hasteboots_layout_word64.core.alloc.layout.Layout
abbrev Alignment := hasteboots_layout_word64.core.mem.alignment.Alignment
abbrev Tag := hasteboots_layout_word64.core.mem.alignment.AlignmentEnum

def alignmentWord (alignment : Alignment) : U64 :=
  hasteboots_layout_word64.core.mem.alignment.AlignmentEnum.read_discriminant alignment._inner_repr_trick

def decode (layout : SourceLayout) : NativeByteMemory.Layout :=
  ⟨layout.size.val, (alignmentWord layout.align).val⟩

theorem source_size (layout : SourceLayout) :
    (do let size ← hasteboots_layout_word64.size layout; pure size.val) = ok (decode layout).size := rfl

theorem source_alignment (layout : SourceLayout) :
    (do let alignment ← hasteboots_layout_word64.align layout; pure alignment.val) = ok (decode layout).alignment := by
  rcases layout with ⟨size, ⟨tag⟩⟩
  cases tag <;> rfl

theorem alignment_power (alignment : Alignment) :
    (alignmentWord alignment).val ∈ (List.range 64).map (fun exponent => 2 ^ exponent) := by
  rcases alignment with ⟨tag⟩
  cases tag <;> decide

theorem valid_iff_checked_size (layout : SourceLayout) :
    (decode layout).Valid ↔
      layout.size.val + ((alignmentWord layout.align).val - 1) ≤ 2 ^ 63 - 1 := by
  exact and_iff_right (alignment_power layout.align)

theorem allocated_source_layout (state : NativeByteMemory.State)
    (base : NativePointerStorage.Address) (layout : SourceLayout)
    (pointer : NativePointerStorage.Pointer) (next : NativeByteMemory.State)
    (executed : NativeByteMemory.allocate state base (decode layout) = some (pointer, next)) :
    layout.size.val + ((alignmentWord layout.align).val - 1) ≤ 2 ^ 63 - 1 ∧
      next.blocks.head? = some (NativeByteMemory.freshBlock state base (decode layout)) := by
  obtain ⟨_, rfl, valid, _⟩ := NativeByteMemory.allocate_success state base (decode layout) pointer next executed
  exact ⟨(valid_iff_checked_size layout).mp valid.1, rfl⟩

theorem deallocation_source_layout (state : NativeByteMemory.State) (layout : SourceLayout)
    (pointer : NativePointerStorage.Pointer) (next : NativeByteMemory.State)
    (executed : NativeByteMemory.deallocate state pointer (decode layout) = some next) :
    ∃ block ∈ state.blocks, pointer = block.pointer ∧
      block.layout.size = layout.size.val ∧ block.layout.alignment = (alignmentWord layout.align).val := by
  obtain ⟨block, member, same, layoutEq⟩ := NativeByteMemory.deallocate_selected state pointer (decode layout) next executed
  exact ⟨block, member, same, congrArg NativeByteMemory.Layout.size layoutEq.symm,
    congrArg NativeByteMemory.Layout.alignment layoutEq.symm⟩

end HasteBootsByteMemoryLayout
