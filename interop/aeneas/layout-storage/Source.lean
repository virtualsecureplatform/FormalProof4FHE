namespace HasteBootsLayoutStorage.Source
open Aeneas Aeneas.Std
open FormalProof4FHE.HasteBoots
abbrev Layout := hasteboots_layout_word64.core.alloc.layout.Layout

def word (value : U64) : NativeWord64Memory.Word := value.bv.toFin

def words (value : Layout) : NativeLayoutBytes.Words :=
  ⟨word value.size, word (HasteBootsByteMemoryLayout.alignmentWord value.align)⟩

theorem word_value (value : U64) : (word value).val = value.val := rfl

theorem words_valid (value : Layout) : (words value).Valid :=
  HasteBootsByteMemoryLayout.alignment_power value.align

theorem source_size (value : Layout) :
    (do let size ← hasteboots_layout_word64.size value; pure (word size)) = .ok (words value).size := rfl

theorem source_alignment (value : Layout) :
    (do let alignment ← hasteboots_layout_word64.align value; pure (word alignment)) = .ok (words value).alignment := by
  rcases value with ⟨size,⟨tag⟩⟩
  cases tag <;> rfl

theorem bytes_roundtrip (value : Layout) :
    NativeLayoutBytes.decode (NativeLayoutBytes.encode (words value)) = some (words value) :=
  NativeLayoutBytes.decode_encode (words value) (words_valid value)

theorem size_field (value : Layout) :
    NativeRecordValues.get ((words value).value layoutTag alignmentTag enumTag) [.unwrap layoutTag,.left] =
      some (.scalar (.usize (word value.size))) := NativeLayoutBytes.size_field _ _ _ _

theorem alignment_field (value : Layout) :
    NativeRecordValues.get ((words value).value layoutTag alignmentTag enumTag)
      [.unwrap layoutTag,.right,.left,.unwrap alignmentTag,.left] =
      some (.enumeration enumTag (word (HasteBootsByteMemoryLayout.alignmentWord value.align))) :=
  NativeLayoutBytes.alignment_field _ _ _ _

theorem caller_entry (world : NativeReferenceMachine.State) (pointer : NativeSliceLLBC.Raw) (value : Layout)
    (thin : pointer.length = none) :
    NativeRecordLLBC.initial HasteBootsAllocatorCaller.f2.types HasteBootsAllocatorCaller.f2.argCount
      [.scalar (.raw pointer),(words value).value layoutTag alignmentTag enumTag] world =
      some (HasteBootsAllocatorCaller.entry world pointer (words value).size (words value).alignment) := by
  rw [value_exact]
  exact HasteBootsAllocatorCaller.initial_exact _ _ _ _ thin (alignment_member _ (words_valid value))

end HasteBootsLayoutStorage.Source
