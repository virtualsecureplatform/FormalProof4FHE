namespace HasteBootsByteReferenceHeap
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open HasteBootsSlice64Runtime

def encodeByte (byte : NativeByteMemory.Byte) : U8 := ⟨BitVec.ofFin byte⟩
def decodeByte (byte : U8) : NativeByteMemory.Byte := byte.bv.toFin

theorem decode_encode (byte : NativeByteMemory.Byte) : decodeByte (encodeByte byte) = byte := rfl

theorem encode_decode (byte : U8) : encodeByte (decodeByte byte) = byte := by
  cases byte
  rfl

def encodeBytes (bytes : List NativeByteMemory.Byte) : Option (HasteBootsSlice64Runtime.Slice U8) :=
  if bound : bytes.length < 2 ^ 64 then
    some ⟨bytes.map encodeByte, by simpa only [List.length_map] using bound⟩
  else none

/-- Logical current-heap observation; it neither grants nor demands borrow permissions. -/
def Represents (state : NativeByteMemory.State) (pointer : NativePointerStorage.Pointer)
    (layout : NativeByteMemory.Layout) (slice : HasteBootsSlice64Runtime.Slice U8) : Prop :=
  NativeByteRange.loadRange state pointer layout = some (slice.val.map decodeByte)

def observe (state : NativeByteMemory.State) (pointer : NativePointerStorage.Pointer)
    (layout : NativeByteMemory.Layout) : Option (HasteBootsSlice64Runtime.Slice U8) :=
  (NativeByteRange.loadRange state pointer layout).bind encodeBytes

theorem encoded_values (bytes : List NativeByteMemory.Byte) (slice : HasteBootsSlice64Runtime.Slice U8)
    (encoded : encodeBytes bytes = some slice) : slice.val.map decodeByte = bytes := by
  unfold encodeBytes at encoded
  split at encoded
  · cases encoded
    simp only [List.map_map, Function.comp_def, decode_encode]
    exact List.map_id bytes
  · cases encoded

theorem observe_represents (state : NativeByteMemory.State) (pointer : NativePointerStorage.Pointer)
    (layout : NativeByteMemory.Layout) (slice : HasteBootsSlice64Runtime.Slice U8)
    (observed : observe state pointer layout = some slice) : Represents state pointer layout slice := by
  unfold observe at observed
  cases loaded : NativeByteRange.loadRange state pointer layout with
  | none => simp only [loaded, Option.bind] at observed; cases observed
  | some bytes =>
    simp only [loaded, Option.bind] at observed
    rw [Represents, encoded_values bytes slice observed]
    exact loaded

theorem observe_of_loaded (state : NativeByteMemory.State) (pointer : NativePointerStorage.Pointer)
    (layout : NativeByteMemory.Layout) (bytes : List NativeByteMemory.Byte)
    (loaded : NativeByteRange.loadRange state pointer layout = some bytes) :
    ∃ slice, observe state pointer layout = some slice ∧ Represents state pointer layout slice := by
  have length := NativeByteRange.loadRange_length state pointer layout bytes loaded
  have size := NativeByteRange.range_size_bound state pointer layout bytes loaded
  have bound : bytes.length < 2 ^ 64 := by omega
  let slice : HasteBootsSlice64Runtime.Slice U8 := ⟨bytes.map encodeByte, by simpa only [List.length_map] using bound⟩
  have observed : observe state pointer layout = some slice := by
    simp only [observe, loaded, Option.bind, encodeBytes, dite_eq_left bound]
    rfl
  exact ⟨slice, observed, observe_represents state pointer layout slice observed⟩

theorem represents_length (state : NativeByteMemory.State) (pointer : NativePointerStorage.Pointer)
    (layout : NativeByteMemory.Layout) (slice : HasteBootsSlice64Runtime.Slice U8)
    (view : Represents state pointer layout slice) : slice.val.length = layout.size := by
  have length := NativeByteRange.loadRange_length state pointer layout _ view
  simpa only [List.length_map] using length

theorem source_write_heap (state next : NativeByteBorrow.State)
    (valid : NativeByteMemory.WellFormed state.memory) (tag : Nat) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases tag = some lease)
    (slice : HasteBootsSlice64Runtime.Slice U8) (view : Represents state.memory lease.pointer lease.layout slice)
    (offset : U64) (value : U8)
    (written : NativeByteBorrow.write state tag offset.val (decodeByte value) = some next) :
    hasteboots_byte_reference.checked_write slice offset value = ok (true, set slice offset value) ∧
    Represents next.memory lease.pointer lease.layout (set slice offset value) := by
  obtain ⟨actual, _, actualFound, _, inside, _⟩ := NativeByteBorrow.write_success state tag offset.val (decodeByte value) next written
  have same : actual = lease := Option.some.inj (actualFound.symm.trans found)
  subst actual
  have length := represents_length state.memory lease.pointer lease.layout slice view
  refine ⟨hasteboots_byte_reference.checked_write_inside slice offset value (by omega), ?_⟩
  have updated := NativeByteRangeUpdate.borrowed_write_range state next valid tag offset.val lease found _ view (decodeByte value) written
  simpa only [Represents, set_values, List.map_set] using updated

theorem source_read_heap (state : NativeByteBorrow.State)
    (valid : NativeByteMemory.WellFormed state.memory) (tag : Nat) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases tag = some lease)
    (slice : HasteBootsSlice64Runtime.Slice U8) (view : Represents state.memory lease.pointer lease.layout slice)
    (offset : U64) (byte : NativeByteMemory.Byte)
    (read : NativeByteBorrow.read state tag offset.val 1 = some [byte]) :
    hasteboots_byte_reference.checked_read slice offset = ok (some (encodeByte byte)) := by
  have selected := NativeByteRangeUpdate.borrowed_read_selected state valid tag offset.val lease found _ view byte read
  rw [List.getElem?_map] at selected
  cases atIndex : slice.val[offset.val]? with
  | none => simp only [atIndex, Option.map_none] at selected; cases selected
  | some value =>
    simp only [atIndex, Option.map_some] at selected
    have equalByte := Option.some.inj selected
    have equalValue : value = encodeByte byte := (encode_decode value).symm.trans (congrArg encodeByte equalByte)
    exact hasteboots_byte_reference.checked_read_found slice offset _ (atIndex.trans (congrArg some equalValue))

theorem source_write_authorized (state : NativeByteBorrow.State)
    (valid : NativeByteMemory.WellFormed state.memory) (tag : Nat) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases tag = some lease) (exclusive : lease.mode = .exclusive)
    (slice : HasteBootsSlice64Runtime.Slice U8) (view : Represents state.memory lease.pointer lease.layout slice)
    (offset : U64) (inside : offset.val < lease.layout.size) (reference : NativePointerStorage.Pointer)
    (advanced : NativeByteRange.pointerAt lease.pointer offset.val = some reference)
    (allowed : NativeByteBorrow.throughAllowed state tag .exclusive reference ⟨1, 1⟩ = true) (value : U8) :
    ∃ next, NativeByteBorrow.write state tag offset.val (decodeByte value) = some next ∧
      hasteboots_byte_reference.checked_write slice offset value = ok (true, set slice offset value) ∧
      Represents next.memory lease.pointer lease.layout (set slice offset value) := by
  obtain ⟨next, written⟩ := NativeByteRangeUpdate.borrowed_write_of_allowed state valid tag offset.val lease found
    exclusive _ view inside reference advanced allowed (decodeByte value)
  exact ⟨next, written, source_write_heap state next valid tag lease found slice view offset value written⟩

end HasteBootsByteReferenceHeap
