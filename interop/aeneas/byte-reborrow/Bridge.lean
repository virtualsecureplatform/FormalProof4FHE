namespace HasteBootsByteReborrowHeap
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open HasteBootsSlice64Runtime HasteBootsByteReferenceHeap

theorem replace_heap (state next : NativeByteBorrow.State) (valid : NativeByteBorrow.WellFormed state)
    (parent : Nat) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases parent = some lease)
    (slice : HasteBootsSlice64Runtime.Slice U8) (view : Represents state.memory lease.pointer lease.layout slice)
    (offset : U64) (value : U8) (old : NativeByteMemory.Byte)
    (executed : NativeByteReborrow.replaceAt state parent offset.val (decodeByte value) = some (some old, next)) :
    hasteboots_byte_reborrow.replace_at slice offset value = ok (some (encodeByte old), set slice offset value) ∧
    Represents next.memory lease.pointer lease.layout (set slice offset value) ∧
    next.leases = state.leases ∧ next.nextTag = state.nextTag + 1 ∧ NativeByteBorrow.WellFormed next := by
  obtain ⟨selected, updated⟩ := NativeByteReborrow.success_memory state valid.1 parent offset.val lease found _ view
    (decodeByte value) old next executed
  rw [List.getElem?_map] at selected
  have sourceSelected : slice.val[offset.val]? = some (encodeByte old) := by
    cases atIndex : slice.val[offset.val]? with
    | none => simp only [atIndex, Option.map_none] at selected; cases selected
    | some previous =>
      simp only [atIndex, Option.map_some] at selected
      have same := Option.some.inj selected
      have sameValue : previous = encodeByte old := (encode_decode previous).symm.trans (congrArg encodeByte same)
      exact congrArg some sameValue
  obtain ⟨restored, counter, _⟩ := NativeByteReborrow.scope_restored state valid.2 parent offset.val
    (decodeByte value) old next executed
  refine ⟨hasteboots_byte_reborrow.replace_at_found slice offset _ value sourceSelected, ?_, restored, counter,
    NativeByteReborrow.success_wellFormed state valid parent offset.val (decodeByte value) old next executed⟩
  simpa only [Represents, set_values, List.map_set] using updated

theorem replace_granted (state : NativeByteBorrow.State) (valid : NativeByteBorrow.WellFormed state)
    (parent : Nat) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases parent = some lease)
    (slice : HasteBootsSlice64Runtime.Slice U8) (view : Represents state.memory lease.pointer lease.layout slice)
    (offset : U64) (inside : offset.val < lease.layout.size) (pointer : NativePointerStorage.Pointer)
    (advanced : NativeByteRange.pointerAt lease.pointer offset.val = some pointer)
    (child : Nat) (borrowed : NativeByteBorrow.State)
    (issued : NativeByteBorrow.borrow state (some parent) .exclusive pointer ⟨1, 1⟩ = some (child, borrowed)) (value : U8) :
    ∃ old next, NativeByteReborrow.replaceAt state parent offset.val (decodeByte value) = some (some old, next) ∧
      hasteboots_byte_reborrow.replace_at slice offset value = ok (some (encodeByte old), set slice offset value) ∧
      Represents next.memory lease.pointer lease.layout (set slice offset value) ∧
      next.leases = state.leases ∧ next.nextTag = state.nextTag + 1 ∧ NativeByteBorrow.WellFormed next := by
  obtain ⟨old, next, executed⟩ := NativeByteReborrow.issued_executes state valid parent offset.val lease found inside
    pointer advanced child borrowed issued (decodeByte value)
  exact ⟨old, next, executed, replace_heap state next valid parent lease found slice view offset value old executed⟩

theorem replace_outside_unchanged (state : NativeByteBorrow.State) (parent : Nat) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases parent = some lease)
    (slice : HasteBootsSlice64Runtime.Slice U8) (view : Represents state.memory lease.pointer lease.layout slice)
    (offset : U64) (outside : ¬ offset.val < lease.layout.size) (value : U8) :
    NativeByteReborrow.replaceAt state parent offset.val (decodeByte value) = some (none, state) ∧
    hasteboots_byte_reborrow.replace_at slice offset value = ok (none, slice) := by
  have length := represents_length state.memory lease.pointer lease.layout slice view
  exact ⟨NativeByteReborrow.outside state parent offset.val lease found outside (decodeByte value),
    hasteboots_byte_reborrow.replace_at_outside slice offset value (by omega)⟩

end HasteBootsByteReborrowHeap
