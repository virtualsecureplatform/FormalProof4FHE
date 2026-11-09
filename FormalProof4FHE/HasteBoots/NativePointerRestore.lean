module
public import FormalProof4FHE.HasteBoots.NativeEmptyVecStorage
@[expose] public section

/-! A typed pointer store may preserve address bytes while installing the complete
source pointer's provenance. Integer bytes alone do not supply that provenance.
These facts concern the checked memory model, not compiler or native ABI validity. -/
namespace FormalProof4FHE.HasteBoots.NativePointerRestore
open NativePointerStorage (Pointer)
open NativeByteMemory (Byte Block)
open NativeByteRange
open NativeByteRangeWrite

/-- A successful initialized read identifies every stored cell in its prefix. -/
theorem readSpan_cells (cells : List (Option Byte)) (size : Nat) (values : List Byte)
    (read : readSpan cells size = some values) : cells.take size = values.map some := by
  induction size generalizing cells values with
  | zero => simp only [readSpan] at read; cases read; rfl
  | succ size ih =>
    cases cells with
    | nil => cases read
    | cons cell cells =>
      cases cell with
      | none => cases read
      | some byte =>
        cases rest : readSpan cells size with
        | none => simp only [readSpan,rest,Option.map_none] at read; cases read
        | some tail =>
          simp only [readSpan,rest,Option.map_some,Option.some.injEq] at read
          subst values
          simp only [List.take_succ_cons,List.map_cons,ih cells tail rest]

theorem overwrite_same (cells : List (Option Byte)) (offset : Nat) (values : List Byte)
    (read : readSpan (cells.drop offset) values.length = some values) : overwrite cells offset values = cells := by
  have identified := readSpan_cells (cells.drop offset) values.length values read
  unfold overwrite
  rw [← identified]
  have recover := List.take_append_drop values.length (cells.drop offset)
  rw [List.drop_drop] at recover
  rw [recover,List.take_append_drop]

/-- Reading then writing the same initialized bytes succeeds without changing
any allocation record or any byte, even when the location is a subrange. -/
theorem storeBlocks_same (blocks : List Block) (pointer : Pointer) (values : List Byte)
    (positive : 0 < values.length)
    (read : readBlocks blocks pointer values.length = some values) : storeBlocks blocks pointer values = some blocks := by
  induction blocks with
  | nil => cases read
  | cons block blocks ih =>
    unfold readBlocks at read
    unfold storeBlocks
    split at read
    next covered =>
      have cells := readSpan_cells (block.bytes.drop (pointer.address.val - block.base.val)) values.length values read
      have sizes := congrArg List.length cells
      simp only [List.length_take,List.length_drop,List.length_map] at sizes
      have bounded : pointer.address.val - block.base.val + values.length ≤ block.bytes.length := by omega
      simp only [covered,ite_true,bounded,overwrite_same block.bytes _ values read]
    next missing =>
      simp only [missing,ite_false,ih read,Option.map_some]

theorem storeRange_same (memory : NativeByteMemory.State) (pointer : Pointer) (alignment : Nat) (values : List Byte)
    (read : loadRange memory pointer ⟨values.length,alignment⟩ = some values) :
    storeRange memory pointer alignment values = some memory := by
  have geometry := loadRange_geometry memory pointer _ values read
  cases values with
  | nil => simp only [storeRange,geometry,ite_true,List.isEmpty_nil]
  | cons byte values =>
    have positive : (byte :: values).length ≠ 0 := by exact Nat.succ_ne_zero _
    have blocks : readBlocks memory.blocks pointer (byte :: values).length = some (byte :: values) := by
      simpa only [loadRange,geometry,ite_true,positive,ite_false] using read
    have stored := storeBlocks_same memory.blocks pointer (byte :: values) (by exact Nat.succ_pos _) blocks
    simp only [storeRange,geometry,ite_true,List.isEmpty_cons,Bool.false_eq_true,ite_false,stored,Option.map_some]

theorem storeWord_same (memory : NativeByteMemory.State) (slot : Pointer) (word : NativeWord64Memory.Word)
    (read : NativeWord64Memory.load memory slot = some word) : NativeWord64Memory.store memory slot word = some memory := by
  have bytes := (NativeWord64Memory.load_iff_bytes memory slot word).mp read
  have stored := storeRange_same memory slot 8 (NativeWord64Memory.encode word) (by
    simpa only [NativeWord64Memory.encode_length] using bytes)
  exact stored

/-- Complete pointer provenance comes from the supplied typed value; the byte
memory remains exactly unchanged when its address is already present. -/
theorem restore (heap : NativePointerByteMemory.State) (slot value : Pointer) (owner : NativePointerStorage.Origin)
    (ownerEq : slot.provenance = some owner)
    (read : NativeWord64Memory.load heap.memory slot = some value.address) :
    ∃ next, NativePointerByteMemory.store heap slot value = some next ∧
      next.memory = heap.memory ∧ NativePointerByteMemory.load next slot = some value ∧
      next.shadow = NativePointerShadow.replace heap.shadow owner slot.address.val (List.replicate 8 value.provenance) := by
  have stored := storeWord_same heap.memory slot value.address read
  let next : NativePointerByteMemory.State := ⟨heap.memory,
    NativePointerShadow.replace heap.shadow owner slot.address.val (List.replicate 8 value.provenance)⟩
  have executed : NativePointerByteMemory.store heap slot value = some next := by
    simp only [NativePointerByteMemory.store,ownerEq,stored,Option.bind_eq_bind',Option.bind,pure,next]
  exact ⟨next,executed,rfl,NativePointerByteMemory.store_then_load heap next slot value executed,rfl⟩

end FormalProof4FHE.HasteBoots.NativePointerRestore
