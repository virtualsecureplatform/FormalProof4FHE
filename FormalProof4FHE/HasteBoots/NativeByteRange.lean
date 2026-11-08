module
public import FormalProof4FHE.HasteBoots.NativeByteMemory
@[expose] public section

/-! Checked byte ranges and byte-slice reads over the allocation lifecycle.
These are geometry/initialization checks, not Rust references or borrow grants.
No compiler dereference, alias discipline or physical-work rule is supplied. -/
namespace FormalProof4FHE.HasteBoots.NativeByteRange
open NativePointerStorage (Pointer)
open NativeByteMemory (Byte Layout Block State)

/-- Even a zero-byte range has a nonnull, aligned address. Arithmetic uses
unbounded naturals and checks the extent before any address conversion. -/
def Geometry (pointer : Pointer) (layout : Layout) : Prop :=
  layout.Valid ∧ pointer.address.val ≠ 0 ∧
    pointer.address.val % layout.alignment = 0 ∧
    pointer.address.val + layout.size < 2 ^ 64

instance (pointer : Pointer) (layout : Layout) : Decidable (Geometry pointer layout) := by
  unfold Geometry
  infer_instance

/-- A positive range fits in a single live allocation with matching origin. -/
def Covers (block : Block) (pointer : Pointer) (size : Nat) : Prop :=
  pointer.provenance = some block.origin ∧ block.base.val ≤ pointer.address.val ∧
    pointer.address.val + size ≤ block.base.val + block.layout.size

instance (block : Block) (pointer : Pointer) (size : Nat) : Decidable (Covers block pointer size) := by
  unfold Covers
  infer_instance

def checkRange (state : State) (pointer : Pointer) (layout : Layout) : Bool :=
  decide (Geometry pointer layout) &&
    (if layout.size = 0 then true else state.blocks.any (fun block => decide (Covers block pointer layout.size)))

/-- Read exactly the requested number of initialized bytes; never truncate. -/
def readSpan : List (Option Byte) → Nat → Option (List Byte)
  | _, 0 => some []
  | [], _ + 1 => none
  | none :: _, _ + 1 => none
  | some byte :: tail, size + 1 => (readSpan tail size).map (byte :: ·)

def readBlocks : List Block → Pointer → Nat → Option (List Byte)
  | [], _, _ => none
  | block :: tail, pointer, size =>
      if Covers block pointer size then
        readSpan (block.bytes.drop (pointer.address.val - block.base.val)) size
      else readBlocks tail pointer size

def loadRange (state : State) (pointer : Pointer) (layout : Layout) : Option (List Byte) :=
  if Geometry pointer layout then
    if layout.size = 0 then some [] else readBlocks state.blocks pointer layout.size
  else none

/-- A byte-slice view has byte elements, not an arbitrary pointee stride. -/
def loadSlice {mutable : Bool} (state : State)
    (pointer : NativeRawPointer.RawPtr (List Byte) mutable) : Option (List Byte) :=
  match pointer.metadata with
  | .slice length => loadRange state pointer.storage ⟨length.val, 1⟩
  | .thin | .vtable _ => none

theorem readSpan_length (bytes : List (Option Byte)) (size : Nat) (output : List Byte)
    (executed : readSpan bytes size = some output) : output.length = size := by
  induction size generalizing bytes output with
  | zero => simp only [readSpan] at executed; cases executed; rfl
  | succ size ih =>
    cases bytes with
    | nil => cases executed
    | cons value tail =>
      cases value with
      | none => cases executed
      | some byte =>
        unfold readSpan at executed
        cases rest : readSpan tail size with
        | none => simp only [rest, Option.map_none] at executed; cases executed
        | some result =>
          simp only [rest, Option.map_some] at executed
          cases executed
          exact congrArg Nat.succ (ih tail result rest)

theorem readSpan_selected (bytes : List (Option Byte)) (size : Nat) (output : List Byte)
    (executed : readSpan bytes size = some output) (index : Nat) (byte : Byte)
    (selected : output[index]? = some byte) : bytes[index]? = some (some byte) := by
  induction size generalizing bytes output index with
  | zero => simp only [readSpan] at executed; cases executed; simp only [List.getElem?_nil] at selected; cases selected
  | succ size ih =>
    cases bytes with
    | nil => cases executed
    | cons value tail =>
      cases value with
      | none => cases executed
      | some stored =>
        unfold readSpan at executed
        cases rest : readSpan tail size with
        | none => simp only [rest, Option.map_none] at executed; cases executed
        | some result =>
          simp only [rest, Option.map_some] at executed
          cases executed
          cases index with
          | zero => cases selected; rfl
          | succ index => exact ih tail result rest index selected

theorem readSpan_uninitialized (size offset requested : Nat) (positive : 0 < requested) :
    readSpan ((List.replicate size (none : Option Byte)).drop offset) requested = none := by
  cases requested with
  | zero => cases positive
  | succ requested =>
    rw [List.drop_replicate]
    cases size - offset <;> rfl

theorem readBlocks_selected (blocks : List Block) (pointer : Pointer) (size : Nat) (output : List Byte)
    (executed : readBlocks blocks pointer size = some output) :
    ∃ block ∈ blocks, Covers block pointer size ∧
      readSpan (block.bytes.drop (pointer.address.val - block.base.val)) size = some output := by
  induction blocks with
  | nil => cases executed
  | cons block tail ih =>
    unfold readBlocks at executed
    split at executed
    · rename_i covered
      exact ⟨block, List.mem_cons_self, covered, executed⟩
    · obtain ⟨selected, member, covered, initialized⟩ := ih executed
      exact ⟨selected, List.mem_cons_of_mem block member, covered, initialized⟩

theorem loadRange_geometry (state : State) (pointer : Pointer) (layout : Layout) (output : List Byte)
    (executed : loadRange state pointer layout = some output) : Geometry pointer layout := by
  unfold loadRange at executed
  split at executed
  · assumption
  · cases executed

theorem loadRange_length (state : State) (pointer : Pointer) (layout : Layout) (output : List Byte)
    (executed : loadRange state pointer layout = some output) : output.length = layout.size := by
  unfold loadRange at executed
  split at executed
  · split at executed
    · rename_i zero
      cases executed
      exact zero.symm
    · obtain ⟨_, _, _, initialized⟩ := readBlocks_selected _ _ _ _ executed
      exact readSpan_length _ _ _ initialized
  · cases executed

theorem loadRange_positive_selected (state : State) (pointer : Pointer) (layout : Layout)
    (positive : 0 < layout.size) (output : List Byte)
    (executed : loadRange state pointer layout = some output) :
    ∃ block ∈ state.blocks, Covers block pointer layout.size ∧
      readSpan (block.bytes.drop (pointer.address.val - block.base.val)) layout.size = some output := by
  unfold loadRange at executed
  split at executed
  · split at executed
    · omega
    · exact readBlocks_selected _ _ _ _ executed
  · cases executed

theorem loadRange_checked (state : State) (pointer : Pointer) (layout : Layout) (output : List Byte)
    (executed : loadRange state pointer layout = some output) : checkRange state pointer layout = true := by
  have geometry := loadRange_geometry state pointer layout output executed
  unfold checkRange
  rw [decide_eq_true geometry, Bool.true_and]
  split
  · rfl
  · rename_i nonzero
    have positive : 0 < layout.size := Nat.pos_of_ne_zero nonzero
    obtain ⟨block, member, covered, _⟩ := loadRange_positive_selected state pointer layout positive output executed
    exact List.any_eq_true.mpr ⟨block, member, decide_eq_true covered⟩

theorem empty_range (state : State) (pointer : Pointer) (alignment : Nat)
    (geometry : Geometry pointer ⟨0, alignment⟩) : loadRange state pointer ⟨0, alignment⟩ = some [] := by
  simp only [loadRange, ite_eq_left geometry, ite_true]

theorem null_range (state : State) (pointer : Pointer) (zero : pointer.address.val = 0)
    (layout : Layout) : loadRange state pointer layout = none := by
  have invalid : ¬ Geometry pointer layout := fun geometry => geometry.2.1 zero
  exact ite_eq_right invalid

theorem empty_check (state : State) (pointer : Pointer) (alignment : Nat) :
    checkRange state pointer ⟨0, alignment⟩ = decide (Geometry pointer ⟨0, alignment⟩) := by
  simp only [checkRange, ite_true, Bool.and_true]

theorem positive_without_origin (state : State) (pointer : Pointer) (layout : Layout)
    (positive : 0 < layout.size) (absent : pointer.provenance = none) : loadRange state pointer layout = none := by
  cases executed : loadRange state pointer layout with
  | none => rfl
  | some output =>
    obtain ⟨block, _, covered, _⟩ := loadRange_positive_selected state pointer layout positive output executed
    have impossible := covered.1
    rw [absent] at impossible
    cases impossible

theorem positive_after_deallocation (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (layout : Layout) (next : State)
    (released : NativeByteMemory.deallocate state pointer layout = some next)
    (reference : Pointer) (sameOrigin : reference.provenance = pointer.provenance)
    (requested : Layout) (positive : 0 < requested.size) : loadRange next reference requested = none := by
  unfold NativeByteMemory.deallocate at released
  cases rest : NativeByteMemory.releaseBlocks state.blocks pointer layout with
  | none => simp only [rest, Option.map_none] at released; cases released
  | some blocks =>
    simp only [rest, Option.map_some] at released
    cases released
    cases executed : loadRange {state with blocks := blocks} reference requested with
    | none => rfl
    | some output =>
      obtain ⟨block, member, covered, _⟩ := loadRange_positive_selected _ reference requested positive output executed
      have absent := NativeByteMemory.release_origin_absent state.blocks
        (valid.2.imp (fun pair => pair.2)) pointer layout blocks rest block member
      exact False.elim (absent (sameOrigin.symm.trans covered.1))

theorem positive_range_single_allocation (state : State) (pointer : Pointer) (layout : Layout)
    (positive : 0 < layout.size) (output : List Byte)
    (executed : loadRange state pointer layout = some output) :
    ∃ block ∈ state.blocks, pointer.provenance = some block.origin ∧
      block.base.val ≤ pointer.address.val ∧
      pointer.address.val + layout.size ≤ block.base.val + block.layout.size := by
  obtain ⟨block, member, covered, _⟩ := loadRange_positive_selected state pointer layout positive output executed
  exact ⟨block, member, covered⟩

theorem range_size_bound (state : State) (pointer : Pointer) (layout : Layout) (output : List Byte)
    (executed : loadRange state pointer layout = some output) : layout.size ≤ 2 ^ 63 - 1 :=
  NativeByteMemory.layout_size_bound layout (loadRange_geometry state pointer layout output executed).1

theorem range_no_wrap (state : State) (pointer : Pointer) (layout : Layout) (output : List Byte)
    (executed : loadRange state pointer layout = some output) : pointer.address.val + layout.size < 2 ^ 64 :=
  (loadRange_geometry state pointer layout output executed).2.2.2

theorem slice_thin_rejected {mutable : Bool} (state : State)
    (pointer : NativeRawPointer.RawPtr (List Byte) mutable) (thin : pointer.metadata = .thin) :
    loadSlice state pointer = none := by
  simp only [loadSlice, thin]

theorem slice_length {mutable : Bool} (state : State)
    (pointer : NativeRawPointer.RawPtr (List Byte) mutable) (length : NativePointerStorage.Address)
    (metadata : pointer.metadata = .slice length) (output : List Byte)
    (executed : loadSlice state pointer = some output) : output.length = length.val := by
  simp only [loadSlice, metadata] at executed
  exact loadRange_length state pointer.storage ⟨length.val, 1⟩ output executed

/-- Checked byte-offset arithmetic preserves the origin but grants no access. -/
def pointerAt (pointer : Pointer) (offset : Nat) : Option Pointer :=
  if bound : pointer.address.val + offset < 2 ^ 64 then
    some ⟨⟨pointer.address.val + offset, bound⟩, pointer.provenance⟩
  else none

theorem pointerAt_fields (pointer : Pointer) (offset : Nat) (result : Pointer)
    (executed : pointerAt pointer offset = some result) :
    result.address.val = pointer.address.val + offset ∧ result.provenance = pointer.provenance := by
  unfold pointerAt at executed
  split at executed
  · cases executed; exact ⟨rfl, rfl⟩
  · cases executed

theorem loadBlocks_of_member (blocks : List Block)
    (unique : blocks.Pairwise (fun left right => left.origin ≠ right.origin))
    (block : Block) (member : block ∈ blocks) (pointer : Pointer)
    (matched : NativeByteMemory.Matches block pointer) (byte : Byte)
    (initialized : block.bytes[pointer.address.val - block.base.val]? = some (some byte)) :
    NativeByteMemory.loadBlocks blocks pointer = some byte := by
  induction blocks with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨separated, uniqueTail⟩ := List.pairwise_cons.mp unique
    rcases List.mem_cons.mp member with same | later
    · subst head
      simp only [NativeByteMemory.loadBlocks, ite_eq_left matched, initialized, Option.bind, id_eq]
    · have unmatched : ¬ NativeByteMemory.Matches head pointer := by
        intro matchesHead
        exact separated block later (Option.some.inj (matchesHead.1.symm.trans matched.1))
      simp only [NativeByteMemory.loadBlocks, ite_eq_right unmatched]
      exact ih uniqueTail later

theorem range_agrees_with_byte_load (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (layout : Layout) (output : List Byte)
    (executed : loadRange state pointer layout = some output)
    (index : Nat) (bound : index < layout.size) (byte : Byte) (selected : output[index]? = some byte) :
    ∃ reference, pointerAt pointer index = some reference ∧ NativeByteMemory.loadByte state reference = some byte := by
  have geometry := loadRange_geometry state pointer layout output executed
  obtain ⟨block, member, covered, initialized⟩ :=
    loadRange_positive_selected state pointer layout (by omega) output executed
  have fits : pointer.address.val + index < 2 ^ 64 := by
    have whole := geometry.2.2.2
    omega
  let reference : Pointer := ⟨⟨pointer.address.val + index, fits⟩, pointer.provenance⟩
  refine ⟨reference, ?_, ?_⟩
  · exact dite_eq_left fits
  · apply loadBlocks_of_member state.blocks (valid.2.imp (fun pair => pair.2)) block member reference
    · refine ⟨covered.1, ?_, ?_, ?_⟩
      · change pointer.address.val + index ≠ 0
        have nonzero := geometry.2.1
        omega
      · change block.base.val ≤ pointer.address.val + index
        have lower := covered.2.1
        omega
      · change pointer.address.val + index < block.base.val + block.layout.size
        have upper := covered.2.2
        omega
    · have read := readSpan_selected _ _ _ initialized index byte selected
      rw [List.getElem?_drop] at read
      have offset : pointer.address.val + index - block.base.val =
          pointer.address.val - block.base.val + index := by
        have lower := covered.2.1
        omega
      change block.bytes[pointer.address.val + index - block.base.val]? = some (some byte)
      rw [offset]
      exact read

theorem readBlocks_of_member (blocks : List Block)
    (unique : blocks.Pairwise (fun left right => left.origin ≠ right.origin))
    (block : Block) (member : block ∈ blocks) (pointer : Pointer) (size : Nat)
    (covered : Covers block pointer size) (output : List Byte)
    (initialized : readSpan (block.bytes.drop (pointer.address.val - block.base.val)) size = some output) :
    readBlocks blocks pointer size = some output := by
  induction blocks with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨separated, uniqueTail⟩ := List.pairwise_cons.mp unique
    rcases List.mem_cons.mp member with same | later
    · subst head
      simp only [readBlocks, ite_eq_left covered, initialized]
    · have uncovered : ¬ Covers head pointer size := by
        intro coversHead
        exact separated block later (Option.some.inj (coversHead.1.symm.trans covered.1))
      simp only [readBlocks, ite_eq_right uncovered]
      exact ih uniqueTail later

theorem loadRange_of_ready (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (layout : Layout) (geometry : Geometry pointer layout) (positive : 0 < layout.size)
    (block : Block) (member : block ∈ state.blocks) (covered : Covers block pointer layout.size) (output : List Byte)
    (initialized : readSpan (block.bytes.drop (pointer.address.val - block.base.val)) layout.size = some output) :
    loadRange state pointer layout = some output := by
  unfold loadRange
  rw [ite_eq_left geometry, ite_eq_right (Nat.ne_of_gt positive)]
  exact readBlocks_of_member state.blocks (valid.2.imp (fun pair => pair.2)) block member pointer layout.size covered output initialized

theorem slice_vtable_rejected {mutable : Bool} (state : State)
    (pointer : NativeRawPointer.RawPtr (List Byte) mutable) (table : Pointer)
    (vtable : pointer.metadata = .vtable table) : loadSlice state pointer = none := by
  simp only [loadSlice, vtable]

end FormalProof4FHE.HasteBoots.NativeByteRange
