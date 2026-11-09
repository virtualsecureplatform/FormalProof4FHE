module
public import FormalProof4FHE.HasteBoots.NativeHeapFrame
@[expose] public section

/-! Exact heap transitions behind allocation-loss bounds. Every transition
records a positive, well-formed modeled deallocation of a complete pointer.
This is not native allocator correctness or an ownership/lifetime refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeHeapRelease
open NativePointerStorage (Pointer)
open NativeByteMemory (Layout Block)
open NativePointerByteMemory (State)

def count (heap : State) : Nat := heap.memory.blocks.length

theorem deallocate_count (before after : State) (pointer : Pointer) (layout : Layout)
    (freed : NativePointerByteMemory.deallocate before pointer layout = some after) :
    count after + 1 = count before := by
  obtain ⟨_,_,memory,_⟩ := NativePointerByteMemory.deallocate_success before after pointer layout freed
  exact NativeByteMemory.deallocate_changes_live_count before.memory pointer layout after.memory memory

theorem deallocate_blocks (before after : State) (pointer : Pointer) (layout : Layout)
    (freed : NativePointerByteMemory.deallocate before pointer layout = some after) :
    after.memory.blocks.Sublist before.memory.blocks := by
  obtain ⟨_,_,memory,_⟩ := NativePointerByteMemory.deallocate_success before after pointer layout freed
  simp only [NativeByteMemory.deallocate, Option.map_eq_some_iff] at memory
  obtain ⟨blocks,released,same⟩ := memory
  have blocksEq : after.memory.blocks = blocks := (congrArg NativeByteMemory.State.blocks same).symm
  rw [blocksEq]
  exact NativeByteMemory.release_sublist before.memory.blocks pointer layout blocks released

/-- A sequence of actual heap deallocations. There are no byte writes,
allocations, address-only constructors or arbitrary state replacements. -/
inductive Releases : State → State → Prop where
  | refl (heap : State) : Releases heap heap
  | free {before middle after : State} (earlier : Releases before middle) (pointer : Pointer) (layout : Layout)
      (positive : 0 < layout.size) (valid : layout.Valid) (nonnull : pointer.address.val ≠ 0)
      (freed : NativePointerByteMemory.deallocate middle pointer layout = some after) : Releases before after

theorem Releases.trans {before middle after : State} (first : Releases before middle)
    (second : Releases middle after) : Releases before after := by
  induction second with
  | refl => exact first
  | free earlier pointer layout positive valid nonnull freed ih =>
    exact .free ih pointer layout positive valid nonnull freed

theorem Releases.no_growth {before after : State} (released : Releases before after) : count after ≤ count before := by
  induction released with
  | refl => exact Nat.le_refl _
  | free earlier pointer layout positive valid nonnull freed ih =>
    have removed := deallocate_count _ _ pointer layout freed
    omega

theorem Releases.unchanged {before after : State} (released : Releases before after)
    (same : count after = count before) : after = before := by
  cases released with
  | refl => rfl
  | free earlier pointer layout positive valid nonnull freed =>
    have previous := earlier.no_growth
    have removed := deallocate_count _ _ pointer layout freed
    omega

/-- A one-allocation loss identifies an actual single free on the original
heap, rather than just a final allocation count. -/
theorem Releases.single {before after : State} (released : Releases before after)
    (one : count after + 1 = count before) :
    ∃ pointer layout, 0 < layout.size ∧ layout.Valid ∧ pointer.address.val ≠ 0 ∧
      NativePointerByteMemory.deallocate before pointer layout = some after := by
  cases released with
  | refl => omega
  | @free middle after earlier pointer layout positive valid nonnull freed =>
    have removed := deallocate_count middle after pointer layout freed
    have sameCount : count middle = count before := by omega
    have same := earlier.unchanged sameCount
    subst middle
    exact ⟨pointer,layout,positive,valid,nonnull,freed⟩

theorem Releases.blocks_sublist {before after : State} (released : Releases before after) :
    after.memory.blocks.Sublist before.memory.blocks := by
  induction released with
  | refl => exact List.Sublist.refl _
  | free earlier pointer layout positive valid nonnull freed ih =>
    exact (deallocate_blocks _ _ pointer layout freed).trans ih

theorem Releases.generation {before after : State} (released : Releases before after) :
    after.memory.nextGeneration = before.memory.nextGeneration := by
  induction released with
  | refl => rfl
  | free earlier pointer layout positive valid nonnull freed ih =>
    obtain ⟨_,_,memory,_⟩ := NativePointerByteMemory.deallocate_success _ _ pointer layout freed
    exact (NativeByteMemory.deallocate_generation _ pointer layout _ memory).trans ih

theorem Releases.shadow_sublist {before after : State} (released : Releases before after) :
    after.shadow.Sublist before.shadow := by
  induction released with
  | refl => exact List.Sublist.refl _
  | free earlier pointer layout positive valid nonnull freed ih =>
    obtain ⟨owner,_,_,shadow⟩ := NativePointerByteMemory.deallocate_success _ _ pointer layout freed
    rw [shadow]
    exact List.filter_sublist.trans ih

/-- The removed pointer is the full base pointer of an originally live block.
Only metadata stored in that block is removed; dangling values stored in other
owners are retained, even if their pointed-to origin is the removed origin. -/
theorem Releases.single_block {before after : State} (released : Releases before after)
    (one : count after + 1 = count before) :
    ∃ block ∈ before.memory.blocks,
      0 < block.layout.size ∧ block.layout.Valid ∧ block.base.val ≠ 0 ∧
      NativePointerByteMemory.deallocate before block.pointer block.layout = some after ∧
      after.shadow = before.shadow.filter (fun cell => decide (cell.owner ≠ block.origin)) := by
  obtain ⟨pointer,layout,positive,valid,nonnull,freed⟩ := released.single one
  obtain ⟨owner,origin,memory,shadow⟩ := NativePointerByteMemory.deallocate_success before after pointer layout freed
  obtain ⟨block,member,samePointer,sameLayout⟩ := NativeByteMemory.deallocate_selected before.memory pointer layout after.memory memory
  subst pointer
  subst layout
  have sameOrigin : owner = block.origin := by
    change some block.origin = some owner at origin
    exact (Option.some.inj origin).symm
  subst owner
  exact ⟨block,member,positive,valid,nonnull,freed,shadow⟩

theorem release_readBlocks (blocks output : List Block) (pointer : Pointer) (layout : Layout)
    (freed : NativeByteMemory.releaseBlocks blocks pointer layout = some output)
    (query : Pointer) (size : Nat) (different : query.provenance ≠ pointer.provenance) :
    NativeByteRange.readBlocks output query size = NativeByteRange.readBlocks blocks query size := by
  induction blocks generalizing output with
  | nil => cases freed
  | cons block tail ih =>
    unfold NativeByteMemory.releaseBlocks at freed
    split at freed
    next selected =>
      rcases selected with ⟨rfl,rfl⟩
      cases freed
      have outside : ¬ NativeByteRange.Covers block query size := fun covered => different covered.1
      simp only [NativeByteRange.readBlocks, outside, ite_false]
    next =>
      cases rest : NativeByteMemory.releaseBlocks tail pointer layout with
      | none => simp only [rest, Option.map_none] at freed; cases freed
      | some kept =>
        simp only [rest, Option.map_some] at freed
        cases freed
        simp only [NativeByteRange.readBlocks, ih kept rest]

theorem deallocate_range_frame (before after : State) (pointer : Pointer) (layout : Layout)
    (freed : NativePointerByteMemory.deallocate before pointer layout = some after)
    (query : Pointer) (view : Layout) (different : query.provenance ≠ pointer.provenance) :
    NativeByteRange.loadRange after.memory query view = NativeByteRange.loadRange before.memory query view := by
  obtain ⟨_,_,memory,_⟩ := NativePointerByteMemory.deallocate_success before after pointer layout freed
  simp only [NativeByteMemory.deallocate, Option.map_eq_some_iff] at memory
  obtain ⟨blocks,released,same⟩ := memory
  have blocksEq : after.memory.blocks = blocks := (congrArg NativeByteMemory.State.blocks same).symm
  simp only [NativeByteRange.loadRange, blocksEq, release_readBlocks before.memory.blocks blocks pointer layout released query view.size different]

theorem shadow_lookup_filter_owner (cells : List NativePointerShadow.Cell)
    (removed owner : NativePointerStorage.Origin) (different : owner ≠ removed) (address : Nat) :
    NativePointerShadow.lookup (cells.filter (fun cell => decide (cell.owner ≠ removed))) owner address =
      NativePointerShadow.lookup cells owner address := by
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
    by_cases deleted : cell.owner = removed
    · have outside : cell.owner ≠ owner := by
        intro same
        exact different (same.symm.trans deleted)
      have test : decide (cell.owner ≠ removed) = false := by simp [deleted]
      simpa only [List.filter_cons, test, Bool.false_eq_true, ite_false, NativePointerShadow.lookup, outside, false_and] using ih
    · have test : decide (cell.owner ≠ removed) = true := by simp [deleted]
      simp only [List.filter_cons, test, ite_true, NativePointerShadow.lookup, ih]

theorem shadow_uniform_filter_owner (cells : List NativePointerShadow.Cell)
    (removed owner : NativePointerStorage.Origin) (different : owner ≠ removed) (base size : Nat) :
    NativePointerShadow.uniform (cells.filter (fun cell => decide (cell.owner ≠ removed))) owner base size =
      NativePointerShadow.uniform cells owner base size := by
  simp only [NativePointerShadow.uniform, shadow_lookup_filter_owner cells removed owner different]

theorem deallocate_load_frame (before after : State) (pointer : Pointer) (layout : Layout)
    (freed : NativePointerByteMemory.deallocate before pointer layout = some after)
    (slot : Pointer) (different : slot.provenance ≠ pointer.provenance) :
    NativePointerByteMemory.load after slot = NativePointerByteMemory.load before slot := by
  obtain ⟨owner,origin,_,shadow⟩ := NativePointerByteMemory.deallocate_success before after pointer layout freed
  have words : NativeWord64Memory.load after.memory slot = NativeWord64Memory.load before.memory slot := by
    simp only [NativeWord64Memory.load, deallocate_range_frame before after pointer layout freed slot ⟨8,8⟩ different]
  cases slotOrigin : slot.provenance with
  | none => simp only [NativePointerByteMemory.load, slotOrigin, Option.bind_eq_bind', Option.bind_none]
  | some storage =>
    have storageDifferent : storage ≠ owner := by
      intro same
      apply different
      rw [slotOrigin,origin,same]
    simp only [NativePointerByteMemory.load, slotOrigin, Option.bind_eq_bind', Option.bind_some,
      words,shadow,shadow_uniform_filter_owner _ owner storage storageDifferent]

end FormalProof4FHE.HasteBoots.NativeHeapRelease
