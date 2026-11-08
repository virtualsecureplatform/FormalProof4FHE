module
public import FormalProof4FHE.HasteBoots.NativeByteBorrow
@[expose] public section

/-! Current heap range views after actual byte stores. Views are observations,
not extra borrow permissions or physical-work steps. -/
namespace FormalProof4FHE.HasteBoots.NativeByteRangeUpdate
open NativePointerStorage (Pointer)
open NativeByteMemory (Byte Block Layout)
open NativeByteRange

theorem readSpan_set (bytes : List (Option Byte)) (size : Nat) (output : List Byte)
    (read : readSpan bytes size = some output) (index : Nat) (inside : index < size) (byte : Byte) :
    readSpan (bytes.set index (some byte)) size = some (output.set index byte) := by
  induction size generalizing bytes output index with
  | zero => omega
  | succ size ih =>
    cases bytes with
    | nil => cases read
    | cons head tail =>
      cases head with
      | none => cases read
      | some value =>
        unfold readSpan at read
        cases rest : readSpan tail size with
        | none => simp only [rest, Option.map_none] at read; cases read
        | some values =>
          simp only [rest, Option.map_some] at read
          cases read
          cases index with
          | zero => simp only [List.set_cons_zero, readSpan, rest, Option.map_some]
          | succ index =>
            simp only [List.set_cons_succ, readSpan,
              ih tail values rest index (by omega), Option.map_some]

theorem readSpan_drop_set (bytes : List (Option Byte)) (start size : Nat) (output : List Byte)
    (read : readSpan (bytes.drop start) size = some output) (index : Nat)
    (inside : index < size) (byte : Byte) :
    readSpan ((bytes.set (start + index) (some byte)).drop start) size = some (output.set index byte) := by
  rw [← List.set_drop]
  exact readSpan_set _ _ _ read index inside byte

theorem covered_offset_matches (block : Block) (pointer reference : Pointer) (size index : Nat)
    (covered : Covers block pointer size) (nonzero : pointer.address.val ≠ 0) (inside : index < size)
    (address : reference.address.val = pointer.address.val + index)
    (origin : reference.provenance = pointer.provenance) : NativeByteMemory.Matches block reference := by
  refine ⟨origin.trans covered.1, ?_, ?_, ?_⟩
  · omega
  · have lower := covered.2.1; omega
  · have upper := covered.2.2; omega

theorem storeBlocks_range (blocks : List Block)
    (unique : blocks.Pairwise (fun left right => left.origin ≠ right.origin))
    (pointer reference : Pointer) (size : Nat) (output : List Byte)
    (read : readBlocks blocks pointer size = some output)
    (nonzero : pointer.address.val ≠ 0) (index : Nat) (inside : index < size)
    (address : reference.address.val = pointer.address.val + index)
    (origin : reference.provenance = pointer.provenance) (byte : Byte) (next : List Block)
    (stored : NativeByteMemory.storeBlocks blocks reference byte = some next) :
    readBlocks next pointer size = some (output.set index byte) := by
  induction blocks generalizing next with
  | nil => cases read
  | cons block tail ih =>
    obtain ⟨separated, uniqueTail⟩ := List.pairwise_cons.mp unique
    unfold readBlocks at read
    split at read
    next covered =>
      have matched := covered_offset_matches block pointer reference size index covered nonzero inside address origin
      simp only [NativeByteMemory.storeBlocks, ite_eq_left matched] at stored
      split at stored
      next =>
        cases stored
        have lower := covered.2.1
        have offset : reference.address.val - block.base.val = pointer.address.val - block.base.val + index := by omega
        simp only [readBlocks, Covers] at covered ⊢
        rw [ite_eq_left covered, offset]
        exact readSpan_drop_set block.bytes _ size output read index inside byte
      next => cases stored
    next notCovered =>
      have notMatched : ¬ NativeByteMemory.Matches block reference := by
        intro matched
        obtain ⟨selected, member, covered, _⟩ := readBlocks_selected tail pointer size output read
        exact separated selected member (Option.some.inj (matched.1.symm.trans (origin.trans covered.1)))
      simp only [NativeByteMemory.storeBlocks, ite_eq_right notMatched] at stored
      cases rest : NativeByteMemory.storeBlocks tail reference byte with
      | none => simp only [rest, Option.map_none] at stored; cases stored
      | some updated =>
        simp only [rest, Option.map_some] at stored
        cases stored
        simp only [readBlocks, ite_eq_right notCovered]
        exact ih uniqueTail read updated rest

theorem storeByte_range (state next : NativeByteMemory.State)
    (valid : NativeByteMemory.WellFormed state) (pointer : Pointer) (layout : Layout)
    (output : List Byte) (read : loadRange state pointer layout = some output)
    (index : Nat) (inside : index < layout.size) (reference : Pointer)
    (advanced : pointerAt pointer index = some reference) (byte : Byte)
    (stored : NativeByteMemory.storeByte state reference byte = some next) :
    loadRange next pointer layout = some (output.set index byte) := by
  have geometry := loadRange_geometry state pointer layout output read
  have positive : layout.size ≠ 0 := by omega
  have fields := pointerAt_fields pointer index reference advanced
  simp only [loadRange, ite_eq_left geometry, ite_eq_right positive] at read ⊢
  unfold NativeByteMemory.storeByte at stored
  cases result : NativeByteMemory.storeBlocks state.blocks reference byte with
  | none => simp only [result, Option.map_none] at stored; cases stored
  | some blocks =>
    simp only [result, Option.map_some] at stored
    cases stored
    exact storeBlocks_range state.blocks (valid.2.imp (fun pair => pair.2)) pointer reference
      layout.size output read geometry.2.1 index inside fields.1 fields.2 byte blocks result

theorem borrowed_write_range (state next : NativeByteBorrow.State)
    (valid : NativeByteMemory.WellFormed state.memory) (tag index : Nat) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases tag = some lease) (output : List Byte)
    (view : loadRange state.memory lease.pointer lease.layout = some output) (byte : Byte)
    (written : NativeByteBorrow.write state tag index byte = some next) :
    loadRange next.memory lease.pointer lease.layout = some (output.set index byte) := by
  obtain ⟨actual, reference, actualFound, _, inside, advanced, _, stored, _, _⟩ :=
    NativeByteBorrow.write_success state tag index byte next written
  have same : actual = lease := Option.some.inj (actualFound.symm.trans found)
  subst actual
  exact storeByte_range state.memory next.memory valid lease.pointer lease.layout output view
    index inside reference advanced byte stored

theorem pointerAt_zero (pointer : Pointer) : pointerAt pointer 0 = some pointer := by
  unfold pointerAt
  simp only [Nat.add_zero, dite_eq_left pointer.address.isLt]

theorem borrowed_read_selected (state : NativeByteBorrow.State)
    (valid : NativeByteMemory.WellFormed state.memory) (tag index : Nat) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases tag = some lease) (output : List Byte)
    (view : loadRange state.memory lease.pointer lease.layout = some output) (byte : Byte)
    (read : NativeByteBorrow.read state tag index 1 = some [byte]) : output[index]? = some byte := by
  obtain ⟨actual, reference, actualFound, inside, advanced, _, loaded⟩ :=
    NativeByteBorrow.read_success state tag index 1 [byte] read
  have same : actual = lease := Option.some.inj (actualFound.symm.trans found)
  subst actual
  have size := loadRange_length state.memory lease.pointer lease.layout output view
  have bound : index < output.length := by omega
  have selected : output[index]? = some output[index] := List.getElem?_eq_getElem bound
  obtain ⟨snapshotRef, snapshotAdvanced, snapshotLoad⟩ :=
    range_agrees_with_byte_load state.memory valid lease.pointer lease.layout output view index (by omega) _ selected
  have equalRef : snapshotRef = reference := Option.some.inj (snapshotAdvanced.symm.trans advanced)
  subst snapshotRef
  obtain ⟨readRef, readAdvanced, readLoad⟩ :=
    range_agrees_with_byte_load state.memory valid reference ⟨1, 1⟩ [byte] loaded 0 (by decide) byte rfl
  rw [pointerAt_zero] at readAdvanced
  have equalRead : reference = readRef := Option.some.inj readAdvanced
  subst readRef
  have equalByte := Option.some.inj (snapshotLoad.symm.trans readLoad)
  exact selected.trans (congrArg some equalByte)

theorem storeBlocks_of_load (blocks : List Block) (pointer : Pointer) (previous : Byte)
    (loaded : NativeByteMemory.loadBlocks blocks pointer = some previous) (byte : Byte) :
    ∃ next, NativeByteMemory.storeBlocks blocks pointer byte = some next := by
  induction blocks with
  | nil => cases loaded
  | cons block tail ih =>
    unfold NativeByteMemory.loadBlocks at loaded
    split at loaded
    next matched =>
      have bound : pointer.address.val - block.base.val < block.bytes.length := by
        by_contra outside
        have missing := List.getElem?_eq_none (Nat.le_of_not_lt outside)
        rw [missing] at loaded
        cases loaded
      exact ⟨{block with bytes := block.bytes.set (pointer.address.val - block.base.val) (some byte)} :: tail,
        by simp only [NativeByteMemory.storeBlocks, ite_eq_left matched, ite_eq_left bound]⟩
    next notMatched =>
      obtain ⟨next, stored⟩ := ih loaded
      exact ⟨block :: next, by simp only [NativeByteMemory.storeBlocks, ite_eq_right notMatched, stored, Option.map_some]⟩

theorem storeByte_of_range (state : NativeByteMemory.State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (layout : Layout) (output : List Byte)
    (view : loadRange state pointer layout = some output) (index : Nat) (inside : index < layout.size)
    (reference : Pointer) (advanced : pointerAt pointer index = some reference) (byte : Byte) :
    ∃ next, NativeByteMemory.storeByte state reference byte = some next := by
  have length := loadRange_length state pointer layout output view
  have bound : index < output.length := by omega
  obtain ⟨actual, actualAdvanced, loaded⟩ := range_agrees_with_byte_load state valid pointer layout output view
    index inside output[index] (List.getElem?_eq_getElem bound)
  have same : actual = reference := Option.some.inj (actualAdvanced.symm.trans advanced)
  subst actual
  obtain ⟨blocks, stored⟩ := storeBlocks_of_load state.blocks reference output[index] loaded byte
  exact ⟨{state with blocks}, by simp only [NativeByteMemory.storeByte, stored, Option.map_some]⟩

theorem borrowed_write_of_allowed (state : NativeByteBorrow.State)
    (valid : NativeByteMemory.WellFormed state.memory) (tag index : Nat) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases tag = some lease) (exclusive : lease.mode = .exclusive)
    (output : List Byte) (view : loadRange state.memory lease.pointer lease.layout = some output)
    (inside : index < lease.layout.size) (reference : Pointer)
    (advanced : pointerAt lease.pointer index = some reference)
    (allowed : NativeByteBorrow.throughAllowed state tag .exclusive reference ⟨1, 1⟩ = true) (byte : Byte) :
    ∃ next, NativeByteBorrow.write state tag index byte = some next := by
  obtain ⟨memory, stored⟩ := storeByte_of_range state.memory valid lease.pointer lease.layout output view index inside reference advanced byte
  refine ⟨{state with memory}, ?_⟩
  simp only [NativeByteBorrow.write, found, Option.bind, ite_eq_left (And.intro exclusive inside),
    advanced, ite_eq_left allowed, stored, Option.map_some]

end FormalProof4FHE.HasteBoots.NativeByteRangeUpdate
