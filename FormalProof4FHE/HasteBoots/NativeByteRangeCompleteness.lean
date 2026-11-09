module
public import FormalProof4FHE.HasteBoots.NativeResidentVec
@[expose] public section

/-! Initialized byte prefixes provide every bounded subrange. Unused allocation
capacity is not required to contain initialized bytes. These are modeled memory
facts; borrow permissions and source termination are separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeByteRangeCompleteness
open NativePointerStorage (Pointer)
open NativeByteMemory (Byte State)
open NativeByteRange

theorem readSpan_take (bytes : List (Option Byte)) (size requested : Nat) (output : List Byte)
    (read : readSpan bytes size = some output) (bounded : requested ≤ size) :
    readSpan bytes requested = some (output.take requested) := by
  induction requested generalizing bytes size output with
  | zero => simp only [readSpan,List.take_zero]
  | succ requested ih =>
    cases size with
    | zero => omega
    | succ size =>
      cases bytes with
      | nil => cases read
      | cons value tail =>
        cases value with
        | none => cases read
        | some byte =>
          cases rest : readSpan tail size with
          | none => simp only [readSpan,rest,Option.map_none] at read; cases read
          | some result =>
            simp only [readSpan,rest,Option.map_some,Option.some.injEq] at read
            subst output
            simp only [readSpan,List.take_succ_cons,ih tail size result rest (by omega),Option.map_some]

theorem readSpan_drop (bytes : List (Option Byte)) (size offset : Nat) (output : List Byte)
    (read : readSpan bytes size = some output) (bounded : offset ≤ size) :
    readSpan (bytes.drop offset) (size - offset) = some (output.drop offset) := by
  induction offset generalizing bytes size output with
  | zero => simpa only [List.drop_zero,Nat.sub_zero] using read
  | succ offset ih =>
    cases size with
    | zero => omega
    | succ size =>
      cases bytes with
      | nil => cases read
      | cons value tail =>
        cases value with
        | none => cases read
        | some byte =>
          cases rest : readSpan tail size with
          | none => simp only [readSpan,rest,Option.map_none] at read; cases read
          | some result =>
            simp only [readSpan,rest,Option.map_some,Option.some.injEq] at read
            subst output
            simpa only [List.drop_succ_cons,Nat.succ_sub_succ_eq_sub] using
              ih tail size result rest (by omega)

theorem readSpan_subrange (bytes : List (Option Byte)) (size offset requested : Nat) (output : List Byte)
    (read : readSpan bytes size = some output) (bounded : offset + requested ≤ size) :
    readSpan (bytes.drop offset) requested = some ((output.drop offset).take requested) :=
  readSpan_take _ (size - offset) requested _ (readSpan_drop bytes size offset output read (by omega)) (by omega)

/-- Adjacent initialized spans compose without assuming their surrounding bytes. -/
theorem readSpan_join (bytes : List (Option Byte)) (first second : Nat)
    (left right : List Byte) (initial : readSpan bytes first = some left)
    (following : readSpan (bytes.drop first) second = some right) :
    readSpan bytes (first + second) = some (left ++ right) := by
  induction first generalizing bytes left with
  | zero =>
    simp only [readSpan,Option.some.injEq] at initial
    subst left
    simpa only [Nat.zero_add,List.nil_append,List.drop_zero] using following
  | succ first ih =>
    cases bytes with
    | nil => cases initial
    | cons value tail =>
      cases value with
      | none => cases initial
      | some byte =>
        cases rest : readSpan tail first with
        | none => simp only [readSpan,rest,Option.map_none] at initial; cases initial
        | some output =>
          simp only [readSpan,rest,Option.map_some,Option.some.injEq] at initial
          subst left
          simp only [List.drop_succ_cons] at following
          simpa only [Nat.succ_add,readSpan,List.cons_append,Option.map_some] using
            congrArg (Option.map (byte :: ·)) (ih tail output rest following)

theorem block_origin_unique (blocks : List NativeByteMemory.Block)
    (unique : blocks.Pairwise (fun left right => left.origin ≠ right.origin))
    (left right : NativeByteMemory.Block) (leftMember : left ∈ blocks)
    (rightMember : right ∈ blocks) (same : left.origin = right.origin) : left = right := by
  induction blocks with
  | nil => cases leftMember
  | cons head tail ih =>
    obtain ⟨separated,remaining⟩ := List.pairwise_cons.mp unique
    rcases List.mem_cons.mp leftMember with rfl | laterLeft
    · rcases List.mem_cons.mp rightMember with rfl | laterRight
      · rfl
      · exact False.elim (separated right laterRight same)
    · rcases List.mem_cons.mp rightMember with rfl | laterRight
      · exact False.elim (separated left laterLeft same.symm)
      · exact ih remaining laterLeft laterRight

/-- Joining positive adjacent reads requires the same complete origin and a
well-formed heap; adjacent numerical addresses alone do not suffice. -/
theorem loadRange_join (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer shifted : Pointer) (first second alignment : Nat) (left right : List Byte)
    (firstPositive : 0 < first) (secondPositive : 0 < second)
    (atOffset : pointerAt pointer first = some shifted)
    (geometry : Geometry pointer ⟨first + second,alignment⟩)
    (initial : loadRange state pointer ⟨first,alignment⟩ = some left)
    (following : loadRange state shifted ⟨second,alignment⟩ = some right) :
    loadRange state pointer ⟨first + second,alignment⟩ = some (left ++ right) := by
  obtain ⟨firstBlock,firstMember,firstCover,firstRead⟩ :=
    loadRange_positive_selected state pointer _ firstPositive left initial
  obtain ⟨secondBlock,secondMember,secondCover,secondRead⟩ :=
    loadRange_positive_selected state shifted _ secondPositive right following
  obtain ⟨address,origin⟩ := pointerAt_fields pointer first shifted atOffset
  have same : firstBlock.origin = secondBlock.origin :=
    Option.some.inj (firstCover.1.symm.trans (origin.symm.trans secondCover.1))
  have blocksEqual := block_origin_unique state.blocks (valid.2.imp (fun pair => pair.2))
    firstBlock secondBlock firstMember secondMember same
  subst secondBlock
  have delta : shifted.address.val - firstBlock.base.val =
      (pointer.address.val - firstBlock.base.val) + first := by
    have lower := firstCover.2.1
    omega
  rw [delta,← List.drop_drop] at secondRead
  have joined := readSpan_join _ first second left right firstRead secondRead
  have covered : Covers firstBlock pointer (first + second) := by
    refine ⟨firstCover.1,firstCover.2.1,?_⟩
    have upper : shifted.address.val + second ≤ firstBlock.base.val + firstBlock.layout.size := secondCover.2.2
    change pointer.address.val + (first + second) ≤ firstBlock.base.val + firstBlock.layout.size
    omega
  exact loadRange_of_ready state valid pointer ⟨first + second,alignment⟩ geometry (by change 0 < first + second; omega)
    firstBlock firstMember covered _ joined

theorem byte_geometry_subrange (pointer shifted : Pointer) (size offset requested : Nat)
    (geometry : Geometry pointer ⟨size,1⟩) (bounded : offset + requested ≤ size)
    (atOffset : pointerAt pointer offset = some shifted) : Geometry shifted ⟨requested,1⟩ := by
  obtain ⟨address,_⟩ := pointerAt_fields pointer offset shifted atOffset
  obtain ⟨layout,nonnull,_,noWrap⟩ := geometry
  change pointer.address.val + size < 2^64 at noWrap
  refine ⟨⟨by change (1 : Nat) ∈ (List.range 64).map (fun exponent => 2 ^ exponent); decide,?_⟩,?_,by simp only [Nat.mod_one],?_⟩
  · have limit := layout.2
    simp only [Nat.sub_self,Nat.add_zero] at limit ⊢
    omega
  · rw [address]
    omega
  · change shifted.address.val + requested < 2^64
    rw [address]
    omega

/-- Every bounded subrange of an initialized byte prefix is initialized with
exactly the corresponding bytes, retaining the complete pointer origin. -/
theorem loadRange_subrange (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (size offset requested : Nat) (output : List Byte)
    (loaded : loadRange state pointer ⟨size,1⟩ = some output) (bounded : offset + requested ≤ size) :
    ∃ shifted, pointerAt pointer offset = some shifted ∧
      loadRange state shifted ⟨requested,1⟩ = some ((output.drop offset).take requested) := by
  have geometry := loadRange_geometry state pointer ⟨size,1⟩ output loaded
  have noWrap := geometry.2.2.2
  change pointer.address.val + size < 2^64 at noWrap
  have addressBound : pointer.address.val + offset < 2^64 := by omega
  let shifted : Pointer := ⟨⟨pointer.address.val + offset,addressBound⟩,pointer.provenance⟩
  have atOffset : pointerAt pointer offset = some shifted := by
    simp only [pointerAt,addressBound,↓reduceDIte,shifted]
  refine ⟨shifted,atOffset,?_⟩
  have subGeometry := byte_geometry_subrange pointer shifted size offset requested geometry bounded atOffset
  by_cases empty : requested = 0
  · subst requested
    simpa only [List.take_zero] using empty_range state shifted 1 subGeometry
  · have positive : 0 < requested := Nat.pos_of_ne_zero empty
    have sizePositive : size ≠ 0 := by omega
    have blocksRead : readBlocks state.blocks pointer size = some output := by
      simpa only [loadRange,geometry,ite_true,sizePositive,ite_false] using loaded
    obtain ⟨block,member,covered,initialized⟩ := readBlocks_selected state.blocks pointer size output blocksRead
    have subCovered : Covers block shifted requested := by
      refine ⟨covered.1,?_,?_⟩ <;> dsimp only [shifted] <;> have start := covered.2.1 <;> have finish := covered.2.2 <;> omega
    have subInitialized := readSpan_subrange _ size offset requested output initialized bounded
    have delta : shifted.address.val - block.base.val = (pointer.address.val - block.base.val) + offset := by
      dsimp only [shifted]
      have start := covered.2.1
      omega
    rw [List.drop_drop,← delta] at subInitialized
    exact loadRange_of_ready state valid shifted ⟨requested,1⟩ subGeometry positive block member subCovered _ subInitialized
end FormalProof4FHE.HasteBoots.NativeByteRangeCompleteness

namespace FormalProof4FHE.HasteBoots.NativeResidentVec
open NativePointerStorage (Pointer)

/-- The stored fields initialize the whole header, including the pointer bytes.
The complete pointer origin remains a separate shadow-memory observation. -/
theorem Descriptor.header_initialized {world : NativeReferenceMachine.State} {index : Nat}
    (descriptor : Descriptor world index)
    (valid : NativeByteMemory.WellFormed world.pointers.heap.memory) :
    ∃ bytes, NativeByteRange.loadRange world.pointers.heap.memory descriptor.lease.pointer
      ⟨24,8⟩ = some bytes := by
  have wordBytes (slot : Pointer) (word : NativeWord64Memory.Word)
      (stored : NativeWord64Memory.load world.pointers.heap.memory slot = some word) :
      ∃ bytes, NativeByteRange.loadRange world.pointers.heap.memory slot ⟨8,8⟩ = some bytes := by
    simp only [NativeWord64Memory.load,Option.bind_eq_some_iff] at stored
    obtain ⟨bytes,read,_⟩ := stored
    exact ⟨bytes,read⟩
  obtain ⟨capacityBytes,capacityRead⟩ := wordBytes _ _ descriptor.capacityStored
  obtain ⟨_,_,pointerWord,_⟩ := NativePointerByteMemory.load_success _ _ _ descriptor.pointerStored
  obtain ⟨pointerBytes,pointerRead⟩ := wordBytes _ _ pointerWord
  obtain ⟨lengthBytes,lengthRead⟩ := wordBytes _ _ descriptor.lengthStored
  have capacityEq : descriptor.capacitySlot = descriptor.lease.pointer := by
    have atZero : NativeByteRange.pointerAt descriptor.lease.pointer 0 = some descriptor.lease.pointer := by
      simp only [NativeByteRange.pointerAt,Nat.add_zero,descriptor.lease.pointer.address.isLt,↓reduceDIte]
    exact Option.some.inj (descriptor.capacityAt.symm.trans atZero)
  rw [capacityEq] at capacityRead
  have capGeometry := NativeByteRange.loadRange_geometry _ _ _ _ capacityRead
  have lenGeometry := NativeByteRange.loadRange_geometry _ _ _ _ lengthRead
  have lengthAddress := (NativeByteRange.pointerAt_fields _ _ _ descriptor.lengthAt).1
  have geometry (size : Nat) (bound : size ≤ 24) (layout : (NativeByteMemory.Layout.mk size 8).Valid) :
      NativeByteRange.Geometry descriptor.lease.pointer ⟨size,8⟩ := by
    refine ⟨layout,capGeometry.2.1,capGeometry.2.2.1,?_⟩
    have endBound : descriptor.lengthSlot.address.val + 8 < 2^64 := lenGeometry.2.2.2
    change descriptor.lease.pointer.address.val + size < 2^64
    omega
  have firstRead := NativeByteRangeCompleteness.loadRange_join _ valid _ _ 8 8 8
    capacityBytes pointerBytes (by decide) (by decide) descriptor.pointerAt
    (geometry 16 (by decide) (by decide)) capacityRead pointerRead
  exact ⟨_,NativeByteRangeCompleteness.loadRange_join _ valid _ _ 16 8 8
    _ lengthBytes (by decide) (by decide) descriptor.lengthAt
    (geometry 24 (by decide) (by decide)) firstRead lengthRead⟩

theorem InitializedElements.subrange {world : NativeReferenceMachine.State} {index : Nat}
    {descriptor : Descriptor world index} (initialized : InitializedElements descriptor)
    (valid : NativeByteMemory.WellFormed world.pointers.heap.memory) (offset size : Nat)
    (bounded : offset + size ≤ descriptor.length.val) :
    ∃ pointer bytes, NativeByteRange.pointerAt descriptor.buffer offset = some pointer ∧
      NativeByteRange.loadRange world.pointers.heap.memory pointer ⟨size,1⟩ = some bytes := by
  obtain ⟨bytes,loaded⟩ := initialized
  obtain ⟨pointer,shifted,read⟩ := NativeByteRangeCompleteness.loadRange_subrange _ valid descriptor.buffer
    descriptor.length.val offset size bytes loaded bounded
  exact ⟨pointer,_,shifted,read⟩

theorem InitializedElements.byte {world : NativeReferenceMachine.State} {index : Nat}
    {descriptor : Descriptor world index} (initialized : InitializedElements descriptor)
    (valid : NativeByteMemory.WellFormed world.pointers.heap.memory) (offset : Nat)
    (bounded : offset < descriptor.length.val) :
    ∃ pointer byte, NativeByteRange.pointerAt descriptor.buffer offset = some pointer ∧
      NativeByteRange.loadRange world.pointers.heap.memory pointer ⟨1,1⟩ = some [byte] := by
  obtain ⟨pointer,bytes,shifted,loaded⟩ := initialized.subrange valid offset 1 (by omega)
  have size := NativeByteRange.loadRange_length _ pointer ⟨1,1⟩ bytes loaded
  cases bytes with
  | nil => cases size
  | cons byte tail =>
    have empty : tail = [] := List.eq_nil_of_length_eq_zero (by simpa only [List.length_cons] using Nat.succ.inj size)
    subst tail
    exact ⟨pointer,byte,shifted,loaded⟩
end FormalProof4FHE.HasteBoots.NativeResidentVec
