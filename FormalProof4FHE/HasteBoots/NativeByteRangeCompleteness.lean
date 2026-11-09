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
