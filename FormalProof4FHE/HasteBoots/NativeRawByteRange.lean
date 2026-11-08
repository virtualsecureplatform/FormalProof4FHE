module
public import FormalProof4FHE.HasteBoots.NativeByteRangeWrite
@[expose] public section

/-! Untyped cell snapshots and replacement preserve initialization state.
These are memory-policy operations, not a native memcpy/atomicity/cost proof. -/
namespace FormalProof4FHE.HasteBoots.NativeRawByteRange
open NativePointerStorage (Pointer)
open NativeByteMemory (Byte Block Layout State)
open NativeByteRange (Geometry Covers)

abbrev Cell := Option Byte

def overwrite (bytes : List Cell) (offset : Nat) (values : List Cell) : List Cell :=
  bytes.take offset ++ (values ++ bytes.drop (offset + values.length))

def readBlocks : List Block → Pointer → Nat → Option (List Cell)
  | [], _, _ => none
  | block :: tail, pointer, size =>
    if Covers block pointer size then
      let values := (block.bytes.drop (pointer.address.val - block.base.val)).take size
      if values.length = size then some values else none
    else readBlocks tail pointer size

def loadRange (state : State) (pointer : Pointer) (layout : Layout) : Option (List Cell) :=
  if Geometry pointer layout then
    if layout.size = 0 then some [] else readBlocks state.blocks pointer layout.size
  else none

def storeBlocks : List Block → Pointer → List Cell → Option (List Block)
  | [], _, _ => none
  | block :: tail, pointer, values =>
    if Covers block pointer values.length then
      let offset := pointer.address.val - block.base.val
      if offset + values.length ≤ block.bytes.length then
        some ({block with bytes := overwrite block.bytes offset values} :: tail)
      else none
    else (storeBlocks tail pointer values).map (block :: ·)

def storeRange (state : State) (pointer : Pointer) (alignment : Nat) (values : List Cell) : Option State :=
  if Geometry pointer ⟨values.length, alignment⟩ then
    if values.isEmpty then some state
    else (storeBlocks state.blocks pointer values).map (fun blocks => {state with blocks})
  else none

/-- Positive copies snapshot before replacement, permitting overlap. Empty
untyped copies check alignment without requiring a dereferenceable pointer. -/
def copy (state : State) (source target : Pointer) (size alignment : Nat) : Option State :=
  if size = 0 then
    if (⟨0, alignment⟩ : Layout).Valid ∧ source.address.val % alignment = 0 ∧ target.address.val % alignment = 0 then some state
    else none
  else (loadRange state source ⟨size, alignment⟩).bind (storeRange state target alignment)

def copyNonoverlapping (state : State) (source target : Pointer) (size alignment : Nat) : Option State :=
  if ¬ NativeByteBorrow.Overlap source ⟨size, alignment⟩ target ⟨size, alignment⟩ then
    copy state source target size alignment
  else none

theorem overwrite_length (bytes : List Cell) (offset : Nat) (values : List Cell)
    (fits : offset + values.length ≤ bytes.length) : (overwrite bytes offset values).length = bytes.length := by
  simp only [overwrite, List.length_append, List.length_take, List.length_drop]
  omega

theorem overwrite_drop (bytes : List Cell) (offset : Nat) (values : List Cell)
    (fits : offset ≤ bytes.length) :
    (overwrite bytes offset values).drop offset = values ++ bytes.drop (offset + values.length) := by
  simp only [overwrite, List.drop_append, List.drop_take, Nat.sub_self, List.take_zero, List.nil_append,
    List.length_take, Nat.min_eq_left fits, List.drop_zero, Nat.zero_sub]

theorem overwrite_take (bytes : List Cell) (offset : Nat) (values : List Cell)
    (fits : offset ≤ bytes.length) :
    ((overwrite bytes offset values).drop offset).take values.length = values := by
  rw [overwrite_drop bytes offset values fits]
  exact List.take_left

theorem overwrite_frame (bytes : List Cell) (offset : Nat) (values : List Cell)
    (fits : offset ≤ bytes.length) (index : Nat) (outside : index < offset ∨ offset + values.length ≤ index) :
    (overwrite bytes offset values)[index]? = bytes[index]? := by
  rcases outside with before | after
  · simp only [overwrite, List.getElem?_append, List.length_take, Nat.min_eq_left fits, ite_eq_left before, List.getElem?_take]
  · have notBefore : ¬ index < offset := by omega
    have notInside : ¬ index - offset < values.length := by omega
    have address : offset + values.length + (index - offset - values.length) = index := by omega
    simp only [overwrite, List.getElem?_append, List.length_take, Nat.min_eq_left fits, ite_eq_right notBefore,
      ite_eq_right notInside, List.getElem?_drop, address]

theorem readBlocks_selected (blocks : List Block) (pointer : Pointer) (size : Nat) (values : List Cell)
    (loaded : readBlocks blocks pointer size = some values) :
    ∃ block ∈ blocks, Covers block pointer size ∧ values.length = size ∧
      values = (block.bytes.drop (pointer.address.val - block.base.val)).take size := by
  induction blocks with
  | nil => cases loaded
  | cons block tail ih =>
    unfold readBlocks at loaded
    dsimp only at loaded
    split at loaded
    next covered =>
      split at loaded
      next length => cases loaded; exact ⟨block, List.mem_cons_self, covered, length, rfl⟩
      next => cases loaded
    next =>
      obtain ⟨selected, member, covered, length, bytes⟩ := ih loaded
      exact ⟨selected, List.mem_cons_of_mem block member, covered, length, bytes⟩

theorem loadRange_length (state : State) (pointer : Pointer) (layout : Layout) (values : List Cell)
    (loaded : loadRange state pointer layout = some values) : values.length = layout.size := by
  unfold loadRange at loaded
  split at loaded
  · split at loaded
    next zero => cases loaded; exact zero.symm
    next =>
      obtain ⟨_, _, _, length, _⟩ := readBlocks_selected _ _ _ _ loaded
      exact length
  · cases loaded

theorem loadRange_geometry (state : State) (pointer : Pointer) (layout : Layout) (values : List Cell)
    (loaded : loadRange state pointer layout = some values) : Geometry pointer layout := by
  unfold loadRange at loaded
  split at loaded
  · assumption
  · cases loaded

theorem storeBlocks_shape (blocks : List Block) (pointer : Pointer) (values : List Cell) (next : List Block)
    (stored : storeBlocks blocks pointer values = some next) :
    next.map NativeByteMemory.shape = blocks.map NativeByteMemory.shape := by
  induction blocks generalizing next with
  | nil => cases stored
  | cons block tail ih =>
    unfold storeBlocks at stored
    dsimp only at stored
    split at stored
    next =>
      split at stored
      next fits => cases stored; simp only [List.map_cons, NativeByteMemory.shape, overwrite_length block.bytes _ values fits]
      next => cases stored
    next =>
      cases rest : storeBlocks tail pointer values with
      | none => simp only [rest, Option.map_none] at stored; cases stored
      | some result =>
        simp only [rest, Option.map_some] at stored
        cases stored
        simp only [List.map_cons, ih result rest]

theorem storeBlocks_read (blocks : List Block) (pointer : Pointer) (values : List Cell) (next : List Block)
    (stored : storeBlocks blocks pointer values = some next) : readBlocks next pointer values.length = some values := by
  induction blocks generalizing next with
  | nil => cases stored
  | cons block tail ih =>
    unfold storeBlocks at stored
    dsimp only at stored
    split at stored
    next covered =>
      split at stored
      next fits =>
        cases stored
        simp only [readBlocks, Covers] at covered ⊢
        rw [ite_eq_left covered, overwrite_take block.bytes _ values (by omega)]
        simp only [ite_true]
      next => cases stored
    next notCovered =>
      cases rest : storeBlocks tail pointer values with
      | none => simp only [rest, Option.map_none] at stored; cases stored
      | some result =>
        simp only [rest, Option.map_some] at stored
        cases stored
        simp only [readBlocks, ite_eq_right notCovered]
        exact ih result rest

theorem storeRange_success (state next : State) (pointer : Pointer) (alignment : Nat) (values : List Cell)
    (stored : storeRange state pointer alignment values = some next) :
    Geometry pointer ⟨values.length, alignment⟩ ∧ next.nextGeneration = state.nextGeneration ∧
      next.blocks.map NativeByteMemory.shape = state.blocks.map NativeByteMemory.shape := by
  unfold storeRange at stored
  split at stored
  next geometry =>
    split at stored
    · cases stored; exact ⟨geometry, rfl, rfl⟩
    · cases result : storeBlocks state.blocks pointer values with
      | none => simp only [result, Option.map_none] at stored; cases stored
      | some blocks =>
        simp only [result, Option.map_some] at stored
        cases stored
        exact ⟨geometry, rfl, storeBlocks_shape state.blocks pointer values blocks result⟩
  next => cases stored

theorem storeRange_wellFormed (state next : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (alignment : Nat) (values : List Cell)
    (stored : storeRange state pointer alignment values = some next) : NativeByteMemory.WellFormed next := by
  obtain ⟨_, generation, shape⟩ := storeRange_success state next pointer alignment values stored
  apply (NativeByteMemory.wellFormed_shape next).mp
  rw [generation, shape]
  exact (NativeByteMemory.wellFormed_shape state).mpr valid

theorem storeRange_then_load (state next : State) (pointer : Pointer) (alignment : Nat) (values : List Cell)
    (stored : storeRange state pointer alignment values = some next) : loadRange next pointer ⟨values.length, alignment⟩ = some values := by
  unfold storeRange at stored
  split at stored
  next geometry =>
    split at stored
    next empty =>
      have nil := List.isEmpty_iff.mp empty
      subst values
      cases stored
      change Geometry pointer ⟨0, alignment⟩ at geometry
      simp only [loadRange, List.length_nil, ite_eq_left geometry, ite_true]
    next nonempty =>
      cases result : storeBlocks state.blocks pointer values with
      | none => simp only [result, Option.map_none] at stored; cases stored
      | some blocks =>
        simp only [result, Option.map_some] at stored
        cases stored
        have nonzero : values.length ≠ 0 := by
          intro zero
          have nil := List.eq_nil_of_length_eq_zero zero
          subst values
          exact nonempty rfl
        simp only [loadRange, ite_eq_left geometry, ite_eq_right nonzero]
        exact storeBlocks_read state.blocks pointer values blocks result
  next => cases stored

theorem overwrite_initialized (bytes : List Cell) (offset : Nat) (values : List Byte) :
    overwrite bytes offset (values.map some) = NativeByteRangeWrite.overwrite bytes offset values := by
  simp only [overwrite, List.length_map, NativeByteRangeWrite.overwrite]

theorem storeBlocks_initialized (blocks : List Block) (pointer : Pointer) (values : List Byte) :
    storeBlocks blocks pointer (values.map some) = NativeByteRangeWrite.storeBlocks blocks pointer values := by
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
    simp only [storeBlocks, List.length_map, overwrite_initialized, NativeByteRangeWrite.storeBlocks]
    split
    · rfl
    · rw [ih]

theorem storeRange_initialized (state : State) (pointer : Pointer) (alignment : Nat) (values : List Byte) :
    storeRange state pointer alignment (values.map some) = NativeByteRangeWrite.storeRange state pointer alignment values := by
  simp only [storeRange, List.length_map, List.isEmpty_map, storeBlocks_initialized, NativeByteRangeWrite.storeRange]

theorem storeBlocks_available (blocks : List Block) (valid : ∀ block ∈ blocks, block.Valid)
    (pointer : Pointer) (values : List Cell) (covered : ∃ block ∈ blocks, Covers block pointer values.length) :
    ∃ next, storeBlocks blocks pointer values = some next := by
  induction blocks with
  | nil => obtain ⟨_, member, _⟩ := covered; cases member
  | cons block tail ih =>
    by_cases here : Covers block pointer values.length
    · have length := (valid block List.mem_cons_self).2.2.2.2.2
      have fits : pointer.address.val - block.base.val + values.length ≤ block.bytes.length := by
        have lower := here.2.1
        have upper := here.2.2
        omega
      exact ⟨{block with bytes := overwrite block.bytes (pointer.address.val - block.base.val) values} :: tail,
        by simp only [storeBlocks, ite_eq_left here, ite_eq_left fits]⟩
    · obtain ⟨selected, member, range⟩ := covered
      have later : selected ∈ tail := by
        rcases List.mem_cons.mp member with same | later
        · subst selected; exact False.elim (here range)
        · exact later
      obtain ⟨next, stored⟩ := ih (fun selected member => valid selected (List.mem_cons_of_mem block member)) ⟨selected, later, range⟩
      exact ⟨block :: next, by simp only [storeBlocks, ite_eq_right here, stored, Option.map_some]⟩

theorem readBlocks_available (blocks : List Block) (valid : ∀ block ∈ blocks, block.Valid)
    (pointer : Pointer) (size : Nat) (covered : ∃ block ∈ blocks, Covers block pointer size) :
    ∃ values, readBlocks blocks pointer size = some values := by
  induction blocks with
  | nil => obtain ⟨_, member, _⟩ := covered; cases member
  | cons block tail ih =>
    by_cases here : Covers block pointer size
    · have length := (valid block List.mem_cons_self).2.2.2.2.2
      have fits : size ≤ block.bytes.length - (pointer.address.val - block.base.val) := by
        have lower := here.2.1
        have upper := here.2.2
        omega
      refine ⟨(block.bytes.drop (pointer.address.val - block.base.val)).take size, ?_⟩
      simp only [readBlocks, ite_eq_left here, List.length_take, List.length_drop, Nat.min_eq_left fits, ite_true]
    · obtain ⟨selected, member, range⟩ := covered
      have later : selected ∈ tail := by
        rcases List.mem_cons.mp member with same | later
        · subst selected; exact False.elim (here range)
        · exact later
      obtain ⟨values, loaded⟩ := ih (fun selected member => valid selected (List.mem_cons_of_mem block member)) ⟨selected, later, range⟩
      exact ⟨values, by simp only [readBlocks, ite_eq_right here, loaded]⟩

theorem loadRange_of_checked (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (layout : Layout) (checked : NativeByteRange.checkRange state pointer layout = true) :
    ∃ values, loadRange state pointer layout = some values := by
  unfold NativeByteRange.checkRange at checked
  simp only [Bool.and_eq_true] at checked
  have geometry : Geometry pointer layout := of_decide_eq_true checked.1
  by_cases zero : layout.size = 0
  · exact ⟨[], by simp only [loadRange, ite_eq_left geometry, ite_eq_left zero]⟩
  · have any := checked.2
    rw [ite_eq_right zero] at any
    obtain ⟨block, member, covered⟩ := List.any_eq_true.mp any
    obtain ⟨values, loaded⟩ := readBlocks_available state.blocks (fun block member => (valid.1 block member).1)
      pointer layout.size ⟨block, member, of_decide_eq_true covered⟩
    exact ⟨values, by simp only [loadRange, ite_eq_left geometry, ite_eq_right zero, loaded]⟩

theorem storeRange_of_checked (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (alignment : Nat) (values : List Cell)
    (checked : NativeByteRange.checkRange state pointer ⟨values.length, alignment⟩ = true) :
    ∃ next, storeRange state pointer alignment values = some next := by
  unfold NativeByteRange.checkRange at checked
  simp only [Bool.and_eq_true] at checked
  have geometry : Geometry pointer ⟨values.length, alignment⟩ := of_decide_eq_true checked.1
  cases values with
  | nil => exact ⟨state, by simp only [storeRange, ite_eq_left geometry, List.isEmpty_nil, ite_true]⟩
  | cons byte values =>
    have any := checked.2
    simp only [List.length_cons, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, List.any_eq_true] at any
    obtain ⟨block, member, covered⟩ := any
    obtain ⟨blocks, stored⟩ := storeBlocks_available state.blocks (fun block member => (valid.1 block member).1)
      pointer (byte :: values) ⟨block, member, of_decide_eq_true covered⟩
    exact ⟨{state with blocks}, by simp only [storeRange, ite_eq_left geometry, List.isEmpty_cons, Bool.false_eq_true, ite_false, stored, Option.map_some]⟩

theorem readSpan_take (bytes : List Cell) (size : Nat) (values : List Byte)
    (loaded : NativeByteRange.readSpan bytes size = some values) : bytes.take size = values.map some := by
  induction size generalizing bytes values with
  | zero => simp only [NativeByteRange.readSpan] at loaded; cases loaded; rfl
  | succ size ih =>
    cases bytes with
    | nil => cases loaded
    | cons head tail =>
      cases head with
      | none => cases loaded
      | some byte =>
        unfold NativeByteRange.readSpan at loaded
        cases rest : NativeByteRange.readSpan tail size with
        | none => simp only [rest, Option.map_none] at loaded; cases loaded
        | some output =>
          simp only [rest, Option.map_some] at loaded
          cases loaded
          simp only [List.take_succ_cons, List.map_cons, ih tail output rest]

theorem readBlocks_initialized (blocks : List Block) (pointer : Pointer) (size : Nat) (values : List Byte)
    (loaded : NativeByteRange.readBlocks blocks pointer size = some values) :
    readBlocks blocks pointer size = some (values.map some) := by
  induction blocks with
  | nil => cases loaded
  | cons block tail ih =>
    unfold NativeByteRange.readBlocks at loaded
    split at loaded
    next covered =>
      have bytes := readSpan_take _ size values loaded
      have length := NativeByteRange.readSpan_length _ size values loaded
      simp only [readBlocks, ite_eq_left covered, bytes, List.length_map, length, ite_true]
    next notCovered => simp only [readBlocks, ite_eq_right notCovered]; exact ih loaded

theorem loadRange_initialized (state : State) (pointer : Pointer) (layout : Layout) (values : List Byte)
    (loaded : NativeByteRange.loadRange state pointer layout = some values) :
    loadRange state pointer layout = some (values.map some) := by
  unfold NativeByteRange.loadRange at loaded
  split at loaded
  next geometry =>
    split at loaded
    next zero => cases loaded; simp only [loadRange, ite_eq_left geometry, ite_eq_left zero, List.map_nil]
    next nonzero =>
      simp only [loadRange, ite_eq_left geometry, ite_eq_right nonzero]
      exact readBlocks_initialized state.blocks pointer layout.size values loaded
  next => cases loaded

theorem copy_positive (state : State) (source target : Pointer) (size alignment : Nat) (nonzero : size ≠ 0) :
    copy state source target size alignment = (loadRange state source ⟨size, alignment⟩).bind (storeRange state target alignment) := by
  exact ite_eq_right nonzero

theorem copy_success (state next : State) (source target : Pointer) (size alignment : Nat) (nonzero : size ≠ 0)
    (copied : copy state source target size alignment = some next) :
    ∃ values, loadRange state source ⟨size, alignment⟩ = some values ∧ values.length = size ∧
      storeRange state target alignment values = some next ∧ loadRange next target ⟨size, alignment⟩ = some values := by
  rw [copy_positive state source target size alignment nonzero] at copied
  cases loaded : loadRange state source ⟨size, alignment⟩ with
  | none => simp only [loaded, Option.bind] at copied; cases copied
  | some values =>
    simp only [loaded, Option.bind] at copied
    have length := loadRange_length state source ⟨size, alignment⟩ values loaded
    refine ⟨values, rfl, length, copied, ?_⟩
    simpa only [length] using storeRange_then_load state next target alignment values copied

theorem copy_zero (state : State) (source target : Pointer) (alignment : Nat)
    (aligned : (⟨0, alignment⟩ : Layout).Valid ∧ source.address.val % alignment = 0 ∧ target.address.val % alignment = 0) :
    copy state source target 0 alignment = some state := by
  simp only [copy, ite_true, ite_eq_left aligned]

theorem copy_wellFormed (state next : State) (valid : NativeByteMemory.WellFormed state)
    (source target : Pointer) (size alignment : Nat) (copied : copy state source target size alignment = some next) :
    NativeByteMemory.WellFormed next := by
  by_cases zero : size = 0
  · subst size
    unfold copy at copied
    simp only [ite_true] at copied
    split at copied
    · cases copied; exact valid
    · cases copied
  · obtain ⟨values, _, _, stored, _⟩ := copy_success state next source target size alignment zero copied
    exact storeRange_wellFormed state next valid target alignment values stored

theorem copy_of_checked (state : State) (valid : NativeByteMemory.WellFormed state) (source target : Pointer)
    (size alignment : Nat) (nonzero : size ≠ 0)
    (readable : NativeByteRange.checkRange state source ⟨size, alignment⟩ = true)
    (writable : NativeByteRange.checkRange state target ⟨size, alignment⟩ = true) :
    ∃ next, copy state source target size alignment = some next := by
  obtain ⟨values, loaded⟩ := loadRange_of_checked state valid source ⟨size, alignment⟩ readable
  have length := loadRange_length state source ⟨size, alignment⟩ values loaded
  have checked : NativeByteRange.checkRange state target ⟨values.length, alignment⟩ = true := by rw [length]; exact writable
  obtain ⟨next, stored⟩ := storeRange_of_checked state valid target alignment values checked
  exact ⟨next, by simp only [copy_positive state source target size alignment nonzero, loaded, Option.bind, stored]⟩

theorem nonoverlapping_success (state next : State) (source target : Pointer) (size alignment : Nat)
    (copied : copyNonoverlapping state source target size alignment = some next) :
    ¬ NativeByteBorrow.Overlap source ⟨size, alignment⟩ target ⟨size, alignment⟩ ∧
      copy state source target size alignment = some next := by
  unfold copyNonoverlapping at copied
  split at copied
  · exact ⟨by assumption, copied⟩
  · cases copied

theorem storeBlocks_frame (blocks : List Block) (pointer : Pointer) (values : List Cell) (next : List Block)
    (stored : storeBlocks blocks pointer values = some next) (reference : Pointer)
    (separate : reference.provenance ≠ pointer.provenance ∨ reference.address.val < pointer.address.val ∨
      pointer.address.val + values.length ≤ reference.address.val) :
    NativeByteMemory.loadBlocks next reference = NativeByteMemory.loadBlocks blocks reference := by
  induction blocks generalizing next with
  | nil => cases stored
  | cons block tail ih =>
    unfold storeBlocks at stored
    dsimp only at stored
    split at stored
    next covered =>
      split at stored
      next fits =>
        cases stored
        have sameMatches : NativeByteMemory.Matches
            {block with bytes := overwrite block.bytes (pointer.address.val - block.base.val) values} reference ↔
            NativeByteMemory.Matches block reference := Iff.rfl
        simp only [NativeByteMemory.loadBlocks, sameMatches]
        by_cases matched : NativeByteMemory.Matches block reference
        · simp only [ite_eq_left matched]
          have outside : reference.address.val - block.base.val < pointer.address.val - block.base.val ∨
              pointer.address.val - block.base.val + values.length ≤ reference.address.val - block.base.val := by
            rcases separate with different | before | after
            · exact False.elim (different (matched.1.trans covered.1.symm))
            · left; have lower := matched.2.2.1; have base := covered.2.1; omega
            · right; have lower := matched.2.2.1; have base := covered.2.1; omega
          rw [overwrite_frame block.bytes _ values (by omega) _ outside]
        · simp only [ite_eq_right matched]
      next => cases stored
    next notCovered =>
      cases rest : storeBlocks tail pointer values with
      | none => simp only [rest, Option.map_none] at stored; cases stored
      | some result =>
        simp only [rest, Option.map_some] at stored
        cases stored
        simp only [NativeByteMemory.loadBlocks]
        split
        · rfl
        · exact ih result rest

theorem storeRange_frame (state : State) (pointer : Pointer) (alignment : Nat) (values : List Cell) (next : State)
    (stored : storeRange state pointer alignment values = some next) (reference : Pointer)
    (separate : reference.provenance ≠ pointer.provenance ∨ reference.address.val < pointer.address.val ∨
      pointer.address.val + values.length ≤ reference.address.val) :
    NativeByteMemory.loadByte next reference = NativeByteMemory.loadByte state reference := by
  unfold storeRange at stored
  split at stored
  · split at stored
    · cases stored; rfl
    · cases result : storeBlocks state.blocks pointer values with
      | none => simp only [result, Option.map_none] at stored; cases stored
      | some blocks =>
        simp only [result, Option.map_some] at stored
        cases stored
        exact storeBlocks_frame state.blocks pointer values blocks result reference separate
  · cases stored

theorem copy_initialized_store (state next : State) (source target : Pointer) (size alignment : Nat)
    (nonzero : size ≠ 0) (values : List Byte)
    (loaded : NativeByteRange.loadRange state source ⟨size, alignment⟩ = some values)
    (copied : copy state source target size alignment = some next) :
    NativeByteRangeWrite.storeRange state target alignment values = some next := by
  have snapshot := loadRange_initialized state source ⟨size, alignment⟩ values loaded
  rw [copy_positive state source target size alignment nonzero, snapshot] at copied
  simpa only [Option.bind, storeRange_initialized] using copied

end FormalProof4FHE.HasteBoots.NativeRawByteRange
