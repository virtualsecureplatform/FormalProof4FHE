module
public import FormalProof4FHE.HasteBoots.NativeByteBorrow
@[expose] public section

/-! Concrete initialized byte-range stores over one live allocation. The
operations carry no physical-work or native atomicity interpretation. -/
namespace FormalProof4FHE.HasteBoots.NativeByteRangeWrite
open NativePointerStorage (Pointer)
open NativeByteMemory (Byte Block Layout State)
open NativeByteRange (Geometry Covers)

/-- Called only after checking that the full replacement fits. -/
def overwrite (bytes : List (Option Byte)) (offset : Nat) (values : List Byte) : List (Option Byte) :=
  bytes.take offset ++ (values.map some ++ bytes.drop (offset + values.length))

def storeBlocks : List Block → Pointer → List Byte → Option (List Block)
  | [], _, _ => none
  | block :: tail, pointer, values =>
    if Covers block pointer values.length then
      let offset := pointer.address.val - block.base.val
      if offset + values.length ≤ block.bytes.length then
        some ({block with bytes := overwrite block.bytes offset values} :: tail)
      else none
    else (storeBlocks tail pointer values).map (block :: ·)

def storeRange (state : State) (pointer : Pointer) (alignment : Nat) (values : List Byte) : Option State :=
  if Geometry pointer ⟨values.length, alignment⟩ then
    if values.isEmpty then some state
    else (storeBlocks state.blocks pointer values).map (fun blocks => {state with blocks})
  else none

def rawWrite (state : NativeByteBorrow.State) (pointer : Pointer) (alignment : Nat) (values : List Byte) :
    Option NativeByteBorrow.State :=
  if NativeByteBorrow.rawAllowed state .exclusive pointer ⟨values.length, alignment⟩ then
    (storeRange state.memory pointer alignment values).map (fun memory => {state with memory})
  else none

def write (state : NativeByteBorrow.State) (tag offset : Nat) (values : List Byte) : Option NativeByteBorrow.State :=
  (NativeByteBorrow.lookup state.leases tag).bind (fun lease =>
    if lease.mode = .exclusive ∧ offset + values.length ≤ lease.layout.size then
      (NativeByteRange.pointerAt lease.pointer offset).bind (fun pointer =>
        if NativeByteBorrow.throughAllowed state tag .exclusive pointer ⟨values.length, 1⟩ then
          (storeRange state.memory pointer 1 values).map (fun memory => {state with memory})
        else none)
    else none)

theorem overwrite_length (bytes : List (Option Byte)) (offset : Nat) (values : List Byte)
    (fits : offset + values.length ≤ bytes.length) : (overwrite bytes offset values).length = bytes.length := by
  simp only [overwrite, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem overwrite_drop (bytes : List (Option Byte)) (offset : Nat) (values : List Byte)
    (fits : offset ≤ bytes.length) :
    (overwrite bytes offset values).drop offset = values.map some ++ bytes.drop (offset + values.length) := by
  simp only [overwrite, List.drop_append, List.drop_take, Nat.sub_self, List.take_zero, List.nil_append,
    List.length_take, Nat.min_eq_left fits, List.drop_zero, Nat.zero_sub]

theorem readSpan_initialized (values : List Byte) (tail : List (Option Byte)) :
    NativeByteRange.readSpan (values.map some ++ tail) values.length = some values := by
  induction values with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil, NativeByteRange.readSpan]
  | cons byte values ih => simp only [List.map_cons, List.cons_append, List.length_cons, NativeByteRange.readSpan, ih, Option.map_some]

theorem overwrite_initialized (bytes : List (Option Byte)) (offset : Nat) (values : List Byte)
    (fits : offset ≤ bytes.length) :
    NativeByteRange.readSpan ((overwrite bytes offset values).drop offset) values.length = some values := by
  rw [overwrite_drop bytes offset values fits]
  exact readSpan_initialized values _

theorem overwrite_selected (bytes : List (Option Byte)) (offset : Nat) (values : List Byte)
    (fits : offset ≤ bytes.length) (index : Nat) (byte : Byte) (selected : values[index]? = some byte) :
    (overwrite bytes offset values)[offset + index]? = some (some byte) := by
  have read := NativeByteRange.readSpan_selected _ _ _ (overwrite_initialized bytes offset values fits) index byte selected
  simpa only [List.getElem?_drop] using read

theorem overwrite_frame (bytes : List (Option Byte)) (offset : Nat) (values : List Byte)
    (fits : offset ≤ bytes.length) (index : Nat) (outside : index < offset ∨ offset + values.length ≤ index) :
    (overwrite bytes offset values)[index]? = bytes[index]? := by
  rcases outside with before | after
  · simp only [overwrite, List.getElem?_append, List.length_take, Nat.min_eq_left fits, ite_eq_left before,
      List.getElem?_take]
  · have notBefore : ¬ index < offset := by omega
    have notInside : ¬ index - offset < values.length := by omega
    have address : offset + values.length + (index - offset - values.length) = index := by omega
    simp only [overwrite, List.getElem?_append, List.length_take, Nat.min_eq_left fits, ite_eq_right notBefore,
      List.length_map, ite_eq_right notInside, List.getElem?_drop, address]

theorem storeBlocks_shape (blocks : List Block) (pointer : Pointer) (values : List Byte) (next : List Block)
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
      next fits =>
        cases stored
        simp only [List.map_cons, NativeByteMemory.shape, overwrite_length block.bytes _ values fits]
      next => cases stored
    next =>
      cases rest : storeBlocks tail pointer values with
      | none => simp only [rest, Option.map_none] at stored; cases stored
      | some result =>
        simp only [rest, Option.map_some] at stored
        cases stored
        simp only [List.map_cons, ih result rest]

theorem storeBlocks_initialized (blocks : List Block) (pointer : Pointer) (values : List Byte) (next : List Block)
    (stored : storeBlocks blocks pointer values = some next) :
    NativeByteRange.readBlocks next pointer values.length = some values := by
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
        simp only [NativeByteRange.readBlocks, Covers] at covered ⊢
        rw [ite_eq_left covered]
        exact overwrite_initialized block.bytes _ values (by omega)
      next => cases stored
    next notCovered =>
      cases rest : storeBlocks tail pointer values with
      | none => simp only [rest, Option.map_none] at stored; cases stored
      | some result =>
        simp only [rest, Option.map_some] at stored
        cases stored
        simp only [NativeByteRange.readBlocks, ite_eq_right notCovered]
        exact ih result rest

theorem storeRange_success (state : State) (pointer : Pointer) (alignment : Nat) (values : List Byte) (next : State)
    (stored : storeRange state pointer alignment values = some next) :
    Geometry pointer ⟨values.length, alignment⟩ ∧ next.nextGeneration = state.nextGeneration ∧
      next.blocks.map NativeByteMemory.shape = state.blocks.map NativeByteMemory.shape := by
  unfold storeRange at stored
  split at stored
  next geometry =>
    split at stored
    next => cases stored; exact ⟨geometry, rfl, rfl⟩
    next =>
      cases result : storeBlocks state.blocks pointer values with
      | none => simp only [result, Option.map_none] at stored; cases stored
      | some blocks =>
        simp only [result, Option.map_some] at stored
        cases stored
        exact ⟨geometry, rfl, storeBlocks_shape state.blocks pointer values blocks result⟩
  next => cases stored

theorem storeRange_wellFormed (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (alignment : Nat) (values : List Byte) (next : State)
    (stored : storeRange state pointer alignment values = some next) : NativeByteMemory.WellFormed next := by
  obtain ⟨_, generation, shape⟩ := storeRange_success state pointer alignment values next stored
  apply (NativeByteMemory.wellFormed_shape next).mp
  rw [generation, shape]
  exact (NativeByteMemory.wellFormed_shape state).mpr valid

theorem storeRange_then_load (state : State) (pointer : Pointer) (alignment : Nat) (values : List Byte) (next : State)
    (stored : storeRange state pointer alignment values = some next) :
    NativeByteRange.loadRange next pointer ⟨values.length, alignment⟩ = some values := by
  unfold storeRange at stored
  split at stored
  next geometry =>
    split at stored
    next empty =>
      cases stored
      have nil : values = [] := List.isEmpty_iff.mp empty
      subst values
      exact NativeByteRange.empty_range state pointer alignment geometry
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
          cases nonempty rfl
        simp only [NativeByteRange.loadRange, ite_eq_left geometry, ite_eq_right nonzero]
        exact storeBlocks_initialized state.blocks pointer values blocks result
  next => cases stored

theorem storeBlocks_available (blocks : List Block) (valid : ∀ block ∈ blocks, block.Valid)
    (pointer : Pointer) (values : List Byte) (covered : ∃ block ∈ blocks, Covers block pointer values.length) :
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

theorem storeRange_of_checked (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (alignment : Nat) (values : List Byte)
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
    obtain ⟨block, member, range⟩ := any
    obtain ⟨blocks, stored⟩ := storeBlocks_available state.blocks (fun block member => (valid.1 block member).1)
      pointer (byte :: values) ⟨block, member, of_decide_eq_true range⟩
    exact ⟨{state with blocks}, by simp only [storeRange, ite_eq_left geometry, List.isEmpty_cons, Bool.false_eq_true, ite_false, stored, Option.map_some]⟩

theorem storeRange_empty (state : State) (pointer : Pointer) (alignment : Nat)
    (geometry : Geometry pointer ⟨0, alignment⟩) : storeRange state pointer alignment [] = some state := by
  simp only [storeRange, List.length_nil, ite_eq_left geometry, List.isEmpty_nil, ite_true]

theorem storeRange_invalid (state : State) (pointer : Pointer) (alignment : Nat) (values : List Byte)
    (invalid : ¬ Geometry pointer ⟨values.length, alignment⟩) : storeRange state pointer alignment values = none := by
  exact ite_eq_right invalid

theorem storeBlocks_frame (blocks : List Block) (pointer : Pointer) (values : List Byte) (next : List Block)
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

theorem storeRange_frame (state : State) (pointer : Pointer) (alignment : Nat) (values : List Byte) (next : State)
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

theorem storeBlocks_selected (blocks : List Block) (pointer : Pointer) (values : List Byte) (next : List Block)
    (stored : storeBlocks blocks pointer values = some next) : ∃ block ∈ blocks, Covers block pointer values.length := by
  induction blocks generalizing next with
  | nil => cases stored
  | cons block tail ih =>
    unfold storeBlocks at stored
    dsimp only at stored
    split at stored
    next covered => exact ⟨block, List.mem_cons_self, covered⟩
    next =>
      cases rest : storeBlocks tail pointer values with
      | none => simp only [rest, Option.map_none] at stored; cases stored
      | some result =>
        obtain ⟨selected, member, covered⟩ := ih result rest
        exact ⟨selected, List.mem_cons_of_mem block member, covered⟩

theorem storeRange_positive_selected (state : State) (pointer : Pointer) (alignment : Nat) (values : List Byte)
    (positive : 0 < values.length) (next : State) (stored : storeRange state pointer alignment values = some next) :
    ∃ block ∈ state.blocks, Covers block pointer values.length := by
  unfold storeRange at stored
  split at stored
  · split at stored
    next empty =>
      have nil := List.isEmpty_iff.mp empty
      subst values
      cases positive
    next =>
      cases result : storeBlocks state.blocks pointer values with
      | none => simp only [result, Option.map_none] at stored; cases stored
      | some blocks => exact storeBlocks_selected state.blocks pointer values blocks result
  · cases stored

theorem storeRange_without_origin (state : State) (pointer : Pointer) (absent : pointer.provenance = none)
    (alignment : Nat) (values : List Byte) (positive : 0 < values.length) : storeRange state pointer alignment values = none := by
  cases stored : storeRange state pointer alignment values with
  | none => rfl
  | some next =>
    obtain ⟨_, _, covered⟩ := storeRange_positive_selected state pointer alignment values positive next stored
    have impossible := covered.1
    rw [absent] at impossible
    cases impossible

theorem rawWrite_success (state next : NativeByteBorrow.State) (pointer : Pointer) (alignment : Nat) (values : List Byte)
    (executed : rawWrite state pointer alignment values = some next) :
    NativeByteBorrow.rawAllowed state .exclusive pointer ⟨values.length, alignment⟩ = true ∧
      storeRange state.memory pointer alignment values = some next.memory ∧
      next.nextTag = state.nextTag ∧ next.leases = state.leases := by
  unfold rawWrite at executed
  split at executed
  · rename_i allowed
    cases stored : storeRange state.memory pointer alignment values with
    | none => simp only [stored, Option.map_none] at executed; cases executed
    | some memory =>
      simp only [stored, Option.map_some] at executed
      cases executed
      exact ⟨allowed, rfl, rfl, rfl⟩
  · cases executed

theorem write_success (state next : NativeByteBorrow.State) (tag offset : Nat) (values : List Byte)
    (executed : write state tag offset values = some next) :
    ∃ lease pointer, NativeByteBorrow.lookup state.leases tag = some lease ∧ lease.mode = .exclusive ∧
      offset + values.length ≤ lease.layout.size ∧ NativeByteRange.pointerAt lease.pointer offset = some pointer ∧
      NativeByteBorrow.throughAllowed state tag .exclusive pointer ⟨values.length, 1⟩ = true ∧
      storeRange state.memory pointer 1 values = some next.memory ∧ next.nextTag = state.nextTag ∧ next.leases = state.leases := by
  unfold write at executed
  cases found : NativeByteBorrow.lookup state.leases tag with
  | none => simp only [found, Option.bind] at executed; cases executed
  | some lease =>
    simp only [found, Option.bind] at executed
    split at executed
    next bounds =>
      cases advanced : NativeByteRange.pointerAt lease.pointer offset with
      | none => simp only [advanced] at executed; cases executed
      | some pointer =>
        simp only [advanced] at executed
        split at executed
        next allowed =>
          cases stored : storeRange state.memory pointer 1 values with
          | none => simp only [stored, Option.map_none] at executed; cases executed
          | some memory =>
            simp only [stored, Option.map_some] at executed
            cases executed
            exact ⟨lease, pointer, rfl, bounds.1, bounds.2, advanced, allowed, stored, rfl, rfl⟩
        next => cases executed
    next => cases executed

theorem rawWrite_wellFormed (state next : NativeByteBorrow.State) (valid : NativeByteBorrow.WellFormed state)
    (pointer : Pointer) (alignment : Nat) (values : List Byte) (executed : rawWrite state pointer alignment values = some next) :
    NativeByteBorrow.WellFormed next := by
  obtain ⟨_, stored, counter, leases⟩ := rawWrite_success state next pointer alignment values executed
  exact ⟨storeRange_wellFormed state.memory valid.1 pointer alignment values next.memory stored,
    NativeByteBorrow.ledger_transport state next valid.2 counter leases⟩

theorem write_wellFormed (state next : NativeByteBorrow.State) (valid : NativeByteBorrow.WellFormed state)
    (tag offset : Nat) (values : List Byte) (executed : write state tag offset values = some next) : NativeByteBorrow.WellFormed next := by
  obtain ⟨_, pointer, _, _, _, _, _, stored, counter, leases⟩ := write_success state next tag offset values executed
  exact ⟨storeRange_wellFormed state.memory valid.1 pointer 1 values next.memory stored,
    NativeByteBorrow.ledger_transport state next valid.2 counter leases⟩

theorem storeRange_checked (state : State) (pointer : Pointer) (alignment : Nat) (values : List Byte) (next : State)
    (stored : storeRange state pointer alignment values = some next) :
    NativeByteRange.checkRange state pointer ⟨values.length, alignment⟩ = true := by
  have geometry := (storeRange_success state pointer alignment values next stored).1
  unfold NativeByteRange.checkRange
  rw [decide_eq_true geometry, Bool.true_and]
  split
  · rfl
  · rename_i nonzero
    obtain ⟨block, member, covered⟩ := storeRange_positive_selected state pointer alignment values (Nat.pos_of_ne_zero nonzero) next stored
    exact List.any_eq_true.mpr ⟨block, member, decide_eq_true covered⟩

theorem storeRange_defined_iff (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (alignment : Nat) (values : List Byte) :
    (∃ next, storeRange state pointer alignment values = some next) ↔
      NativeByteRange.checkRange state pointer ⟨values.length, alignment⟩ = true := by
  constructor
  · rintro ⟨next, stored⟩
    exact storeRange_checked state pointer alignment values next stored
  · exact storeRange_of_checked state valid pointer alignment values

theorem storeRange_after_deallocation (state : State) (valid : NativeByteMemory.WellFormed state)
    (pointer : Pointer) (layout : Layout) (next : State)
    (released : NativeByteMemory.deallocate state pointer layout = some next) (reference : Pointer)
    (sameOrigin : reference.provenance = pointer.provenance) (alignment : Nat) (values : List Byte)
    (positive : 0 < values.length) : storeRange next reference alignment values = none := by
  unfold NativeByteMemory.deallocate at released
  cases rest : NativeByteMemory.releaseBlocks state.blocks pointer layout with
  | none => simp only [rest, Option.map_none] at released; cases released
  | some blocks =>
    simp only [rest, Option.map_some] at released
    cases released
    cases stored : storeRange {state with blocks} reference alignment values with
    | none => rfl
    | some output =>
      obtain ⟨block, member, covered⟩ := storeRange_positive_selected _ reference alignment values positive output stored
      have absent := NativeByteMemory.release_origin_absent state.blocks (valid.2.imp (fun pair => pair.2))
        pointer layout blocks rest block member
      exact False.elim (absent (sameOrigin.symm.trans covered.1))

/-- Memory-policy transitions include every earlier byte-ledger transition.
These are not native machine instructions or a cost model. -/
inductive Step : NativeByteBorrow.State → NativeByteBorrow.State → Prop where
  | byte {state next : NativeByteBorrow.State} (executed : NativeByteBorrow.Step state next) : Step state next
  | rawWrite (state next : NativeByteBorrow.State) (pointer : Pointer) (alignment : Nat) (values : List Byte)
      (executed : NativeByteRangeWrite.rawWrite state pointer alignment values = some next) : Step state next
  | write (state next : NativeByteBorrow.State) (tag offset : Nat) (values : List Byte)
      (executed : NativeByteRangeWrite.write state tag offset values = some next) : Step state next

inductive Reachable : NativeByteBorrow.State → Prop where
  | empty : Reachable NativeByteBorrow.empty
  | step {state next : NativeByteBorrow.State} (previous : Reachable state) (executed : Step state next) : Reachable next

inductive Runs (start : NativeByteBorrow.State) : NativeByteBorrow.State → Prop where
  | refl : Runs start start
  | step {state next : NativeByteBorrow.State} (previous : Runs start state) (executed : Step state next) : Runs start next

theorem step_wellFormed {state next : NativeByteBorrow.State} (valid : NativeByteBorrow.WellFormed state)
    (executed : Step state next) : NativeByteBorrow.WellFormed next := by
  cases executed with
  | byte executed => exact NativeByteBorrow.step_wellFormed valid executed
  | rawWrite pointer alignment values executed => exact rawWrite_wellFormed state next valid pointer alignment values executed
  | write tag offset values executed => exact write_wellFormed state next valid tag offset values executed

theorem reachable_wellFormed {state : NativeByteBorrow.State} (reachable : Reachable state) : NativeByteBorrow.WellFormed state := by
  induction reachable with
  | empty => exact NativeByteBorrow.empty_wellFormed
  | step previous executed ih => exact step_wellFormed ih executed

theorem step_counter {state next : NativeByteBorrow.State} (executed : Step state next) : state.nextTag ≤ next.nextTag := by
  cases executed with
  | byte executed => exact NativeByteBorrow.step_counter executed
  | rawWrite pointer alignment values executed => rw [(rawWrite_success state next pointer alignment values executed).2.2.1]; exact Nat.le_refl _
  | write tag offset values executed =>
    obtain ⟨_, _, _, _, _, _, _, _, counter, _⟩ := write_success state next tag offset values executed
    rw [counter]
    exact Nat.le_refl _

theorem step_keeps_revoked {state next : NativeByteBorrow.State} (executed : Step state next) (tag : Nat)
    (before : tag < state.nextTag) (absent : NativeByteBorrow.lookup state.leases tag = none) :
    NativeByteBorrow.lookup next.leases tag = none := by
  cases executed with
  | byte executed => exact NativeByteBorrow.step_keeps_revoked executed tag before absent
  | rawWrite pointer alignment values executed => rw [(rawWrite_success state next pointer alignment values executed).2.2.2]; exact absent
  | write selected offset values executed =>
    obtain ⟨_, _, _, _, _, _, _, _, _, leases⟩ := write_success state next selected offset values executed
    rw [leases]
    exact absent

theorem runs_keep_revoked {state next : NativeByteBorrow.State} (executed : Runs state next) (tag : Nat)
    (before : tag < state.nextTag) (absent : NativeByteBorrow.lookup state.leases tag = none) :
    tag < next.nextTag ∧ NativeByteBorrow.lookup next.leases tag = none := by
  induction executed with
  | refl => exact ⟨before, absent⟩
  | step previous transition ih =>
    exact ⟨Nat.lt_of_lt_of_le ih.1 (step_counter transition), step_keeps_revoked transition tag ih.1 ih.2⟩

theorem lift_byte_runs {state next : NativeByteBorrow.State} (executed : NativeByteBorrow.Runs state next) : Runs state next := by
  induction executed with
  | refl => exact Runs.refl
  | step previous transition ih => exact Runs.step ih (Step.byte transition)

theorem overwrite_singleton (bytes : List (Option Byte)) (offset : Nat) (byte : Byte) (inside : offset < bytes.length) :
    overwrite bytes offset [byte] = bytes.set offset (some byte) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left inside]
  rfl

theorem storeBlocks_singleton (blocks : List Block) (pointer : Pointer) (nonzero : pointer.address.val ≠ 0) (byte : Byte) :
    storeBlocks blocks pointer [byte] = NativeByteMemory.storeBlocks blocks pointer byte := by
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
    have covered : Covers block pointer [byte].length ↔ NativeByteMemory.Matches block pointer := by
      unfold Covers NativeByteMemory.Matches
      constructor
      · rintro ⟨origin, lower, upper⟩
        exact ⟨origin, nonzero, lower, by change pointer.address.val + 1 ≤ _ at upper; omega⟩
      · rintro ⟨origin, _, lower, upper⟩
        exact ⟨origin, lower, by change pointer.address.val + 1 ≤ _; omega⟩
    simp only [storeBlocks, NativeByteMemory.storeBlocks, covered]
    split
    next =>
      have fits : pointer.address.val - block.base.val + [byte].length ≤ block.bytes.length ↔
          pointer.address.val - block.base.val < block.bytes.length := by simp only [List.length_cons, List.length_nil]; omega
      simp only [fits]
      split
      next inside => rw [overwrite_singleton block.bytes _ byte inside]
      next => rfl
    next => rw [ih]

theorem storeRange_singleton (state : State) (pointer : Pointer) (alignment : Nat) (byte : Byte)
    (geometry : Geometry pointer ⟨1, alignment⟩) :
    storeRange state pointer alignment [byte] = NativeByteMemory.storeByte state pointer byte := by
  simp only [storeRange, List.length_cons, List.length_nil, ite_eq_left geometry, List.isEmpty_cons,
    Bool.false_eq_true, ite_false, storeBlocks_singleton state.blocks pointer geometry.2.1 byte, NativeByteMemory.storeByte]

theorem storeRange_allocation_count (state : State) (pointer : Pointer) (alignment : Nat) (values : List Byte) (next : State)
    (stored : storeRange state pointer alignment values = some next) : next.blocks.length = state.blocks.length := by
  have shape := (storeRange_success state pointer alignment values next stored).2.2
  simpa only [List.length_map] using congrArg List.length shape

end FormalProof4FHE.HasteBoots.NativeByteRangeWrite
