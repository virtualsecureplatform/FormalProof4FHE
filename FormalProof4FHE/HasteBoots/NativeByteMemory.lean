module
public import FormalProof4FHE.HasteBoots.NativePointerRepresentation
public import Mathlib.Data.List.Basic
@[expose] public section

/-! Checked byte-allocation lifecycle over the shared pointer data. Operations
change actual modeled bytes and live allocations. This is not yet a Rust heap,
borrow/aliasing, Aeneas dereference or physical-work refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeByteMemory
open NativePointerStorage (Address Origin Pointer)

abbrev Byte := Fin 256

structure Layout where
  size : Nat
  alignment : Nat
  deriving DecidableEq

/-- The rounded allocation-size bound for the fixed 64-bit target. -/
def Layout.Valid (layout : Layout) : Prop :=
  layout.alignment ∈ (List.range 64).map (fun exponent => 2 ^ exponent) ∧
    layout.size + (layout.alignment - 1) ≤ 2 ^ 63 - 1

instance (layout : Layout) : Decidable layout.Valid := by
  unfold Layout.Valid
  infer_instance

structure Block where
  origin : Origin
  base : Address
  layout : Layout
  bytes : List (Option Byte)
  deriving DecidableEq

structure State where
  nextGeneration : Nat
  blocks : List Block
  deriving DecidableEq

def empty : State := ⟨0, []⟩

def Block.pointer (block : Block) : Pointer := ⟨block.base, some block.origin⟩

def Disjoint (left right : Block) : Prop :=
  left.base.val + left.layout.size ≤ right.base.val ∨
    right.base.val + right.layout.size ≤ left.base.val

instance (left right : Block) : Decidable (Disjoint left right) := by
  unfold Disjoint
  infer_instance

def Block.Valid (block : Block) : Prop :=
  block.layout.Valid ∧ 0 < block.layout.size ∧ block.base.val ≠ 0 ∧
    block.base.val % block.layout.alignment = 0 ∧
    block.base.val + block.layout.size ≤ 2 ^ 64 ∧
    block.bytes.length = block.layout.size

def WellFormed (state : State) : Prop :=
  (∀ block ∈ state.blocks, block.Valid ∧ block.origin.generation < state.nextGeneration) ∧
    state.blocks.Pairwise (fun left right => Disjoint left right ∧ left.origin ≠ right.origin)

def freshBlock (state : State) (base : Address) (layout : Layout) : Block :=
  ⟨⟨base.val, state.nextGeneration⟩, base, layout, List.replicate layout.size none⟩

/-- The allocator address is an outcome, checked here rather than accompanied
by a freshness certificate. Zero-size allocation is outside this primitive. -/
def allocate (state : State) (base : Address) (layout : Layout) : Option (Pointer × State) :=
  let block := freshBlock state base layout
  if layout.Valid ∧ 0 < layout.size ∧ base.val ≠ 0 ∧
      base.val % layout.alignment = 0 ∧ base.val + layout.size ≤ 2 ^ 64 ∧
      state.blocks.all (fun old => decide (Disjoint block old)) then
    some (block.pointer, ⟨state.nextGeneration + 1, block :: state.blocks⟩)
  else none

/-- A byte access stays in one live allocation and carries its exact origin. -/
def Matches (block : Block) (pointer : Pointer) : Prop :=
  pointer.provenance = some block.origin ∧ pointer.address.val ≠ 0 ∧
    block.base.val ≤ pointer.address.val ∧
    pointer.address.val < block.base.val + block.layout.size

instance (block : Block) (pointer : Pointer) : Decidable (Matches block pointer) := by
  unfold Matches
  infer_instance

def loadBlocks : List Block → Pointer → Option Byte
  | [], _ => none
  | block :: tail, pointer =>
      if Matches block pointer then
        (block.bytes[pointer.address.val - block.base.val]?).bind id
      else loadBlocks tail pointer

def loadByte (state : State) (pointer : Pointer) : Option Byte := loadBlocks state.blocks pointer

def storeBlocks : List Block → Pointer → Byte → Option (List Block)
  | [], _, _ => none
  | block :: tail, pointer, byte =>
      if Matches block pointer then
        let offset := pointer.address.val - block.base.val
        if offset < block.bytes.length then
          some ({block with bytes := block.bytes.set offset (some byte)} :: tail)
        else none
      else (storeBlocks tail pointer byte).map (block :: ·)

def storeByte (state : State) (pointer : Pointer) (byte : Byte) : Option State :=
  (storeBlocks state.blocks pointer byte).map (fun blocks => {state with blocks})

/-- Deallocation requires the original base, origin and exact allocation layout.
A successful step removes that allocation and all of its initialized bytes. -/
def releaseBlocks : List Block → Pointer → Layout → Option (List Block)
  | [], _, _ => none
  | block :: tail, pointer, layout =>
      if pointer = block.pointer ∧ layout = block.layout then some tail
      else (releaseBlocks tail pointer layout).map (block :: ·)

def deallocate (state : State) (pointer : Pointer) (layout : Layout) : Option State :=
  (releaseBlocks state.blocks pointer layout).map (fun blocks => {state with blocks})

theorem empty_wellFormed : WellFormed empty := by
  simp [WellFormed, empty]

theorem disjoint_symm (left right : Block) : Disjoint left right ↔ Disjoint right left := by
  exact or_comm

theorem allocate_success (state : State) (base : Address) (layout : Layout)
    (pointer : Pointer) (next : State) (executed : allocate state base layout = some (pointer, next)) :
    pointer = (freshBlock state base layout).pointer ∧
    next = ⟨state.nextGeneration + 1, freshBlock state base layout :: state.blocks⟩ ∧
    (freshBlock state base layout).Valid ∧
    ∀ old ∈ state.blocks, Disjoint (freshBlock state base layout) old := by
  unfold allocate at executed
  dsimp only at executed
  split at executed
  · rename_i accepted
    cases executed
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact ⟨accepted.1, accepted.2.1, accepted.2.2.1, accepted.2.2.2.1,
        accepted.2.2.2.2.1, List.length_replicate⟩
    · simpa only [List.all_eq_true, decide_eq_true_eq] using accepted.2.2.2.2.2
  · cases executed

theorem allocate_wellFormed (state : State) (valid : WellFormed state) (base : Address)
    (layout : Layout) (pointer : Pointer) (next : State)
    (executed : allocate state base layout = some (pointer, next)) : WellFormed next := by
  obtain ⟨_, same, freshValid, separated⟩ := allocate_success state base layout pointer next executed
  subst next
  constructor
  · intro block member
    rcases List.mem_cons.mp member with rfl | old
    · exact ⟨freshValid, Nat.lt_succ_self _⟩
    · exact ⟨(valid.1 block old).1, Nat.lt_trans (valid.1 block old).2 (Nat.lt_succ_self _)⟩
  · rw [List.pairwise_cons]
    refine ⟨?_, valid.2⟩
    intro old member
    refine ⟨separated old member, ?_⟩
    intro same
    have generation := congrArg Origin.generation same
    have before := (valid.1 old member).2
    change state.nextGeneration = old.origin.generation at generation
    omega

theorem allocate_initialized_none (state : State) (base : Address) (layout : Layout) :
    (freshBlock state base layout).bytes = List.replicate layout.size none := rfl

theorem load_without_origin (blocks : List Block) (pointer : Pointer)
    (absent : pointer.provenance = none) : loadBlocks blocks pointer = none := by
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
    have unmatched : ¬ Matches block pointer := by
      intro matched
      have contradiction := matched.1
      rw [absent] at contradiction
      cases contradiction
    simp only [loadBlocks, ite_eq_right unmatched, ih]

theorem load_zero (blocks : List Block) (pointer : Pointer)
    (zero : pointer.address.val = 0) : loadBlocks blocks pointer = none := by
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
    have unmatched : ¬ Matches block pointer := fun matched => matched.2.1 zero
    simp only [loadBlocks, ite_eq_right unmatched, ih]

theorem store_blocks_length (blocks : List Block) (pointer : Pointer) (byte : Byte)
    (output : List Block) (executed : storeBlocks blocks pointer byte = some output) :
    output.length = blocks.length := by
  induction blocks generalizing output with
  | nil => cases executed
  | cons block tail ih =>
    unfold storeBlocks at executed
    dsimp only at executed
    split at executed
    · split at executed
      · cases executed; rfl
      · cases executed
    · cases rest : storeBlocks tail pointer byte with
      | none => simp only [rest, Option.map_none] at executed; cases executed
      | some result =>
        simp only [rest, Option.map_some] at executed
        cases executed
        exact congrArg Nat.succ (ih result rest)

theorem store_then_load (blocks : List Block) (pointer : Pointer) (byte : Byte)
    (output : List Block) (executed : storeBlocks blocks pointer byte = some output) :
    loadBlocks output pointer = some byte := by
  induction blocks generalizing output with
  | nil => cases executed
  | cons block tail ih =>
    unfold storeBlocks at executed
    dsimp only at executed
    split at executed
    · rename_i matched
      split at executed
      · rename_i bound
        cases executed
        have stillMatched : Matches {block with bytes := (block.bytes.set
            (pointer.address.val - block.base.val) (some byte))} pointer := matched
        simp only [loadBlocks, ite_eq_left stillMatched, List.getElem?_set_self bound]
        rfl
      · cases executed
    · rename_i unmatched
      cases rest : storeBlocks tail pointer byte with
      | none => simp only [rest, Option.map_none] at executed; cases executed
      | some result =>
        simp only [rest, Option.map_some] at executed
        cases executed
        simp only [loadBlocks, ite_eq_right unmatched, ih result rest]

theorem release_length (blocks : List Block) (pointer : Pointer) (layout : Layout)
    (output : List Block) (executed : releaseBlocks blocks pointer layout = some output) :
    output.length + 1 = blocks.length := by
  induction blocks generalizing output with
  | nil => cases executed
  | cons block tail ih =>
    unfold releaseBlocks at executed
    split at executed
    · cases executed; rfl
    · cases rest : releaseBlocks tail pointer layout with
      | none => simp only [rest, Option.map_none] at executed; cases executed
      | some result =>
        simp only [rest, Option.map_some] at executed
        cases executed
        have shorter := ih result rest
        simp only [List.length_cons]
        omega

theorem release_sublist (blocks : List Block) (pointer : Pointer) (layout : Layout)
    (output : List Block) (executed : releaseBlocks blocks pointer layout = some output) :
    output.Sublist blocks := by
  induction blocks generalizing output with
  | nil => cases executed
  | cons block tail ih =>
    unfold releaseBlocks at executed
    split at executed
    · cases executed; exact List.Sublist.cons _ (List.Sublist.refl _)
    · cases rest : releaseBlocks tail pointer layout with
      | none => simp only [rest, Option.map_none] at executed; cases executed
      | some result =>
        simp only [rest, Option.map_some] at executed
        cases executed
        exact List.Sublist.cons_cons _ (ih result rest)

theorem deallocate_changes_live_count (state : State) (pointer : Pointer) (layout : Layout)
    (next : State) (executed : deallocate state pointer layout = some next) :
    next.blocks.length + 1 = state.blocks.length := by
  unfold deallocate at executed
  cases rest : releaseBlocks state.blocks pointer layout with
  | none => simp only [rest, Option.map_none] at executed; cases executed
  | some result =>
    simp only [rest, Option.map_some] at executed
    cases executed
    exact release_length state.blocks pointer layout result rest

theorem release_selected (blocks : List Block) (pointer : Pointer) (layout : Layout)
    (output : List Block) (executed : releaseBlocks blocks pointer layout = some output) :
    ∃ block ∈ blocks, pointer = block.pointer ∧ layout = block.layout := by
  induction blocks generalizing output with
  | nil => cases executed
  | cons block tail ih =>
    unfold releaseBlocks at executed
    split at executed
    · rename_i matched
      exact ⟨block, List.mem_cons_self, matched⟩
    · cases rest : releaseBlocks tail pointer layout with
      | none => simp only [rest, Option.map_none] at executed; cases executed
      | some result =>
        obtain ⟨selected, member, same⟩ := ih result rest
        exact ⟨selected, List.mem_cons_of_mem block member, same⟩

theorem deallocate_wellFormed (state : State) (valid : WellFormed state)
    (pointer : Pointer) (layout : Layout) (next : State)
    (executed : deallocate state pointer layout = some next) : WellFormed next := by
  unfold deallocate at executed
  cases rest : releaseBlocks state.blocks pointer layout with
  | none => simp only [rest, Option.map_none] at executed; cases executed
  | some result =>
    simp only [rest, Option.map_some] at executed
    cases executed
    have included := release_sublist state.blocks pointer layout result rest
    exact ⟨fun block member => valid.1 block (included.subset member), valid.2.sublist included⟩

/-- A proof-only shape erasure preserves every byte-array length. It is never
used as a memory operation or as a replacement for a destructor. -/
def shape (block : Block) : Block :=
  {block with bytes := List.replicate block.bytes.length none}

theorem shape_valid (block : Block) : (shape block).Valid ↔ block.Valid := by
  simp only [Block.Valid, shape, List.length_replicate]

theorem wellFormed_shape (state : State) :
    WellFormed {state with blocks := state.blocks.map shape} ↔ WellFormed state := by
  constructor
  · intro valid
    constructor
    · intro block member
      have selected := valid.1 (shape block) (List.mem_map.mpr ⟨block, member, rfl⟩)
      exact ⟨(shape_valid block).mp selected.1, selected.2⟩
    · have pairs := valid.2
      rw [List.pairwise_map] at pairs
      exact pairs
  · intro valid
    constructor
    · intro block member
      obtain ⟨old, selected, rfl⟩ := List.mem_map.mp member
      exact ⟨(shape_valid old).mpr (valid.1 old selected).1, (valid.1 old selected).2⟩
    · rw [List.pairwise_map]
      exact valid.2

theorem store_preserves_shape (blocks : List Block) (pointer : Pointer) (byte : Byte)
    (output : List Block) (executed : storeBlocks blocks pointer byte = some output) :
    output.map shape = blocks.map shape := by
  induction blocks generalizing output with
  | nil => cases executed
  | cons block tail ih =>
    unfold storeBlocks at executed
    dsimp only at executed
    split at executed
    · split at executed
      · cases executed
        simp only [List.map_cons, shape, List.length_set]
      · cases executed
    · cases rest : storeBlocks tail pointer byte with
      | none => simp only [rest, Option.map_none] at executed; cases executed
      | some result =>
        simp only [rest, Option.map_some] at executed
        cases executed
        simp only [List.map_cons, ih result rest]

theorem store_wellFormed (state : State) (valid : WellFormed state)
    (pointer : Pointer) (byte : Byte) (next : State)
    (executed : storeByte state pointer byte = some next) : WellFormed next := by
  unfold storeByte at executed
  cases rest : storeBlocks state.blocks pointer byte with
  | none => simp only [rest, Option.map_none] at executed; cases executed
  | some result =>
    simp only [rest, Option.map_some] at executed
    cases executed
    apply (wellFormed_shape _).mp
    have same := store_preserves_shape state.blocks pointer byte result rest
    change WellFormed ⟨state.nextGeneration, result.map shape⟩
    rw [same]
    exact (wellFormed_shape state).mpr valid

theorem storeByte_then_loadByte (state : State) (pointer : Pointer) (byte : Byte) (next : State)
    (executed : storeByte state pointer byte = some next) : loadByte next pointer = some byte := by
  unfold storeByte at executed
  cases rest : storeBlocks state.blocks pointer byte with
  | none => simp only [rest, Option.map_none] at executed; cases executed
  | some result =>
    simp only [rest, Option.map_some] at executed
    cases executed
    exact store_then_load state.blocks pointer byte result rest

theorem load_without_matching_origin (blocks : List Block) (pointer : Pointer)
    (absent : ∀ block ∈ blocks, pointer.provenance ≠ some block.origin) :
    loadBlocks blocks pointer = none := by
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
    have unmatched : ¬ Matches block pointer := fun matched => absent block List.mem_cons_self matched.1
    simp only [loadBlocks, ite_eq_right unmatched]
    exact ih (fun old member => absent old (List.mem_cons_of_mem block member))

theorem release_origin_absent (blocks : List Block)
    (unique : blocks.Pairwise (fun left right => left.origin ≠ right.origin))
    (pointer : Pointer) (layout : Layout) (output : List Block)
    (executed : releaseBlocks blocks pointer layout = some output) :
    ∀ block ∈ output, pointer.provenance ≠ some block.origin := by
  induction blocks generalizing output with
  | nil => cases executed
  | cons block tail ih =>
    obtain ⟨separate, uniqueTail⟩ := List.pairwise_cons.mp unique
    unfold releaseBlocks at executed
    split at executed
    · rename_i matched
      cases executed
      intro old member same
      have different := separate old member
      rw [matched.1] at same
      exact different (Option.some.inj same)
    · cases rest : releaseBlocks tail pointer layout with
      | none => simp only [rest, Option.map_none] at executed; cases executed
      | some result =>
        simp only [rest, Option.map_some] at executed
        cases executed
        intro old member
        rcases List.mem_cons.mp member with rfl | later
        · obtain ⟨removed, selected, same, _⟩ := release_selected tail pointer layout result rest
          intro equal
          have different := separate removed selected
          rw [same] at equal
          exact different (Option.some.inj equal).symm
        · exact ih uniqueTail result rest old later

theorem deallocated_pointer_unreadable (state : State) (valid : WellFormed state)
    (pointer : Pointer) (layout : Layout) (next : State)
    (executed : deallocate state pointer layout = some next) : loadByte next pointer = none := by
  unfold deallocate at executed
  cases rest : releaseBlocks state.blocks pointer layout with
  | none => simp only [rest, Option.map_none] at executed; cases executed
  | some result =>
    simp only [rest, Option.map_some] at executed
    cases executed
    exact load_without_matching_origin result pointer
      (release_origin_absent state.blocks (valid.2.imp (fun pair => pair.2)) pointer layout result rest)

theorem allocate_uninitialized (state : State) (base : Address) (layout : Layout)
    (pointer : Pointer) (next : State) (executed : allocate state base layout = some (pointer, next)) :
    loadByte next pointer = none := by
  obtain ⟨rfl, rfl, valid, _⟩ := allocate_success state base layout pointer next executed
  have matched : Matches (freshBlock state base layout) (freshBlock state base layout).pointer := by
    exact ⟨rfl, valid.2.2.1, Nat.le_refl _, Nat.lt_add_of_pos_right valid.2.1⟩
  change (if Matches (freshBlock state base layout) (freshBlock state base layout).pointer then
    ((freshBlock state base layout).bytes[base.val - base.val]?).bind id else _) = none
  rw [ite_eq_left matched]
  change ((List.replicate layout.size (none : Option Byte))[base.val - base.val]?).bind id = none
  rw [Nat.sub_self]
  cases layout.size with
  | zero => rfl
  | succ n => rfl

theorem allocate_frame_load (state : State) (base : Address) (layout : Layout)
    (fresh : Pointer) (next : State) (executed : allocate state base layout = some (fresh, next))
    (pointer : Pointer) (different : pointer.provenance ≠ fresh.provenance) :
    loadByte next pointer = loadByte state pointer := by
  obtain ⟨rfl, rfl, _, _⟩ := allocate_success state base layout fresh next executed
  have unmatched : ¬ Matches (freshBlock state base layout) pointer := fun matched => different matched.1
  exact ite_eq_right unmatched

theorem deallocate_selected (state : State) (pointer : Pointer) (layout : Layout)
    (next : State) (executed : deallocate state pointer layout = some next) :
    ∃ block ∈ state.blocks, pointer = block.pointer ∧ layout = block.layout := by
  unfold deallocate at executed
  cases rest : releaseBlocks state.blocks pointer layout with
  | none => simp only [rest, Option.map_none] at executed; cases executed
  | some result => exact release_selected state.blocks pointer layout result rest

theorem deallocate_generation (state : State) (pointer : Pointer) (layout : Layout)
    (next : State) (executed : deallocate state pointer layout = some next) :
    next.nextGeneration = state.nextGeneration := by
  unfold deallocate at executed
  cases rest : releaseBlocks state.blocks pointer layout with
  | none => simp only [rest, Option.map_none] at executed; cases executed
  | some result =>
    simp only [rest, Option.map_some] at executed
    cases executed
    rfl

theorem stale_after_reallocation (state : State) (valid : WellFormed state)
    (pointer : Pointer) (layout : Layout) (retired : State)
    (released : deallocate state pointer layout = some retired)
    (base : Address) (newLayout : Layout) (fresh : Pointer) (next : State)
    (allocated : allocate retired base newLayout = some (fresh, next)) : loadByte next pointer = none := by
  obtain ⟨old, member, same, _⟩ := deallocate_selected state pointer layout retired released
  have oldBefore := (valid.1 old member).2
  have counter := deallocate_generation state pointer layout retired released
  have freshPointer := (allocate_success retired base newLayout fresh next allocated).1
  have different : pointer.provenance ≠ fresh.provenance := by
    rw [same, freshPointer]
    intro equal
    have generation := congrArg Origin.generation (Option.some.inj equal)
    change old.origin.generation = retired.nextGeneration at generation
    omega
  rw [allocate_frame_load retired base newLayout fresh next allocated pointer different]
  exact deallocated_pointer_unreadable state valid pointer layout retired released

theorem layout_alignment (layout : Layout) (valid : layout.Valid) :
    ∃ exponent < 64, layout.alignment = 2 ^ exponent := by
  obtain ⟨exponent, member, same⟩ := List.mem_map.mp valid.1
  exact ⟨exponent, List.mem_range.mp member, same.symm⟩

theorem layout_size_bound (layout : Layout) (valid : layout.Valid) : layout.size ≤ 2 ^ 63 - 1 := by
  have rounded := valid.2
  omega

theorem allocate_of_available (state : State) (base : Address) (layout : Layout)
    (valid : layout.Valid) (positive : 0 < layout.size) (nonzero : base.val ≠ 0)
    (aligned : base.val % layout.alignment = 0) (fits : base.val + layout.size ≤ 2 ^ 64)
    (separated : ∀ old ∈ state.blocks, Disjoint (freshBlock state base layout) old) :
    allocate state base layout = some ((freshBlock state base layout).pointer,
      ⟨state.nextGeneration + 1, freshBlock state base layout :: state.blocks⟩) := by
  unfold allocate
  exact ite_eq_left ⟨valid, positive, nonzero, aligned, fits,
    List.all_eq_true.mpr (fun block member => decide_eq_true (separated block member))⟩

theorem store_at_matching_head (block : Block) (valid : block.Valid) (tail : List Block)
    (pointer : Pointer) (matched : Matches block pointer) (byte : Byte) :
    storeBlocks (block :: tail) pointer byte =
      some ({block with bytes := (block.bytes.set (pointer.address.val - block.base.val) (some byte))} :: tail) := by
  have length := valid.2.2.2.2.2
  have lower := matched.2.2.1
  have upper := matched.2.2.2
  have bound : pointer.address.val - block.base.val < block.bytes.length := by omega
  unfold storeBlocks
  rw [ite_eq_left matched]
  dsimp only
  rw [ite_eq_left bound]

theorem deallocate_head (state : State) (block : Block) :
    deallocate {state with blocks := block :: state.blocks} block.pointer block.layout = some state := by
  simp only [deallocate, releaseBlocks, and_self, ite_true, Option.map_some]

theorem deallocated_alias_unreadable (state : State) (valid : WellFormed state)
    (pointer : Pointer) (layout : Layout) (next : State)
    (executed : deallocate state pointer layout = some next)
    (reference : Pointer) (sameOrigin : reference.provenance = pointer.provenance) : loadByte next reference = none := by
  unfold deallocate at executed
  cases rest : releaseBlocks state.blocks pointer layout with
  | none => simp only [rest, Option.map_none] at executed; cases executed
  | some result =>
    simp only [rest, Option.map_some] at executed
    cases executed
    apply load_without_matching_origin
    intro block member
    rw [sameOrigin]
    exact release_origin_absent state.blocks (valid.2.imp (fun pair => pair.2)) pointer layout result rest block member

theorem uninitialized_bytes (size offset : Nat) :
    ((List.replicate size (none : Option Byte))[offset]?).bind id = none := by
  induction size generalizing offset with
  | zero => cases offset <;> rfl
  | succ size ih =>
    cases offset with
    | zero => rfl
    | succ offset => exact ih offset

theorem fresh_block_uninitialized (state : State) (base : Address) (layout : Layout)
    (tail : List Block) (pointer : Pointer) (matched : Matches (freshBlock state base layout) pointer) :
    loadBlocks (freshBlock state base layout :: tail) pointer = none := by
  unfold loadBlocks
  rw [ite_eq_left matched]
  exact uninitialized_bytes layout.size _

theorem load_selected (blocks : List Block) (pointer : Pointer) (byte : Byte)
    (executed : loadBlocks blocks pointer = some byte) :
    ∃ block ∈ blocks, Matches block pointer ∧
      block.bytes[pointer.address.val - block.base.val]? = some (some byte) := by
  induction blocks with
  | nil => cases executed
  | cons block tail ih =>
    unfold loadBlocks at executed
    split at executed
    · rename_i matched
      cases found : block.bytes[pointer.address.val - block.base.val]? with
      | none => simp only [found, Option.bind] at executed; cases executed
      | some value =>
        cases value with
        | none => simp only [found, Option.bind] at executed; cases executed
        | some stored =>
          simp only [found, Option.bind, id_eq] at executed
          cases executed
          exact ⟨block, List.mem_cons_self, matched, found⟩
    · obtain ⟨selected, member, matched, initialized⟩ := ih executed
      exact ⟨selected, List.mem_cons_of_mem block member, matched, initialized⟩

theorem store_frame_other_origin (blocks : List Block) (pointer : Pointer) (byte : Byte)
    (output : List Block) (executed : storeBlocks blocks pointer byte = some output)
    (reader : Pointer) (different : reader.provenance ≠ pointer.provenance) :
    loadBlocks output reader = loadBlocks blocks reader := by
  induction blocks generalizing output with
  | nil => cases executed
  | cons block tail ih =>
    unfold storeBlocks at executed
    dsimp only at executed
    split at executed
    · rename_i matched
      split at executed
      · cases executed
        have unmatched : ¬ Matches block reader := fun read => different (read.1.trans matched.1.symm)
        have stillUnmatched : ¬ Matches {block with bytes := (block.bytes.set
            (pointer.address.val - block.base.val) (some byte))} reader := unmatched
        simp only [loadBlocks, ite_eq_right unmatched, ite_eq_right stillUnmatched]
      · cases executed
    · cases rest : storeBlocks tail pointer byte with
      | none => simp only [rest, Option.map_none] at executed; cases executed
      | some result =>
        simp only [rest, Option.map_some] at executed
        cases executed
        unfold loadBlocks
        split
        · rfl
        · exact ih result rest

inductive Step : State → State → Prop where
  | allocate (state : State) (base : Address) (layout : Layout) (pointer : Pointer) (next : State)
      (executed : NativeByteMemory.allocate state base layout = some (pointer, next)) : Step state next
  | store (state : State) (pointer : Pointer) (byte : Byte) (next : State)
      (executed : storeByte state pointer byte = some next) : Step state next
  | deallocate (state : State) (pointer : Pointer) (layout : Layout) (next : State)
      (executed : NativeByteMemory.deallocate state pointer layout = some next) : Step state next

inductive Reachable : State → Prop where
  | empty : Reachable NativeByteMemory.empty
  | step {state next : State} (previous : Reachable state) (executed : Step state next) : Reachable next

theorem step_wellFormed {state next : State} (valid : WellFormed state)
    (executed : Step state next) : WellFormed next := by
  cases executed with
  | allocate base layout pointer next executed => exact allocate_wellFormed state valid base layout pointer next executed
  | store pointer byte next executed => exact store_wellFormed state valid pointer byte next executed
  | deallocate pointer layout next executed => exact deallocate_wellFormed state valid pointer layout next executed

theorem reachable_wellFormed {state : State} (reachable : Reachable state) : WellFormed state := by
  induction reachable with
  | empty => exact empty_wellFormed
  | step previous executed ih => exact step_wellFormed ih executed

end FormalProof4FHE.HasteBoots.NativeByteMemory
