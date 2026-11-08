module
public import FormalProof4FHE.HasteBoots.NativeWord64Memory
public import FormalProof4FHE.HasteBoots.NativeRawByteRange
public import FormalProof4FHE.HasteBoots.NativePointerShadow
@[expose] public section

/-! Thin pointer storage in actual bytes with finite per-byte allocation origins.
This layer does not authenticate supplied values or establish Rust alias rules. -/
namespace FormalProof4FHE.HasteBoots.NativePointerByteMemory
open NativePointerStorage (Address Origin Pointer)
open NativeByteMemory (Byte Layout)

structure State where
  memory : NativeByteMemory.State
  shadow : List NativePointerShadow.Cell
  deriving DecidableEq

def empty : State := ⟨NativeByteMemory.empty, []⟩

def load (state : State) (slot : Pointer) : Option Pointer := do
  let owner ← slot.provenance
  let address ← NativeWord64Memory.load state.memory slot
  let origin ← NativePointerShadow.uniform state.shadow owner slot.address.val 8
  pure ⟨address, origin⟩

def store (state : State) (slot value : Pointer) : Option State := do
  let owner ← slot.provenance
  let memory ← NativeWord64Memory.store state.memory slot value.address
  pure ⟨memory, NativePointerShadow.replace state.shadow owner slot.address.val
    (List.replicate 8 value.provenance)⟩

/-- Numerical writes erase origins, including writes of unchanged bits. -/
def writeBytes (state : State) (slot : Pointer) (alignment : Nat) (bytes : List Byte) : Option State := do
  let memory ← NativeByteRangeWrite.storeRange state.memory slot alignment bytes
  let shadow := match slot.provenance with
    | none => state.shadow
    | some owner => NativePointerShadow.clear state.shadow owner slot.address.val bytes.length
  pure ⟨memory, shadow⟩

def writeWord (state : State) (slot : Pointer) (word : NativeWord64Memory.Word) : Option State :=
  writeBytes state slot 8 (NativeWord64Memory.encode word)

/-- Both byte and metadata snapshots precede replacement, including overlap. -/
def copy (state : State) (source target : Pointer) (size alignment : Nat) : Option State :=
  if size = 0 then
    (NativeRawByteRange.copy state.memory source target size alignment).map (fun memory => {state with memory})
  else do
    let sourceOwner ← source.provenance
    let targetOwner ← target.provenance
    let memory ← NativeRawByteRange.copy state.memory source target size alignment
    pure ⟨memory, NativePointerShadow.replace state.shadow targetOwner target.address.val
      (NativePointerShadow.snapshot state.shadow sourceOwner source.address.val size)⟩

def copyNonoverlapping (state : State) (source target : Pointer) (size alignment : Nat) : Option State :=
  if ¬ NativeByteBorrow.Overlap source ⟨size, alignment⟩ target ⟨size, alignment⟩ then
    copy state source target size alignment
  else none

def allocate (state : State) (base : Address) (layout : Layout) : Option (Pointer × State) :=
  (NativeByteMemory.allocate state.memory base layout).map (fun (pointer, memory) => (pointer, ⟨memory, state.shadow⟩))

/-- Freeing storage removes its metadata, retaining other stored dangling values. -/
def deallocate (state : State) (pointer : Pointer) (layout : Layout) : Option State := do
  let owner ← pointer.provenance
  let memory ← NativeByteMemory.deallocate state.memory pointer layout
  pure ⟨memory, state.shadow.filter (fun cell => decide (cell.owner ≠ owner))⟩

theorem store_success (state next : State) (slot value : Pointer) (stored : store state slot value = some next) :
    ∃ owner, slot.provenance = some owner ∧ NativeWord64Memory.store state.memory slot value.address = some next.memory ∧
      next.shadow = NativePointerShadow.replace state.shadow owner slot.address.val (List.replicate 8 value.provenance) := by
  unfold store at stored
  cases ownerEq : slot.provenance with
  | none => simp only [ownerEq, Option.bind_eq_bind', Option.bind] at stored; cases stored
  | some owner =>
    simp only [ownerEq, Option.bind_eq_bind', Option.bind] at stored
    cases memoryEq : NativeWord64Memory.store state.memory slot value.address with
    | none => simp only [memoryEq] at stored; cases stored
    | some memory =>
      simp only [memoryEq, pure] at stored
      cases stored
      exact ⟨owner, rfl, rfl, rfl⟩

theorem store_then_load (state next : State) (slot value : Pointer) (stored : store state slot value = some next) :
    load next slot = some value := by
  obtain ⟨owner, ownerEq, memoryEq, shadowEq⟩ := store_success state next slot value stored
  have read := NativeWord64Memory.store_then_load state.memory next.memory slot value.address memoryEq
  have origin := NativePointerShadow.replace_uniform state.shadow owner slot.address.val 8 value.provenance (by decide)
  simp only [load, ownerEq, Option.bind_eq_bind', Option.bind, read, shadowEq, origin, pure]

theorem store_wellFormed (state next : State) (valid : NativeByteMemory.WellFormed state.memory)
    (slot value : Pointer) (stored : store state slot value = some next) : NativeByteMemory.WellFormed next.memory := by
  obtain ⟨_, _, memoryEq, _⟩ := store_success state next slot value stored
  exact NativeWord64Memory.store_wellFormed state.memory next.memory valid slot value.address memoryEq

theorem load_success (state : State) (slot value : Pointer) (loaded : load state slot = some value) :
    ∃ owner, slot.provenance = some owner ∧ NativeWord64Memory.load state.memory slot = some value.address ∧
      NativePointerShadow.uniform state.shadow owner slot.address.val 8 = some value.provenance := by
  unfold load at loaded
  simp only [Option.bind_eq_bind'] at loaded
  cases ownerEq : slot.provenance with
  | none => simp only [ownerEq, Option.bind] at loaded; cases loaded
  | some owner =>
    simp only [ownerEq, Option.bind] at loaded
    cases addressEq : NativeWord64Memory.load state.memory slot with
    | none => simp only [addressEq] at loaded; cases loaded
    | some address =>
      simp only [addressEq] at loaded
      cases originEq : NativePointerShadow.uniform state.shadow owner slot.address.val 8 with
      | none => simp only [originEq] at loaded; cases loaded
      | some origin =>
        simp only [originEq, pure] at loaded
        cases loaded
        exact ⟨owner, rfl, rfl, originEq⟩

theorem writeBytes_success (state next : State) (slot : Pointer) (alignment : Nat) (bytes : List Byte)
    (written : writeBytes state slot alignment bytes = some next) :
    NativeByteRangeWrite.storeRange state.memory slot alignment bytes = some next.memory ∧
      next.shadow = match slot.provenance with
        | none => state.shadow
        | some owner => NativePointerShadow.clear state.shadow owner slot.address.val bytes.length := by
  unfold writeBytes at written
  cases memoryEq : NativeByteRangeWrite.storeRange state.memory slot alignment bytes with
  | none => simp only [memoryEq, Option.bind_eq_bind', Option.bind] at written; cases written
  | some memory =>
    simp only [memoryEq, Option.bind_eq_bind', Option.bind, pure] at written
    cases written
    exact ⟨rfl, rfl⟩

theorem writeWord_then_load (state next : State) (slot : Pointer) (owner : Origin) (ownerEq : slot.provenance = some owner)
    (word : NativeWord64Memory.Word) (written : writeWord state slot word = some next) :
    load next slot = some ⟨word, none⟩ := by
  obtain ⟨memoryEq, shadowEq⟩ := writeBytes_success state next slot 8 (NativeWord64Memory.encode word) written
  have read := NativeWord64Memory.store_then_load state.memory next.memory slot word memoryEq
  simp only [ownerEq, NativeWord64Memory.encode_length] at shadowEq
  have origin := NativePointerShadow.clear_uniform state.shadow owner slot.address.val 8 (by decide)
  simp only [load, ownerEq, Option.bind_eq_bind', Option.bind, read, shadowEq, origin, pure]

theorem writeBytes_wellFormed (state next : State) (valid : NativeByteMemory.WellFormed state.memory)
    (slot : Pointer) (alignment : Nat) (bytes : List Byte) (written : writeBytes state slot alignment bytes = some next) :
    NativeByteMemory.WellFormed next.memory := by
  obtain ⟨memoryEq, _⟩ := writeBytes_success state next slot alignment bytes written
  exact NativeByteRangeWrite.storeRange_wellFormed state.memory valid slot alignment bytes next.memory memoryEq

theorem uniform_lookup (cells : List NativePointerShadow.Cell) (owner : Origin) (base size : Nat) (origin : Option Origin)
    (uniform : NativePointerShadow.uniform cells owner base size = some origin) :
    ∀ index < size, NativePointerShadow.lookup cells owner (base + index) = origin := by
  unfold NativePointerShadow.uniform at uniform
  dsimp only at uniform
  split at uniform
  next same =>
    cases uniform
    intro index inside
    exact of_decide_eq_true (List.all_eq_true.mp same index (List.mem_range.mpr inside))
  next => cases uniform

theorem snapshot_at (cells : List NativePointerShadow.Cell) (owner : Origin) (base size index : Nat) (inside : index < size) :
    (NativePointerShadow.snapshot cells owner base size)[index]? = some (NativePointerShadow.lookup cells owner (base + index)) := by
  simp only [NativePointerShadow.snapshot, List.getElem?_map, List.getElem?_range, inside, Option.map_some]

theorem snapshot_uniform (cells : List NativePointerShadow.Cell) (owner : Origin) (base size : Nat) (origin : Option Origin)
    (uniform : NativePointerShadow.uniform cells owner base size = some origin) :
    NativePointerShadow.snapshot cells owner base size = List.replicate size origin := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < size
  · rw [snapshot_at cells owner base size index inside, uniform_lookup cells owner base size origin uniform index inside]
    simp only [List.getElem?_replicate, inside, ite_true]
  · have outside : (NativePointerShadow.snapshot cells owner base size)[index]? = none :=
      List.getElem?_eq_none (by simpa only [NativePointerShadow.snapshot_length] using Nat.le_of_not_gt inside)
    rw [outside]
    simp only [List.getElem?_replicate, inside, ite_false]

theorem copy_success (state next : State) (source target : Pointer) (size alignment : Nat) (nonzero : size ≠ 0)
    (copied : copy state source target size alignment = some next) :
    ∃ sourceOwner targetOwner, source.provenance = some sourceOwner ∧ target.provenance = some targetOwner ∧
      NativeRawByteRange.copy state.memory source target size alignment = some next.memory ∧
      next.shadow = NativePointerShadow.replace state.shadow targetOwner target.address.val
        (NativePointerShadow.snapshot state.shadow sourceOwner source.address.val size) := by
  rw [copy, ite_eq_right nonzero] at copied
  simp only [Option.bind_eq_bind'] at copied
  cases sourceEq : source.provenance with
  | none => simp only [sourceEq, Option.bind] at copied; cases copied
  | some sourceOwner =>
    simp only [sourceEq, Option.bind] at copied
    cases targetEq : target.provenance with
    | none => simp only [targetEq] at copied; cases copied
    | some targetOwner =>
      simp only [targetEq] at copied
      cases memoryEq : NativeRawByteRange.copy state.memory source target size alignment with
      | none => simp only [memoryEq] at copied; cases copied
      | some memory =>
        simp only [memoryEq, pure] at copied
        cases copied
        exact ⟨sourceOwner, targetOwner, rfl, rfl, rfl, rfl⟩

theorem copy_then_load (state next : State) (source target value : Pointer)
    (loaded : load state source = some value) (copied : copy state source target 8 8 = some next) :
    load next target = some value := by
  obtain ⟨sourceOwner, targetOwner, sourceEq, targetEq, memoryEq, shadowEq⟩ :=
    copy_success state next source target 8 8 (by decide) copied
  obtain ⟨owner, ownerEq, addressEq, originEq⟩ := load_success state source value loaded
  have sameOwner : owner = sourceOwner := Option.some.inj (ownerEq.symm.trans sourceEq)
  subst owner
  have bytesRead := (NativeWord64Memory.load_iff_bytes state.memory source value.address).mp addressEq
  have bytesStored := NativeRawByteRange.copy_initialized_store state.memory next.memory source target 8 8
    (by decide) (NativeWord64Memory.encode value.address) bytesRead memoryEq
  have read := NativeWord64Memory.store_then_load state.memory next.memory target value.address bytesStored
  rw [snapshot_uniform state.shadow sourceOwner source.address.val 8 value.provenance originEq] at shadowEq
  have origin := NativePointerShadow.replace_uniform state.shadow targetOwner target.address.val 8 value.provenance (by decide)
  simp only [load, targetEq, Option.bind_eq_bind', Option.bind, read, shadowEq, origin, pure]

theorem copy_zero (state next : State) (source target : Pointer) (alignment : Nat)
    (copied : copy state source target 0 alignment = some next) : next.shadow = state.shadow := by
  simp only [copy, ite_true] at copied
  cases memoryEq : NativeRawByteRange.copy state.memory source target 0 alignment with
  | none => simp only [memoryEq, Option.map_none] at copied; cases copied
  | some memory => simp only [memoryEq, Option.map_some] at copied; cases copied; rfl

theorem copy_wellFormed (state next : State) (valid : NativeByteMemory.WellFormed state.memory)
    (source target : Pointer) (size alignment : Nat) (copied : copy state source target size alignment = some next) :
    NativeByteMemory.WellFormed next.memory := by
  by_cases zero : size = 0
  · subst size
    simp only [copy, ite_true] at copied
    cases memoryEq : NativeRawByteRange.copy state.memory source target 0 alignment with
    | none => simp only [memoryEq, Option.map_none] at copied; cases copied
    | some memory =>
      simp only [memoryEq, Option.map_some] at copied
      cases copied
      exact NativeRawByteRange.copy_wellFormed state.memory memory valid source target 0 alignment memoryEq
  · obtain ⟨_, _, _, _, memoryEq, _⟩ := copy_success state next source target size alignment zero copied
    exact NativeRawByteRange.copy_wellFormed state.memory next.memory valid source target size alignment memoryEq

theorem nonoverlapping_success (state next : State) (source target : Pointer) (size alignment : Nat)
    (copied : copyNonoverlapping state source target size alignment = some next) :
    ¬ NativeByteBorrow.Overlap source ⟨size, alignment⟩ target ⟨size, alignment⟩ ∧
      copy state source target size alignment = some next := by
  unfold copyNonoverlapping at copied
  split at copied
  next separate => exact ⟨separate, copied⟩
  next => cases copied

theorem allocate_success (state next : State) (base : Address) (layout : Layout) (pointer : Pointer)
    (allocated : allocate state base layout = some (pointer, next)) :
    NativeByteMemory.allocate state.memory base layout = some (pointer, next.memory) ∧ next.shadow = state.shadow := by
  unfold allocate at allocated
  cases memoryEq : NativeByteMemory.allocate state.memory base layout with
  | none => simp only [memoryEq, Option.map_none] at allocated; cases allocated
  | some result =>
    rcases result with ⟨reference, memory⟩
    simp only [memoryEq, Option.map_some] at allocated
    cases allocated
    exact ⟨rfl, rfl⟩

theorem allocate_wellFormed (state next : State) (valid : NativeByteMemory.WellFormed state.memory)
    (base : Address) (layout : Layout) (pointer : Pointer) (allocated : allocate state base layout = some (pointer, next)) :
    NativeByteMemory.WellFormed next.memory := by
  exact NativeByteMemory.allocate_wellFormed state.memory valid base layout pointer next.memory
    (allocate_success state next base layout pointer allocated).1

theorem deallocate_success (state next : State) (pointer : Pointer) (layout : Layout)
    (freed : deallocate state pointer layout = some next) :
    ∃ owner, pointer.provenance = some owner ∧ NativeByteMemory.deallocate state.memory pointer layout = some next.memory ∧
      next.shadow = state.shadow.filter (fun cell => decide (cell.owner ≠ owner)) := by
  unfold deallocate at freed
  simp only [Option.bind_eq_bind'] at freed
  cases ownerEq : pointer.provenance with
  | none => simp only [ownerEq, Option.bind] at freed; cases freed
  | some owner =>
    simp only [ownerEq, Option.bind] at freed
    cases memoryEq : NativeByteMemory.deallocate state.memory pointer layout with
    | none => simp only [memoryEq] at freed; cases freed
    | some memory =>
      simp only [memoryEq, pure] at freed
      cases freed
      exact ⟨owner, rfl, rfl, rfl⟩

theorem deallocate_wellFormed (state next : State) (valid : NativeByteMemory.WellFormed state.memory)
    (pointer : Pointer) (layout : Layout) (freed : deallocate state pointer layout = some next) :
    NativeByteMemory.WellFormed next.memory := by
  obtain ⟨_, _, memoryEq, _⟩ := deallocate_success state next pointer layout freed
  exact NativeByteMemory.deallocate_wellFormed state.memory valid pointer layout next.memory memoryEq

theorem load_without_storage_origin (state : State) (slot : Pointer) (missing : slot.provenance = none) :
    load state slot = none := by
  simp only [load, missing, Option.bind_eq_bind', Option.bind]

theorem store_defined_iff (state : State) (valid : NativeByteMemory.WellFormed state.memory)
    (slot value : Pointer) (owner : Origin) (ownerEq : slot.provenance = some owner) :
    (∃ next, store state slot value = some next) ↔ NativeByteRange.checkRange state.memory slot ⟨8, 8⟩ = true := by
  rw [← NativeWord64Memory.store_defined_iff state.memory valid slot value.address]
  constructor
  · rintro ⟨next, stored⟩
    exact ⟨next.memory, (store_success state next slot value stored).choose_spec.2.1⟩
  · rintro ⟨memory, stored⟩
    refine ⟨⟨memory, NativePointerShadow.replace state.shadow owner slot.address.val (List.replicate 8 value.provenance)⟩, ?_⟩
    simp only [store, ownerEq, Option.bind_eq_bind', Option.bind, stored, pure]

theorem store_after_deallocation (state next : State) (valid : NativeByteMemory.WellFormed state.memory)
    (pointer : Pointer) (layout : Layout) (freed : deallocate state pointer layout = some next)
    (slot value : Pointer) (sameOrigin : slot.provenance = pointer.provenance) : store next slot value = none := by
  obtain ⟨owner, ownerEq, memoryEq, _⟩ := deallocate_success state next pointer layout freed
  have rejected := NativeWord64Memory.store_after_deallocation state.memory valid pointer layout next.memory memoryEq
    slot sameOrigin value.address
  simp only [store, sameOrigin, ownerEq, Option.bind_eq_bind', Option.bind, rejected]

theorem load_after_deallocation (state next : State) (valid : NativeByteMemory.WellFormed state.memory)
    (pointer : Pointer) (layout : Layout) (freed : deallocate state pointer layout = some next)
    (slot : Pointer) (sameOrigin : slot.provenance = pointer.provenance) : load next slot = none := by
  obtain ⟨owner, ownerEq, memoryEq, _⟩ := deallocate_success state next pointer layout freed
  have rejected := NativeByteRange.positive_after_deallocation state.memory valid pointer layout next.memory memoryEq
    slot sameOrigin ⟨8, 8⟩ (by decide)
  simp only [load, sameOrigin, ownerEq, Option.bind_eq_bind', Option.bind, NativeWord64Memory.load, rejected]

theorem deallocate_metadata (state next : State) (pointer : Pointer) (layout : Layout)
    (freed : deallocate state pointer layout = some next) (cell : NativePointerShadow.Cell) :
    cell ∈ next.shadow ↔ cell ∈ state.shadow ∧ some cell.owner ≠ pointer.provenance := by
  obtain ⟨owner, ownerEq, _, shadowEq⟩ := deallocate_success state next pointer layout freed
  simp only [shadowEq, List.mem_filter, decide_eq_true_eq, ownerEq, ne_eq, Option.some.injEq]

theorem load_origin_recorded (state : State) (slot value : Pointer) (origin : Origin)
    (loaded : load state slot = some value) (hasOrigin : value.provenance = some origin) :
    ∃ cell ∈ state.shadow, some cell.owner = slot.provenance ∧ cell.address = slot.address.val ∧ cell.origin = origin := by
  obtain ⟨owner, ownerEq, _, uniform⟩ := load_success state slot value loaded
  have found := uniform_lookup state.shadow owner slot.address.val 8 value.provenance uniform 0 (by decide)
  simp only [Nat.add_zero, hasOrigin] at found
  obtain ⟨cell, member, cellOwner, addressEq, originEq⟩ := NativePointerShadow.lookup_selected state.shadow owner slot.address.val origin found
  exact ⟨cell, member, by rw [cellOwner, ownerEq], addressEq, originEq⟩

theorem install_origin_source (cells : List NativePointerShadow.Cell) (owner : Origin) (base : Nat)
    (origins : List (Option Origin)) (cell : NativePointerShadow.Cell)
    (member : cell ∈ NativePointerShadow.install owner base origins cells) :
    cell ∈ cells ∨ some cell.origin ∈ origins := by
  induction origins generalizing base with
  | nil => exact Or.inl member
  | cons origin tail ih =>
    cases origin with
    | none =>
      rcases ih (base + 1) member with old | introduced
      · exact Or.inl old
      · exact Or.inr (List.mem_cons_of_mem none introduced)
    | some value =>
      rcases List.mem_cons.mp member with same | later
      · subst cell
        exact Or.inr List.mem_cons_self
      · rcases ih (base + 1) later with old | introduced
        · exact Or.inl old
        · exact Or.inr (List.mem_cons_of_mem (some value) introduced)

theorem replace_origin_source (cells : List NativePointerShadow.Cell) (owner : Origin) (base : Nat)
    (origins : List (Option Origin)) (cell : NativePointerShadow.Cell)
    (member : cell ∈ NativePointerShadow.replace cells owner base origins) :
    cell ∈ cells ∨ some cell.origin ∈ origins := by
  rcases install_origin_source (NativePointerShadow.clear cells owner base origins.length) owner base origins cell member with old | introduced
  · exact Or.inl (List.mem_filter.mp old).1
  · exact Or.inr introduced

theorem snapshot_origin_source (cells : List NativePointerShadow.Cell) (owner : Origin) (base size : Nat) (origin : Origin)
    (member : some origin ∈ NativePointerShadow.snapshot cells owner base size) :
    ∃ cell ∈ cells, cell.origin = origin := by
  obtain ⟨index, _, found⟩ := List.mem_map.mp member
  obtain ⟨cell, present, _, _, same⟩ := NativePointerShadow.lookup_selected cells owner (base + index) origin found
  exact ⟨cell, present, same⟩

theorem store_origin_source (state next : State) (slot value : Pointer) (stored : store state slot value = some next)
    (cell : NativePointerShadow.Cell) (member : cell ∈ next.shadow) :
    cell ∈ state.shadow ∨ value.provenance = some cell.origin := by
  obtain ⟨owner, _, _, shadowEq⟩ := store_success state next slot value stored
  rw [shadowEq] at member
  rcases replace_origin_source state.shadow owner slot.address.val (List.replicate 8 value.provenance) cell member with old | introduced
  · exact Or.inl old
  · simp only [List.mem_replicate] at introduced
    exact Or.inr introduced.2.symm

theorem copy_origin_source (state next : State) (source target : Pointer) (size alignment : Nat)
    (copied : copy state source target size alignment = some next) (cell : NativePointerShadow.Cell) (member : cell ∈ next.shadow) :
    ∃ original ∈ state.shadow, original.origin = cell.origin := by
  by_cases zero : size = 0
  · subst size
    rw [copy_zero state next source target alignment copied] at member
    exact ⟨cell, member, rfl⟩
  · obtain ⟨sourceOwner, targetOwner, _, _, _, shadowEq⟩ := copy_success state next source target size alignment zero copied
    rw [shadowEq] at member
    rcases replace_origin_source state.shadow targetOwner target.address.val
      (NativePointerShadow.snapshot state.shadow sourceOwner source.address.val size) cell member with old | introduced
    · exact ⟨cell, old, rfl⟩
    · exact snapshot_origin_source state.shadow sourceOwner source.address.val size cell.origin introduced

theorem writeBytes_origin_source (state next : State) (slot : Pointer) (alignment : Nat) (bytes : List Byte)
    (written : writeBytes state slot alignment bytes = some next) (cell : NativePointerShadow.Cell) (member : cell ∈ next.shadow) :
    cell ∈ state.shadow := by
  obtain ⟨_, shadowEq⟩ := writeBytes_success state next slot alignment bytes written
  rw [shadowEq] at member
  cases ownerEq : slot.provenance with
  | none => simpa only [ownerEq] using member
  | some owner =>
    simp only [ownerEq] at member
    exact (List.mem_filter.mp member).1

end FormalProof4FHE.HasteBoots.NativePointerByteMemory
