module
public import FormalProof4FHE.HasteBoots.NativePointerByteMemory
@[expose] public section

/-! Closed pointer-value construction over concrete bytes and origin metadata.
Allocation identity here does not confer actor authority or Rust borrow rights. -/
namespace FormalProof4FHE.HasteBoots.NativePointerMachine
open NativePointerStorage (Address Origin Pointer)
open NativeByteMemory (Byte Layout)

structure Allocation where
  base : Address
  layout : Layout
  generation : Nat
  deriving DecidableEq

def Allocation.origin (event : Allocation) : Origin := ⟨event.base.val, event.generation⟩

structure State where
  heap : NativePointerByteMemory.State
  registers : List Pointer
  history : List Allocation
  deriving DecidableEq

/-- Operands contain no allocation identities or pointer records. The allocator
address is an outcome checked by the concrete allocator. -/
inductive Op where
  | allocate (base : Address) (layout : Layout)
  | fromAddress (address : Address)
  | withAddress (register : Nat) (address : Address)
  | load (slot : Nat)
  | store (slot value : Nat)
  | writeBytes (slot alignment : Nat) (bytes : List Byte)
  | copy (source target size alignment : Nat)
  | copyNonoverlapping (source target size alignment : Nat)
  | free (register : Nat) (layout : Layout)
  deriving DecidableEq

def empty : State := ⟨NativePointerByteMemory.empty, [], []⟩

def push (state : State) (value : Pointer) : State := {state with registers := value :: state.registers}

def setHeap (state : State) (heap : NativePointerByteMemory.State) : State := {state with heap}

def execute (state : State) : Op → Option State
  | .allocate base layout =>
    (NativePointerByteMemory.allocate state.heap base layout).map (fun (pointer, heap) =>
      ⟨heap, pointer :: state.registers, ⟨base, layout, state.heap.memory.nextGeneration⟩ :: state.history⟩)
  | .fromAddress address => some (push state ⟨address, none⟩)
  | .withAddress register address =>
    state.registers[register]?.map (fun pointer => push state ⟨address, pointer.provenance⟩)
  | .load slot => state.registers[slot]?.bind (fun pointer =>
    (NativePointerByteMemory.load state.heap pointer).map (push state))
  | .store slot value => state.registers[slot]?.bind (fun pointer =>
    state.registers[value]?.bind (fun data =>
      (NativePointerByteMemory.store state.heap pointer data).map (setHeap state)))
  | .writeBytes slot alignment bytes => state.registers[slot]?.bind (fun pointer =>
    (NativePointerByteMemory.writeBytes state.heap pointer alignment bytes).map (setHeap state))
  | .copy source target size alignment => state.registers[source]?.bind (fun sourcePointer =>
    state.registers[target]?.bind (fun targetPointer =>
      (NativePointerByteMemory.copy state.heap sourcePointer targetPointer size alignment).map (setHeap state)))
  | .copyNonoverlapping source target size alignment => state.registers[source]?.bind (fun sourcePointer =>
    state.registers[target]?.bind (fun targetPointer =>
      (NativePointerByteMemory.copyNonoverlapping state.heap sourcePointer targetPointer size alignment).map (setHeap state)))
  | .free register layout => state.registers[register]?.bind (fun pointer =>
    (NativePointerByteMemory.deallocate state.heap pointer layout).map (setHeap state))

def run (state : State) : List Op → Option State
  | [] => some state
  | op :: tail => (execute state op).bind (fun next => run next tail)

def Issued (state : State) (origin : Origin) : Prop :=
  ∃ event ∈ state.history, event.origin = origin

def Authentic (state : State) : Prop :=
  (∀ pointer ∈ state.registers, ∀ origin, pointer.provenance = some origin → Issued state origin) ∧
  (∀ cell ∈ state.heap.shadow, Issued state cell.origin)

def WellFormed (state : State) : Prop :=
  NativeByteMemory.WellFormed state.heap.memory ∧ Authentic state ∧
    ∀ event ∈ state.history, event.generation < state.heap.memory.nextGeneration

inductive Reachable : State → Prop where
  | empty : Reachable empty
  | step {state next : State} (before : Reachable state) (op : Op) (executed : execute state op = some next) : Reachable next

inductive Runs : State → State → Prop where
  | refl (state : State) : Runs state state
  | step {start state next : State} (before : Runs start state) (op : Op) (executed : execute state op = some next) : Runs start next

theorem empty_wellFormed : WellFormed empty := by
  refine ⟨NativeByteMemory.empty_wellFormed, ?_, ?_⟩
  · constructor
    · intro pointer member; cases member
    · intro cell member; cases member
  · exact fun _ member => nomatch member

theorem register_authentic (state : State) (authentic : Authentic state) (index : Nat) (pointer : Pointer)
    (selected : state.registers[index]? = some pointer) (origin : Origin) (hasOrigin : pointer.provenance = some origin) :
    Issued state origin := authentic.1 pointer (List.mem_of_getElem? selected) origin hasOrigin

theorem push_wellFormed (state : State) (valid : WellFormed state) (pointer : Pointer)
    (authentic : ∀ origin, pointer.provenance = some origin → Issued state origin) : WellFormed (push state pointer) := by
  refine ⟨valid.1, ⟨?_, valid.2.1.2⟩, valid.2.2⟩
  intro value member origin hasOrigin
  rcases List.mem_cons.mp member with same | old
  · subst value; exact authentic origin hasOrigin
  · exact valid.2.1.1 value old origin hasOrigin

theorem setHeap_wellFormed (state : State) (valid : WellFormed state) (heap : NativePointerByteMemory.State)
    (heapValid : NativeByteMemory.WellFormed heap.memory)
    (generation : heap.memory.nextGeneration = state.heap.memory.nextGeneration)
    (authentic : ∀ cell ∈ heap.shadow, Issued state cell.origin) : WellFormed (setHeap state heap) := by
  refine ⟨heapValid, ⟨valid.2.1.1, authentic⟩, ?_⟩
  intro event member
  dsimp only [setHeap]
  rw [generation]
  exact valid.2.2 event member

theorem store_generation (heap next : NativePointerByteMemory.State) (slot value : Pointer)
    (stored : NativePointerByteMemory.store heap slot value = some next) :
    next.memory.nextGeneration = heap.memory.nextGeneration := by
  obtain ⟨_, _, memoryEq, _⟩ := NativePointerByteMemory.store_success heap next slot value stored
  exact (NativeByteRangeWrite.storeRange_success heap.memory slot 8 (NativeWord64Memory.encode value.address) next.memory memoryEq).2.1

theorem write_generation (heap next : NativePointerByteMemory.State) (slot : Pointer) (alignment : Nat) (bytes : List Byte)
    (written : NativePointerByteMemory.writeBytes heap slot alignment bytes = some next) :
    next.memory.nextGeneration = heap.memory.nextGeneration := by
  have stored := (NativePointerByteMemory.writeBytes_success heap next slot alignment bytes written).1
  exact (NativeByteRangeWrite.storeRange_success heap.memory slot alignment bytes next.memory stored).2.1

theorem raw_copy_generation (memory next : NativeByteMemory.State) (source target : Pointer) (size alignment : Nat)
    (copied : NativeRawByteRange.copy memory source target size alignment = some next) :
    next.nextGeneration = memory.nextGeneration := by
  by_cases zero : size = 0
  · subst size
    unfold NativeRawByteRange.copy at copied
    simp only [ite_true] at copied
    split at copied
    · cases copied; rfl
    · cases copied
  · obtain ⟨values, _, _, stored, _⟩ := NativeRawByteRange.copy_success memory next source target size alignment zero copied
    exact (NativeRawByteRange.storeRange_success memory next target alignment values stored).2.1

theorem copy_generation (heap next : NativePointerByteMemory.State) (source target : Pointer) (size alignment : Nat)
    (copied : NativePointerByteMemory.copy heap source target size alignment = some next) :
    next.memory.nextGeneration = heap.memory.nextGeneration := by
  by_cases zero : size = 0
  · subst size
    simp only [NativePointerByteMemory.copy, ite_true, Option.map_eq_some_iff] at copied
    obtain ⟨memory, copied, same⟩ := copied
    subst next
    exact raw_copy_generation heap.memory memory source target 0 alignment copied
  · obtain ⟨_, _, _, _, copied, _⟩ := NativePointerByteMemory.copy_success heap next source target size alignment zero copied
    exact raw_copy_generation heap.memory next.memory source target size alignment copied

theorem free_generation (heap next : NativePointerByteMemory.State) (pointer : Pointer) (layout : Layout)
    (freed : NativePointerByteMemory.deallocate heap pointer layout = some next) :
    next.memory.nextGeneration = heap.memory.nextGeneration := by
  obtain ⟨_, _, memoryEq, _⟩ := NativePointerByteMemory.deallocate_success heap next pointer layout freed
  exact NativeByteMemory.deallocate_generation heap.memory pointer layout next.memory memoryEq

theorem store_wellFormed (state : State) (valid : WellFormed state) (heap : NativePointerByteMemory.State)
    (slot value : Pointer) (valueAuthentic : ∀ origin, value.provenance = some origin → Issued state origin)
    (stored : NativePointerByteMemory.store state.heap slot value = some heap) : WellFormed (setHeap state heap) := by
  apply setHeap_wellFormed state valid heap
    (NativePointerByteMemory.store_wellFormed state.heap heap valid.1 slot value stored)
    (store_generation state.heap heap slot value stored)
  intro cell member
  rcases NativePointerByteMemory.store_origin_source state.heap heap slot value stored cell member with old | introduced
  · exact valid.2.1.2 cell old
  · exact valueAuthentic cell.origin introduced

theorem write_wellFormed (state : State) (valid : WellFormed state) (heap : NativePointerByteMemory.State)
    (slot : Pointer) (alignment : Nat) (bytes : List Byte)
    (written : NativePointerByteMemory.writeBytes state.heap slot alignment bytes = some heap) : WellFormed (setHeap state heap) := by
  apply setHeap_wellFormed state valid heap
    (NativePointerByteMemory.writeBytes_wellFormed state.heap heap valid.1 slot alignment bytes written)
    (write_generation state.heap heap slot alignment bytes written)
  intro cell member
  exact valid.2.1.2 cell (NativePointerByteMemory.writeBytes_origin_source state.heap heap slot alignment bytes written cell member)

theorem copy_wellFormed (state : State) (valid : WellFormed state) (heap : NativePointerByteMemory.State)
    (source target : Pointer) (size alignment : Nat)
    (copied : NativePointerByteMemory.copy state.heap source target size alignment = some heap) : WellFormed (setHeap state heap) := by
  apply setHeap_wellFormed state valid heap
    (NativePointerByteMemory.copy_wellFormed state.heap heap valid.1 source target size alignment copied)
    (copy_generation state.heap heap source target size alignment copied)
  intro cell member
  obtain ⟨original, present, same⟩ := NativePointerByteMemory.copy_origin_source state.heap heap source target size alignment copied cell member
  rw [← same]
  exact valid.2.1.2 original present

theorem free_wellFormed (state : State) (valid : WellFormed state) (heap : NativePointerByteMemory.State)
    (pointer : Pointer) (layout : Layout) (freed : NativePointerByteMemory.deallocate state.heap pointer layout = some heap) :
    WellFormed (setHeap state heap) := by
  apply setHeap_wellFormed state valid heap
    (NativePointerByteMemory.deallocate_wellFormed state.heap heap valid.1 pointer layout freed)
    (free_generation state.heap heap pointer layout freed)
  intro cell member
  exact valid.2.1.2 cell ((NativePointerByteMemory.deallocate_metadata state.heap heap pointer layout freed cell).mp member).1

theorem allocate_wellFormed (state : State) (valid : WellFormed state) (base : Address) (layout : Layout)
    (pointer : Pointer) (heap : NativePointerByteMemory.State)
    (allocated : NativePointerByteMemory.allocate state.heap base layout = some (pointer, heap)) :
    WellFormed ⟨heap, pointer :: state.registers, ⟨base, layout, state.heap.memory.nextGeneration⟩ :: state.history⟩ := by
  obtain ⟨allocatedMemory, shadowEq⟩ := NativePointerByteMemory.allocate_success state.heap heap base layout pointer allocated
  obtain ⟨pointerEq, memoryEq, _, _⟩ := NativeByteMemory.allocate_success state.heap.memory base layout pointer heap.memory allocatedMemory
  have generation : heap.memory.nextGeneration = state.heap.memory.nextGeneration + 1 := by rw [memoryEq]
  have pointerOrigin : pointer.provenance = some (⟨base.val, state.heap.memory.nextGeneration⟩ : Origin) := by rw [pointerEq]; rfl
  have oldIssued : ∀ origin, Issued state origin →
      Issued ⟨heap, pointer :: state.registers, ⟨base, layout, state.heap.memory.nextGeneration⟩ :: state.history⟩ origin := by
    rintro origin ⟨event, member, same⟩
    exact ⟨event, List.mem_cons_of_mem _ member, same⟩
  refine ⟨NativePointerByteMemory.allocate_wellFormed state.heap heap valid.1 base layout pointer allocated, ⟨?_, ?_⟩, ?_⟩
  · intro value member origin hasOrigin
    rcases List.mem_cons.mp member with same | old
    · subst value
      have sameOrigin : origin = (⟨base.val, state.heap.memory.nextGeneration⟩ : Origin) := Option.some.inj (hasOrigin.symm.trans pointerOrigin)
      exact ⟨⟨base, layout, state.heap.memory.nextGeneration⟩, List.mem_cons_self, sameOrigin.symm⟩
    · exact oldIssued origin (valid.2.1.1 value old origin hasOrigin)
  · intro cell member
    rw [shadowEq] at member
    exact oldIssued cell.origin (valid.2.1.2 cell member)
  · intro event member
    rcases List.mem_cons.mp member with same | old
    · subst event; dsimp only; rw [generation]; omega
    · have before := valid.2.2 event old
      dsimp only
      rw [generation]
      omega

theorem load_wellFormed (state : State) (valid : WellFormed state) (slot value : Pointer)
    (loaded : NativePointerByteMemory.load state.heap slot = some value) : WellFormed (push state value) := by
  apply push_wellFormed state valid value
  intro origin hasOrigin
  obtain ⟨cell, member, _, _, same⟩ := NativePointerByteMemory.load_origin_recorded state.heap slot value origin loaded hasOrigin
  rw [← same]
  exact valid.2.1.2 cell member

def historyAfter (state : State) : Op → List Allocation
  | .allocate base layout => ⟨base, layout, state.heap.memory.nextGeneration⟩ :: state.history
  | _ => state.history

theorem execute_invariants (state next : State) (valid : WellFormed state) (op : Op)
    (executed : execute state op = some next) : WellFormed next ∧ next.history = historyAfter state op := by
  cases op with
  | allocate base layout =>
    simp only [execute, Option.map_eq_some_iff] at executed
    obtain ⟨⟨pointer, heap⟩, allocated, same⟩ := executed
    subst next
    exact ⟨allocate_wellFormed state valid base layout pointer heap allocated, rfl⟩
  | fromAddress address =>
    cases executed
    refine ⟨push_wellFormed state valid ⟨address, none⟩ ?_, rfl⟩
    intro origin hasOrigin
    cases hasOrigin
  | withAddress index address =>
    simp only [execute, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, selected, same⟩ := executed
    subst next
    refine ⟨push_wellFormed state valid ⟨address, pointer.provenance⟩ ?_, rfl⟩
    intro origin hasOrigin
    exact register_authentic state valid.2.1 index pointer selected origin hasOrigin
  | load slot =>
    simp only [execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, _, value, loaded, same⟩ := executed
    subst next
    exact ⟨load_wellFormed state valid pointer value loaded, rfl⟩
  | store slot value =>
    simp only [execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, _, data, selected, heap, stored, same⟩ := executed
    subst next
    refine ⟨store_wellFormed state valid heap pointer data ?_ stored, rfl⟩
    exact register_authentic state valid.2.1 value data selected
  | writeBytes slot alignment bytes =>
    simp only [execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, _, heap, written, same⟩ := executed
    subst next
    exact ⟨write_wellFormed state valid heap pointer alignment bytes written, rfl⟩
  | copy source target size alignment =>
    simp only [execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨sourcePointer, _, targetPointer, _, heap, copied, same⟩ := executed
    subst next
    exact ⟨copy_wellFormed state valid heap sourcePointer targetPointer size alignment copied, rfl⟩
  | copyNonoverlapping source target size alignment =>
    simp only [execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨sourcePointer, _, targetPointer, _, heap, copied, same⟩ := executed
    subst next
    have copied := (NativePointerByteMemory.nonoverlapping_success state.heap heap sourcePointer targetPointer size alignment copied).2
    exact ⟨copy_wellFormed state valid heap sourcePointer targetPointer size alignment copied, rfl⟩
  | free register layout =>
    simp only [execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, _, heap, freed, same⟩ := executed
    subst next
    exact ⟨free_wellFormed state valid heap pointer layout freed, rfl⟩

theorem execute_wellFormed (state next : State) (valid : WellFormed state) (op : Op)
    (executed : execute state op = some next) : WellFormed next := (execute_invariants state next valid op executed).1

theorem reachable_wellFormed (state : State) (reachable : Reachable state) : WellFormed state := by
  induction reachable with
  | empty => exact empty_wellFormed
  | step before op executed ih => exact execute_wellFormed _ _ ih op executed

theorem run_wellFormed (state next : State) (valid : WellFormed state) (ops : List Op)
    (ran : run state ops = some next) : WellFormed next := by
  induction ops generalizing state with
  | nil => cases ran; exact valid
  | cons op tail ih =>
    simp only [run, Option.bind_eq_some_iff] at ran
    obtain ⟨middle, executed, later⟩ := ran
    exact ih middle (execute_wellFormed state middle valid op executed) later

theorem run_reachable (state next : State) (reachable : Reachable state) (ops : List Op)
    (ran : run state ops = some next) : Reachable next := by
  induction ops generalizing state with
  | nil => cases ran; exact reachable
  | cons op tail ih =>
    simp only [run, Option.bind_eq_some_iff] at ran
    obtain ⟨middle, executed, later⟩ := ran
    exact ih middle (Reachable.step reachable op executed) later

theorem issued_generation (state : State) (valid : WellFormed state) (origin : Origin) (issued : Issued state origin) :
    origin.generation < state.heap.memory.nextGeneration := by
  obtain ⟨event, member, same⟩ := issued
  rw [← same]
  exact valid.2.2 event member

theorem fresh_not_issued (state : State) (valid : WellFormed state) (base : Address) :
    ¬ Issued state ⟨base.val, state.heap.memory.nextGeneration⟩ := by
  intro issued
  have impossible := issued_generation state valid ⟨base.val, state.heap.memory.nextGeneration⟩ issued
  exact Nat.lt_irrefl _ impossible

theorem reachable_register_origin (state : State) (reachable : Reachable state) (index : Nat) (pointer : Pointer)
    (selected : state.registers[index]? = some pointer) (origin : Origin) (hasOrigin : pointer.provenance = some origin) :
    Issued state origin ∧ origin.generation < state.heap.memory.nextGeneration := by
  have valid := reachable_wellFormed state reachable
  have issued := register_authentic state valid.2.1 index pointer selected origin hasOrigin
  exact ⟨issued, issued_generation state valid origin issued⟩

theorem reachable_stored_origin (state : State) (reachable : Reachable state) (cell : NativePointerShadow.Cell)
    (member : cell ∈ state.heap.shadow) : Issued state cell.origin ∧ cell.origin.generation < state.heap.memory.nextGeneration := by
  have valid := reachable_wellFormed state reachable
  have issued := valid.2.1.2 cell member
  exact ⟨issued, issued_generation state valid cell.origin issued⟩

theorem unissued_register_impossible (state : State) (reachable : Reachable state) (index : Nat) (pointer : Pointer)
    (selected : state.registers[index]? = some pointer) (origin : Origin) (unissued : ¬ Issued state origin) :
    pointer.provenance ≠ some origin := by
  intro hasOrigin
  exact unissued (reachable_register_origin state reachable index pointer selected origin hasOrigin).1

theorem runs_wellFormed (start state : State) (valid : WellFormed start) (runs : Runs start state) : WellFormed state := by
  induction runs with
  | refl => exact valid
  | step before op executed ih => exact execute_wellFormed _ _ ih op executed

theorem runs_reachable (start state : State) (reachable : Reachable start) (runs : Runs start state) : Reachable state := by
  induction runs with
  | refl => exact reachable
  | step before op executed ih => exact Reachable.step ih op executed

theorem reachable_event_allocation (state : State) (reachable : Reachable state) (event : Allocation) (member : event ∈ state.history) :
    ∃ before after, Reachable before ∧ execute before (.allocate event.base event.layout) = some after ∧
      before.heap.memory.nextGeneration = event.generation ∧ Runs after state := by
  induction reachable with
  | empty => cases member
  | @step before after beforeReach op executed ih =>
    have oldEvent : event ∈ before.history → ∃ earlier later, Reachable earlier ∧
        execute earlier (.allocate event.base event.layout) = some later ∧
        earlier.heap.memory.nextGeneration = event.generation ∧ Runs later after := by
      intro old
      obtain ⟨earlier, later, earlierReach, allocated, generation, suffix⟩ := ih old
      exact ⟨earlier, later, earlierReach, allocated, generation, Runs.step suffix op executed⟩
    rw [(execute_invariants before after (reachable_wellFormed before beforeReach) op executed).2] at member
    cases op with
    | allocate base layout =>
      rcases List.mem_cons.mp member with same | old
      · subst event
        exact ⟨before, after, beforeReach, executed, rfl, Runs.refl after⟩
      · exact oldEvent old
    | fromAddress address => exact oldEvent member
    | withAddress register address => exact oldEvent member
    | load slot => exact oldEvent member
    | store slot value => exact oldEvent member
    | writeBytes slot alignment bytes => exact oldEvent member
    | copy source target size alignment => exact oldEvent member
    | copyNonoverlapping source target size alignment => exact oldEvent member
    | free register layout => exact oldEvent member

theorem reachable_origin_allocation (state : State) (reachable : Reachable state) (origin : Origin) (issued : Issued state origin) :
    ∃ event ∈ state.history, event.origin = origin ∧ ∃ before after, Reachable before ∧
      execute before (.allocate event.base event.layout) = some after ∧ before.heap.memory.nextGeneration = event.generation ∧ Runs after state := by
  obtain ⟨event, member, same⟩ := issued
  exact ⟨event, member, same, reachable_event_allocation state reachable event member⟩

theorem reachable_origin_allocator_result (state : State) (reachable : Reachable state) (origin : Origin)
    (issued : Issued state origin) : ∃ before after base layout pointer memory, Reachable before ∧
      execute before (.allocate base layout) = some after ∧ Runs after state ∧
      NativeByteMemory.allocate before.heap.memory base layout = some (pointer, memory) ∧ pointer.provenance = some origin := by
  obtain ⟨event, _, sameOrigin, before, after, beforeReach, executed, generation, suffix⟩ :=
    reachable_origin_allocation state reachable origin issued
  have actual := executed
  simp only [execute, Option.map_eq_some_iff] at executed
  obtain ⟨⟨pointer, heap⟩, allocated, _⟩ := executed
  have allocatedMemory := (NativePointerByteMemory.allocate_success before.heap heap event.base event.layout pointer allocated).1
  have pointerEq := (NativeByteMemory.allocate_success before.heap.memory event.base event.layout pointer heap.memory allocatedMemory).1
  refine ⟨before, after, event.base, event.layout, pointer, heap.memory, beforeReach, actual, suffix, allocatedMemory, ?_⟩
  rw [pointerEq]
  change some (⟨event.base.val, before.heap.memory.nextGeneration⟩ : Origin) = some origin
  rw [generation]
  exact congrArg some sameOrigin

theorem reachable_register_allocator_result (state : State) (reachable : Reachable state) (index : Nat) (value : Pointer)
    (selected : state.registers[index]? = some value) (origin : Origin) (hasOrigin : value.provenance = some origin) :
    ∃ before after base layout pointer memory, Reachable before ∧
      execute before (.allocate base layout) = some after ∧ Runs after state ∧
      NativeByteMemory.allocate before.heap.memory base layout = some (pointer, memory) ∧ pointer.provenance = some origin := by
  exact reachable_origin_allocator_result state reachable origin
    (reachable_register_origin state reachable index value selected origin hasOrigin).1

theorem reachable_stored_allocator_result (state : State) (reachable : Reachable state) (cell : NativePointerShadow.Cell)
    (member : cell ∈ state.heap.shadow) : ∃ before after base layout pointer memory, Reachable before ∧
      execute before (.allocate base layout) = some after ∧ Runs after state ∧
      NativeByteMemory.allocate before.heap.memory base layout = some (pointer, memory) ∧ pointer.provenance = some cell.origin := by
  exact reachable_origin_allocator_result state reachable cell.origin (reachable_stored_origin state reachable cell member).1

theorem reachable_unique_generations (state : State) (reachable : Reachable state) :
    state.history.Pairwise (fun left right => left.generation ≠ right.generation) := by
  induction reachable with
  | empty => exact List.Pairwise.nil
  | @step before after beforeReach op executed ih =>
    have historyEq := (execute_invariants before after (reachable_wellFormed before beforeReach) op executed).2
    rw [historyEq]
    cases op with
    | allocate base layout =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih⟩
      intro event member
      have bound := (reachable_wellFormed before beforeReach).2.2 event member
      dsimp only
      omega
    | fromAddress address => exact ih
    | withAddress register address => exact ih
    | load slot => exact ih
    | store slot value => exact ih
    | writeBytes slot alignment bytes => exact ih
    | copy source target size alignment => exact ih
    | copyNonoverlapping source target size alignment => exact ih
    | free register layout => exact ih

theorem run_register_allocator_result (ops : List Op) (state : State) (ran : run empty ops = some state)
    (index : Nat) (value : Pointer) (selected : state.registers[index]? = some value)
    (origin : Origin) (hasOrigin : value.provenance = some origin) :
    ∃ before after base layout pointer memory, Reachable before ∧
      execute before (.allocate base layout) = some after ∧ Runs after state ∧
      NativeByteMemory.allocate before.heap.memory base layout = some (pointer, memory) ∧ pointer.provenance = some origin := by
  exact reachable_register_allocator_result state (run_reachable empty state Reachable.empty ops ran) index value selected origin hasOrigin

theorem run_stored_allocator_result (ops : List Op) (state : State) (ran : run empty ops = some state)
    (cell : NativePointerShadow.Cell) (member : cell ∈ state.heap.shadow) :
    ∃ before after base layout pointer memory, Reachable before ∧
      execute before (.allocate base layout) = some after ∧ Runs after state ∧
      NativeByteMemory.allocate before.heap.memory base layout = some (pointer, memory) ∧ pointer.provenance = some cell.origin := by
  exact reachable_stored_allocator_result state (run_reachable empty state Reachable.empty ops ran) cell member

end FormalProof4FHE.HasteBoots.NativePointerMachine
