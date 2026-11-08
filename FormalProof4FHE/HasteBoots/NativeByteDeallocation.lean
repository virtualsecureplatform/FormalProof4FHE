module
public import FormalProof4FHE.HasteBoots.NativeSliceLLBC
@[expose] public section

/-! Checked deallocation from typed operands over the shared live heap.
This specifies a closed external boundary; native ABI correspondence is unproved. -/
namespace FormalProof4FHE.HasteBoots.NativeByteDeallocation
open NativeReferenceMachine (State)
open NativeSliceLLBC (Raw Value Frame Flow Operand)
open NativeWord64Memory (Word)

/-- Resolve an existing complete pointer, check the nonzero layout, and execute
an actual permission-checked free. Address bits cannot select an origin. -/
def execute (world : State) (pointer : Raw) (size alignment : Word) : Option State :=
  if (pointer.length = none ∧ pointer.storage.address.val ≠ 0) ∧ 0 < size.val ∧ (NativeByteMemory.Layout.mk size.val alignment.val).Valid then
    let register := world.pointers.registers.idxOf pointer.storage
    if world.pointers.registers[register]? = some pointer.storage then
      NativeReferenceMachine.execute world (.raw (.free register ⟨size.val, alignment.val⟩))
    else none
  else none

/-- The boundary returns unit only after the actual free succeeds. Invalid
operands and rejected frees preserve the machine prefix already reached. -/
def eval (frame : Frame) (args : List Operand) : Flow :=
  match NativeSliceLLBC.evalArgs frame args with
  | none => .invalid frame.world
  | some (values, caller) => match values with
    | [.raw pointer, .usize size, .usize alignment] => match execute caller.world pointer size alignment with
      | none => .invalid caller.world
      | some world => .returned .unit world
    | _ => .invalid caller.world

theorem execute_success (world next : State) (pointer : Raw) (size alignment : Word)
    (freed : execute world pointer size alignment = some next) :
    (pointer.length = none ∧ pointer.storage.address.val ≠ 0) ∧ 0 < size.val ∧ (NativeByteMemory.Layout.mk size.val alignment.val).Valid ∧
      world.pointers.registers[world.pointers.registers.idxOf pointer.storage]? = some pointer.storage ∧
      NativeReferenceMachine.execute world
        (.raw (.free (world.pointers.registers.idxOf pointer.storage) ⟨size.val, alignment.val⟩)) = some next := by
  unfold execute at freed
  split at freed
  next valid =>
    dsimp only at freed
    split at freed
    next selected => exact ⟨valid.1, valid.2.1, valid.2.2, selected, freed⟩
    next => cases freed
  next => cases freed

theorem execute_projects (world next : State) (pointer : Raw) (size alignment : Word)
    (freed : execute world pointer size alignment = some next) : NativeReferenceMachine.Runs world next :=
  .step (.refl world) _ (execute_success world next pointer size alignment freed).2.2.2.2

theorem execute_heap (world next : State) (pointer : Raw) (size alignment : Word)
    (freed : execute world pointer size alignment = some next) :
    ∃ heap, NativePointerByteMemory.deallocate world.pointers.heap pointer.storage ⟨size.val, alignment.val⟩ = some heap ∧
      next = {world with pointers := {world.pointers with heap}} := by
  obtain ⟨_, _, _, selected, actual⟩ := execute_success world next pointer size alignment freed
  simp only [NativeReferenceMachine.execute] at actual
  split at actual
  next =>
    simp only [NativePointerMachine.execute, selected, Option.bind_some, Option.map_eq_some_iff] at actual
    obtain ⟨pointers, ⟨heap, released, samePointers⟩, sameWorld⟩ := actual
    cases samePointers
    cases sameWorld
    exact ⟨heap, released, rfl⟩
  next => cases actual

theorem execute_frees_one (world next : State) (pointer : Raw) (size alignment : Word)
    (freed : execute world pointer size alignment = some next) :
    next.pointers.heap.memory.blocks.length + 1 = world.pointers.heap.memory.blocks.length := by
  obtain ⟨heap, released, rfl⟩ := execute_heap world next pointer size alignment freed
  obtain ⟨_, _, memory, _⟩ := NativePointerByteMemory.deallocate_success _ _ _ _ released
  exact NativeByteMemory.deallocate_changes_live_count _ _ _ _ memory

theorem execute_unreadable (world next : State) (pointer : Raw) (size alignment : Word)
    (valid : NativeByteMemory.WellFormed world.pointers.heap.memory)
    (freed : execute world pointer size alignment = some next) :
    NativeByteMemory.loadByte next.pointers.heap.memory pointer.storage = none := by
  obtain ⟨heap, released, rfl⟩ := execute_heap world next pointer size alignment freed
  obtain ⟨_, _, memory, _⟩ := NativePointerByteMemory.deallocate_success _ _ _ _ released
  exact NativeByteMemory.deallocated_pointer_unreadable _ valid _ _ _ memory

theorem execute_preserves_history (world next : State) (pointer : Raw) (size alignment : Word)
    (freed : execute world pointer size alignment = some next) :
    next.pointers.history = world.pointers.history ∧ next.pointers.registers = world.pointers.registers ∧
      next.nextTag = world.nextTag ∧ next.leases = world.leases ∧ next.references = world.references ∧
      next.births = world.births ∧ next.outputs = world.outputs ∧
      next.pointers.heap.memory.nextGeneration = world.pointers.heap.memory.nextGeneration := by
  obtain ⟨heap, released, rfl⟩ := execute_heap world next pointer size alignment freed
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, NativePointerMachine.free_generation _ _ _ _ released⟩

theorem execute_no_overlap (world next : State) (pointer : Raw) (size alignment : Word)
    (freed : execute world pointer size alignment = some next)
    (lease : NativeByteBorrow.Lease) (member : lease ∈ world.leases) :
    ¬ NativeByteBorrow.Overlap pointer.storage ⟨size.val, alignment.val⟩ lease.pointer lease.layout := by
  obtain ⟨_, _, _, selected, actual⟩ := execute_success world next pointer size alignment freed
  exact NativeReferenceMachine.raw_free_no_overlap _ _ _ _ _ selected actual lease member

theorem eval_projects (frame : Frame) (args : List Operand) :
    NativeReferenceMachine.Runs frame.world (eval frame args).world := by
  cases evaluated : NativeSliceLLBC.evalArgs frame args with
  | none => simp only [eval, evaluated]; exact .refl _
  | some result =>
    rcases result with ⟨values, caller⟩
    simp only [eval, evaluated]
    have same := NativeSliceLLBC.evalArgs_world frame caller args values evaluated
    rw [← same]
    split
    next pointer size alignment =>
      split
      next => exact .refl _
      next freed => exact execute_projects _ _ _ _ _ freed
    next => exact .refl _


theorem eval_return_success (frame : Frame) (args : List Operand) (value : Value) (next : State)
    (returned : eval frame args = .returned value next) :
    value = .unit ∧ ∃ pointer size alignment, execute frame.world pointer size alignment = some next := by
  cases evaluated : NativeSliceLLBC.evalArgs frame args with
  | none => simp only [eval, evaluated] at returned; cases returned
  | some result =>
    rcases result with ⟨values, caller⟩
    simp only [eval, evaluated] at returned
    have same := NativeSliceLLBC.evalArgs_world frame caller args values evaluated
    split at returned
    next pointer size alignment =>
      cases freed : execute caller.world pointer size alignment with
      | none => simp only [freed] at returned; cases returned
      | some world =>
        simp only [freed] at returned
        cases returned
        rw [same] at freed
        exact ⟨rfl, pointer, size, alignment, freed⟩
    next => cases returned

theorem eval_return_frees_one (frame : Frame) (args : List Operand) (value : Value) (next : State)
    (returned : eval frame args = .returned value next) :
    next.pointers.heap.memory.blocks.length + 1 = frame.world.pointers.heap.memory.blocks.length := by
  obtain ⟨_, pointer, size, alignment, freed⟩ := eval_return_success frame args value next returned
  exact execute_frees_one frame.world next pointer size alignment freed

end FormalProof4FHE.HasteBoots.NativeByteDeallocation
