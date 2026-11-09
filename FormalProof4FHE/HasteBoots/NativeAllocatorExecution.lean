module
public import FormalProof4FHE.HasteBoots.NativeRawVecFields
@[expose] public section

/-! Executable allocation outcomes over the shared heap machine. These are
checked model operations, not native allocator ABI or physical-work refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeAllocatorExecution
open NativeReferenceMachine (State)
open NativeRawVecFields (Result)
open NativeWord64Memory (Word)
open NativePointerStorage (Pointer Address)

inductive Symbol where
  | allocate
  | zeroed
  deriving DecidableEq

def Symbol.name : Symbol → String
  | .allocate => "alloc::alloc::__rust_alloc"
  | .zeroed => "alloc::alloc::__rust_alloc_zeroed"

def request (size alignment : Word) : NativeByteMemory.Layout := ⟨size.val,alignment.val⟩

def nullValue : NativeSliceLLBC.Value := .raw ⟨⟨0,none⟩,none⟩

def run (world : State) (symbol : Symbol) (outcome : Option Address) (size alignment : Word) : Result NativeSliceLLBC.Value :=
  if (request size alignment).Valid ∧ 0 < size.val then
    match outcome with
    | none => .value nullValue world
    | some base => match NativeReferenceMachine.execute world (.raw (.allocate base (request size alignment))) with
      | none => .invalid world
      | some allocated => match allocated.pointers.registers[0]? with
        | none => .invalid allocated
        | some pointer => match symbol with
          | .allocate => .value (.raw ⟨pointer,none⟩) allocated
          | .zeroed => match NativeReferenceMachine.execute allocated
              (.raw (.writeBytes 0 alignment.val (List.replicate size.val 0))) with
            | none => .invalid allocated
            | some initialized => .value (.raw ⟨pointer,none⟩) initialized
  else .invalid world

def allocated (world : State) (base : Address) (layout : NativeByteMemory.Layout) : State :=
  let block := NativeByteMemory.freshBlock world.pointers.heap.memory base layout
  {world with pointers := ⟨⟨⟨world.pointers.heap.memory.nextGeneration+1,block :: world.pointers.heap.memory.blocks⟩,
    world.pointers.heap.shadow⟩,block.pointer :: world.pointers.registers,
    ⟨base,layout,world.pointers.heap.memory.nextGeneration⟩ :: world.pointers.history⟩}

theorem allocation_step (world : State) (base : Address) (layout : NativeByteMemory.Layout)
    (valid : layout.Valid) (positive : 0 < layout.size) (nonzero : base.val ≠ 0)
    (aligned : base.val % layout.alignment = 0) (bounded : base.val + layout.size ≤ 2^64)
    (separated : ∀ old ∈ world.pointers.heap.memory.blocks,
      NativeByteMemory.Disjoint (NativeByteMemory.freshBlock world.pointers.heap.memory base layout) old) :
    NativeReferenceMachine.execute world (.raw (.allocate base layout)) = some (allocated world base layout) := by
  have memory := NativeByteMemory.allocate_of_available world.pointers.heap.memory base layout valid positive nonzero aligned bounded separated
  simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,ite_true,
    NativePointerMachine.execute,NativePointerByteMemory.allocate,memory,Option.map_some,
    NativeReferenceMachine.setPointers,allocated]

theorem failure_result (world : State) (symbol : Symbol) (size alignment : Word)
    (valid : (request size alignment).Valid) (positive : 0 < size.val) :
    run world symbol none size alignment = .value nullValue world := by
  rw [run,ite_eq_left ⟨valid,positive⟩]

theorem zero_size_rejected (world : State) (symbol : Symbol) (outcome : Option Address) (alignment : Word) :
    run world symbol outcome 0 alignment = .invalid world := by
  simp [run]

theorem uninitialized_result (world : State) (base : Address) (size alignment : Word)
    (valid : (request size alignment).Valid) (positive : 0 < size.val)
    (nonzero : base.val ≠ 0) (aligned : base.val % alignment.val = 0)
    (bounded : base.val + size.val ≤ 2^64)
    (separated : ∀ old ∈ world.pointers.heap.memory.blocks,
      NativeByteMemory.Disjoint (NativeByteMemory.freshBlock world.pointers.heap.memory base (request size alignment)) old) :
    run world .allocate (some base) size alignment =
      .value (.raw ⟨(NativeByteMemory.freshBlock world.pointers.heap.memory base (request size alignment)).pointer,none⟩)
        (allocated world base (request size alignment)) := by
  have step := allocation_step world base (request size alignment) valid positive nonzero aligned bounded separated
  simp only [run,ite_eq_left (show (request size alignment).Valid ∧ 0 < size.val from ⟨valid,positive⟩),step,allocated,List.getElem?_cons_zero]

theorem initialized_result (world allocatedWorld initialized : State) (base : Address) (size alignment : Word)
    (pointer : Pointer) (valid : (request size alignment).Valid) (positive : 0 < size.val)
    (step : NativeReferenceMachine.execute world (.raw (.allocate base (request size alignment))) = some allocatedWorld)
    (registered : allocatedWorld.pointers.registers[0]? = some pointer)
    (written : NativeReferenceMachine.execute allocatedWorld
      (.raw (.writeBytes 0 alignment.val (List.replicate size.val 0))) = some initialized) :
    run world .zeroed (some base) size alignment = .value (.raw ⟨pointer,none⟩) initialized := by
  simp only [run,ite_eq_left (show (request size alignment).Valid ∧ 0 < size.val from ⟨valid,positive⟩),step,registered,written]

theorem run_projects (world : State) (symbol : Symbol) (outcome : Option Address) (size alignment : Word) :
    NativeReferenceMachine.Runs world (run world symbol outcome size alignment).world := by
  by_cases accepted : (request size alignment).Valid ∧ 0 < size.val
  · cases outcome with
    | none => simp only [run,ite_eq_left accepted,Result.world]; exact .refl _
    | some base =>
      cases step : NativeReferenceMachine.execute world (.raw (.allocate base (request size alignment))) with
      | none => simp only [run,ite_eq_left accepted,step,Result.world]; exact .refl _
      | some next =>
        have first := NativeReferenceMachine.Runs.step (.refl world) _ step
        cases registered : next.pointers.registers[0]? with
        | none => simpa only [run,ite_eq_left accepted,step,registered,Result.world] using first
        | some pointer =>
          cases symbol with
          | allocate => simpa only [run,ite_eq_left accepted,step,registered,Result.world] using first
          | zeroed =>
            cases written : NativeReferenceMachine.execute next (.raw (.writeBytes 0 alignment.val (List.replicate size.val 0))) with
            | none => simpa only [run,ite_eq_left accepted,step,registered,written,Result.world] using first
            | some initialized =>
              have later := NativeReferenceMachine.Runs.step first _ written
              simpa only [run,ite_eq_left accepted,step,registered,written,Result.world] using later
  · simp only [run,ite_eq_right accepted,Result.world]; exact .refl _

theorem allocated_origin (world : State) (base : Address) (layout : NativeByteMemory.Layout) :
    ((allocated world base layout).pointers.registers[0]?).map Pointer.provenance =
      some (some ⟨base.val,world.pointers.heap.memory.nextGeneration⟩) := rfl

theorem allocated_uninitialized (world : State) (base : Address) (layout : NativeByteMemory.Layout) :
    ((allocated world base layout).pointers.heap.memory.blocks[0]?).map NativeByteMemory.Block.bytes =
      some (List.replicate layout.size none) := rfl

theorem zero_write_loaded (world initialized : State) (pointer : Pointer) (size alignment : Word)
    (registered : world.pointers.registers[0]? = some pointer)
    (written : NativeReferenceMachine.execute world
      (.raw (.writeBytes 0 alignment.val (List.replicate size.val 0))) = some initialized) :
    NativeByteRange.loadRange initialized.pointers.heap.memory pointer (request size alignment) =
      some (List.replicate size.val 0) := by
  simp only [NativeReferenceMachine.execute] at written
  split at written
  · obtain ⟨pointers,actual,same⟩ := Option.map_eq_some_iff.mp written
    cases same
    simp only [NativePointerMachine.execute,registered,Option.bind_some,Option.map_eq_some_iff] at actual
    obtain ⟨heap,stored,same⟩ := actual
    cases same
    have storedRange := (NativePointerByteMemory.writeBytes_success _ _ _ _ _ stored).1
    have loaded := NativeByteRangeWrite.storeRange_then_load _ _ _ _ _ storedRange
    simpa only [NativeReferenceMachine.setPointers,NativePointerMachine.setHeap,List.length_replicate,request] using loaded
  · cases written

theorem run_reachable (world : State) (symbol : Symbol) (outcome : Option Address) (size alignment : Word)
    (before : NativeReferenceMachine.Reachable world) : NativeReferenceMachine.Reachable (run world symbol outcome size alignment).world := by
  exact NativeSliceLLBC.reference_runs_reachable _ _ before (run_projects world symbol outcome size alignment)

theorem zero_write_complete (world : State) (pointer : Pointer) (size alignment : Word)
    (registered : world.pointers.registers[0]? = some pointer)
    (valid : NativeByteMemory.WellFormed world.pointers.heap.memory)
    (checked : NativeByteRange.checkRange world.pointers.heap.memory pointer (request size alignment) = true)
    (allowed : NativeReferenceMachine.rawPermission world 0 .exclusive (request size alignment) = true) :
    ∃ initialized, NativeReferenceMachine.execute world
      (.raw (.writeBytes 0 alignment.val (List.replicate size.val 0))) = some initialized ∧
      NativeByteRange.loadRange initialized.pointers.heap.memory pointer (request size alignment) = some (List.replicate size.val 0) := by
  have ranged : NativeByteRange.checkRange world.pointers.heap.memory pointer
      ⟨(List.replicate size.val (0 : NativeByteMemory.Byte)).length,alignment.val⟩ = true := by
    simpa only [List.length_replicate,request] using checked
  obtain ⟨memory,stored⟩ := NativeByteRangeWrite.storeRange_of_checked world.pointers.heap.memory valid pointer alignment.val
    (List.replicate size.val 0) ranged
  let heap : NativePointerByteMemory.State := ⟨memory,match pointer.provenance with
    | none => world.pointers.heap.shadow
    | some owner => NativePointerShadow.clear world.pointers.heap.shadow owner pointer.address.val size.val⟩
  have heapWrite : NativePointerByteMemory.writeBytes world.pointers.heap pointer alignment.val (List.replicate size.val 0) = some heap := by
    simp only [NativePointerByteMemory.writeBytes,stored,List.length_replicate]
    rfl
  let initialized : State := {world with pointers := NativePointerMachine.setHeap world.pointers heap}
  have permission : NativeReferenceMachine.rawPermission world 0 .exclusive ⟨size.val,alignment.val⟩ = true := allowed
  have executed : NativeReferenceMachine.execute world
      (.raw (.writeBytes 0 alignment.val (List.replicate size.val 0))) = some initialized := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,List.length_replicate,permission,
      ite_true,NativePointerMachine.execute,registered,Option.bind_some,heapWrite,Option.map_some,
      NativeReferenceMachine.setPointers,initialized]
  exact ⟨initialized,executed,zero_write_loaded world initialized pointer size alignment registered executed⟩

end FormalProof4FHE.HasteBoots.NativeAllocatorExecution
