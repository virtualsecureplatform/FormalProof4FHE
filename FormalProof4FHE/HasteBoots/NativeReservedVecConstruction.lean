module
public import FormalProof4FHE.HasteBoots.NativeReservedVecStorage
@[expose] public section

/-! Fresh modeled byte allocation followed by provenance-preserving reservation
storage. The original Rust with_capacity body and external allocator ABI are
separate obligations; this is not their implementation correspondence. -/
namespace FormalProof4FHE.HasteBoots.NativeReservedVecConstruction
open NativeReferenceMachine (State)
open NativePointerStorage (Pointer Address)
open NativeWord64Memory (Word)

def buffer (world : State) (base : Address) : Pointer :=
  ⟨base,some ⟨base.val,world.pointers.heap.memory.nextGeneration⟩⟩

def reserve (world : State) (headerRegister : Nat) (base : Address) (capacity : Word) : Option State := do
  let allocated ← NativeReferenceMachine.execute world (.raw (.allocate base ⟨capacity.val,1⟩))
  NativeReservedVecStorage.install allocated (headerRegister + 1) 0 capacity

/-- Allocation success, complete buffer ownership and all resident destruction
conditions follow from explicit allocator geometry and physical separation. -/
theorem reserve_complete (world : State) (headerRegister : Nat) (header : Pointer) (base : Address) (capacity : Word)
    (reachable : NativeReferenceMachine.Reachable world)
    (headerResident : world.pointers.registers[headerRegister]? = some header)
    (checked : NativeByteRange.checkRange world.pointers.heap.memory header ⟨24,8⟩ = true)
    (headerAvailable : NativeVecBytePrefix.Available world header 24)
    (positive : 0 < capacity.val) (capacityBound : capacity.val < 2^63)
    (nonnull : base.val ≠ 0) (addressBound : base.val + capacity.val ≤ 2^64)
    (space : ∀ block ∈ world.pointers.heap.memory.blocks,
      NativeByteMemory.Disjoint (NativeByteMemory.freshBlock world.pointers.heap.memory base ⟨capacity.val,1⟩) block)
    (bufferAvailable : NativeVecBytePrefix.Available world (buffer world base) capacity.val)
    (headerSeparate : ¬ NativeByteBorrow.Overlap (buffer world base) ⟨capacity.val,1⟩ header ⟨24,8⟩) :
    ∃ next, ∃ ready : NativeReservedVecStorage.Ready next capacity (buffer world base) header,
      reserve world headerRegister base capacity = some next ∧ NativeReferenceMachine.Reachable next ∧
      NativeResidentVec.OwnsBuffer ready.descriptor ∧
      NativeVecBytePrefix.Available next ready.descriptor.buffer ready.descriptor.capacity.val ∧
      next.leases = ready.descriptor.lease :: world.leases ∧
      next.references = ⟨world.nextTag⟩ :: world.references ∧ ready.descriptor.reference = ⟨world.nextTag⟩ := by
  let fresh := NativeByteMemory.freshBlock world.pointers.heap.memory base ⟨capacity.val,1⟩
  have layoutValid : (NativeByteMemory.Layout.mk capacity.val 1).Valid := by
    refine ⟨by change 1 ∈ (List.range 64).map (fun exponent => 2 ^ exponent); decide,?_⟩
    change capacity.val + (1-1) ≤ 2^63-1
    omega
  have separate := List.all_eq_true.mpr (fun block member => decide_eq_true (space block member))
  let allocated : State := {world with pointers :=
    ⟨⟨⟨world.pointers.heap.memory.nextGeneration + 1,fresh :: world.pointers.heap.memory.blocks⟩,world.pointers.heap.shadow⟩,
      buffer world base :: world.pointers.registers,
      ⟨base,⟨capacity.val,1⟩,world.pointers.heap.memory.nextGeneration⟩ :: world.pointers.history⟩}
  have allocator : NativeByteMemory.allocate world.pointers.heap.memory base ⟨capacity.val,1⟩ =
      some (fresh.pointer,⟨world.pointers.heap.memory.nextGeneration + 1,fresh :: world.pointers.heap.memory.blocks⟩) := by
    unfold NativeByteMemory.allocate
    dsimp only
    split
    · rfl
    · rename_i rejected
      exact False.elim (rejected ⟨layoutValid,positive,nonnull,Nat.mod_one _,addressBound,separate⟩)
  have allocatedStep : NativeReferenceMachine.execute world (.raw (.allocate base ⟨capacity.val,1⟩)) = some allocated := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,ite_true,NativePointerMachine.execute,
      NativePointerByteMemory.allocate,allocator,Option.map_some,NativeReferenceMachine.setPointers,allocated,fresh,buffer]
    rfl
  have allocatedReachable := NativeReferenceMachine.Reachable.step reachable _ allocatedStep
  have checkedParts : decide (NativeByteRange.Geometry header ⟨24,8⟩) = true ∧
      world.pointers.heap.memory.blocks.any (fun block => decide (NativeByteRange.Covers block header 24)) = true := by
    simpa only [NativeByteRange.checkRange,Bool.and_eq_true,show (24 : Nat) ≠ 0 by decide,ite_false] using checked
  have checkedAfter : NativeByteRange.checkRange allocated.pointers.heap.memory header ⟨24,8⟩ = true := by
    change decide (NativeByteRange.Geometry header ⟨24,8⟩) &&
      (decide (NativeByteRange.Covers fresh header 24) || world.pointers.heap.memory.blocks.any
        (fun block => decide (NativeByteRange.Covers block header 24))) = true
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
    exact ⟨of_decide_eq_true checkedParts.1,Or.inr checkedParts.2⟩
  obtain ⟨next,ready,installed,reached,_,loans,references,reference,shapes⟩ :=
    NativeReservedVecStorage.install_complete allocated (headerRegister + 1) 0 capacity (buffer world base) header allocatedReachable
      (by simpa only [allocated,List.getElem?_cons_succ] using headerResident) rfl checkedAfter headerAvailable capacityBound nonnull
  have owned : NativeResidentVec.OwnsBuffer ready.descriptor := by
    apply ready.owned allocated.pointers.heap.memory positive shapes
    exact ⟨fresh,List.mem_cons_self,rfl,rfl⟩
  have available := ready.available allocated loans bufferAvailable headerSeparate
  refine ⟨next,ready,?_,reached,owned,available,loans,references,reference⟩
  simp only [reserve,allocatedStep,Option.bind_eq_bind',Option.bind,installed]

end FormalProof4FHE.HasteBoots.NativeReservedVecConstruction
