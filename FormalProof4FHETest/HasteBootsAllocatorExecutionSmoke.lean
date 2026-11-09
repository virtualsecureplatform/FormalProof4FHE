module
import FormalProof4FHE.HasteBoots.NativeAllocatorLLBC
namespace FormalProof4FHETest.HasteBootsAllocatorExecutionSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordValues (Ty Value)

private def alignmentType : Ty := .record 11 (.pair (.enumeration 12 [1]) (.scalar .unit))
private def alignmentValue : Value := .record 11 (.pair (.enumeration 12 1) (.scalar .unit))
private def foreignFunction (symbol : NativeAllocatorExecution.Symbol) (outcome : Option NativePointerStorage.Address) : NativeAllocatorLLBC.Function :=
  ⟨symbol.name,.externalBody,[.scalar (.raw false),.scalar .usize,alignmentType],2,
    .legacy (.live 0 .done) (.allocate symbol outcome 11 12 0 [.copy 1 [],.move 2 []] (.legacy .ret .done))⟩

example (world : NativeReferenceMachine.State) (symbol : NativeAllocatorExecution.Symbol) :
    NativeAllocatorExecution.run world symbol none 3 1 = .value NativeAllocatorExecution.nullValue world :=
  NativeAllocatorExecution.failure_result world symbol 3 1 (by decide) (by decide)

example (world : NativeReferenceMachine.State) (outcome : Option NativePointerStorage.Address) :
    NativeAllocatorExecution.run world .allocate outcome 0 1 = .invalid world :=
  NativeAllocatorExecution.zero_size_rejected world .allocate outcome 1

example : NativeAllocatorExecution.run NativeReferenceMachine.empty .allocate (some 8) 3 3 = .invalid NativeReferenceMachine.empty := by decide

example : NativeAllocatorExecution.run NativeReferenceMachine.empty .allocate (some 8) 3 1 =
    .value (.raw ⟨⟨8,some ⟨8,0⟩⟩,none⟩) (NativeAllocatorExecution.allocated NativeReferenceMachine.empty 8 ⟨3,1⟩) := by decide

example :
    (match NativeAllocatorExecution.run NativeReferenceMachine.empty .allocate (some 8) 3 1 with
    | .value (.raw pointer) world => NativeByteRange.loadRange world.pointers.heap.memory pointer.storage ⟨3,1⟩
    | _ => none) = none := by decide

example :
    (match NativeAllocatorExecution.run NativeReferenceMachine.empty .zeroed (some 8) 3 1 with
    | .value (.raw pointer) world => NativeByteRange.loadRange world.pointers.heap.memory pointer.storage ⟨3,1⟩
    | _ => none) = some [0,0,0] := by decide

example : NativeAllocatorExecution.run NativeReferenceMachine.empty .allocate (some 0) 3 1 = .invalid NativeReferenceMachine.empty := by decide

example : NativeAllocatorLLBC.invokeValues (foreignFunction .allocate none) NativeReferenceMachine.empty
    [.scalar (.usize 3),alignmentValue] = .returned (.scalar (.raw ⟨⟨0,none⟩,none⟩)) NativeReferenceMachine.empty := by decide

example : NativeAllocatorLLBC.invokeValues (foreignFunction .allocate (some 8)) NativeReferenceMachine.empty
    [.scalar (.usize 3),alignmentValue] = .returned (.scalar (.raw ⟨⟨8,some ⟨8,0⟩⟩,none⟩))
      (NativeAllocatorExecution.allocated NativeReferenceMachine.empty 8 ⟨3,1⟩) := by decide

example :
    (match NativeAllocatorLLBC.invokeValues (foreignFunction .zeroed (some 8)) NativeReferenceMachine.empty
        [.scalar (.usize 3),alignmentValue] with
    | .returned (.scalar (.raw pointer)) world => NativeByteRange.loadRange world.pointers.heap.memory pointer.storage ⟨3,1⟩
    | _ => none) = some [0,0,0] := by decide

example : NativeAllocatorLLBC.invokeValues (foreignFunction .allocate (some 8)) NativeReferenceMachine.empty
    [.boolean true,alignmentValue] = .invalid NativeReferenceMachine.empty := by decide

example (frame : NativeRecordLLBC.Frame) (body : NativeRecordLLBC.Body) :
    NativeAllocatorLLBC.eval (.legacy body .done) frame = NativeRecordLLBC.eval body frame := NativeAllocatorLLBC.legacy_done frame body

example :
    (let function : NativeAllocatorLLBC.Function :=
      ⟨"model.allocate_and_free",.transparent,[.scalar .unit,.scalar .usize,alignmentType,.scalar (.raw false)],2,
        .legacy (.live 3 .done) (.allocate .allocate (some 8) 11 12 3 [.copy 1 [],.copy 2 []]
          (.legacy (.deallocate (.copy 3 []) (.copy 1 []) (.copy 2 [(.unwrap 11),.left]) 12) .done))⟩
     match NativeAllocatorLLBC.invokeValues function NativeReferenceMachine.empty [.scalar (.usize 3),alignmentValue] with
     | .returned (.scalar .unit) world => (world.pointers.heap.memory.blocks.length,world.pointers.heap.memory.nextGeneration)
     | _ => (99,99)) = (0,1) := by decide

example (function : NativeAllocatorLLBC.Function) (world : NativeReferenceMachine.State) (args : List NativeRecordLLBC.Input)
    (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (NativeAllocatorLLBC.invoke function world args).world :=
  NativeAllocatorLLBC.invoke_reachable function world args reachable
end FormalProof4FHETest.HasteBootsAllocatorExecutionSmoke
