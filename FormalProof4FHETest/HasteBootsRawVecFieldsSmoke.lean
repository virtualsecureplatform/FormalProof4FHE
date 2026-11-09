module
import FormalProof4FHE.HasteBoots.NativeRawVecFields

namespace FormalProof4FHETest.HasteBootsRawVecFieldsSmoke
open FormalProof4FHE.HasteBoots
open NativeRawVecFields

private def ready (value : NativeWord64Memory.Word) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,8⟩), .raw (.allocate 128 ⟨16,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode value)),
     .raw (.withAddress 0 136), .raw (.store 0 2), .borrow 1 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty

example : (ready 8).nextTag = 1 := by decide
example : select (ready 8) 0 = some ⟨0⟩ := by decide
example : select (ready 8) 1 = none := by decide
example : (match capacity (ready 8) 0 with
    | .value value next => (value.val,next.outputs.length,next.pointers.registers.length,
      next.pointers.heap == (ready 8).pointers.heap)
    | _ => (99,99,99,false)) = (8,1,4,true) := by decide
example : (match capacity (ready 0) 0 with | .value value _ => value.val | _ => 99) = 0 := by decide
example : (match capacity (ready ⟨2^63-1,by decide⟩) 0 with
    | .value value _ => value.val | _ => 99) = 2^63-1 := by decide
example : (match capacity (ready ⟨2^63,by decide⟩) 0 with
    | .invalid next => (next.outputs.length,next.pointers.registers.length,
      next.pointers.heap == (ready ⟨2^63,by decide⟩).pointers.heap)
    | _ => (99,99,false)) = (1,4,true) := by decide
example : (match pointer (ready 8) 0 with
    | .value value next => (value,next.pointers.registers.length,next.outputs.length,
      next.pointers.heap == (ready 8).pointers.heap)
    | _ => (⟨0,none⟩,99,99,false)) = (⟨64,some ⟨64,0⟩⟩,5,0,true) := by decide
example : capacity (ready 8) 99 = .invalid (ready 8) := by decide
example : pointer (ready 8) 99 = .invalid (ready 8) := by decide

private def withoutShadow : NativeReferenceMachine.State :=
  {ready 8 with pointers := {(ready 8).pointers with heap := {(ready 8).pointers.heap with shadow := []}}}
example : (match pointer withoutShadow 0 with | .value value _ => value | _ => ⟨0,none⟩) = ⟨64,none⟩ := by decide
private def mixedShadow : NativeReferenceMachine.State :=
  {ready 8 with pointers := {(ready 8).pointers with heap := {(ready 8).pointers.heap with
    shadow := (ready 8).pointers.heap.shadow.drop 1}}}
example : pointer mixedShadow 0 = .invalid mixedShadow := by decide
private def revoked : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute (ready 8) (.endBorrow 0)).getD NativeReferenceMachine.empty
example : select revoked 0 = none := by decide
example : capacity revoked 0 = .invalid revoked := by decide
example : pointer revoked 0 = .invalid revoked := by decide
private def shortLease : NativeReferenceMachine.State :=
  {ready 8 with leases := (ready 8).leases.map (fun lease => {lease with layout := ⟨8,8⟩})}
example : capacity shortLease 0 = .invalid shortLease := by decide
private def wrongAlignment : NativeReferenceMachine.State :=
  {ready 8 with leases := (ready 8).leases.map (fun lease => {lease with layout := ⟨16,1⟩})}
example : pointer wrongAlignment 0 = .invalid wrongAlignment := by decide
private def exclusiveLease : NativeReferenceMachine.State :=
  {ready 8 with leases := (ready 8).leases.map (fun lease => {lease with mode := .exclusive})}
example : select exclusiveLease 0 = none := by decide

private def nullStored : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,8⟩), .raw (.allocate 128 ⟨16,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)), .raw (.withAddress 0 136),
     .raw (.fromAddress 0), .raw (.store 1 0), .borrow 2 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty
example : (match pointer nullStored 0 with
    | .invalid next => (next.pointers.registers.length,next.outputs.length,next.pointers.heap == nullStored.pointers.heap)
    | _ => (99,99,false)) = (6,0,true) := by decide
-- Deliberately alter initialized storage while retaining the resident lease.
private def uninitialized : NativeReferenceMachine.State :=
  let original := ready 8
  let heap := original.pointers.heap
  let memory := {heap.memory with blocks := heap.memory.blocks.map (fun block =>
    if block.base.val = 128 then {block with bytes := List.replicate 16 none} else block)}
  {original with pointers := {original.pointers with heap := {heap with memory}}}
example : select uninitialized 0 = some ⟨0⟩ := by decide
example : capacity uninitialized 0 = .invalid uninitialized := by decide
example : pointer uninitialized 0 = .invalid uninitialized := by decide
private def reused : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run (ready 8)
    [.raw (.free 2 ⟨8,8⟩), .raw (.allocate 64 ⟨8,8⟩)]).getD NativeReferenceMachine.empty
example : reused.pointers.registers[0]? = some ⟨64,some ⟨64,2⟩⟩ := by decide
example : (match pointer reused 0 with | .value value _ => value | _ => ⟨0,none⟩) =
    ⟨64,some ⟨64,0⟩⟩ := by decide

end FormalProof4FHETest.HasteBootsRawVecFieldsSmoke
