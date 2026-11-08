namespace HasteBootsSliceReferenceSmoke
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC
open HasteBootsSliceReferenceBody

private def ready : Option NativeReferenceMachine.State := NativeReferenceMachine.run NativeReferenceMachine.empty
  [.raw (.allocate ⟨64, by decide⟩ ⟨32, 8⟩), .raw (.writeBytes 0 8 (List.replicate 32 0))]
private def observe (id : Function) : Option (Nat × Nat × Nat × Nat) := do
  let world ← ready
  pure (match invoke id world [.rawRegister 0, .usize ⟨3, by decide⟩] with
    | .returned (.reference _ reference length) next => (reference.tag, length.val, next.nextTag, next.leases.length)
    | _ => (99, 0, 0, 0))
example : observe f4 = some (0, 3, 1, 1) := by decide
example : observe f5 = some (0, 3, 1, 1) := by decide
example : observe f0 = some (1, 3, 2, 2) := by decide
example : observe f1 = some (3, 3, 4, 4) := by decide
example : (do
    let world ← ready
    let next := (invoke f1 world [.rawRegister 0, .usize ⟨3, by decide⟩]).world
    pure (next.leases.map (fun lease => (lease.tag, lease.parent, lease.layout.size)), next.pointers.heap == world.pointers.heap)) =
    some ([(3,some 2,24), (2,some 1,24), (1,some 0,24), (0,none,24)], true) := by decide
example : (do
    let world ← ready
    let next := (invoke f1 world [.rawRegister 0, .usize ⟨3, by decide⟩]).world
    NativeReferenceMachine.execute next (.raw (.writeBytes 0 1 [99]))) = none := by decide
example : (do
    let world ← ready
    let next := (invoke f1 world [.rawRegister 0, .usize ⟨3, by decide⟩]).world
    NativeReferenceMachine.execute next (.endBorrow 3)) = none := by decide
example : (do
    let world ← ready
    let next := (invoke f1 world [.rawRegister 0, .usize ⟨3, by decide⟩]).world
    let next ← NativeReferenceMachine.run next [.endBorrow 0, .endBorrow 1, .endBorrow 2, .endBorrow 3, .raw (.free 0 ⟨32,8⟩)]
    pure (next.nextTag, next.leases.length, next.pointers.heap.memory.blocks.length)) = some (4,0,0) := by decide
example : (do
    let world ← ready
    let next := (invoke f1 world [.rawRegister 0, .usize ⟨3, by decide⟩]).world
    let next ← NativeReferenceMachine.execute next (.access 0 16 (.read 8 8))
    next.outputs.head?) = some [0,0,0,0,0,0,0,0] := by decide
example : (do
    let world ← ready
    pure (invoke f5 world [.rawRegister 0, .usize ⟨5, by decide⟩] == .invalid world)) = some true := by decide
example : (do
    let world ← NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.fromAddress ⟨8, by decide⟩)]
    pure (match invoke f5 world [.rawRegister 0, .usize ⟨0, by decide⟩] with
      | .returned (.reference true reference length) next => (reference.tag, length.val, next.pointers.heap.memory.blocks.length)
      | _ => (99, 99, 99))) = some (0,0,0) := by decide
example : (do
    let world ← NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.fromAddress ⟨0, by decide⟩)]
    pure (invoke f4 world [.rawRegister 0, .usize ⟨0, by decide⟩] == .invalid world)) = some true := by decide
example : (do
    let world ← NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.allocate ⟨64, by decide⟩ ⟨32,8⟩)]
    pure (invoke f5 world [.rawRegister 0, .usize ⟨3, by decide⟩] == .invalid world)) = some true := by decide
example : observe f6 = some (0, 3, 1, 1) := by decide
example : observe f7 = some (0, 3, 1, 1) := by decide
example : observe f2 = some (1, 3, 2, 2) := by decide
example : observe f3 = some (3, 3, 4, 4) := by decide
example : (do
    let world ← ready
    let next := (invoke f3 world [.rawRegister 0, .usize ⟨3, by decide⟩]).world
    pure (next.leases.map (fun lease => lease.layout.size))) = some [3,3,3,3] := by decide
example : (do
    let world ← ready
    let world ← NativeReferenceMachine.execute world (.raw (.withAddress 0 ⟨65, by decide⟩))
    pure (invoke f5 world [.rawRegister 0, .usize ⟨1, by decide⟩] == .invalid world,
      match invoke f7 world [.rawRegister 0, .usize ⟨1, by decide⟩] with
      | .returned _ next => next.leases.head?.map (fun lease => (lease.pointer.address.val, lease.layout.size, lease.layout.alignment))
      | _ => none)) = some (true, some (65,1,1)) := by decide
example : (do
    let world ← ready
    pure (invoke f7 world [.rawRegister 0, .usize ⟨33, by decide⟩] == .invalid world)) = some true := by decide
end HasteBootsSliceReferenceSmoke
