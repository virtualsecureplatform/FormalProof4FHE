namespace HasteBootsReferenceRetagSmoke
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC NativeReferenceCleanup
open HasteBootsReferenceRetagBody

private def ready : Option NativeReferenceMachine.State := NativeReferenceMachine.run NativeReferenceMachine.empty
  [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0))]
private def args : List Input := [.rawRegister 0, .usize ⟨3, by decide⟩]

example : (do
    let world ← ready
    pure (match invoke f1 world args with
      | .returned .unit next => (next.nextTag, next.leases.length)
      | _ => (99,99))) = some (3,3) := by decide

example : (do
    let world ← ready
    pure (match invoke f2 world args with
      | .returned .unit next => (next.nextTag, next.leases.map (fun lease => (lease.tag, lease.parent)))
      | _ => (99,[]))) = some (4,[(3,some 2),(2,some 1),(1,some 0),(0,none)]) := by decide

example : (do
    let world ← ready
    pure (match invokeUnit f1 world args with
      | .returned .unit next => (next.nextTag, next.leases.length, next.pointers == world.pointers)
      | _ => (99,99,false))) = some (3,0,true) := by decide

example : (do
    let world ← ready
    pure (match invokeUnit f2 world args with
      | .returned .unit next => (next.nextTag, next.leases.length, next.pointers == world.pointers)
      | _ => (99,99,false))) = some (4,0,true) := by decide

example : (do
    let world ← ready
    NativeReferenceMachine.execute (invoke f2 world args).world (.endBorrow 3)) = none := by decide

example : (do
    let world ← ready
    let final ← NativeReferenceMachine.execute (invokeUnit f2 world args).world (.raw (.free 0 ⟨8,8⟩))
    pure (final.pointers.heap.memory.blocks.length, final.nextTag, final.births.length)) = some (0,4,4) := by decide

example : (do
    let world ← ready
    let entered ← NativeReferenceMachine.execute world (.borrow 0 .shared ⟨3,1⟩)
    let final := (invokeUnit f1 entered args).world
    pure (final.nextTag, final.leases.map NativeByteBorrow.Lease.tag)) = some (4,[0]) := by decide

example : (do
    let world ← ready
    let entered ← NativeReferenceMachine.execute world (.borrow 0 .exclusive ⟨3,1⟩)
    pure (invokeUnit f2 entered args == .invalid entered)) = some true := by decide

example : (do
    let world ← ready
    pure (invoke f0 world [.rawRegister 0] == .invalid world)) = some true := by decide

example : (do
    let world ← ready
    let entered ← NativeReferenceMachine.execute world (.borrow 0 .exclusive ⟨3,1⟩)
    pure (match applyBody f5 entered [.reference true ⟨0⟩ ⟨3, by decide⟩] with
      | .returned (.reference true reference _) final => (reference.tag, final.nextTag, final.leases.length)
      | _ => (99,99,99))) = some (1,2,2) := by decide

end HasteBootsReferenceRetagSmoke
