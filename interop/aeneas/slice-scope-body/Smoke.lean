namespace HasteBootsSliceScopeSmoke
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC NativeReferenceCleanup
open HasteBootsSliceScopeBody

private def ready : Option NativeReferenceMachine.State := NativeReferenceMachine.run NativeReferenceMachine.empty
  [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0))]

private def args : List Input := [.rawRegister 0, .usize ⟨3, by decide⟩]

example : (do
    let world ← ready
    pure (match invoke f0 world args with
      | .returned .unit next => (next.nextTag, next.leases.length)
      | _ => (99,99))) = some (1,1) := by decide

example : (do
    let world ← ready
    pure (match invoke f1 world args with
      | .returned .unit next => (next.nextTag, next.leases.length)
      | _ => (99,99))) = some (2,2) := by decide

example : (do
    let world ← ready
    pure (match invokeUnit f0 world args with
      | .returned .unit next => (next.nextTag, next.leases.length, next.pointers == world.pointers)
      | _ => (99,99,false))) = some (1,0,true) := by decide

example : (do
    let world ← ready
    pure (match invokeUnit f1 world args with
      | .returned .unit next => (next.nextTag, next.leases.length, next.pointers == world.pointers)
      | _ => (99,99,false))) = some (2,0,true) := by decide

example : (do
    let world ← ready
    let afterScope := (invokeUnit f1 world args).world
    let final ← NativeReferenceMachine.execute afterScope (.raw (.free 0 ⟨8,8⟩))
    pure (final.pointers.heap.memory.blocks.length, final.births.length, final.nextTag)) = some (0,2,2) := by decide

example : (do
    let world ← ready
    NativeReferenceMachine.execute (invokeUnit f1 world args).world (.access 0 0 (.read 1 1))) = none := by decide

example : (do
    let world ← ready
    let entered ← NativeReferenceMachine.execute world (.borrow 0 .shared ⟨8,8⟩)
    let final := (invokeUnit f0 entered args).world
    pure (final.leases.map NativeByteBorrow.Lease.tag, final.nextTag,
      final.pointers == entered.pointers)) = some ([0],2,true) := by decide

example : (do
    let world ← ready
    let entered ← NativeReferenceMachine.execute world (.borrow 0 .shared ⟨8,8⟩)
    NativeReferenceMachine.execute (invokeUnit f0 entered args).world (.raw (.free 0 ⟨8,8⟩))) = none := by decide

example : (do
    let world ← ready
    let entered ← NativeReferenceMachine.execute world (.borrow 0 .exclusive ⟨8,8⟩)
    pure (invokeUnit f1 entered args == .invalid entered)) = some true := by decide

example : (do
    let world ← ready
    pure (invokeUnit f1 world [.rawRegister 0, .usize ⟨9, by decide⟩] == .invalid world)) = some true := by decide

end HasteBootsSliceScopeSmoke
