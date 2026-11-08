module
import FormalProof4FHE.HasteBoots.NativeReferenceCleanup

namespace FormalProof4FHETest.HasteBootsReferenceCleanupSmoke
open FormalProof4FHE.HasteBoots
open NativeReferenceCleanup

private def ready : Option NativeReferenceMachine.State := NativeReferenceMachine.run NativeReferenceMachine.empty
  [.raw (.allocate ⟨64, by decide⟩ ⟨8, 8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0))]

private def nested : Option (NativeReferenceMachine.State × NativeReferenceMachine.State × NativeReferenceMachine.State) := do
  let entered ← ready
  let parent ← NativeReferenceMachine.execute entered (.borrow 0 .exclusive ⟨8, 8⟩)
  let child ← NativeReferenceMachine.execute parent (.reborrow 0 0 .exclusive ⟨8, 8⟩)
  pure (entered, parent, child)

example : (do
    let (entered, _, current) ← nested
    let result := closeScope entered current
    pure (result.ended, result.pending, result.world.leases.length, result.world.nextTag)) = some ([1,0], [], 0, 2) := by decide

example : (do
    let (entered, _, current) ← nested
    let result := closeScope entered current
    pure (result.world.pointers == current.pointers, result.world.references == current.references,
      result.world.births == current.births)) = some (true, true, true) := by decide

example : (do
    let (_, entered, current) ← nested
    let result := closeScope entered current
    pure (result.ended, result.pending, result.world.leases.map NativeByteBorrow.Lease.tag)) =
    some ([1], [], [0]) := by decide

example : (do
    let (_, _, current) ← nested
    let result := release current [0,1]
    pure (result.ended, result.pending, result.world == current)) = some ([], [0,1], true) := by decide

example : (do
    let (_, _, current) ← nested
    let result := release current [1,0,99]
    pure (result.ended, result.pending, result.world.leases.length,
      result.world.pointers == current.pointers)) = some ([1,0], [99], 0, true) := by decide

example : (do
    let (entered, _, current) ← nested
    let result := closeScope entered current
    let stale := release result.world [1]
    pure (stale.ended, stale.pending, stale.world == result.world)) = some ([], [1], true) := by decide

example : (do
    let (entered, _, current) ← nested
    NativeReferenceMachine.execute (closeScope entered current).world (.access 0 0 (.read 1 1))) = none := by decide

example : (do
    let (entered, _, current) ← nested
    let final ← NativeReferenceMachine.execute (closeScope entered current).world (.raw (.free 0 ⟨8,8⟩))
    pure (final.pointers.heap.memory.blocks.length, final.births.length, final.nextTag)) = some (0,2,2) := by decide

example : (do
    let (_, entered, current) ← nested
    NativeReferenceMachine.execute (closeScope entered current).world (.raw (.free 0 ⟨8,8⟩))) = none := by decide

example : (do
    let (entered, _, current) ← nested
    let flow := settleUnit entered (.returned .unit current)
    pure (match flow with
      | .returned .unit next => (next.leases.length, next.nextTag)
      | _ => (99,99))) = some (0,2) := by decide

example : (do
    let (entered, _, current) ← nested
    pure (settleUnit entered (.returned (.reference true ⟨1⟩ ⟨8, by decide⟩) current) ==
      .returned (.reference true ⟨1⟩ ⟨8, by decide⟩) current)) = some true := by decide

example : (do
    let (entered, _, current) ← nested
    pure (settleUnit entered (.invalid current) == .invalid current,
      settleUnit entered (.unwind current) == .unwind current)) = some (true,true) := by decide

example : (do
    let entered ← ready
    let parent ← NativeReferenceMachine.execute entered (.borrow 0 .exclusive ⟨8,8⟩)
    let malformed := {parent with references := []}
    let result := closeScope entered malformed
    pure (result.ended, result.pending, result.world == malformed,
      settleUnit entered (.returned .unit malformed) == .invalid malformed)) = some ([],[0],true,true) := by decide

end FormalProof4FHETest.HasteBootsReferenceCleanupSmoke
