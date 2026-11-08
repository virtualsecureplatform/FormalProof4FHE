module
import FormalProof4FHE.HasteBoots.NativeReferenceCleanup

namespace FormalProof4FHETest.HasteBootsRetagSmoke
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC

private def ready (mode : NativeByteBorrow.Mode) : Option NativeReferenceMachine.State :=
  NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0)), .borrow 0 mode ⟨3,1⟩]
private def frame (world : NativeReferenceMachine.State) (mutable : Bool) : Option Frame :=
  initial [.unit,.reference mutable] 1 [.reference mutable ⟨0⟩ ⟨3, by decide⟩] world

example : (do
    let world ← ready .exclusive
    let start ← frame world true
    let (value, next) ← evalRvalue start (.use (.move 1) true .byte)
    pure (value == .reference true ⟨1⟩ ⟨3, by decide⟩, next.world.nextTag,
      next.world.leases.length, readLocal next 1)) = some (true,2,2,none) := by decide

example : (do
    let world ← ready .exclusive
    let start ← frame world true
    let (value, next) ← evalRvalue start (.use (.move 1) false .byte)
    pure (value == .reference true ⟨0⟩ ⟨3, by decide⟩, next.world == world, readLocal next 1)) =
    some (true,true,none) := by decide

example : (do
    let world ← ready .shared
    let start ← frame world false
    let (value, next) ← evalRvalue start (.use (.copy 1) true .byte)
    pure (value == .reference false ⟨1⟩ ⟨3, by decide⟩, next.world.nextTag, next.world.leases.length,
      readLocal next 1 == some (.reference false ⟨0⟩ ⟨3, by decide⟩))) = some (true,2,2,true) := by decide

example : (do
    let world ← ready .shared
    let start ← frame world false
    let (value, next) ← evalRvalue start (.use (.copy 1) false .byte)
    pure (value == .reference false ⟨0⟩ ⟨3, by decide⟩, next == start)) = some (true,true) := by decide

example : (do
    let world ← ready .exclusive
    let start ← frame world true
    evalRvalue start (.use (.move 1) true .word)) = none := by decide

example : (do
    let world ← ready .exclusive
    let ended ← NativeReferenceMachine.execute world (.endBorrow 0)
    let start ← frame ended true
    evalRvalue start (.use (.move 1) true .byte)) = none := by decide

example : (do
    let world ← ready .exclusive
    let start ← frame world true
    let (_, next) ← evalRvalue start (.use (.move 1) true .byte)
    NativeReferenceMachine.execute next.world (.endBorrow 1)) = none := by decide

example : (do
    let world ← ready .exclusive
    let start ← frame world true
    let (_, next) ← evalRvalue start (.use (.move 1) true .byte)
    let cleaned := NativeReferenceCleanup.closeScope world next.world
    pure (cleaned.ended, cleaned.pending, cleaned.world.leases.map NativeByteBorrow.Lease.tag,
      cleaned.world.pointers == world.pointers)) = some ([1],[],[0],true) := by decide

example : (do
    let world ← ready .exclusive
    let start ← initial [.unit,.usize] 1 [.usize ⟨7, by decide⟩] world
    pure (evalRvalue start (.use (.copy 1) true .byte) == evalRvalue start (.use (.copy 1) false .byte))) = some true := by decide

end FormalProof4FHETest.HasteBootsRetagSmoke
