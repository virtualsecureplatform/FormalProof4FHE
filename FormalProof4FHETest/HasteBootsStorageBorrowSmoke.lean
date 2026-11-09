module
import FormalProof4FHE.HasteBoots.NativeStorageBorrowMachine
namespace FormalProof4FHETest.HasteBootsStorageBorrowSmoke
open FormalProof4FHE.HasteBoots
open NativeStorageBorrowMachine

private def setup : List Op :=
  [.legacy (.raw (.allocate 64 ⟨16,8⟩)),.legacy (.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0))),
   .storageBorrow none 0 .shared ⟨16,8⟩]
private def ready : NativeReferenceMachine.State := (run NativeReferenceMachine.empty setup).getD NativeReferenceMachine.empty
private theorem issued : run NativeReferenceMachine.empty setup = some ready := by decide
private theorem reachable : Reachable ready := run_projects _ _ _ issued

example : ready.references = [⟨0⟩] := by decide
example : NativeByteRange.loadRange ready.pointers.heap.memory ⟨72,some ⟨64,0⟩⟩ ⟨8,8⟩ = none := by decide
example : NativeReservationErrorFields.read ready 0 = .value .capacityOverflow
    (NativeReservationErrorFields.wordAccess ready 0 0).world := by decide
example : Reachable (NativeReservationErrorFields.read ready 0).world := read_reachable ready 0 reachable
example : NativeReferenceMachine.WellFormed ready := reachable_wellFormed ready reachable
example : execute ready (.legacy (.access 0 8 (.read 8 8))) = none := by decide
example : execute ready (.storageBorrow none 0 .exclusive ⟨16,8⟩) = none := by decide
example : execute ready (.storageBorrow (some 0) 0 .exclusive ⟨16,8⟩) = none := by decide
example : execute ready (.storageBorrow (some 1) 0 .shared ⟨16,8⟩) = none := by decide
example : execute ready (.legacy (.raw (.free 0 ⟨16,8⟩))) = none := by decide

private def forged : NativeReferenceMachine.State :=
  (run ready [.legacy (.raw (.fromAddress 64))]).getD NativeReferenceMachine.empty
example : execute forged (.storageBorrow none 0 .shared ⟨16,8⟩) = none := by decide
private def shifted : NativeReferenceMachine.State :=
  (run ready [.legacy (.raw (.withAddress 0 72))]).getD NativeReferenceMachine.empty
example : execute shifted (.storageBorrow (some 0) 0 .shared ⟨16,8⟩) = none := by decide
private def misaligned : NativeReferenceMachine.State :=
  (run ready [.legacy (.raw (.withAddress 0 68))]).getD NativeReferenceMachine.empty
example : execute misaligned (.storageBorrow none 0 .shared ⟨8,8⟩) = none := by decide

private def child : NativeReferenceMachine.State :=
  (execute ready (.storageBorrow (some 0) 0 .shared ⟨8,8⟩)).getD NativeReferenceMachine.empty
example : child.references = [⟨1⟩,⟨0⟩] := by decide
example : NativeByteBorrow.lookup child.leases 1 = some ⟨1,some 0,⟨64,some ⟨64,0⟩⟩,⟨8,8⟩,.shared⟩ := by decide
example : execute child (.legacy (.endBorrow 1)) = none := by decide
example : (run child [.legacy (.endBorrow 0),.legacy (.endBorrow 1)]).isSome = true := by decide
example : NativeIncomingReference.Preserves ready child := storage_incoming ready child (some 0) 0 .shared ⟨8,8⟩ (by decide)
example : child.pointers.heap = ready.pointers.heap := storage_heap ready child (some 0) 0 .shared ⟨8,8⟩ (by decide)

private def uninitialized : NativeReferenceMachine.State :=
  (run NativeReferenceMachine.empty [.legacy (.raw (.allocate 64 ⟨16,8⟩)),.storageBorrow none 0 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty
example : uninitialized.references = [⟨0⟩] := by decide
example : NativeReservationErrorFields.read uninitialized 0 = .invalid uninitialized := by decide

example (state next : NativeReferenceMachine.State) (parent : Option Nat) (mode : NativeByteBorrow.Mode)
    (pointer : NativePointerStorage.Pointer) (layout : NativeByteMemory.Layout)
    (borrowed : NativeReferenceMachine.grant state parent mode pointer layout = some next) :
    grant state parent mode pointer layout = some next := legacy_grant_refines _ _ _ _ _ _ borrowed

end FormalProof4FHETest.HasteBootsStorageBorrowSmoke
