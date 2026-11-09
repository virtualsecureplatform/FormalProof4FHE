module
import FormalProof4FHE.HasteBoots.NativeReservationErrorFields
namespace FormalProof4FHETest.HasteBootsReservationErrorFieldsSmoke
open FormalProof4FHE.HasteBoots
open NativeReservationErrorFields
open NativeRawVecFields (Result)

private def ready (size alignment : NativeWord64Memory.Word) (mode : NativeByteBorrow.Mode := .shared) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨16,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode alignment)),
     .raw (.withAddress 0 72),.raw (.writeBytes 0 8 (NativeWord64Memory.encode size)),
     .borrow 1 mode ⟨16,8⟩]).getD NativeReferenceMachine.empty

example : (ready 3 1).references = [⟨0⟩] := by decide
example : read (ready 3 1) 0 = .value (.allocationError 3 1)
    (wordAccess (wordAccess (ready 3 1) 0 0).world 0 8).world := by decide
example : read (ready 32 16) 0 = .value (.allocationError 32 16)
    (wordAccess (wordAccess (ready 32 16) 0 0).world 0 8).world := by decide
example : read (ready 0 0) 0 = .value .capacityOverflow (wordAccess (ready 0 0) 0 0).world := by decide
example : (read (ready 0 0) 0).world.outputs.length = (ready 0 0).outputs.length + 1 := by decide
example : read (ready 3 3) 0 = .invalid (wordAccess (wordAccess (ready 3 3) 0 0).world 0 8).world := by decide
example : read (ready (2^63) 1) 0 = .invalid (wordAccess (wordAccess (ready (2^63) 1) 0 0).world 0 8).world := by decide
example : read (ready 3 1 .exclusive) 0 = .invalid (ready 3 1 .exclusive) := by decide
example : read (ready 3 1) 1 = .invalid (ready 3 1) := by decide

private def padded : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨16,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0))]).getD NativeReferenceMachine.empty

-- This test supplies an existing resident loan; it does not issue that loan.
-- The current full-byte borrow primitive cannot issue it with this padding.
private def paddedResident : NativeReferenceMachine.State :=
  {padded with
    nextTag := 1
    references := [⟨0⟩]
    leases := [⟨0,none,⟨64,some ⟨64,0⟩⟩,⟨16,8⟩,.shared⟩]
    births := [⟨0,none,⟨64,some ⟨64,0⟩⟩,⟨16,8⟩,.shared⟩]}

example : NativeByteRange.loadRange paddedResident.pointers.heap.memory ⟨72,some ⟨64,0⟩⟩ ⟨8,8⟩ = none := by decide
example : NativeReferenceMachine.execute padded (.borrow 0 .shared ⟨16,8⟩) = none := by decide
example : read paddedResident 0 = .value .capacityOverflow (wordAccess paddedResident 0 0).world := by decide
example : (read paddedResident 0).world.outputs.length = 1 := by decide
example : (read paddedResident 0).world.pointers.heap = paddedResident.pointers.heap := read_heap _ _

private def blocked : NativeReferenceMachine.State :=
  let base := ready 3 1
  {base with nextTag := 2,leases := ⟨1,none,⟨64,some ⟨64,0⟩⟩,⟨16,8⟩,.exclusive⟩ :: base.leases}
example : read blocked 0 = .invalid blocked := by decide

example (world : NativeReferenceMachine.State) (index : Nat)
    (reachable : NativeReferenceMachine.Reachable world) : NativeReferenceMachine.Reachable (read world index).world :=
  read_reachable world index reachable

end FormalProof4FHETest.HasteBootsReservationErrorFieldsSmoke
