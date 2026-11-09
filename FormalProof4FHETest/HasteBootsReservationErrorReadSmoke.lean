module
import FormalProof4FHE.HasteBoots.NativeReservationErrorRead
namespace FormalProof4FHETest.HasteBootsReservationErrorReadSmoke
open FormalProof4FHE.HasteBoots
open NativeReservationErrorLocal (Tags encode kindValue snapshotLocal)
open NativeReservationErrorRead
open NativeReservationErrorFields (Kind wordAccess)
open NativeRecordValues (Ty)
private def tags : Tags := ⟨9,18,4,11,12⟩
private def alignmentType : Ty := .record 11 (.pair (.enumeration 12 [1,8]) (.scalar .unit))
private def layoutType : Ty := .record 4 (.pair (.scalar .usize) (.pair alignmentType (.scalar .unit)))
private def errorType : Ty := .record 9 (.pair (.record 18 (.choice (.scalar .unit)
    (.pair layoutType (.pair (.scalar .unit) (.scalar .unit))))) (.scalar .unit))
private def frame (kind : Kind) (world : NativeReferenceMachine.State := NativeReferenceMachine.empty) : NativeRecordLLBC.Frame :=
  ⟨[errorType],[.live (some (encode tags kind))],world⟩
private def ready (kind : Kind) : NativeReferenceMachine.State := (snapshotLocal tags (frame kind) 0 64).world
private def operand : NativeRecordValues.Value := .scalar (.reference false ⟨0⟩ 2)
example : getKind tags (ready .capacityOverflow) operand = .value (kindValue tags .capacityOverflow)
    (wordAccess (ready .capacityOverflow) 0 0).world := by decide
example : (getKind tags (ready .capacityOverflow) operand).world.outputs.length = 1 := by decide
example : getKind tags (ready (.allocationError 3 8)) operand = .value (kindValue tags (.allocationError 3 8))
    (wordAccess (wordAccess (ready (.allocationError 3 8)) 0 0).world 0 8).world := by decide
example : (getKind tags (ready (.allocationError 3 8)) operand).world.outputs.length = 2 := by decide
example : ∃ kind final, NativeRecordLLBC.read (frame .capacityOverflow) 0 [] = some (encode tags kind) ∧
    getKind tags (ready .capacityOverflow) operand = .value (kindValue tags kind) final :=
  snapshotLocal_getKind_complete tags (frame .capacityOverflow) 0 64 _ operand NativeReferenceMachine.empty_wellFormed (by decide)
example : (getKind tags (ready (.allocationError 3 8)) operand).world.pointers.heap = (ready (.allocationError 3 8)).pointers.heap := getKind_heap _ _ _
example : getKind tags (ready .capacityOverflow) (.scalar (.reference true ⟨0⟩ 2)) = .invalid (ready .capacityOverflow) := by decide
example : getKind tags (ready .capacityOverflow) (.scalar (.reference false ⟨0⟩ 0)) = .invalid (ready .capacityOverflow) := by decide
example : getKind tags (ready .capacityOverflow) (.scalar (.reference false ⟨100⟩ 2)) = .invalid (ready .capacityOverflow) := by decide
example : getKind tags (ready .capacityOverflow) (.scalar (.raw ⟨⟨64,some ⟨64,0⟩⟩,none⟩)) = .invalid (ready .capacityOverflow) := by decide
private def second : NativeReferenceMachine.State :=
  (snapshotLocal tags (frame (.allocationError 3 8) (ready .capacityOverflow)) 0 96).world
example : second.references = [⟨1⟩,⟨0⟩] := by decide
example : getKind tags second operand = .value (kindValue tags .capacityOverflow) (wordAccess second 1 0).world := by decide
example : getKind tags second (.scalar (.reference false ⟨1⟩ 2)) = .value (kindValue tags (.allocationError 3 8))
    (wordAccess (wordAccess second 0 0).world 0 8).world := by decide
private def revoked : NativeReferenceMachine.State :=
  (NativeStorageBorrowMachine.execute second (.legacy (.endBorrow 1))).getD NativeReferenceMachine.empty
example : getKind tags revoked operand = .invalid revoked := by decide
private def partialState : NativeReferenceMachine.State :=
  (NativeStorageBorrowMachine.run NativeReferenceMachine.empty
    [.legacy (.raw (.allocate 64 ⟨16,8⟩)),.legacy (.raw (.writeBytes 0 8 (NativeWord64Memory.encode 1))),
     .storageBorrow none 0 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty
example : getKind tags partialState operand = .invalid (wordAccess partialState 0 0).world := by decide
example : (getKind tags partialState operand).world.outputs.length = 1 := by decide
example : (getKind tags partialState operand).world.pointers.heap = partialState.pointers.heap := getKind_heap _ _ _
end FormalProof4FHETest.HasteBootsReservationErrorReadSmoke
