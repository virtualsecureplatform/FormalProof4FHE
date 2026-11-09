module
import FormalProof4FHE.HasteBoots.NativeReservationErrorLocal
namespace FormalProof4FHETest.HasteBootsReservationErrorLocalSmoke
open FormalProof4FHE.HasteBoots
open NativeReservationErrorLocal
open NativeRecordLLBC (Frame)
open NativeRecordValues (Ty)
open NativeReservationErrorFields (Kind)

private def tags : Tags := ⟨9,18,4,11,12⟩
private def alignmentType : Ty := .record 11 (.pair (.enumeration 12 [1,8]) (.scalar .unit))
private def layoutType : Ty := .record 4 (.pair (.scalar .usize) (.pair alignmentType (.scalar .unit)))
private def errorType : Ty := .record 9 (.pair (.record 18 (.choice (.scalar .unit)
    (.pair layoutType (.pair (.scalar .unit) (.scalar .unit))))) (.scalar .unit))
private def frame (kind : Kind) : Frame := ⟨[errorType],[.live (some (encode tags kind))],NativeReferenceMachine.empty⟩
private def ready (kind : Kind) : NativeReferenceMachine.State := (snapshotLocal tags (frame kind) 0 64).world

example : snapshotLocal tags (frame .capacityOverflow) 0 64 = .value (.scalar (.reference false ⟨0⟩ 2)) (ready .capacityOverflow) := by decide
example : NativeReservationErrorFields.read (ready .capacityOverflow) 0 = .value .capacityOverflow
    (NativeReservationErrorFields.wordAccess (ready .capacityOverflow) 0 0).world := by decide
example : NativeByteRange.loadRange (ready .capacityOverflow).pointers.heap.memory ⟨72,some ⟨64,0⟩⟩ ⟨8,8⟩ = none := by decide
example : snapshotLocal tags (frame (.allocationError 3 8)) 0 64 =
    .value (.scalar (.reference false ⟨0⟩ 2)) (ready (.allocationError 3 8)) := by decide
example : NativeReservationErrorFields.read (ready (.allocationError 3 8)) 0 = .value (.allocationError 3 8)
    (NativeReservationErrorFields.wordAccess (NativeReservationErrorFields.wordAccess (ready (.allocationError 3 8)) 0 0).world 0 8).world := by decide
example : NativeStorageBorrowMachine.Reachable (ready .capacityOverflow) :=
  snapshotLocal_reachable tags (frame .capacityOverflow) 0 64 (.refl _)
example : NativeReferenceMachine.WellFormed (ready (.allocationError 3 8)) :=
  snapshotLocal_wellFormed tags (frame (.allocationError 3 8)) 0 64 NativeReferenceMachine.empty_wellFormed
example : ∃ kind, decode tags (encode tags .capacityOverflow) = some kind ∧ Valid kind ∧
    Resident (ready .capacityOverflow) (.scalar (.reference false ⟨0⟩ 2)) kind :=
  snapshot_resident tags NativeReferenceMachine.empty _ 64 _ _ NativeReferenceMachine.empty_wellFormed (by decide)
example : snapshotLocal tags (frame .capacityOverflow) 1 64 = .invalid NativeReferenceMachine.empty := by decide
example : snapshotLocal tags {frame .capacityOverflow with slots := [.dead]} 0 64 = .invalid NativeReferenceMachine.empty := by decide
example : snapshotLocal tags {frame .capacityOverflow with slots := [.live (some .uninit)]} 0 64 = .invalid NativeReferenceMachine.empty := by decide
example : snapshotLocal tags {frame .capacityOverflow with types := [.scalar .usize]} 0 64 = .invalid NativeReferenceMachine.empty := by decide
example : snapshotLocal {tags with error := 10} (frame .capacityOverflow) 0 64 = .invalid NativeReferenceMachine.empty := by decide
example : snapshotValue tags NativeReferenceMachine.empty 64 (encode {tags with kind := 17} .capacityOverflow) = .invalid NativeReferenceMachine.empty := by decide
example : snapshotValue tags NativeReferenceMachine.empty 64 (encode tags (.allocationError 3 3)) = .invalid NativeReferenceMachine.empty := by decide
example : snapshotValue tags NativeReferenceMachine.empty 64 (encode tags (.allocationError 3 0)) = .invalid NativeReferenceMachine.empty := by decide
example : snapshotValue tags NativeReferenceMachine.empty 64 (encode tags (.allocationError (2^63) 1)) = .invalid NativeReferenceMachine.empty := by decide
example : snapshotLocal tags (frame .capacityOverflow) 0 0 = .invalid NativeReferenceMachine.empty := by decide

private def edge : NativePointerStorage.Address := 2^64-16
private def prefixOps : List NativeStorageBorrowMachine.Op :=
  [.legacy (.raw (.allocate edge ⟨16,8⟩)),.legacy (.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)))]
private def partialState : NativeReferenceMachine.State :=
  (NativeStorageBorrowMachine.run NativeReferenceMachine.empty prefixOps).getD NativeReferenceMachine.empty
example : snapshotLocal tags (frame .capacityOverflow) 0 edge = .invalid partialState := by decide
example : partialState.pointers.heap.memory.nextGeneration = 1 := by decide
example : partialState.references = [] := by decide
example : NativeStorageBorrowMachine.Reachable partialState :=
  NativeStorageBorrowMachine.run_projects _ _ prefixOps (by decide)

end FormalProof4FHETest.HasteBootsReservationErrorLocalSmoke
