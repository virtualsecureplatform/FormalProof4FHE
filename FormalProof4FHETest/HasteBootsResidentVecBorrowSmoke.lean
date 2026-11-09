module
import FormalProof4FHE.HasteBoots.NativeResidentVecBorrow
namespace FormalProof4FHETest.HasteBootsResidentVecBorrowSmoke
open FormalProof4FHE.HasteBoots
open NativeResidentVecBorrow
open NativeReferenceMachine (State)
open NativeSliceLLBC (Value)
private def header : NativePointerStorage.Pointer := ⟨128,some ⟨128,1⟩⟩
private def buffer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def ready : State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.allocate 128 ⟨24,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),.raw (.withAddress 0 136),
     .raw (.store 0 2),.raw (.withAddress 1 144),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),.borrow 2 .exclusive ⟨24,8⟩]).getD NativeReferenceMachine.empty
private def input : Value := .reference true ⟨0⟩ 3
private theorem initial_resident : Resident ready input header 8 0 buffer := by
  refine ⟨true,⟨0⟩,3,⟨0,none,header,⟨24,8⟩,.exclusive⟩,rfl,by decide,by decide,rfl,rfl,
    Or.inl ⟨rfl,rfl⟩,by decide,?_⟩
  constructor <;> decide
private def observed (result : NativeRawVecFields.Result Value) : Value × State :=
  match result with | .value value world => (value,world) | .invalid world => (.unit,world)
private def whole := observed (NativeVecReference.reborrow ready input .whole)
private def rawvec := observed (NativeVecReference.reborrow whole.2 whole.1 .rawVec)
private def reservation : NativeRawVecMutBorrow.Reservation :=
  match NativeRawVecMutBorrow.reserve rawvec.2 rawvec.1 with
  | .value reservation _ => reservation
  | .invalid _ => ⟨⟨0⟩,header⟩
private def prepared := (NativeRawVecMutBorrow.reserve rawvec.2 rawvec.1).world
private def activated := observed (NativeRawVecMutBorrow.activate prepared reservation)
private def shared := observed (NativeRawVecBorrow.reborrow activated.2 activated.1 .whole)
private theorem whole_resident : Resident whole.2 whole.1 header 8 0 buffer :=
  vec_reborrow initial_resident .whole (by decide)
private theorem rawvec_resident : Resident rawvec.2 rawvec.1 header 8 0 buffer :=
  vec_reborrow whole_resident .rawVec (by decide)
private theorem prepared_resident : Resident prepared rawvec.1 header 8 0 buffer :=
  (rawvec_reserve rawvec_resident reservation (by decide)).2
private theorem activated_resident : Resident activated.2 activated.1 header 8 0 buffer :=
  rawvec_activate prepared_resident reservation (by decide) (by decide)
private theorem shared_resident : Resident shared.2 shared.1 header 8 0 buffer :=
  rawvec_reborrow activated_resident (by decide)
example : whole.1 = .reference true ⟨1⟩ 3 ∧ rawvec.1 = .reference true ⟨2⟩ 2 := by decide
example : reservation.pointer = header ∧ reservation.pointer ≠ buffer := by decide
example : prepared.nextTag = rawvec.2.nextTag ∧ prepared.leases = rawvec.2.leases := by decide
example : activated.1 = .reference true ⟨3⟩ 2 ∧ shared.1 = .reference false ⟨4⟩ 2 := by decide
example : shared.2.pointers.heap = ready.pointers.heap := by decide
example : NativeByteRange.loadRange shared.2.pointers.heap.memory buffer ⟨8,1⟩ = none := by decide

private def firstCapacity := observed (NativeRawVecReference.eval shared.2 shared.1 .capacity)
private def secondCapacity := observed (NativeRawVecReference.eval firstCapacity.2 shared.1 .capacity)
private def loadedPointer := observed (NativeRawVecReference.eval secondCapacity.2 shared.1 .pointer)
private theorem after_first : Resident firstCapacity.2 shared.1 header 8 0 buffer :=
  rawvec_capacity_preserves (output := firstCapacity.1) shared_resident (by decide)
private theorem after_second : Resident secondCapacity.2 shared.1 header 8 0 buffer :=
  rawvec_capacity_preserves (output := secondCapacity.1) after_first (by decide)
example : firstCapacity.1 = .usize 8 := rawvec_capacity (next := firstCapacity.2) shared_resident (by decide)
example : secondCapacity.1 = .usize 8 := rawvec_capacity (next := secondCapacity.2) after_first (by decide)
example : loadedPointer.1 = .raw ⟨buffer,none⟩ := rawvec_pointer (next := loadedPointer.2) after_second (by decide)
example : Resident loadedPointer.2 shared.1 header 8 0 buffer := rawvec_pointer_preserves (output := loadedPointer.1) after_second (by decide)
-- The stable value survives index shifts; the former Vec register index does not.
example : NativeVecReference.decodeExclusive shared.2 0 = none := by decide
example : NativeRawVecFields.pointerAccess shared.2 4 = .invalid shared.2 := by decide
-- The original source reference is retained while its child loans are closed.
private def cleaned := (NativeReferenceCleanup.closeScope ready shared.2).world
example : cleaned.leases.map NativeByteBorrow.Lease.tag = [0] := by decide
example : NativeRawVecReference.eval cleaned shared.1 .pointer = .invalid cleaned := by decide
example : NativeByteBorrow.lookup cleaned.leases 0 = NativeByteBorrow.lookup shared.2.leases 0 :=
  closeScope_lookup ready shared.2 0 (by decide)
example : NativeRawVecFields.pointerAccess cleaned 4 ≠ .invalid cleaned := by decide
-- Partial cleanup also retains every incoming reference.
private def blocked := {shared.2 with references := shared.2.references.filter (fun reference => decide (reference.tag ≠ 4))}
example : (NativeReferenceCleanup.closeScope ready blocked).pending = [4,3,2,1] := by decide
example : NativeByteBorrow.lookup (NativeReferenceCleanup.closeScope ready blocked).world.leases 0 =
    NativeByteBorrow.lookup blocked.leases 0 := closeScope_lookup ready blocked 0 (by decide)
end FormalProof4FHETest.HasteBootsResidentVecBorrowSmoke
