module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC

namespace FormalProof4FHETest.HasteBootsRawVecBorrowSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 128 ⟨16,8⟩),.raw (.writeBytes 0 8 (List.replicate 16 0)),
     .borrow 0 .exclusive ⟨16,8⟩]).getD NativeReferenceMachine.empty
private def frame : Frame := ⟨[.scalar (.reference true)],
  [.live (some (.scalar (.reference true ⟨0⟩ 2)))],ready⟩

example : ready.nextTag = 1 := by decide
example : decode ready (.rawVecExclusiveReference 0) = some (.scalar (.reference true ⟨0⟩ 2)) := by decide
example : decode ready (.rawVecSharedReference 0) = none := by decide
example : evalOperand frame (.copy 0) = none := by decide
example : (match evalRvalue frame (.borrowRawVec .whole 0) with
    | .value value next => (value,next.world.nextTag,next.world.leases.head?.map NativeByteBorrow.Lease.layout,
      next.world.pointers.registers.length,next.world.pointers.heap == ready.pointers.heap)
    | _ => (.uninit,99,none,99,false)) = (.scalar (.reference false ⟨1⟩ 2),2,some ⟨16,8⟩,2,true) := by decide
example : (match evalRvalue frame (.borrowRawVec .allocator 0) with
    | .value value next => (value,next.world.leases.head?.map NativeByteBorrow.Lease.pointer,
      next.world.leases.head?.map NativeByteBorrow.Lease.layout,next.world.nextTag)
    | _ => (.uninit,none,none,99)) = (.scalar (.reference false ⟨1⟩ 0),some ⟨144,some ⟨128,0⟩⟩,some ⟨0,1⟩,2) := by decide
example : evalRvalue frame (.borrowRawVec .whole 99) = .invalid ready := by decide
private def blocked : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.reborrow 0 0 .exclusive ⟨16,8⟩)).getD NativeReferenceMachine.empty
example : blocked.nextTag = 2 := by decide
example : (match NativeRawVecBorrow.reborrow blocked (.reference true ⟨0⟩ 2) .whole with
    | .invalid next => (next.nextTag,next.pointers.registers.length,next.leases == blocked.leases,
      next.pointers.heap == blocked.pointers.heap)
    | _ => (99,99,false,false)) = (2,2,true,true) := by decide
private def revoked : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.endBorrow 0)).getD NativeReferenceMachine.empty
example : NativeRawVecBorrow.decodeExclusive revoked 0 = none := by decide
example : NativeRawVecBorrow.reborrow revoked (.reference true ⟨0⟩ 2) .whole = .invalid revoked := by decide
example : NativeRawVecBorrow.reborrow ready (.reference false ⟨0⟩ 2) .whole = .invalid ready := by decide
example : NativeRawVecBorrow.reborrow ready (.reference true ⟨0⟩ 0) .whole = .invalid ready := by decide
example : NativeRawVecBorrow.reborrow ready .unit .allocator = .invalid ready := by decide
private def shifted : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.reborrow 0 0 .shared ⟨16,8⟩)).getD NativeReferenceMachine.empty
example : (match NativeRawVecBorrow.reborrow shifted (.reference true ⟨0⟩ 2) .allocator with
    | .value value next => (value,next.nextTag,next.leases.head?.map NativeByteBorrow.Lease.parent)
    | _ => (.usize 99,99,none)) = (.reference false ⟨2⟩ 0,3,some (some 0)) := by decide

end FormalProof4FHETest.HasteBootsRawVecBorrowSmoke
