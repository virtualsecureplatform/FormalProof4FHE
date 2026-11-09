module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC
namespace FormalProof4FHETest.HasteBootsVecReferenceSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.allocate 128 ⟨24,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),.raw (.withAddress 0 136),
     .raw (.store 0 2),.raw (.withAddress 1 144),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 3)),.borrow 2 .exclusive ⟨24,8⟩]).getD NativeReferenceMachine.empty
private def frame : Frame := ⟨[.scalar (.reference true)],
  [.live (some (.scalar (.reference true ⟨0⟩ 3)))],ready⟩
example : ready.nextTag = 1 := by decide
example : decode ready (.vectorExclusiveReference 0) = some (.scalar (.reference true ⟨0⟩ 3)) := by decide
example : decode ready (.rawVecExclusiveReference 0) = none := by decide
example : decode ready (.vectorSharedReference 0) = none := by decide
example : evalOperand frame (.copy 0 []) = none := by decide
example : (match evalRvalue frame (.vec (.field .pointer) 0 []) with
    | .value value next => (value,next.world.outputs.length,next.world.nextTag)
    | _ => (.uninit,99,99)) = (.scalar (.raw ⟨⟨64,some ⟨64,0⟩⟩,none⟩),0,1) := by decide
example : (match evalRvalue frame (.vec (.field .length) 0 []) with
    | .value value next => (value,next.world.outputs.length,next.world.pointers.heap == ready.pointers.heap)
    | _ => (.uninit,99,false)) = (.scalar (.usize 3),1,true) := by decide
example : (match evalRvalue frame (.vec (.borrow .whole) 0 []) with
    | .value value next => (value,next.world.nextTag,next.world.leases.head?.map NativeByteBorrow.Lease.layout)
    | _ => (.uninit,99,none)) = (.scalar (.reference true ⟨1⟩ 3),2,some ⟨24,8⟩) := by decide
example : (match evalRvalue frame (.vec (.borrow .rawVec) 0 []) with
    | .value value next => (value,next.world.nextTag,next.world.leases.head?.map NativeByteBorrow.Lease.layout)
    | _ => (.uninit,99,none)) = (.scalar (.reference true ⟨1⟩ 2),2,some ⟨16,8⟩) := by decide
example : NativeVecReference.reborrow ready (.reference false ⟨0⟩ 3) .whole = .invalid ready := by decide
example : NativeVecReference.reborrow ready (.reference true ⟨0⟩ 2) .rawVec = .invalid ready := by decide
private def blocked : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.reborrow 0 2 .shared ⟨24,8⟩)).getD NativeReferenceMachine.empty
example : (match NativeVecReference.reborrow blocked (.reference true ⟨0⟩ 3) .rawVec with
    | .invalid next => (next.nextTag,next.pointers.registers.length,next.pointers.heap == blocked.pointers.heap)
    | _ => (99,99,false)) = (2,5,true) := by decide
private def revoked : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.endBorrow 0)).getD NativeReferenceMachine.empty
example : NativeVecReference.decodeExclusive revoked 0 = none := by decide
example : NativeVecReference.readField revoked (.reference true ⟨0⟩ 3) .length = .invalid revoked := by decide
private def partsFrame : Frame := ⟨[.scalar (.raw false),.scalar .usize],
  [.live (some (.scalar (.raw ⟨⟨64,some ⟨64,0⟩⟩,none⟩))),.live (some (.scalar (.usize 3)))],ready⟩
example : (match evalRvalue partsFrame (.parts (.copy 0 []) (.copy 1 [])) with
    | .value value next => (value,next.world == ready)
    | _ => (.uninit,false)) = (.scalar (.raw ⟨⟨64,some ⟨64,0⟩⟩,some 3⟩),true) := by decide
example : evalRvalue partsFrame (.parts (.copy 1 []) (.copy 0 [])) = .invalid ready := by decide
-- Data bytes have not been initialized: slice issuance rejects after resident reads.
private def fatFrame : Frame := ⟨[.scalar (.raw true)],
  [.live (some (.scalar (.raw ⟨⟨64,some ⟨64,0⟩⟩,some 3⟩)))],ready⟩
example : evalRvalue fatFrame (.borrowSlice 0 []) = .invalid ready := by decide
end FormalProof4FHETest.HasteBootsVecReferenceSmoke
