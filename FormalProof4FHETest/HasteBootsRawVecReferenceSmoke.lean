module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC

namespace FormalProof4FHETest.HasteBootsRawVecReferenceSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def ready (size : Nat) (cap : NativeWord64Memory.Word := 8) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,8⟩), .raw (.allocate 128 ⟨size,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode cap ++ NativeWord64Memory.encode 64 ++
       (if size = 24 then NativeWord64Memory.encode 5 else []))),
     .borrow 0 .shared ⟨size,8⟩]).getD NativeReferenceMachine.empty
private def frame (world : NativeReferenceMachine.State) (count : NativeWord64Memory.Word) : Frame :=
  ⟨[.scalar .usize,.scalar (.reference false)],
    [.live none,.live (some (.scalar (.reference false ⟨0⟩ count)))],world⟩

example : (ready 16).nextTag = 1 ∧ (ready 24).nextTag = 1 := by decide
example : decode (ready 16) (.rawVecSharedReference 0) = some (.scalar (.reference false ⟨0⟩ 2)) := by decide
example : decode (ready 24) (.vectorSharedReference 0) = some (.scalar (.reference false ⟨0⟩ 3)) := by decide
example : decode (ready 24) (.rawVecSharedReference 0) = none := by decide
example : decode (ready 16) (.vectorSharedReference 0) = none := by decide
example : (match evalRvalue (frame (ready 16) 2) (.rawVecField .capacity (.copy 1)) with
    | .value value next => (value,next.world.outputs.length,next.world.pointers.registers.length)
    | _ => (.uninit,99,99)) = (.scalar (.usize 8),1,3) := by decide
example : (match evalRvalue (frame (ready 24) 3) (.rawVecField .pointer (.copy 1)) with
    | .value (.scalar (.raw pointer)) _ => (pointer.storage.address.val,pointer.storage.provenance)
    | _ => (0,some ⟨9,9⟩)) = (64,none) := by decide
private def shifted : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute (ready 16) (.reborrow 0 0 .shared ⟨16,8⟩)).getD NativeReferenceMachine.empty
example : shifted.references = [⟨1⟩,⟨0⟩] := by decide
example : NativeRawVecReference.resolve shifted ⟨0⟩ = some 1 := by decide
example : (match evalRvalue (frame shifted 2) (.rawVecField .capacity (.copy 1)) with
    | .value value _ => value | _ => .uninit) = .scalar (.usize 8) := by decide
example : (match evalRvalue (frame (ready 24) 3) (.use (.copy 1) true .word) with
    | .value (.scalar (.reference false reference count)) next =>
      (reference.tag,count.val,next.world.nextTag,next.world.leases.head?.map NativeByteBorrow.Lease.layout)
    | _ => (99,99,99,none)) = (1,3,2,some ⟨24,8⟩) := by decide
private def revoked : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute (ready 16) (.endBorrow 0)).getD NativeReferenceMachine.empty
example : NativeRawVecReference.resolve revoked ⟨0⟩ = none := by decide
example : evalRvalue (frame revoked 2) (.rawVecField .capacity (.copy 1)) = .invalid revoked := by decide
example : evalRvalue (frame (ready 16) 0) (.rawVecField .capacity (.copy 1)) = .invalid (ready 16) := by decide
example : evalRvalue (frame (ready 16) 2) (.rawVecField .capacity (.copy 99)) = .invalid (ready 16) := by decide
example : (match eval (.assign 0 (.rawVecField .capacity (.copy 1)) .ret)
    {frame (ready 24) 3 with slots := [.dead,.live (some (.scalar (.reference false ⟨0⟩ 3)))]} with
    | .invalid next => (next.outputs.length,next.pointers.registers.length)
    | _ => (99,99)) = (1,3) := by decide
example : (match evalRvalue (frame (ready 24 ⟨2^63,by decide⟩) 3) (.rawVecField .capacity (.copy 1)) with
    | .invalid next => (next.outputs.length,next.pointers.registers.length)
    | _ => (99,99)) = (1,3) := by decide

end FormalProof4FHETest.HasteBootsRawVecReferenceSmoke
