module
import FormalProof4FHE.HasteBoots.NativeHeapFrame
namespace FormalProof4FHETest.HasteBootsHeapFrameSmoke
open FormalProof4FHE.HasteBoots
example : NativeHeapFrame.readOnly (.raw (.allocate 64 ⟨8,1⟩)) = false := rfl
example : NativeHeapFrame.readOnly (.raw (.free 0 ⟨8,1⟩)) = false := rfl
example : NativeHeapFrame.readOnly (.raw (.writeBytes 0 1 [7])) = false := rfl
example : NativeHeapFrame.readOnly (.access 0 0 (.storePointer 1)) = false := rfl
example (index : Nat) : NativeHeapFrame.readOnly (.access index 16 (.read 8 8)) = true := rfl
example (parent pointer : Nat) : NativeHeapFrame.readOnly (.reborrow parent pointer .exclusive ⟨16,8⟩) = true := rfl
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 128 ⟨16,8⟩),.raw (.writeBytes 0 8 (List.replicate 16 0)),.borrow 0 .exclusive ⟨16,8⟩]).getD NativeReferenceMachine.empty
private def frame : NativeRecordLLBC.Frame := ⟨[.scalar (.reference true)],
  [.live (some (.scalar (.reference true ⟨0⟩ 2)))],ready⟩
-- A null resident pointer rejects after the actual pointer-load prefix.
private def shared : NativeReferenceMachine.State :=
  match NativeRawVecBorrow.reborrow ready (.reference true ⟨0⟩ 2) .whole with
  | .value _ next => next
  | _ => NativeReferenceMachine.empty
example : (match NativeRawVecReference.eval shared (.reference false ⟨1⟩ 2) .pointer with
    | .invalid next => (next.pointers.registers.length,next.pointers.heap == shared.pointers.heap,next.nextTag)
    | _ => (99,false,99)) = (4,true,2) := by decide
example : (match NativeRecordLLBC.evalRvalue frame (.borrowRawVec .whole 0 []) with
    | .value _ next => (next.world.pointers.heap == ready.pointers.heap,next.world.nextTag)
    | _ => (false,99)) = (true,2) := by decide
end FormalProof4FHETest.HasteBootsHeapFrameSmoke
