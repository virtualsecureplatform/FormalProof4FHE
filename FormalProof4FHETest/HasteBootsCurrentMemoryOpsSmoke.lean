module
import FormalProof4FHE.HasteBoots.NativeRecordLLBC

namespace FormalProof4FHETest.HasteBootsCurrentMemoryOpsSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def frame : Frame := ⟨[],[],NativeReferenceMachine.empty⟩
example : evalRvalue frame (.mulUsizeUB (.usize 3) (.usize 8)) = .value (.scalar (.usize 24)) frame := by decide
example : evalRvalue frame (.mulUsizeUB (.usize 0) (.usize ⟨2^64-1,by decide⟩)) = .value (.scalar (.usize 0)) frame := by decide
example : evalRvalue frame (.mulUsizeUB (.usize ⟨2^64-1,by decide⟩) (.usize 1)) =
    .value (.scalar (.usize ⟨2^64-1,by decide⟩)) frame := by decide
example : evalRvalue frame (.mulUsizeUB (.usize ⟨2^63,by decide⟩) (.usize 2)) = .invalid frame.world := by decide
example : evalRvalue frame (.mulUsizeUB .unit (.usize 2)) = .invalid frame.world := by decide
example : evalRvalue frame (.recordResult 7 true (.use (.usize 8) false)) =
    .value (.record 7 (.pair (.scalar (.usize 8)) (.scalar .unit))) frame := by decide
example : evalRvalue frame (.recordResult 4 false .unit) = .value (.record 4 (.scalar .unit)) frame := by decide
example : evalRvalue frame (.recordResult 4 false (.use (.usize 8) false)) = .invalid frame.world := by decide
example : evalRvalue frame (.recordResult 7 true (.mulUsizeUB (.usize ⟨2^63,by decide⟩) (.usize 2))) = .invalid frame.world := by decide
example : enumWordValue 12 (.enumeration 12 8) = some (.scalar (.usize 8)) := by decide
example : enumWordValue 12 (.enumeration 13 8) = none := by decide
example : evalRvalue frame (.enumWord .unit 12) = .invalid frame.world := by decide
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 128 ⟨16,8⟩),.raw (.writeBytes 0 8 (List.replicate 16 0)),
     .borrow 0 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty
example : ready.nextTag = 1 := by decide
example : (match NativeRawVecReference.eval ready (.reference false ⟨0⟩ 2) .marker with
    | .value value next => (value,next.outputs,next.pointers.registers.length,next.pointers.heap == ready.pointers.heap)
    | _ => (.usize 99,[],99,false)) = (.unit,[[]],2,true) := by decide
example : NativeRawVecReference.eval ready (.reference false ⟨99⟩ 2) .marker = .invalid ready := by decide
private def receiver : Frame := ⟨[.scalar (.reference false)],
  [.live (some (.scalar (.reference false ⟨0⟩ 2)))],ready⟩
example : (match evalRvalue receiver (.recordResult 4 false (.rawVecField .marker (.copy 0) true)) with
    | .value value next => (value,next.world.outputs,next.world.pointers.registers.length)
    | _ => (.uninit,[],99)) = (.record 4 (.scalar .unit),[[]],2) := by decide

end FormalProof4FHETest.HasteBootsCurrentMemoryOpsSmoke
