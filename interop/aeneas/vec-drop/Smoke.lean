namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeRecordDropCalls
open NativeRecordLLBC (Flow)

private def world (cap length : NativeWord64Memory.Word) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.writeBytes 0 1 (List.replicate 8 0)),
     .raw (.allocate 128 ⟨24,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode cap)),
     .raw (.withAddress 0 136),.raw (.store 0 2),.raw (.withAddress 1 144),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode length)),.borrow 2 .exclusive ⟨24,8⟩]).getD NativeReferenceMachine.empty

syntax "run_vec_drop" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
| `(tactic| run_vec_drop) => do
  let target ← getMainTarget
  let args := target.getAppArgs
  let code ← whnf args[0]!
  match code.getAppFn.constName! with
  | ``Code.done => evalTactic (← `(tactic| exact Runs.done _))
  | ``Code.scope => evalTactic (← `(tactic| apply Runs.scopeNext; run_vec_drop; (first | rfl | (simp [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom]; rfl)); run_vec_drop))
  | ``Code.native =>
    let result ← whnf (← mkAppM ``NativeRecordLLBC.eval #[code.getAppArgs[0]!,args[1]!])
    if result.getAppFn.constName! == ``NativeRecordLLBC.Flow.normal then
      evalTactic (← `(tactic| apply Runs.nativeNext; rfl; run_vec_drop))
    else evalTactic (← `(tactic| apply Runs.nativeStop; rfl; decide))
  | ``Code.call => evalTactic (← `(tactic| apply Runs.callNext; rfl; run_vec_drop; (first | rfl | (simp [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom]; rfl)); run_vec_drop))
  | ``Code.loop =>
    let normalized ← reduce args[1]!
    let goal ← getMainGoal
    let changed ← goal.change (mkAppN target.getAppFn #[args[0]!,normalized,args[2]!])
    replaceMainGoal [changed]
    evalTactic (← `(tactic| apply HasteBootsVecDrop.loop_complete; rfl; simp [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom]; try decide))
  | _ => throwError "Unknown retained code node"

example : (world 8 3).nextTag = 1 := by decide
example : ∃ flow, Invokes f1 (world 8 3) [.vectorExclusiveReference 0] flow ∧
    (match flow with | .returned (.scalar .unit) _ => true | _ => false) = true ∧
    flow.world.nextTag = 15 ∧ flow.world.leases.map NativeByteBorrow.Lease.tag = [0] ∧
    flow.world.pointers.heap.memory.blocks.length = 1 ∧ flow.world.outputs.length = 4 := by
  econstructor
  constructor
  · apply Invokes.run [.scalar (.reference true ⟨0⟩ 3)]
    · decide
    · rfl
    · run_vec_drop
  · decide

example : ∃ flow, Invokes f1 (world 0 0) [.vectorExclusiveReference 0] flow ∧
    (match flow with | .returned (.scalar .unit) _ => true | _ => false) = true ∧
    flow.world.nextTag = 8 ∧ flow.world.leases.map NativeByteBorrow.Lease.tag = [0] ∧
    flow.world.pointers.heap = (world 0 0).pointers.heap ∧ flow.world.outputs.length = 2 := by
  econstructor
  constructor
  · apply Invokes.run [.scalar (.reference true ⟨0⟩ 3)]
    · decide
    · rfl
    · run_vec_drop
  · decide

example : ∃ flow, Invokes f1 (world 8 0) [.vectorExclusiveReference 0] flow ∧
    (match flow with | .returned (.scalar .unit) _ => true | _ => false) = true ∧
    flow.world.nextTag = 9 ∧ flow.world.leases.map NativeByteBorrow.Lease.tag = [0] ∧
    flow.world.pointers.heap.memory.blocks.length = 1 ∧ flow.world.outputs.length = 4 := by
  econstructor
  constructor
  · apply Invokes.run [.scalar (.reference true ⟨0⟩ 3)]
    · decide
    · rfl
    · run_vec_drop
  · decide

syntax "run_vec_rejected" : tactic
macro_rules
  | `(tactic| run_vec_rejected) => `(tactic|
  first
  | exact Runs.done _
  | (apply Runs.nativeStop; rfl; decide)
  | (apply Runs.nativeNext; rfl; run_vec_rejected)
  | (apply Runs.scopeStop; run_vec_rejected; rfl; decide)
  | (apply Runs.scopeNext; run_vec_rejected; rfl; run_vec_rejected)
  | (apply Runs.callStopped; rfl; run_vec_rejected; rfl)
  | (apply Runs.callNext; rfl; run_vec_rejected; rfl; run_vec_rejected))

example : ∃ flow, Invokes f1 (world 8 9) [.vectorExclusiveReference 0] flow ∧
    (match flow with | .invalid _ => true | _ => false) = true ∧
    flow.world.nextTag = 2 ∧ flow.world.pointers.heap = (world 8 9).pointers.heap ∧
    flow.world.leases.map NativeByteBorrow.Lease.tag = [1,0] := by
  econstructor
  constructor
  · apply Invokes.run [.scalar (.reference true ⟨0⟩ 3)]
    · decide
    · rfl
    · run_vec_rejected
  · decide

example : Invokes f1 (world 8 3) [.vectorSharedReference 0] (.invalid (world 8 3)) :=
  .argumentsInvalid (by decide)
example : Invokes f1 (world 8 3) [.vectorExclusiveReference 99] (.invalid (world 8 3)) :=
  .argumentsInvalid (by decide)
example : f3.classification = .foreignBody := rfl
end HasteBootsVecDrop.Smoke
