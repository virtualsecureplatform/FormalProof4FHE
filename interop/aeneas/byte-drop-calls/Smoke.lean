namespace HasteBootsByteDropCallsSmoke
open FormalProof4FHE.HasteBoots
open NativeByteDropCalls HasteBootsByteDropProbe

private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0))]).getD NativeReferenceMachine.empty

-- This tactic constructs actual retained-code execution derivations. It does
-- not run a replacement implementation of the drop wrappers.
syntax "run_empty_drop" : tactic
macro_rules
  | `(tactic| run_empty_drop) => `(tactic|
  first
  | exact Runs.done _
  | (apply Runs.nativeStop; rfl; decide)
  | (apply Runs.nativeNext; rfl; run_empty_drop)
  | (apply Runs.callNext; rfl; run_empty_drop; rfl; run_empty_drop)
  | (apply HasteBootsByteDropProbe.loop_zero; rfl; rfl))

example : ∃ flow, Invokes f0 ready [.rawRegister 0,.usize ⟨0, by decide⟩] flow ∧
    flow.world.nextTag = 2 ∧ flow.world.leases = [] ∧ flow.world.pointers.heap = ready.pointers.heap := by
  econstructor
  constructor
  · apply Invokes.run
    · rfl
    · rfl
    · run_empty_drop
  · decide

syntax "run_three_drop" : tactic
macro_rules
  | `(tactic| run_three_drop) => `(tactic|
  first
  | exact Runs.done _
  | (apply Runs.nativeStop; rfl; decide)
  | (apply Runs.nativeNext; rfl; run_three_drop)
  | (apply Runs.callNext; rfl; run_three_drop;
      (first | rfl | (simp [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom]; rfl)); run_three_drop)
  | (apply HasteBootsByteDropProbe.loop_complete; rfl;
      simp [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom]; decide))

example : ∃ flow, Invokes f0 ready [.rawRegister 0,.usize ⟨3, by decide⟩] flow ∧
    flow.world.nextTag = 8 ∧ flow.world.leases = [] ∧ flow.world.pointers.heap = ready.pointers.heap := by
  econstructor
  constructor
  · apply Invokes.run
    · rfl
    · rfl
    · run_three_drop
  · decide

example : Invokes f0 ready [.rawRegister 99,.usize ⟨3, by decide⟩] (.invalid ready) :=
  .argumentsInvalid (by decide)

example : Invokes f0 ready [.usize ⟨0, by decide⟩,.usize ⟨3, by decide⟩] (.invalid ready) :=
  .initialInvalid _ (by rfl) (by rfl)

syntax "run_rejected_drop" : tactic
macro_rules
  | `(tactic| run_rejected_drop) => `(tactic|
  first
  | (apply Runs.nativeStop; rfl; decide)
  | (apply Runs.nativeNext; rfl; run_rejected_drop)
  | (apply Runs.callStopped; rfl; run_rejected_drop; rfl)
  | (apply Runs.callNext; rfl; run_rejected_drop; rfl; run_rejected_drop))

-- A valid raw pointer with an extent larger than the allocation reaches the
-- original borrow statement and fails there, before creating a lease.
example : Invokes f0 ready [.rawRegister 0,.usize ⟨9, by decide⟩] (.invalid ready) := by
  apply Invokes.run _ _ (.invalid ready)
  · rfl
  · rfl
  · run_rejected_drop

example : f3.classification = .foreignBody := rfl

end HasteBootsByteDropCallsSmoke
