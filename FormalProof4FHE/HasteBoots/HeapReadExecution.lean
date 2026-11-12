module
public import FormalProof4FHE.HasteBoots.HeapProofIdentityWork
public import FormalProof4FHE.HasteBoots.NativeResidentVec
@[expose] public section

/-! Every retained input read belongs to one successful original operation
sequence from empty memory. Later outputs cannot replace an earlier read. -/
namespace FormalProof4FHE.HasteBoots.HeapReadExecution
open NativeReferenceMachine (State Op)
open InputIndexedOracle (Input)

structure Execution where
  operations : List Op
  finalState : State
  executed : NativeReferenceMachine.run NativeReferenceMachine.empty operations = some finalState

theorem run_append (state : State) (first later : List Op) :
    NativeReferenceMachine.run state (first++later) =
      (NativeReferenceMachine.run state first).bind (fun middle => NativeReferenceMachine.run middle later) := by
  induction first generalizing state with
  | nil => rfl
  | cons op tail ih => simp only [List.cons_append,NativeReferenceMachine.run,ih,Option.bind_assoc]

theorem step_origin (execution : Execution) (earlierOps laterOps : List Op) (op : Op)
    (split : execution.operations = earlierOps++op::laterOps) :
    ∃ before after, NativeReferenceMachine.run NativeReferenceMachine.empty earlierOps = some before ∧
      NativeReferenceMachine.execute before op = some after ∧
      NativeReferenceMachine.run after laterOps = some execution.finalState ∧
      NativeReferenceMachine.run NativeReferenceMachine.empty (earlierOps++[op]) = some after := by
  have ran := execution.executed
  rw [split,run_append] at ran
  obtain ⟨before,earlier,later⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨after,stepped,finished⟩ := Option.bind_eq_some_iff.mp later
  refine ⟨before,after,earlier,stepped,finished,?_⟩
  rw [run_append,earlier,Option.bind_some,NativeReferenceMachine.run,stepped,Option.bind_some,NativeReferenceMachine.run]

structure Observation (execution : Execution) (bytes : Input) where
  earlierOps : List Op
  laterOps : List Op
  reference : ℕ
  offset : ℕ
  size : ℕ
  alignment : ℕ
  split : execution.operations = earlierOps++(.access reference offset (.read size alignment))::laterOps
  output : (NativeReferenceMachine.run NativeReferenceMachine.empty
    (earlierOps++[.access reference offset (.read size alignment)])).bind (fun after => after.outputs.head?) = some bytes

variable {execution : Execution} {bytes : Input}

theorem Observation.origin (observation : Observation execution bytes) :
    ∃ before after pointer,
      NativeReferenceMachine.run NativeReferenceMachine.empty observation.earlierOps = some before ∧
      NativeReferenceMachine.execute before (.access observation.reference observation.offset (.read observation.size observation.alignment)) = some after ∧
      NativeReferenceMachine.run after observation.laterOps = some execution.finalState ∧
      NativeByteRange.loadRange before.pointers.heap.memory pointer ⟨observation.size,observation.alignment⟩ = some bytes ∧
      after.outputs = bytes :: before.outputs ∧ after.pointers.heap = before.pointers.heap := by
  obtain ⟨before,after,earlier,stepped,later,prefixRun⟩ := step_origin execution observation.earlierOps observation.laterOps _ observation.split
  obtain ⟨_,_,pointer,actual,_,_,_,loaded,outputs,heap⟩ := NativeResidentVec.access_read_observation _ _ _ _ _ _ stepped
  have output := observation.output
  rw [prefixRun,Option.bind_some,outputs,List.head?_cons] at output
  have same : actual = bytes := Option.some.inj output
  subst actual
  exact ⟨before,after,pointer,earlier,stepped,later,loaded,outputs,heap⟩

noncomputable def Observation.buffer (observation : Observation execution bytes) : ResidentMessageBounds.Buffer bytes :=
  let before := observation.origin.choose
  let pointer := observation.origin.choose_spec.choose_spec.choose
  ⟨before.pointers.heap.memory,pointer,⟨observation.size,observation.alignment⟩,
    observation.origin.choose_spec.choose_spec.choose_spec.2.2.2.1⟩

theorem Observation.length_eq (observation : Observation execution bytes) : bytes.length = observation.size :=
  NativeByteRange.loadRange_length _ _ _ _ observation.buffer.loaded

theorem Observation.fits (observation : Observation execution bytes) : bytes.length < TranscriptFrame.lengthLimit :=
  ResidentMessageBounds.fits observation.buffer

theorem Observation.prefix_reachable (observation : Observation execution bytes) :
    ∃ before, NativeReferenceMachine.run NativeReferenceMachine.empty observation.earlierOps = some before ∧
      NativeReferenceMachine.Reachable before := by
  obtain ⟨before,_,_,earlier,_,_,_,_,_⟩ := observation.origin
  exact ⟨before,earlier,NativeReferenceMachine.run_reachable NativeReferenceMachine.empty before .empty _ earlier⟩

end FormalProof4FHE.HasteBoots.HeapReadExecution
