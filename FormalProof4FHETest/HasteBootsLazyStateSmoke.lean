module

import all FormalProof4FHE.HasteBoots.OracleMachine
import all Mathlib.Data.List.Sort

open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory

namespace HasteBootsLazyStateSmoke

def input : Input := [7,9]
def world : World
  | .inl (_,offset) => if offset = 3 then 41 else 0
  | .inr _ => 0

def retry : Bool → OracleMachine.Command Bool Unit
  | false => .read input 3 1 (fun values => values.headD 0 == 41)
  | true => .hash input (fun _ => false)

example : (OracleProgram.run (OracleMachine.take retry 0 false) world).run = (.inl false,[]) := rfl
example : (OracleProgram.run (OracleMachine.take retry 1 false) world).run =
    (.inl true,[.output input 3 [41]]) := rfl
example : (OracleProgram.run (OracleMachine.take retry 2 false) world).run.1 = .inl false := by decide +kernel
example : (OracleProgram.run (OracleMachine.take retry 3 false) world).run.2 =
    [.output input 3 [41],.hash input (List.replicate 64 0),.output input 3 [41]] := by decide +kernel
example : (OracleProgram.run (OracleMachine.take retry 4 false) world).run.2.length = 4 := by decide +kernel
example : (OracleProgram.run (OracleMachine.take retry 3 false) (fun _ => 0)).run.2 =
    [.output input 3 [0],.output input 3 [0],.output input 3 [0]] := by decide +kernel

example : (OracleProgram.run (OracleMachine.take retry 1 false) world).run.2.IsPrefix
    (OracleProgram.run (OracleMachine.take retry 4 false) world).run.2 :=
  OracleMachine.log_prefix retry 1 4 (by decide) false world

example : OracleMachine.take retry 5 false = OracleProgram.bind (OracleMachine.take retry 2 false)
    (OracleMachine.resume retry 3) := OracleMachine.take_resume retry 2 3 false

def done : Bool → OracleMachine.Command Bool Unit := fun _ => .done ()
example : (OracleProgram.run (OracleMachine.take done 0 false) world).run = (.inr (),[]) := rfl
example : (OracleProgram.run (OracleMachine.take done 4 false) world).run = (.inr (),[]) := rfl

def finishes (state : ℕ) : OracleMachine.Command ℕ Unit :=
  if state = 2 then .done () else .start input (state+1)

example : (OracleProgram.run (OracleMachine.take finishes 1 0) world).run.1 = .inl 1 := by decide +kernel
example : (OracleProgram.run (OracleMachine.take finishes 2 0) world).run.1 = .inr () := by decide +kernel
example : (OracleProgram.run (OracleMachine.take finishes 7 0) world).run =
    (OracleProgram.run (OracleMachine.take finishes 2 0) world).run :=
  OracleMachine.completed_run finishes 2 5 0 world () (by decide +kernel)

noncomputable section
variable {Cfg Payload : Type} (enc : MerkleOracle.Encoding Input NativeRootMessage.Digest Payload)
  (dummy : NativeRootMessage.Digest) (shape : Cfg → BinaryTree.Skeleton)

/-- Completion at a zero-fuel boundary still returns the complete physical state. -/
example (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := NativeRootMessage.Digest) shape) :
    NativeLazyStateExecution.execute enc dummy shape (OracleMachine.take done 0 false) cache state =
      pure (((.inr (),[]),cache),state) :=
  NativeLazyStateExecution.execute_pure enc dummy shape _ cache state

/-- Repeated cache hits and reads still leave the entire checkpoint registry in place. -/
example (state : CheckpointExecution.State (Input := Input) (Digest := NativeRootMessage.Digest) shape) :
    ((OracleProgram.run (OracleMachine.take retry 4 false) world).run.2.foldl
      (NativeLazyStateExecution.record enc dummy shape) state).checkpoints = state.checkpoints :=
  NativeLazyStateExecution.fold_checkpoints enc dummy shape _ state

/-- A pre-existing loss is retained after every subsequent hash, including cached repeats. -/
example : ((OracleProgram.run (OracleMachine.take retry 4 false) world).run.2.foldl
      (NativeLazyStateExecution.record enc dummy shape)
      { (CheckpointExecution.empty shape) with failed := true }).failed = true :=
  NativeLazyStateExecution.fold_failed enc dummy shape _ _ rfl

/-- The final shared hash state is the canonical projection of the whole native log. -/
example : ((OracleProgram.run (OracleMachine.take retry 4 false) world).run.2.foldl
      (NativeLazyStateExecution.record enc dummy shape) (CheckpointExecution.empty shape)).hash =
    JointHashCache.project (OracleProgram.run (OracleMachine.take retry 4 false) world).run.2 := by
  simpa only [List.nil_append] using NativeLazyStateExecution.fold_project enc dummy shape []
    (OracleProgram.run (OracleMachine.take retry 4 false) world).run.2 (CheckpointExecution.empty shape) rfl

/-- No final cache or monitor field is discarded by the probability equality. -/
example (event : (((Bool ⊕ Unit) × List NativeTranscript.Observation) × NativeShakeCache.Cache) ×
    CheckpointExecution.State (Input := Input) (Digest := NativeRootMessage.Digest) shape → Prop) :
    InputIndexedOracle.law {other | event (((OracleProgram.run (OracleMachine.take retry 4 false) other).run,
      NativeShakeKernel.observed (OracleProgram.run (OracleMachine.take retry 4 false) other).run.2 other),
      (OracleProgram.run (OracleMachine.take retry 4 false) other).run.2.foldl
        (NativeLazyStateExecution.record enc dummy shape) (CheckpointExecution.empty shape))} =
      Pr{let result ← (NativeLazyStateExecution.execute enc dummy shape (OracleMachine.take retry 4 false)
        NativeShakeCache.empty (CheckpointExecution.empty shape))}[event result] :=
  NativeLazyStateExecution.from_empty _ enc dummy shape event

/-- A lifetime event in a genuinely nonterminating retry machine has no chosen query cutoff. -/
example (entry : NativeTranscript.Observation) :
    InputIndexedOracle.law {other | ∃ fuel, entry ∈ (OracleProgram.run (OracleMachine.take retry fuel false) other).run.2} =
      ⨆ fuel : ℕ, Pr{let result ← (NativeLazyStateExecution.execute enc dummy shape
        (OracleMachine.take retry fuel false) NativeShakeCache.empty (CheckpointExecution.empty shape))}[entry ∈ result.1.1.2] := by
  apply OracleMachine.lifetime_law retry false enc dummy shape (fun log => entry ∈ log)
  intro first later isPrefix member
  exact isPrefix.sublist.subset member

end
end HasteBootsLazyStateSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_pure

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_start

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_hash

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.shared_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.shared_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.fold_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.fold_hash

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.fold_checkpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.fold_checkpoints

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.fold_failed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.fold_failed

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.fold_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.fold_project

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_with_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.execute_with_cache

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.state_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.state_law

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.prefix_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.prefix_law

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyStateExecution.from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyStateExecution.from_empty

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachine.take_resume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachine.take_resume

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachine.log_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachine.log_prefix

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachine.compile_resume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachine.compile_resume

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachine.execute_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachine.execute_resume

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachine.conditional_lifetime_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachine.conditional_lifetime_law

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachine.lifetime_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachine.lifetime_law

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachine.completed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachine.completed_run

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachine.completion_lifetime_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachine.completion_lifetime_law

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachine.eventual_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachine.eventual_measurable
