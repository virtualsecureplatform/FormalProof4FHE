module

import all FormalProof4FHE.HasteBoots.NativeGoldPcsExecutionAgrees
import all FormalProof4FHE.HasteBoots.NativeCheckpointProgram
import all FormalProof4FHE.HasteBoots.OracleProgram
import all FormalProof4FHE.HasteBoots.ObservationReplay

open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp

namespace NativeCheckpointSmoke
private noncomputable def byte (n : ℕ) : InputIndexedOracle.Byte := ⟨n % 256,Nat.mod_lt _ (by decide)⟩
private noncomputable def actual : InputIndexedOracle.World
  | .inl (input,offset) => byte (input.length+offset)
  | .inr (input,index) => byte (input.length+index.val)
-- Test interpretation; the production support proof uses the canonical cache.
private noncomputable def handler :
    QueryImpl (CheckpointExecution.Spec unifSpec Unit InputIndexedOracle.Input NativeRootMessage.Digest)
      NativeTranscript.Execution := fun request => match request with
  | .inl size => pure ⟨0,by omega⟩
  | .inr (.inl input) => ObservationReplay.hash actual input
  | .inr (.inr _) => pure ()
private noncomputable def script : OracleProgram.Program (List ℕ × ℕ) :=
  .start [byte 1] (.read [byte 1] 2 3 (fun output =>
    .hash output (fun answer => .pure (output.map Fin.val,(answer ⟨0,by decide⟩).val))))
private noncomputable def result :=
  (simulateQ handler (NativeCheckpointProgram.compile (InputIndexedOracle.shake actual) script)).run
example : result.1 = (OracleProgram.run script actual).run := by decide +kernel
example : result.1.1 = ([3,4,5],3) := by decide +kernel
example : result.2 = [.hash ([3,4,5].map byte)
    (List.ofFn (fun index : Fin 64 => byte (3+index.val)))] := by decide +kernel
end NativeCheckpointSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointProgram.world_reader' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointProgram.world_reader

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointProgram.world_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointProgram.world_hash

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointProgram.hash_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointProgram.hash_record

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointProgram.supported_hash_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointProgram.supported_hash_state

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointProgram.supported_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointProgram.supported_replay

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointProgram.supported_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointProgram.supported_actual

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointProgram.supported_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointProgram.supported_later

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsExecution.completed_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsExecution.completed_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsExecution.completed_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsExecution.completed_native

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsExecution.accepted_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsExecution.accepted_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsExecution.accepted_workers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsExecution.accepted_workers

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsExecutionAgrees.accepted_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsExecutionAgrees.accepted_agrees
