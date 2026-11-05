module

import all FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw
import all Mathlib.Data.List.Sort

open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleSpec OracleComp

namespace HasteBootsHistoryCompositionSmoke

def input : Input := [7,9]
def world : World
  | .inl (_,offset) => if offset = 3 then 41 else if offset = 4 then 88 else 0
  | .inr _ => 0

def past : OracleProgram.Program Input :=
  .read input 3 2 (fun values => .hash input (fun _ => .pure values))

def mixed : OracleProgram.Program Input :=
  .start input (.read input 2 3 (fun first =>
    .hash input (fun digest => .read input (digest 0).val 1 (fun last => .pure (first++last)))))

example : (OracleProgram.run mixed world).run.1 = [0,41,88,0] := by decide +kernel
example : (OracleProgram.run mixed world).run.2.length = 4 := by decide +kernel
example : (OracleProgram.runPrefix 2 mixed world).run.2.length = 2 := by decide +kernel
example : OracleProgram.nextRequest (OracleProgram.runPrefix 2 mixed world).run.1 = some (.hash input) := by
  decide +kernel
example : (OracleHistorySnapshot.read (OracleProgram.run past) input 2 3 world).run.1.2 = [0,41,88] := by
  decide +kernel
example : (OracleHistorySnapshot.hash (OracleProgram.run past) input world).run.2.length = 3 := by
  decide +kernel
example : NativeShakeKernel.observed
    (OracleHistorySnapshot.read (OracleProgram.run past) input 2 3 world).run.2 world (input,2) = some 0 := by
  decide +kernel
example : NativeShakeKernel.observed
    (OracleHistorySnapshot.hash (OracleProgram.run past) input world).run.2 world (input,2) = none := by
  decide +kernel
example : NativeShakeKernel.observed
    (OracleHistorySnapshot.hash (OracleProgram.run past) input world).run.2 world (input,3) = some 41 := by
  decide +kernel
example : NativeShakeKernel.observed
    (OracleHistorySnapshot.read (OracleProgram.run past) input 2 3 world).run.2 world ([7,9,0],3) = none := by
  decide +kernel

noncomputable section
open MeasureTheory ProbabilityTheory

/-- Arbitrary predicates may inspect the full adaptive result and ordered log. -/
example {Cfg Payload : Type} (enc : MerkleOracle.Encoding Input NativeRootMessage.Digest Payload)
    (dummy : NativeRootMessage.Digest) (shape : Cfg → BinaryTree.Skeleton)
    (event : Input × List NativeTranscript.Observation → Prop) :
    InputIndexedOracle.law {other | event (OracleProgram.run mixed other).run} =
      Pr{let result ← (NativeLazyExecution.execute enc dummy shape mixed NativeShakeCache.empty
        (CheckpointExecution.empty shape))}[event result] :=
  NativeLazyExecutionLaw.from_empty mixed enc dummy shape event

/-- The actual prequery history supplies both initial caches. The event may
inspect any final byte-cache coordinate as well as the complete result/log. -/
example {Cfg Payload : Type} (enc : MerkleOracle.Encoding Input NativeRootMessage.Digest Payload)
    (dummy : NativeRootMessage.Digest) (shape : Cfg → BinaryTree.Skeleton)
    (event : (Input × List NativeTranscript.Observation) × NativeShakeCache.Cache → Prop) :
    (InputIndexedOracle.law[|{other | (OracleProgram.run past other).run = (OracleProgram.run past world).run}])
      {other | event ((OracleProgram.run mixed other).run,
        NativeShakeKernel.observed ((OracleProgram.run past other).run.2 ++
          (OracleProgram.run mixed other).run.2) other)} =
      Pr{let result ← (NativeLazyExecution.executeWithCache enc dummy shape mixed
        (NativeShakeKernel.observed (OracleProgram.run past world).run.2 world)
        { (CheckpointExecution.empty shape) with hash := JointHashCache.project (OracleProgram.run past world).run.2 })}[event result] :=
  NativeLazyExecutionLaw.cache_law mixed (OracleProgram.run_replay past) world enc dummy shape _ rfl event

end
end HasteBootsHistoryCompositionSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.output_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.output_coordinate

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.bytes_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.bytes_cons

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.write_world_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.write_world_lookup

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.observed_append_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.observed_append_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.observed_append_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.observed_append_start

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.observed_append_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.observed_append_hash

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.record_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.record_observed

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.fold_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.fold_observed

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.observed_of_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.observed_of_fiber

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.conditional_event_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.conditional_event_congr

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeProjection.read_event_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeProjection.read_event_observed

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistoryComposition.measure_sum_fibers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistoryComposition.measure_sum_fibers

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistoryComposition.average_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistoryComposition.average_event

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistoryComposition.refinement_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistoryComposition.refinement_event

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistorySnapshot.snapshot_replay' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistorySnapshot.snapshot_replay

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistorySnapshot.read_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistorySnapshot.read_replay

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistorySnapshot.read_run' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistorySnapshot.read_run

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistorySnapshot.hash_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistorySnapshot.hash_replay

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistorySnapshot.hash_run' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistorySnapshot.hash_run

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistorySnapshot.read_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistorySnapshot.read_average

/-- info: 'FormalProof4FHE.HasteBoots.OracleHistorySnapshot.hash_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleHistorySnapshot.hash_average

/-- info: 'FormalProof4FHE.HasteBoots.OracleKernelComposition.read_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleKernelComposition.read_score

/-- info: 'FormalProof4FHE.HasteBoots.OracleKernelComposition.read_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleKernelComposition.read_transfer

/-- info: 'FormalProof4FHE.HasteBoots.OracleKernelComposition.hash_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleKernelComposition.hash_score

/-- info: 'FormalProof4FHE.HasteBoots.OracleKernelComposition.hash_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleKernelComposition.hash_transfer

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecution.execute_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecution.execute_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecution.hash_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecution.hash_step

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecution.execute_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecution.execute_hash

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecution.execute_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecution.execute_pure

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecution.execute_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecution.execute_start

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecution.executeWithCache_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecution.executeWithCache_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw.execute_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw.execute_law

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw.prefix_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw.prefix_law

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw.from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw.from_empty

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw.cache_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw.cache_law
