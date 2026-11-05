module

import all FormalProof4FHE.HasteBoots.NativeLazyIndexExecution
import all Mathlib.Data.List.Sort
import all Init.Data.String.Defs

open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte World)
open OracleSpec OracleComp

namespace HasteBootsShakeKernelSmoke

def input : Input := [7,9]
def world : World
  | .inl (_,offset) => if offset = 0 then 7 else if offset = 3 then 41 else
      if offset = 4 then 88 else if offset = 8 then 5 else 0
  | .inr _ => 0

def log : List NativeTranscript.Observation :=
  [.output input 3 [41,88],.hash input (List.replicate 64 0)]


def past : OracleProgram.Program Input :=
  .read input 3 2 (fun bytes => .hash input (fun _ => .pure bytes))

example : (OracleProgram.run past world).run.2 = log := by decide +kernel

def before : NativeShakeCache.Cache := NativeShakeKernel.observed log world

example : before (input,3) = some 41 := by decide +kernel
example : before (input,4) = some 88 := by decide +kernel
example : before (input,0) = none := by decide +kernel
example : before ([7,9,0],3) = none := by decide +kernel

/-- SHA-512 observations never fill SHAKE coordinates, even at equal inputs. -/
example : NativeShakeKernel.observed [.hash input (List.replicate 64 0)] world (input,0) = none := by
  decide +kernel

example : NativeShakeKernel.install before (input,3) 199 (input,3) = some 41 := by decide +kernel
example : NativeShakeKernel.install before (input,5) 199 (input,5) = some 199 := by decide +kernel
example : NativeShakeKernel.install before (input,5) 199 (input,3) = some 41 := by decide +kernel
example : NativeShakeKernel.install before (input,5) 199 (input,6) = none := by decide +kernel

example : (NativeShakeReadLaw.eager input 3 (fun _ : Fin 4 => 17) before).1 = [41,88,17,17] := by
  decide +kernel
example : (NativeShakeReadLaw.eager input 3 (fun _ : Fin 4 => 17) before).2 (input,5) = some 17 := by
  decide +kernel
example : (NativeShakeReadLaw.eager input 3 (fun _ : Fin 4 => 17) before).2 (input,0) = none := by
  decide +kernel
example : (NativeShakeReadLaw.eager input 3 (fun _ : Fin 0 => 17) before).1 = [] := by decide +kernel

/-- Literal retained observations reconstruct repeated and overlapping writes. -/
example : NativeShakeHistory.writeBytes before input 4 [88,17,19] (input,3) = some 41 := by decide +kernel
example : NativeShakeHistory.writeBytes before input 4 [88,17,19] (input,4) = some 88 := by decide +kernel
example : NativeShakeHistory.writeBytes before input 4 [88,17,19] (input,6) = some 19 := by decide +kernel
example : (log ++ [NativeTranscript.Observation.output input 4 [88,17]]).foldl NativeShakeHistory.record NativeShakeCache.empty
    (input,5) = some 17 := by decide +kernel
example : NativeShakeHistory.record before (.start [4]) (input,3) = some 41 := by decide +kernel
example : NativeShakeHistory.record before (.hash input [1]) (input,0) = none := by decide +kernel

/-- The physical sampler uses no random query when both coordinates are cached. -/
example : NativeShakeReadLaw.sample input 3 2 before = pure ([41,88],before) := by
  have first : before (input,3) = some 41 := by decide +kernel
  have second : before (input,4) = some 88 := by decide +kernel
  simp only [NativeShakeReadLaw.sample,NativeShakeKernel.step,NativeShakeKernel.answer,
    NativeShakeKernel.install,first,second,map_pure,pure_bind]

def transcript : NativeTranscript.Transcript := NativeTranscript.new [1] (fun _ => 0)
def domain : NativeUsizeMessage.Usize := ⟨8,by decide⟩
def quota : NativeUsizeMessage.Usize := ⟨2,by decide⟩
def nativeInput : Input := NativePrequeryIndexLaw.requestInput transcript [3] domain quota

def partialCache : NativeShakeCache.Cache :=
  NativeShakeKernel.observed [.output nativeInput 0 [7]] world

def nativeResult (raw : Byte) := NativeLazyIndexExecution.decorate transcript [3] domain quota
  (NativeShakeReadLaw.eager nativeInput 0 (fun _ : Fin 16 => raw) partialCache)

/-- Real native framing/decoding retains the exposed low-byte draw. -/
example : (nativeResult 1).1.1.map (fun result => result.draws) = some [7,1] := by decide +kernel
example : (nativeResult 2).1.1.map (fun result => result.draws) = some [7,2] := by decide +kernel
example : (nativeResult 1).1.1.map (fun result => result.indices) = some [1,7] := by decide +kernel
example : (nativeResult 7).1.1.map (fun result => result.draws) = some [7,7] := by decide +kernel
example : (nativeResult 7).1.1.map (fun result => result.indices) = some [7] := by decide +kernel
example : (nativeResult 1).2 (nativeInput,0) = some 7 := by decide +kernel
example : (nativeResult 1).2 (nativeInput,8) = some 1 := by decide +kernel
example : (nativeResult 1).1.2.length = 2 := by decide +kernel

def invalid : NativeUsizeMessage.Usize := ⟨3,by decide⟩
example : (NativeLazyProgram.compile (Cfg := Unit)
    (NativeIndexRequest.request transcript [3] invalid quota)).run before = pure ((none,[]),before) := by
  rfl

end HasteBootsShakeKernelSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeKernel.reply_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeKernel.reply_law

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeKernel.shared_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeKernel.shared_step

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeKernel.reply_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeKernel.reply_event

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeKernel.step_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeKernel.step_event

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeKernel.observed_append_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeKernel.observed_append_byte

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeKernel.install_masked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeKernel.install_masked

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeKernel.install_other' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeKernel.install_other

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeHistory.byte_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeHistory.byte_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeHistory.read_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeHistory.read_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeHistory.compile_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeHistory.compile_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeHistory.simulated_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeHistory.simulated_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.shared_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.shared_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.answer_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.answer_dist

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.step_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.step_dist

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.eager_uniform_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.eager_uniform_succ

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.sample_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.sample_dist

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.eager_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.eager_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.eager_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.eager_bytes

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.observed_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.observed_mask

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.eager_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.eager_observed

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.read_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.read_event

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeReadLaw.shared_read_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeReadLaw.shared_read_event

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyIndexExecution.finish_ofFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyIndexExecution.finish_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyIndexExecution.compile_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyIndexExecution.compile_request

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyIndexExecution.invalid_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyIndexExecution.invalid_request

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyIndexExecution.request_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyIndexExecution.request_event
