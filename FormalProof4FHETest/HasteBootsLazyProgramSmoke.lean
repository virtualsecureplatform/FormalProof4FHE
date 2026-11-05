module

import all FormalProof4FHE.HasteBoots.NativeLazyProgram

open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Byte Input)
open OracleSpec OracleComp

namespace HasteBootsLazyProgramSmoke

def saved : NativeShakeCache.Cache := fun key =>
  if key.1 = [7,9] then
    if key.2 = 3 then some 41 else if key.2 = 4 then some 88 else none
  else none

example : saved ([7,9],3) = some 41 := by decide +kernel
example : saved ([7,9],4) = some 88 := by decide +kernel
example : saved ([7,9],5) = none := by decide +kernel
example : saved ([7],3) = none := by decide +kernel
example : saved ([7,9,0],3) = none := by decide +kernel
example : NativeShakeCache.empty ([7,9],3) = none := by decide +kernel

example : Function.update saved ([7,9],5) (some 17) ([7,9],3) = some 41 := by
  decide +kernel
example : Function.update saved ([7,9],5) (some 17) ([7,9],5) = some 17 := by
  decide +kernel

def twoReads : OracleProgram.Program Input :=
  .read [7,9] 3 2 (fun _ => .read [7,9] 4 2 (fun bytes => .pure bytes))

def zeroWorld : InputIndexedOracle.World := fun _ => 0

example : OracleProgram.nextRequest
    (OracleProgram.run (NativeProgramPrefix.take 0 twoReads) zeroWorld).run.1 =
    some (.read [7,9] 3 2) := by decide +kernel

example : OracleProgram.nextRequest
    (OracleProgram.run (NativeProgramPrefix.take 1 twoReads) zeroWorld).run.1 =
    some (.read [7,9] 4 2) := by decide +kernel

example : OracleProgram.nextRequest
    (OracleProgram.run (NativeProgramPrefix.take 2 twoReads) zeroWorld).run.1 = none := by
  decide +kernel

example : (OracleProgram.run (NativeProgramPrefix.take 1 twoReads) zeroWorld).run.2 =
    [.output [7,9] 3 [0,0]] := by decide +kernel

noncomputable section

example : (NativeShakeCache.byte (Cfg := Unit) ([7,9],3)).run saved = pure (41,saved) :=
  NativeShakeCache.byte_cached saved _ _ (by decide +kernel)

example : (NativeShakeCache.read (Cfg := Unit) [7,9] 3 2).run saved =
    pure ([41,88],saved) := by
  have result := NativeShakeCache.read_cached (Cfg := Unit) [7,9] 3 2 saved
    (fun index => if index = 0 then 41 else 88) (by
      intro index bounded
      interval_cases index <;> decide +kernel)
  exact result

/-- The compiler actually consumes the retained prequery answers. -/
example : (NativeLazyProgram.compile (Cfg := Unit)
    (.read [7,9] 3 2 (fun bytes => .pure bytes))).run saved =
    pure (([41,88],[.output [7,9] 3 [41,88]]),saved) := by
  have cached := NativeShakeCache.read_cached (Cfg := Unit) [7,9] 3 2 saved
    (fun index => if index = 0 then 41 else 88) (by
      intro index bounded
      interval_cases index <;> decide +kernel)
  simp only [NativeLazyProgram.compile,StateT.run_bind,cached,pure_bind,
    StateT.run_pure,map_pure,NativeCheckpointProgram.prepend]
  rfl

end
end HasteBootsLazyProgramSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.byte_cached' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.byte_cached

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.read_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.read_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.byte_fresh' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.byte_fresh

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.update_preserves' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.update_preserves

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.read_cached' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.read_cached

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.read_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.read_split

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.byte_supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.byte_supported

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.read_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.read_preserves

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyProgram.compile_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyProgram.compile_bind

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyProgram.compile_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyProgram.compile_preserves

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.read_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.read_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeShakeCache.read_again' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeShakeCache.read_again

/-- info: 'FormalProof4FHE.HasteBoots.NativeProgramPrefix.take_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeProgramPrefix.take_run

/-- info: 'FormalProof4FHE.HasteBoots.NativeProgramPrefix.take_resume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeProgramPrefix.take_resume

/-- info: 'FormalProof4FHE.HasteBoots.NativeLazyProgram.compile_resume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeLazyProgram.compile_resume
