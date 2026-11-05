module

import all FormalProof4FHE.HasteBoots.OracleSeedGuessing
import all FormalProof4FHE.HasteBoots.OracleMachineExposure
import all Mathlib.Data.List.Sort
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte World)
open MeasureTheory ProbabilityTheory
namespace HasteBootsFirstExposureSmoke

def input : Input := [7,9]
def otherInput : Input := [7,9,0]
def log : List NativeTranscript.Observation :=
  [.start input,.output input 0 [],.hash input (List.replicate 64 0),.output input 80 [7],
    .output otherInput 0 [5],.output input 63 [41,88],.output input 0 [9]]

example : OracleFirstExposure.locate log (OracleFirstExposure.seedCoordinates input) = some 5 := by decide +kernel
example : OracleFirstExposure.locate (log.take 5) (OracleFirstExposure.seedCoordinates input) = none := by decide +kernel
example : OracleFirstExposure.locate (log++[.output input 1 [8]])
    (OracleFirstExposure.seedCoordinates input) = some 5 := by decide +kernel
example : OracleFirstExposure.locate [.start input,.output input 0 [],.hash input (List.replicate 64 0)]
    (OracleFirstExposure.seedCoordinates input) = none := by decide +kernel
example : OracleFirstExposure.locate [.output otherInput 0 [9]]
    (OracleFirstExposure.seedCoordinates input) = none := by decide +kernel
example : OracleFirstExposure.locate [.output input 64 [9]]
    (OracleFirstExposure.seedCoordinates input) = none := by decide +kernel
example : OracleFirstExposure.locate [.output input 63 [9]]
    (OracleFirstExposure.seedCoordinates input) = some 0 := by decide +kernel
example : OracleFirstExposure.locate [.output input 62 [8,9,10]]
    (OracleFirstExposure.seedCoordinates input) = some 0 := by decide +kernel

noncomputable section
open scoped Classical

def zero : Fin 2 → Byte := fun _ => 0

def bad : Fin 2 → Byte := fun index => if index = 0 then 1 else 0

example : Fintype.card {raw : Fin 2 → Byte // OracleMaskCounting.mask {0} zero raw = zero} = 256 := by
  rw [OracleMaskCounting.fiber_card]
  simp [OracleMaskCounting.compatible,zero]
example : Fintype.card {raw : Fin 2 → Byte // OracleMaskCounting.mask {0} zero raw = bad} = 0 := by
  rw [OracleMaskCounting.fiber_card]
  simp [OracleMaskCounting.compatible,zero,bad]

example : ((uniformOn (Set.univ : Set (Fin 2 → Byte))).map (OracleMaskCounting.mask {0} zero))
    ({zero} : Set (Fin 2 → Byte)) = 1/256 := by
  simpa [Finset.filter_singleton,OracleMaskCounting.compatible,zero] using OracleMaskCounting.targets_probability {0} zero {zero}

example : ((uniformOn (Set.univ : Set (Fin 2 → Byte))).map (OracleMaskCounting.mask {0} zero))
    ({bad} : Set (Fin 2 → Byte)) = 0 := by
  simpa [Finset.filter_singleton,OracleMaskCounting.compatible,zero,bad] using OracleMaskCounting.targets_probability {0} zero {bad}

example : ((uniformOn (Set.univ : Set (Fin 2 → Byte))).map (OracleMaskCounting.mask ∅ zero))
    ({zero} : Set (Fin 2 → Byte)) = 1/65536 := by
  have result := OracleMaskCounting.targets_probability ∅ zero {zero}
  norm_num [Finset.filter_singleton,OracleMaskCounting.compatible,zero] at result
  simpa only [one_div] using result

example : ((uniformOn (Set.univ : Set (Fin 2 → Byte))).map (OracleMaskCounting.mask Finset.univ zero))
    ({zero} : Set (Fin 2 → Byte)) = 1 := by
  simpa [Finset.filter_singleton,OracleMaskCounting.compatible,zero] using OracleMaskCounting.targets_probability Finset.univ zero {zero}

example : ((uniformOn (Set.univ : Set (Fin 2 → Byte))).map (OracleMaskCounting.mask Finset.univ zero))
    ({bad} : Set (Fin 2 → Byte)) = 0 := by
  simpa [Finset.filter_singleton,OracleMaskCounting.compatible,zero,bad] using OracleMaskCounting.targets_probability Finset.univ zero {bad}


def machine (state : ℕ) : OracleMachine.Command ℕ Unit :=
  if state = 0 then .hash input (fun _ => 1) else
  if state = 1 then .read input 80 1 (fun _ => 2) else
  if state = 2 then .read otherInput 0 1 (fun _ => 3) else
    .read input 63 1 (fun _ => state+1)

def world : World := fun _ => 0

example : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take machine 6 0) world).run.2
    (OracleFirstExposure.seedCoordinates input) = some 3 := by decide +kernel

example (targets : Finset NativeRootMessage.Digest) :
    (InputIndexedOracle.law[|{other | (OracleProgram.run (OracleMachine.take machine 3 0) other).run =
      (OracleProgram.run (OracleMachine.take machine 3 0) world).run}])
      {other | InputIndexedOracle.block other input 0 64 ∈ targets} =
      (targets.card : ENNReal)/(2 : ENNReal)^512 :=
  OracleMachineExposure.pre_exposure_targets machine 6 3 0 world input targets (by decide +kernel)

example : ∀ position : Fin 64, (.inl (input,position.val) : InputIndexedOracle.Coordinate) ∉
    ObservationReplay.footprint (OracleProgram.run (OracleMachine.take machine 3 0) world).run.2 :=
  OracleMachineExposure.pre_exposure_fresh machine 6 3 0 world input (by decide +kernel)

/-- A partial read may change pointwise risk, but its average retains the exact old risk. -/
example (targets : Finset (Fin 2 → Byte)) :
    (∫⁻ current, OracleSeedGuessing.risk
      (OracleHistorySnapshot.read (OracleProgram.run (OracleMachine.take machine 3 0)) input 0 1 current).run.2
        current input 0 2 targets ∂InputIndexedOracle.law[|{other |
          (OracleProgram.run (OracleMachine.take machine 3 0) other).run =
          (OracleProgram.run (OracleMachine.take machine 3 0) world).run}]) =
      OracleSeedGuessing.risk (OracleProgram.run (OracleMachine.take machine 3 0) world).run.2 world input 0 2 targets :=
  OracleSeedGuessing.risk_read_average (OracleProgram.run_replay _) world input 0 2 targets input 0 1

end
end HasteBootsFirstExposureSmoke

/-- info: 'FormalProof4FHE.HasteBoots.OracleMaskCounting.fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMaskCounting.fiber_card

/-- info: 'FormalProof4FHE.HasteBoots.OracleMaskCounting.targets_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMaskCounting.targets_card

/-- info: 'FormalProof4FHE.HasteBoots.OracleMaskCounting.targets_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMaskCounting.targets_probability

/-- info: 'FormalProof4FHE.HasteBoots.OracleSeedGuessing.mask_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleSeedGuessing.mask_eq

/-- info: 'FormalProof4FHE.HasteBoots.OracleSeedGuessing.target_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleSeedGuessing.target_law

/-- info: 'FormalProof4FHE.HasteBoots.OracleSeedGuessing.risk_read_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleSeedGuessing.risk_read_average

/-- info: 'FormalProof4FHE.HasteBoots.OracleSeedGuessing.risk_hash_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleSeedGuessing.risk_hash_average

/-- info: 'FormalProof4FHE.HasteBoots.OracleSeedGuessing.fresh_seed_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleSeedGuessing.fresh_seed_targets

/-- info: 'FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_none

/-- info: 'FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_some

/-- info: 'FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_append

/-- info: 'FormalProof4FHE.HasteBoots.OracleFirstExposure.seed_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleFirstExposure.seed_none

/-- info: 'FormalProof4FHE.HasteBoots.OracleFirstExposure.seed_before_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleFirstExposure.seed_before_fresh

/-- info: 'FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_preserved

/-- info: 'FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleFirstExposure.locate_lt

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachineExposure.log_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachineExposure.log_take

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachineExposure.log_length_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachineExposure.log_length_le

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachineExposure.pre_exposure_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachineExposure.pre_exposure_fresh

/-- info: 'FormalProof4FHE.HasteBoots.OracleMachineExposure.pre_exposure_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleMachineExposure.pre_exposure_targets
