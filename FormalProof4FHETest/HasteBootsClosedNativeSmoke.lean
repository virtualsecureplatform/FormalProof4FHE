module
import all FormalProof4FHE.HasteBoots.ClosedByteMachineNativeSoundness
import all FormalProof4FHETest.HasteBootsClosedMachineSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open ClosedByteMachine (Instruction Tape)
namespace HasteBootsClosedNativeSmoke
noncomputable section
open HasteBootsClosedMachineSmoke (delayed empty)

-- The packet lineage has four silent/start instructions before exposure,
-- whereas its earlier observation prefix contains only one start.
example (world : World) : ∃ index < 5,
    CausalStreamExposure.firstRead (ClosedByteMachineRequest.command delayed [])
      (ClosedByteMachineGoldRisk.history delayed [] empty index world).run = some [1] ∧
    CausalFirstStreamPrefix.recover [1] (ClosedByteMachineGoldRisk.history delayed [] empty 5 world).run.2 =
      some (ClosedByteMachineGoldRisk.history delayed [] empty index world).run.2 ∧
    ∃ offset values after, values ≠ [] ∧
      (ClosedByteMachineGoldRisk.history delayed [] empty 5 world).run.2 =
        (ClosedByteMachineGoldRisk.history delayed [] empty index world).run.2 ++ .output [1] offset values :: after := by
  apply ClosedByteMachineLineage.coverage
  rfl

open HasteBootsCalibrationSmoke (ctx tables constructed primitive compatible)
open HasteBootsBatchMeaningSmoke (usize)
def dummy : NativeRootMessage.Digest := fun _ => 0

-- Constructor-backed numerical fixture; no complete native PBS run is asserted.
example (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (world : World)
    (failed : ClosedByteMachineNativeSoundness.Failure Memory code publicData privateData dummy ctx .helper world) :
    ClosedByteMachineGoldAllRisk.Failure code publicData dummy ctx primitive .helper ctx.parent.profile privateData world :=
  ClosedByteMachineNativeSoundness.failure_covered Memory code publicData privateData dummy ctx .helper tables
    (usize 2048) (usize 4) (usize 2) constructed primitive compatible world failed

example (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input) :
    MeasurableSet {world | ClosedByteMachineNativeSoundness.Failure Memory code publicData privateData dummy ctx .helper world} :=
  ClosedByteMachineNativeSoundness.failure_measurable Memory code publicData privateData dummy ctx .helper

example (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input) :
    (2 : ENNReal)^128 * InputIndexedOracle.law
      {world | ClosedByteMachineNativeSoundness.Failure Memory code publicData privateData dummy ctx .helper world} ≤
        (9/4096 : ENNReal)*ClosedByteMachineWork.expectedWork code publicData privateData :=
  ClosedByteMachineNativeSoundness.scaled_lifetime_le_work Memory code publicData privateData dummy ctx .helper tables
    (usize 2048) (usize 4) (usize 2) constructed primitive compatible
end
end HasteBootsClosedNativeSmoke
