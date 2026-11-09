module
import FormalProof4FHE.HasteBoots.PrivateCoinByteFailure
import all FormalProof4FHETest.HasteBootsPrivateCoinExecutableSmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction initialise take)
open PrivateCoinByteLineage (history)
namespace HasteBootsPrivateCoinLineageSmoke
noncomputable section

def empty : ClosedByteMachine.Tape → Input := fun _ => []
def tape : Tape := fun index => if index = 0 then 7 else 8

def code : List Instruction :=
  [.base (.constant 1 9), .base (.push 0 1), .base (.hash 0 2), .coin 0,
   .base (.push 1 0), .base (.start 1), .base (.read 1 3 99 0), .coin 2,
   .base (.read 1 3 71 2), .base (.read 1 3 71 2), .base .halt]

-- The generic clock resumes a silent instruction's returned state.
example (world : World) :
    (OracleProgram.run (InstructionClock.take (fun state : ℕ => .done (state+1)) 3 0) world).run.1 = 3 := by rfl

-- Coin instructions do not become SHAKE exposures.
example (world : World) : CausalStreamExposure.firstRead (PrivateCoinByteRequest.command code [] tape)
    (history code [] empty tape 3 world).run = none := by rfl
example (world : World) : CausalStreamExposure.firstRead (PrivateCoinByteRequest.command code [] tape)
    (history code [] empty tape 6 world).run = none := by rfl
example (world : World) : CausalStreamExposure.firstRead (PrivateCoinByteRequest.command code [] tape)
    (history code [] empty tape 7 world).run = none := by rfl

-- Eight instructions precede the first positive read, but only three mixed
-- observations do. The SHA-512 prequery and zero-length read remain present.
example (world : World) : (history code [] empty tape 8 world).run.2 =
    [.hash [9] (List.ofFn (InputIndexedOracle.sha512 world [9])), .start [7], .output [7] 99 []] := by rfl
example (world : World) : CausalStreamExposure.firstRead (PrivateCoinByteRequest.command code [] tape)
    (history code [] empty tape 8 world).run = some [7] := by rfl
example (world : World) : CausalStreamExposure.firstRead (PrivateCoinByteRequest.command code [] tape)
    (history code [] empty tape 9 world).run = none := by rfl
example (world : World) :
    (OracleProgram.run (take code [] tape 8 (initialise code empty)) world).run.1.cursor = 2 := by rfl

-- The lineage theorem recovers the earlier full history at an actual
-- instruction boundary; it does not substitute the observation count.
example (world : World) : ∃ index < 10,
    CausalStreamExposure.firstRead (PrivateCoinByteRequest.command code [] tape)
      (history code [] empty tape index world).run = some [7] ∧
    CausalFirstStreamPrefix.recover [7] (history code [] empty tape 10 world).run.2 =
      some (history code [] empty tape index world).run.2 ∧
    ∃ offset values after, values ≠ [] ∧
      (history code [] empty tape 10 world).run.2 =
        (history code [] empty tape index world).run.2 ++ .output [7] offset values :: after := by
  apply PrivateCoinByteLineage.coverage
  rfl

-- Resuming after the first read preserves its inherited exposure instead of
-- creating a new first-read charge on the repeated query.
example (world : World) : CausalStreamExposure.seen
    (InstructionClock.history (fun oracle => OracleProgram.run (take code [] tape 9 (initialise code empty)) oracle)
      (PrivateCoinByteRequest.command code [] tape) 1 world).run.2 [7] = true := by rfl

open HasteBootsPrivateCoinExecutableSmoke (target dummy)
example : MeasurableSet {execution | PrivateCoinByteFailure.Failure Unit code [] empty dummy target execution} :=
  PrivateCoinByteFailure.failure_measurable Unit code [] empty dummy target
example (execution : Tape × World)
    (failed : PrivateCoinByteFailure.Failure Unit code [] empty dummy target execution) :
    PrivateCoinByteFailure.Hazards code [] empty dummy target execution :=
  PrivateCoinByteFailure.failure_covered Unit code [] empty dummy target execution failed

-- The measurable event can be averaged without any union factor for coins.
-- Pricing the per-tape failure probability is still a separate obligation.
example (coins : Measure Tape) (charge : Tape → ENNReal)
    (conditional : ∀ random, law {world | PrivateCoinByteFailure.Failure Unit code [] empty dummy target (random,world)} ≤ charge random) :
    (coins.prod law) {execution | PrivateCoinByteFailure.Failure Unit code [] empty dummy target execution} ≤
      ∫⁻ random, charge random ∂coins :=
  PrivateCoinLifetime.independent_bound coins _
    (PrivateCoinByteFailure.failure_measurable Unit code [] empty dummy target) charge conditional
end
end HasteBootsPrivateCoinLineageSmoke
