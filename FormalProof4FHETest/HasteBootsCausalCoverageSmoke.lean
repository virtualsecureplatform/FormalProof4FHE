module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchCausalCoverage
import all FormalProof4FHETest.HasteBootsFieldProximitySmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (World)
open NativeTranscript (Observation Execution)
open OracleProgram (run)
namespace HasteBootsCausalCoverageSmoke
noncomputable section
open HasteBootsBatchMeaningSmoke (world root usize)
section Lineage
def key : InputIndexedOracle.Input := [42]
def prelude : OracleProgram.Program Unit := .hash [88] (fun _ => .start [9] (.pure ()))
def past (oracle : World) := run prelude oracle
def step (state : ℕ) : OracleMachine.Command ℕ Unit := match state with
  | 0 => .start key 1
  | 1 => .read key 0 0 (fun _ => 2)
  | 2 => .hash [77] (fun _ => 3)
  | 3 => .read key 999 1 (fun _ => 4)
  | 4 => .read key 0 8 (fun _ => 5)
  | _ => .done ()
def full := CausalExposureLifetime.history past (fun _ => 0) step 5 world
theorem touched : CausalStreamExposure.seen full.run.2 key = true := by decide +kernel
example : CausalStreamExposure.firstRead step (CausalExposureLifetime.history past (fun _ => 0) step 3 world).run = some key := by decide +kernel
example : CausalFirstStreamPrefix.recover key full.run.2 =
    some (CausalExposureLifetime.history past (fun _ => 0) step 3 world).run.2 := by decide +kernel
-- Starts, empty reads, and hashes survive in the exact prefix but do not expose it.
example : ∃ index < 5,
    CausalStreamExposure.firstRead step (CausalExposureLifetime.history past (fun _ => 0) step index world).run = some key ∧
    CausalFirstStreamPrefix.recover key full.run.2 = some (CausalExposureLifetime.history past (fun _ => 0) step index world).run.2 ∧
    ∃ offset values after, values ≠ [] ∧ full.run.2 =
      (CausalExposureLifetime.history past (fun _ => 0) step index world).run.2 ++ .output key offset values :: after := by
  obtain inherited | later := CausalStreamLineage.coverage past (fun _ => 0) step 5 world key touched
  · have unseen : CausalStreamExposure.seen (past world).run.2 key = false := by decide +kernel
    rw [unseen] at inherited
    contradiction
  · exact later

def partialPast (oracle : World) := run (OracleProgram.Program.read key 999 1 (fun _ => .pure ())) oracle
example : CausalStreamExposure.seen (partialPast world).run.2 key = true := by decide +kernel
example : CausalStreamExposure.firstRead step (CausalExposureLifetime.history partialPast (fun _ => 0) step 3 world).run = none := by decide +kernel
example : CausalStreamExposure.seen (partialPast world).run.2 key = true ∨ ∃ index < 5,
    CausalStreamExposure.firstRead step (CausalExposureLifetime.history partialPast (fun _ => 0) step index world).run = some key ∧
    CausalFirstStreamPrefix.recover key (CausalExposureLifetime.history partialPast (fun _ => 0) step 5 world).run.2 =
      some (CausalExposureLifetime.history partialPast (fun _ => 0) step index world).run.2 ∧
    ∃ offset values after, values ≠ [] ∧ (CausalExposureLifetime.history partialPast (fun _ => 0) step 5 world).run.2 =
      (CausalExposureLifetime.history partialPast (fun _ => 0) step index world).run.2 ++ .output key offset values :: after :=
  CausalStreamLineage.coverage partialPast (fun _ => 0) step 5 world key (by decide +kernel)
end Lineage
namespace ProgramMachine
-- Reify a finite native oracle program as a causal machine for integration testing.
def step {A : Type} : OracleProgram.Program A → OracleMachine.Command (OracleProgram.Program A) A
  | .pure value => .done value
  | .start input next => .start input next
  | .read input offset count next => .read input offset count next
  | .hash input next => .hash input next

theorem log {A : Type} (program : OracleProgram.Program A) (oracle : World) :
    (run (OracleMachine.take step (run program oracle).run.2.length program) oracle).run.2 = (run program oracle).run.2 := by
  induction program with
  | pure value => rfl
  | start input next ih =>
    change .start input :: (run (OracleMachine.take step (run next oracle).run.2.length next) oracle).run.2 = _
    rw [ih]
    rfl
  | read input offset count next ih =>
    change .output input offset (InputIndexedOracle.bytes oracle input offset count) ::
      (run (OracleMachine.take step (run (next (InputIndexedOracle.bytes oracle input offset count)) oracle).run.2.length
        (next (InputIndexedOracle.bytes oracle input offset count))) oracle).run.2 = _
    rw [ih]
    rfl
  | hash input next ih =>
    change .hash input (List.ofFn (InputIndexedOracle.sha512 oracle input)) ::
      (run (OracleMachine.take step (run (next (InputIndexedOracle.sha512 oracle input)) oracle).run.2.length
        (next (InputIndexedOracle.sha512 oracle input))) oracle).run.2 = _
    rw [ih]
    rfl
end ProgramMachine
section Native
open HasteBootsBatchMeaningSmoke (ctx primitive)
open HasteBootsNativeFinishingSmoke (work choose completion parent executed accepted)
open HasteBootsFirstFieldSourceSmoke (decoded parsed)
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

def nativePast (oracle : World) := run (NativeGoldBatchPcsProgram.program ctx choose 6 ()) oracle
theorem replay : ObservationReplay.Replayable nativePast := OracleProgram.run_replay _
def stopped (_ : Unit) : OracleMachine.Command Unit Unit := .done ()
def finished := CausalExposureLifetime.history nativePast (fun _ => ()) stopped 0 world
theorem nativeAccepted : NativeGoldBatchAnySourceRisk.Accepted world finished.run.2 ctx choose 6 () work := by
  refine ⟨?_,completion,parent,executed,accepted,?_⟩
  · exact ⟨HasteBootsFieldInputSmoke.parentFrames,by decide +kernel,HasteBootsRecoveredChallengeSmoke.parentValid,by decide +kernel⟩
  · change (nativePast world).run.2.Sublist ((nativePast world).run.2++[])
    simp

example : CausalStreamExposure.seen finished.run.2 (NativeGoldBatchColumnRequestLaw.input ctx work world) = true ∧
    CausalStreamExposure.seen finished.run.2 (NativeGoldBatchRandomLaw.phase work).pending.input = true :=
  NativeGoldBatchChallengeHistory.accepted_exposures ctx world work _ choose 6 () nativeAccepted
abbrev capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val := by decide +kernel

example (falseClaim : NativeGoldBatchCausalCoverage.FalseClaim root ctx primitive work decoded finished.run.2 capacity 0) :
    NativeGoldBatchCausalCoverage.Covered nativePast (fun _ => ()) stopped 0 world root ctx work decoded primitive 0 :=
  NativeGoldBatchCausalCoverage.accepted_coverage nativePast replay (fun _ => ()) stopped 0 world root ctx work ctx.tables
    (usize 2) (usize 4) (usize 2) HasteBootsBatchMeaningSmoke.constructed primitive choose 6 () decoded parsed (by decide +kernel)
    nativeAccepted capacity 0 (by decide +kernel) falseClaim

-- At zero machine fuel, actual native exposure is explicitly inherited.
example : CausalStreamExposure.seen (nativePast world).run.2 (NativeGoldBatchColumnRequestLaw.input ctx work world) = true :=
  (NativeGoldBatchChallengeHistory.accepted_exposures ctx world work _ choose 6 () nativeAccepted).1
-- The same native verifier also runs entirely after a clean causal prelude.
def clean (_ : World) : Execution Unit := pure ()
theorem cleanReplay : ObservationReplay.Replayable clean := ObservationReplay.pure_replay ()
def initial (_ : Unit) := NativeGoldBatchPcsProgram.program ctx choose 6 ()
def nativeFuel := (nativePast world).run.2.length
def causal := CausalExposureLifetime.history clean initial ProgramMachine.step nativeFuel world
theorem causalLog : causal.run.2 = (nativePast world).run.2 := by
  change [] ++ (run (OracleMachine.take ProgramMachine.step nativeFuel (initial ())) world).run.2 = _
  exact ProgramMachine.log _ world

theorem causalAccepted : NativeGoldBatchAnySourceRisk.Accepted world causal.run.2 ctx choose 6 () work := by
  rw [causalLog]
  exact nativeAccepted
example : CausalStreamExposure.seen (clean world).run.2 (NativeGoldBatchColumnRequestLaw.input ctx work world) = false := rfl
example (falseClaim : NativeGoldBatchCausalCoverage.FalseClaim root ctx primitive work decoded causal.run.2 capacity 0) :
    NativeGoldBatchCausalCoverage.Covered clean initial ProgramMachine.step nativeFuel world root ctx work decoded primitive 0 :=
  NativeGoldBatchCausalCoverage.accepted_coverage clean cleanReplay initial ProgramMachine.step nativeFuel world root ctx work ctx.tables
    (usize 2) (usize 4) (usize 2) HasteBootsBatchMeaningSmoke.constructed primitive choose 6 () decoded parsed (by decide +kernel)
    causalAccepted capacity 0 (by decide +kernel) falseClaim

end Native
end
end HasteBootsCausalCoverageSmoke
