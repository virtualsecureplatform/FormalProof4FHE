module
import FormalProof4FHE.HasteBoots.PrivateCoinClosedGoldRisk
import all FormalProof4FHETest.HasteBootsCalibrationSmoke
import all FormalProof4FHETest.HasteBootsPrivateCoinReplaySmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open PrivateCoinReplay (Tape)
open InputIndexedOracle (Byte Input World)
namespace HasteBootsPrivateCoinWorkSmoke
noncomputable section

-- A private result can vary while every oracle log is empty.
def localResult (tape : Tape) (_ : World) : NativeTranscript.Execution Byte := pure (tape 0)
theorem local_finite : PrivateCoinMachine.FiniteResult localResult := by
  intro tape world
  exact ⟨1, fun other same => congrArg (fun byte => (byte, [])) (same ⟨0, by decide⟩)⟩
example : Measurable (fun execution : Tape × World => ((localResult execution.1 execution.2).run.1.val : ENNReal)) :=
  PrivateCoinScores.score_measurable (fun tape => ObservationReplay.pure_replay (tape 0)) local_finite
    (fun result => (result.1.val : ENNReal))

-- Full-state scores also apply when later oracle responses choose new tape
-- coordinates, rather than only to finite private initialization.
example (fuel : ℕ) :
    Measurable (fun execution : Tape × World =>
      let result := CausalExposureLifetime.history
        (OracleProgram.run (HasteBootsPrivateCoinReplaySmoke.before execution.1)) id
        (HasteBootsPrivateCoinReplaySmoke.step execution.1) fuel execution.2
      (match result.run.1 with | .inl cursor => (cursor : ENNReal) | .inr _ => 0)) :=
  PrivateCoinScores.score_measurable
    (fun tape => CausalExposureLifetime.history_replay
      (OracleProgram.run_replay (HasteBootsPrivateCoinReplaySmoke.before tape)) id
      (HasteBootsPrivateCoinReplaySmoke.step tape) fuel)
    (PrivateCoinMachine.bind_finiteResult HasteBootsPrivateCoinReplaySmoke.before_finite
      (fun state => PrivateCoinMachine.take_finiteResult HasteBootsPrivateCoinReplaySmoke.step_finite fuel state))
    (fun result => match result.1 with | .inl cursor => (cursor : ENNReal) | .inr _ => 0)

-- Private initialization drives distinct halt/reject paths in finite syntax.
def data (tape : Tape) (slot : ClosedByteMachine.Tape) : Input := if slot = 0 then [tape 0] else []
theorem data_finite : PrivateCoinClosedWork.FiniteData data := by
  intro tape
  refine ⟨1, ?_⟩
  intro other same
  have byte := same ⟨0, by decide⟩
  funext slot
  simp only [data, byte]

def code : List ClosedByteMachine.Instruction :=
  [.pop 0 0, .branchZero 0 4, .constant 0 7, .reject, .halt]
def zero : Tape := fun _ => 0
def one : Tape := fun _ => 1
example (world : World) :
    (PrivateCoinClosedWork.program code [] data 10 zero world).run.1.stopped = some .halt := by rfl
example (world : World) :
    (PrivateCoinClosedWork.program code [] data 10 one world).run.1.stopped = some .reject := by rfl
example (world : World) :
    (PrivateCoinClosedWork.program code [] data 10 zero world).run.1.work =
      (ClosedByteMachine.initialise code (data zero)).work + 3 := by rfl
example (world : World) :
    (PrivateCoinClosedWork.program code [] data 10 one world).run.1.work =
      (ClosedByteMachine.initialise code (data one)).work + 4 := by rfl

-- Exact unconditioned averaging retains the rejecting branch's larger cost.
def coinLaw : Measure Tape := (1 / 2 : ENNReal) • Measure.dirac zero + (1 / 2 : ENNReal) • Measure.dirac one
example : (∫⁻ execution, PrivateCoinClosedWork.prefixWork code [] data 10 execution
    ∂coinLaw.prod InputIndexedOracle.law) = (1 / 2 : ENNReal) * 21 + (1 / 2 : ENNReal) * 22 := by
  have atZero : ∀ world, PrivateCoinClosedWork.prefixWork code [] data 10 (zero, world) = (21 : ENNReal) := fun _ => rfl
  have atOne : ∀ world, PrivateCoinClosedWork.prefixWork code [] data 10 (one, world) = (22 : ENNReal) := fun _ => rfl
  rw [lintegral_prod _ (PrivateCoinClosedWork.prefixWork_measurable code [] data data_finite 10).aemeasurable]
  simp [coinLaw, atZero, atOne]

-- Aborting on an empty private stack retains initialization and the failed pop.
example (world : World) :
    (PrivateCoinClosedWork.program [.pop 1 0] [] data 10 zero world).run.1.work =
      (ClosedByteMachine.initialise [.pop 1 0] (data zero)).work + 1 := by rfl
example (world : World) :
    (PrivateCoinClosedWork.program [.pop 1 0] [] data 10 zero world).run.1.stopped = some .abort := by rfl

example : Measurable (PrivateCoinClosedWork.lifetimeWork code [] data) :=
  PrivateCoinClosedWork.lifetimeWork_measurable code [] data data_finite
example (coins : Measure Tape) :
    PrivateCoinClosedWork.expectedWork coins code [] data =
      ∫⁻ tape, ClosedByteMachineWork.expectedWork code [] (data tape) ∂coins :=
  PrivateCoinClosedWork.expectedWork_prod coins code [] data data_finite
example (coins : Measure Tape) :
    PrivateCoinClosedWork.expectedWork coins code [] data =
      ⨆ fuel : ℕ, ∫⁻ execution, PrivateCoinClosedWork.prefixWork code [] data fuel execution
        ∂coins.prod InputIndexedOracle.law :=
  PrivateCoinClosedWork.expectedWork_eq_iSup coins code [] data data_finite
example (coins : Measure Tape) :
    (∑' fuel : ℕ, ∫⁻ execution, PrivateCoinClosedWork.stepCost code [] data fuel execution
      ∂coins.prod InputIndexedOracle.law) ≤ PrivateCoinClosedWork.expectedWork coins code [] data :=
  PrivateCoinClosedWork.expectedStepCosts_le coins code [] data data_finite

open HasteBootsCalibrationSmoke (ctx tables primitive constructed compatible)
open HasteBootsBatchMeaningSmoke (usize)
-- This is the calibrated field/column exposure component, not false PBS.
example (coins : Measure Tape) :
    (coins.prod InputIndexedOracle.law) {execution | PrivateCoinClosedGoldRisk.event code []
      (fun _ => 0) ctx primitive .helper (fun _ => 0) data execution} ≤
        ((17 : ENNReal)/2^141) * PrivateCoinClosedWork.expectedWork coins code [] data :=
  PrivateCoinClosedGoldRisk.lifetime_le_work code [] (fun _ => 0) ctx primitive .helper (fun _ => 0)
    tables (usize 2048) (usize 4) (usize 2) constructed compatible coins data data_finite
example (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod InputIndexedOracle.law) {execution | PrivateCoinClosedGoldRisk.event code []
      (fun _ => 0) ctx primitive .helper (fun _ => 0) data execution} ≤
        PrivateCoinClosedWork.expectedWork coins code [] data :=
  PrivateCoinClosedGoldRisk.scaled_exposure_bound code [] (fun _ => 0) ctx primitive .helper (fun _ => 0)
    tables (usize 2048) (usize 4) (usize 2) constructed compatible coins data data_finite

end
end HasteBootsPrivateCoinWorkSmoke
