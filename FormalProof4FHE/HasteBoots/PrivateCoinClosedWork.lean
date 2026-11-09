module
public import FormalProof4FHE.HasteBoots.PrivateCoinScores
public import FormalProof4FHE.HasteBoots.ClosedByteMachineWork
@[expose] public section

/-! Private random initialization of the closed byte interpreter. The work
counter is the existing specified instruction cost, including initialization,
local steps and unsuccessful termination. This does not price a native RNG
or establish a physical-work refinement. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinClosedWork
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open ClosedByteMachine (Instruction)
noncomputable section

def FiniteData (privateData : Tape → ClosedByteMachine.Tape → Input) : Prop :=
  ∀ tape, ∃ count : ℕ, ∀ other : Tape,
    (∀ index : Fin count, other index = tape index) → privateData other = privateData tape

def program (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (fuel : ℕ) (tape : Tape) :=
  OracleProgram.run (ClosedByteMachine.take code publicData fuel
    (ClosedByteMachine.initialise code (privateData tape)))

theorem finiteResult (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (finiteData : FiniteData privateData)
    (fuel : ℕ) : PrivateCoinMachine.FiniteResult (program code publicData privateData fuel) := by
  intro tape world
  obtain ⟨count, fixed⟩ := finiteData tape
  refine ⟨count, ?_⟩
  intro other same
  simp only [program, fixed other same]

def prefixWork (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (fuel : ℕ) (execution : Tape × World) : ENNReal :=
  ClosedByteMachineWork.prefixWork code publicData (privateData execution.1) fuel execution.2

def lifetimeWork (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (execution : Tape × World) : ENNReal :=
  ClosedByteMachineWork.lifetimeWork code publicData (privateData execution.1) execution.2

def expectedWork (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) : ENNReal :=
  ∫⁻ execution, lifetimeWork code publicData privateData execution ∂coins.prod law

theorem prefixWork_measurable (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (finiteData : FiniteData privateData) (fuel : ℕ) :
    Measurable (prefixWork code publicData privateData fuel) :=
  PrivateCoinScores.score_measurable (fun _ => OracleProgram.run_replay _)
    (finiteResult code publicData privateData finiteData fuel) (fun result => result.1.work)

theorem lifetimeWork_measurable (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (finiteData : FiniteData privateData) :
    Measurable (lifetimeWork code publicData privateData) :=
  Measurable.iSup (prefixWork_measurable code publicData privateData finiteData)

/-- Exact averaging over private coins and the oracle, with no conditioning
on whether the interpreter halted, rejected, aborted or continued forever. -/
theorem expectedWork_prod (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (finiteData : FiniteData privateData) :
    expectedWork coins code publicData privateData =
      ∫⁻ tape, ClosedByteMachineWork.expectedWork code publicData (privateData tape) ∂coins :=
  lintegral_prod _ (lifetimeWork_measurable code publicData privateData finiteData).aemeasurable

theorem expectedWork_eq_iSup (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (finiteData : FiniteData privateData) :
    expectedWork coins code publicData privateData =
      ⨆ fuel : ℕ, ∫⁻ execution, prefixWork code publicData privateData fuel execution ∂coins.prod law := by
  apply lintegral_iSup (prefixWork_measurable code publicData privateData finiteData)
  intro first later bounded execution
  exact ClosedByteMachineWork.prefixWork_mono code publicData (privateData execution.1) execution.2 bounded

theorem initialisation_le_expected (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) :
    (∫⁻ execution : Tape × World, ((ClosedByteMachine.initialise code (privateData execution.1)).work : ENNReal)
      ∂coins.prod law) ≤ expectedWork coins code publicData privateData := by
  exact lintegral_mono fun execution =>
    ClosedByteMachineWork.initialisation_le code publicData (privateData execution.1) execution.2

def stepCost (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (fuel : ℕ) (execution : Tape × World) : ENNReal :=
  ClosedByteMachine.tickCost code publicData (program code publicData privateData fuel execution.1 execution.2).run.1

theorem stepCost_measurable (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (finiteData : FiniteData privateData) (fuel : ℕ) :
    Measurable (stepCost code publicData privateData fuel) :=
  PrivateCoinScores.score_measurable (fun _ => OracleProgram.run_replay _)
    (finiteResult code publicData privateData finiteData fuel)
    (fun result => (ClosedByteMachine.tickCost code publicData result.1 : ENNReal))

/-- Every issued instruction is charged on its actual path. Stopped stuttering
has zero step cost; initialization remains in the lifetime counter. -/
theorem expectedStepCosts_le (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (finiteData : FiniteData privateData) :
    (∑' fuel : ℕ, ∫⁻ execution, stepCost code publicData privateData fuel execution ∂coins.prod law) ≤
      expectedWork coins code publicData privateData := by
  rw [← lintegral_tsum (fun fuel => (stepCost_measurable code publicData privateData finiteData fuel).aemeasurable)]
  exact lintegral_mono fun execution =>
    ClosedByteMachineWork.stepCost_tsum_le code publicData (privateData execution.1) execution.2
end
end FormalProof4FHE.HasteBoots.PrivateCoinClosedWork
