module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteMachine
@[expose] public section

/-! Unconditional expected specified work for runtime private-coin execution.
Initialization and every executed instruction remain in the same counter;
private bytes are charged when consumed, not preloaded at a fuel-dependent
initialization. Native RNG pricing and security coverage remain separate. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteWork
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open OracleProgram (run)
open PrivateCoinByteMachine (Instruction State take tickCost initialise)
noncomputable section

def program (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (fuel : ℕ) (tape : Tape) := run (take code publicData tape fuel (initialise code privateData))

theorem take_succ_work (code : List Instruction) (publicData : Input) (tape : Tape)
    (fuel : ℕ) (state : State) (world : World) :
    (run (take code publicData tape (fuel+1) state) world).run.1.work =
      (run (take code publicData tape fuel state) world).run.1.work +
        tickCost code publicData (run (take code publicData tape fuel state) world).run.1 := by
  rw [PrivateCoinByteMachine.take_resume, OracleProgram.run_bind, ObservationReplay.run_bind]
  simp only [take, OracleProgram.run_bind, ObservationReplay.run_bind, OracleProgram.run, WriterT.run_pure]
  exact PrivateCoinByteMachine.tick_work_eq _ _ _ _ _

theorem take_work_sum (code : List Instruction) (publicData : Input) (tape : Tape)
    (fuel : ℕ) (state : State) (world : World) :
    state.work + ∑ index ∈ Finset.range fuel,
      tickCost code publicData (run (take code publicData tape index state) world).run.1 =
        (run (take code publicData tape fuel state) world).run.1.work := by
  induction fuel with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero]; rfl
  | succ fuel ih =>
    rw [Finset.sum_range_succ, ← Nat.add_assoc, ih]
    exact (take_succ_work _ _ _ _ _ _).symm

def prefixWork (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (fuel : ℕ) (execution : Tape × World) : ENNReal :=
  (program code publicData privateData fuel execution.1 execution.2).run.1.work

def lifetimeWork (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (execution : Tape × World) : ENNReal := ⨆ fuel : ℕ, prefixWork code publicData privateData fuel execution

def expectedWork (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) : ENNReal :=
  ∫⁻ execution, lifetimeWork code publicData privateData execution ∂coins.prod law

theorem prefixWork_measurable (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) :
    Measurable (prefixWork code publicData privateData fuel) :=
  PrivateCoinScores.score_measurable (fun _ => OracleProgram.run_replay _)
    (PrivateCoinByteMachine.take_finiteResult code publicData fuel (initialise code privateData))
    (fun result => (result.1.work : ENNReal))

theorem lifetimeWork_measurable (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) : Measurable (lifetimeWork code publicData privateData) :=
  Measurable.iSup (prefixWork_measurable code publicData privateData)

theorem expectedWork_prod (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) :
    expectedWork coins code publicData privateData =
      ∫⁻ tape, ∫⁻ world, lifetimeWork code publicData privateData (tape, world) ∂law ∂coins :=
  lintegral_prod _ (lifetimeWork_measurable code publicData privateData).aemeasurable

theorem expectedWork_eq_iSup (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) :
    expectedWork coins code publicData privateData =
      ⨆ fuel : ℕ, ∫⁻ execution, prefixWork code publicData privateData fuel execution ∂coins.prod law := by
  apply lintegral_iSup (prefixWork_measurable code publicData privateData)
  intro first later bounded execution
  exact Nat.cast_le.mpr (PrivateCoinByteMachine.work_prefix code publicData execution.1
    first later bounded (initialise code privateData) execution.2)

theorem initialisation_le (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (execution : Tape × World) :
    ((initialise code privateData).work : ENNReal) ≤ lifetimeWork code publicData privateData execution :=
  le_iSup (fun fuel => prefixWork code publicData privateData fuel execution) 0

def stepCost (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (fuel : ℕ) (execution : Tape × World) : ENNReal :=
  tickCost code publicData (program code publicData privateData fuel execution.1 execution.2).run.1

theorem stepCost_measurable (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) : Measurable (stepCost code publicData privateData fuel) :=
  PrivateCoinScores.score_measurable (fun _ => OracleProgram.run_replay _)
    (PrivateCoinByteMachine.take_finiteResult code publicData fuel (initialise code privateData))
    (fun result => (tickCost code publicData result.1 : ENNReal))

theorem stepCosts_le (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (execution : Tape × World) :
    (∑' fuel : ℕ, stepCost code publicData privateData fuel execution) ≤
      lifetimeWork code publicData privateData execution := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro fuel
  have accounted := take_work_sum code publicData execution.1 fuel (initialise code privateData) execution.2
  have bounded : (∑ index ∈ Finset.range fuel,
      tickCost code publicData (program code publicData privateData index execution.1 execution.2).run.1) ≤
      (program code publicData privateData fuel execution.1 execution.2).run.1.work := by
    dsimp only [program] at *
    omega
  calc
    _ = ((∑ index ∈ Finset.range fuel,
      tickCost code publicData (program code publicData privateData index execution.1 execution.2).run.1 : ℕ) : ENNReal) := by
      rw [Nat.cast_sum]
      rfl
    _ ≤ prefixWork code publicData privateData fuel execution := Nat.cast_le.mpr bounded
    _ ≤ _ := le_iSup (fun index => prefixWork code publicData privateData index execution) fuel

theorem expectedStepCosts_le (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) :
    (∑' fuel : ℕ, ∫⁻ execution, stepCost code publicData privateData fuel execution ∂coins.prod law) ≤
      expectedWork coins code publicData privateData := by
  rw [← lintegral_tsum (fun fuel => (stepCost_measurable code publicData privateData fuel).aemeasurable)]
  exact lintegral_mono (stepCosts_le code publicData privateData)

/-- Every byte consumed during runtime, including before reject/abort, is
paid on that execution. Future unused bytes are not charged. -/
theorem consumed_coins_le (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (execution : Tape × World) :
    (⨆ fuel : ℕ, ((2 * (program code publicData privateData fuel execution.1 execution.2).run.1.cursor : ℕ) : ENNReal)) ≤
      lifetimeWork code publicData privateData execution := by
  apply iSup_le
  intro fuel
  have paid := PrivateCoinByteMachine.take_coinWork code publicData execution.1 fuel
    (initialise code privateData) (by simp [initialise]) execution.2
  exact (Nat.cast_le.mpr paid).trans (le_iSup (fun index => prefixWork code publicData privateData index execution) fuel)

theorem expectedCoins_le (coins : Measure Tape) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) :
    (∫⁻ execution : Tape × World,
      (⨆ fuel : ℕ, ((2 * (program code publicData privateData fuel execution.1 execution.2).run.1.cursor : ℕ) : ENNReal))
      ∂coins.prod law) ≤ expectedWork coins code publicData privateData :=
  lintegral_mono (consumed_coins_le code publicData privateData)
end
end FormalProof4FHE.HasteBoots.PrivateCoinByteWork
