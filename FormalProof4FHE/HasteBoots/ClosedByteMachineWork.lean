module
public import FormalProof4FHE.HasteBoots.ClosedByteMachine
public import FormalProof4FHE.HasteBoots.OracleExecutionLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
@[expose] public section

/-! Work of actual closed instruction prefixes, including silent computation,
initialization and unsuccessful termination. Infinite total work is allowed.
These are the interpreter's specified byte-work units, not a completed native
physical-work refinement or a false-acceptance security theorem. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineWork
open InputIndexedOracle (Input World law)
open ClosedByteMachine (Instruction State Tape initialise take)
open MeasureTheory
noncomputable section

def prefixWork (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (fuel : ℕ) (world : World) : ENNReal :=
  (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1.work

def lifetimeWork (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (world : World) : ENNReal :=
  ⨆ fuel : ℕ, prefixWork code publicData privateData fuel world

def expectedWork (code : List Instruction) (publicData : Input) (privateData : Tape → Input) : ENNReal :=
  ∫⁻ world, lifetimeWork code publicData privateData world ∂law

theorem prefixWork_measurable (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (fuel : ℕ) :
    Measurable (prefixWork code publicData privateData fuel) :=
  OracleExecutionLaw.score_measurable (ClosedByteMachine.prefix_replay code publicData fuel (initialise code privateData))
    (fun result => result.1.work)

theorem prefixWork_mono (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (world : World) :
    Monotone (fun fuel => prefixWork code publicData privateData fuel world) := by
  intro first later bounded
  exact Nat.cast_le.mpr (ClosedByteMachine.work_prefix code publicData first later bounded _ world)

theorem lifetimeWork_measurable (code : List Instruction) (publicData : Input) (privateData : Tape → Input) :
    Measurable (lifetimeWork code publicData privateData) :=
  Measurable.iSup (prefixWork_measurable code publicData privateData)

/-- No incomplete-run or infinite tail is discarded from expected work. -/
theorem expectedWork_eq_iSup (code : List Instruction) (publicData : Input) (privateData : Tape → Input) :
    expectedWork code publicData privateData =
      ⨆ fuel : ℕ, ∫⁻ world, prefixWork code publicData privateData fuel world ∂law := by
  unfold expectedWork lifetimeWork
  apply lintegral_iSup (prefixWork_measurable code publicData privateData)
  intro first later bounded world
  exact prefixWork_mono code publicData privateData world bounded

/-- Every instruction's specified work is paid once on its actual path.
Stopped stuttering contributes zero; silent running instructions contribute
positive work. Infinite sums are retained without a runtime cutoff. -/
theorem stepCost_tsum_le (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (world : World) :
    (∑' fuel : ℕ, (ClosedByteMachine.tickCost code publicData
      (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1 : ENNReal)) ≤
        lifetimeWork code publicData privateData world := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro fuel
  have accounted := ClosedByteMachine.take_work_sum code publicData fuel (initialise code privateData) world
  have bounded : (∑ index ∈ Finset.range fuel,
      ClosedByteMachine.tickCost code publicData (OracleProgram.run
        (take code publicData index (initialise code privateData)) world).run.1) ≤
      (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1.work := by omega
  calc
    _ = ((∑ index ∈ Finset.range fuel, ClosedByteMachine.tickCost code publicData
        (OracleProgram.run (take code publicData index (initialise code privateData)) world).run.1 : ℕ) : ENNReal) := by
      rw [Nat.cast_sum]
    _ ≤ prefixWork code publicData privateData fuel world := Nat.cast_le.mpr bounded
    _ ≤ _ := le_iSup (fun index => prefixWork code publicData privateData index world) fuel

theorem initialisation_le (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (world : World) :
    ((initialise code privateData).work : ENNReal) ≤ lifetimeWork code publicData privateData world := by
  exact le_iSup (fun fuel => prefixWork code publicData privateData fuel world) 0
end
end FormalProof4FHE.HasteBoots.ClosedByteMachineWork
