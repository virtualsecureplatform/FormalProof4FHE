module
import FormalProof4FHE.HasteBoots.PrivateCoinByteEmbedding
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (Byte Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction State initialise take)
namespace HasteBootsPrivateCoinByteSmoke
noncomputable section

def empty : ClosedByteMachine.Tape → Input := fun _ => []
def zero : Tape := fun _ => 0
def one : Tape := fun _ => 1

def branch : List Instruction := [.coin 0, .base (.branchZero 0 4), .coin 1, .base .reject, .base .halt]
example (world : World) :
    (PrivateCoinByteWork.program branch [] empty 10 zero world).run.1.cursor = 1 := by rfl
example (world : World) :
    (PrivateCoinByteWork.program branch [] empty 10 one world).run.1.cursor = 2 := by rfl
example (world : World) :
    (PrivateCoinByteWork.program branch [] empty 10 zero world).run.1.work = 20 := by rfl
example (world : World) :
    (PrivateCoinByteWork.program branch [] empty 10 one world).run.1.work = 22 := by rfl
example (world : World) :
    (PrivateCoinByteWork.program branch [] empty 10 one world).run.1.machine.stopped = some .reject := by rfl
example (tape : Tape) (world : World) :
    (PrivateCoinByteWork.program [.base .halt, .coin 0] [] empty 10 tape world).run.1.cursor = 0 := by rfl
example (tape : Tape) (world : World) :
    (PrivateCoinByteWork.program [] [] empty 10 tape world).run.1.machine.stopped = some .abort := by rfl

-- The private byte selects the next actual SHAKE input. It does not emit an
-- oracle log entry of its own or reset the shared oracle world.
def query : List Instruction := [.coin 0, .base (.push 0 0), .base (.read 0 1 5 1)]
example (tape : Tape) (world : World) :
    (PrivateCoinByteWork.program query [] empty 3 tape world).run.2 =
      [.output [tape 0] 5 [InputIndexedOracle.shake world [tape 0] 5]] := by rfl

-- An exact mixture pays for both paths and only the coins actually consumed.
def coins : Measure Tape := (1/2 : ENNReal) • Measure.dirac zero + (1/2 : ENNReal) • Measure.dirac one
example : (∫⁻ execution, PrivateCoinByteWork.prefixWork branch [] empty 10 execution ∂coins.prod law) =
    (1/2 : ENNReal)*20 + (1/2 : ENNReal)*22 := by
  have atZero : ∀ world, PrivateCoinByteWork.prefixWork branch [] empty 10 (zero, world) = (20 : ENNReal) := fun _ => rfl
  have atOne : ∀ world, PrivateCoinByteWork.prefixWork branch [] empty 10 (one, world) = (22 : ENNReal) := fun _ => rfl
  rw [lintegral_prod _ (PrivateCoinByteWork.prefixWork_measurable branch [] empty 10).aemeasurable]
  simp [coins, atZero, atOne]

-- A finite two-instruction loop consumes arbitrarily many private bytes.
def loop : List Instruction := [.coin 0, .base (.jump 0)]

theorem two_steps (tape : Tape) (world : World) (state : State)
    (atStart : state.machine.pc = 0) (active : state.machine.stopped = none) :
    let next := (OracleProgram.run (take loop [] tape 2 state) world).run.1
    next.cursor = state.cursor+1 ∧ next.work = state.work+3 ∧
      next.machine.pc = 0 ∧ next.machine.stopped = none := by
  simp [loop, take, PrivateCoinByteMachine.tick, atStart, active, OracleProgram.bind, OracleProgram.run,
    ClosedByteMachine.charge, ClosedByteMachine.setRegister, ClosedByteMachine.issue, ClosedByteMachine.price,
    State.work, Nat.add_assoc]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem loop_cycles (tape : Tape) (world : World) (count : ℕ) (state : State)
    (atStart : state.machine.pc = 0) (active : state.machine.stopped = none) :
    let next := (OracleProgram.run (take loop [] tape (count*2) state) world).run.1
    next.cursor = state.cursor+count ∧ next.work = state.work+3*count ∧
      next.machine.pc = 0 ∧ next.machine.stopped = none := by
  induction count generalizing state with
  | zero =>
    change state.cursor = state.cursor+0 ∧ state.work = state.work+3*0 ∧
      state.machine.pc = 0 ∧ state.machine.stopped = none
    exact ⟨by omega, by omega, atStart, active⟩
  | succ count ih =>
    have first := two_steps tape world state atStart active
    have later := ih (OracleProgram.run (take loop [] tape 2 state) world).run.1 first.2.2.1 first.2.2.2
    rw [Nat.succ_mul, Nat.add_comm (count*2) 2, PrivateCoinByteMachine.take_resume,
      OracleProgram.run_bind, ObservationReplay.run_bind]
    dsimp only at first later ⊢
    constructor
    · omega
    constructor
    · omega
    exact later.2.2

example (count : ℕ) (tape : Tape) (world : World) :
    (PrivateCoinByteWork.program loop [] empty (count*2) tape world).run.1.cursor = count := by
  have result := loop_cycles tape world count (initialise loop empty) rfl rfl
  simpa only [PrivateCoinByteWork.program, initialise, Nat.zero_add] using result.1

example : Measurable (PrivateCoinByteWork.lifetimeWork loop [] empty) :=
  PrivateCoinByteWork.lifetimeWork_measurable loop [] empty
example (measure : Measure Tape) :
    PrivateCoinByteWork.expectedWork measure branch [] empty =
      ⨆ fuel : ℕ, ∫⁻ execution, PrivateCoinByteWork.prefixWork branch [] empty fuel execution ∂measure.prod law :=
  PrivateCoinByteWork.expectedWork_eq_iSup measure branch [] empty
example (measure : Measure Tape) :
    (∫⁻ execution : Tape × World,
      (⨆ fuel : ℕ, ((2*(PrivateCoinByteWork.program branch [] empty fuel execution.1 execution.2).run.1.cursor : ℕ) : ENNReal))
      ∂measure.prod law) ≤ PrivateCoinByteWork.expectedWork measure branch [] empty :=
  PrivateCoinByteWork.expectedCoins_le measure branch [] empty

-- Original instructions retain their full state/log behavior, from the same
-- machine state and any private cursor.
example (code : List ClosedByteMachine.Instruction) (state : ClosedByteMachine.State)
    (publicData : Input) (tape : Tape) (fuel cursor : ℕ) (world : World) :
    (OracleProgram.run (take (code.map Instruction.base) publicData tape fuel ⟨state,cursor⟩) world).run.2 =
      (OracleProgram.run (ClosedByteMachine.take code publicData fuel state) world).run.2 :=
  congrArg Prod.snd (PrivateCoinByteEmbedding.run_embed code publicData tape fuel state cursor world)
end
end HasteBootsPrivateCoinByteSmoke
