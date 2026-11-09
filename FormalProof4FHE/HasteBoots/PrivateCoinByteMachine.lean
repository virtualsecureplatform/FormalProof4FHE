module
public import FormalProof4FHE.HasteBoots.PrivateCoinClosedWork
public import FormalProof4FHE.HasteBoots.NativeProgramComposition
@[expose] public section

/-! A conservative extension of the closed byte instruction set with runtime
private-byte reads. Coins are read only by the coin instruction, advance a
persistent cursor, and have a specified cost of two byte-work units. This is
an interpreter model, not a native RNG or physical-work refinement. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteMachine
open InputIndexedOracle (Input World)
open OracleProgram (Program run bind)
open PrivateCoinReplay (Tape)
noncomputable section

inductive Instruction where
  | base (instruction : ClosedByteMachine.Instruction)
  | coin (dst : ClosedByteMachine.Register)
  deriving DecidableEq

def Instruction.size : Instruction → ℕ
  | .base instruction => instruction.size
  | .coin _ => 2

structure State where
  machine : ClosedByteMachine.State
  cursor : ℕ

def State.work (state : State) : ℕ := state.machine.work

/-- Finite code/private data installation plus one unit for the coin cursor.
The infinite random tape is not installed or charged in advance. -/
def initialise (code : List Instruction) (privateData : ClosedByteMachine.Tape → Input) : State :=
  let original := ClosedByteMachine.initialise [] privateData
  ⟨{original with work := original.work + 1 + (code.map Instruction.size).sum}, 0⟩

def tick (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) : Program State :=
  match state.machine.stopped with
  | some _ => .pure state
  | none => match code[state.machine.pc]? with
    | none => .pure ⟨{ClosedByteMachine.charge state.machine 1 with stopped := some .abort}, state.cursor⟩
    | some (.base instruction) => bind (ClosedByteMachine.issue publicData state.machine instruction)
        (fun next => .pure ⟨next, state.cursor⟩)
    | some (.coin dst) => .pure ⟨ClosedByteMachine.setRegister (ClosedByteMachine.charge state.machine 2)
        dst (tape state.cursor), state.cursor + 1⟩

def tickCost (code : List Instruction) (publicData : Input) (state : State) : ℕ :=
  match state.machine.stopped with
  | some _ => 0
  | none => match code[state.machine.pc]? with
    | none => 1
    | some (.base instruction) => ClosedByteMachine.price publicData state.machine instruction
    | some (.coin _) => 2

def coinUse (code : List Instruction) (state : State) : ℕ :=
  match state.machine.stopped with
  | some _ => 0
  | none => match code[state.machine.pc]? with
    | some (.coin _) => 1
    | _ => 0

theorem tick_work_eq (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) (world : World) :
    (run (tick code publicData tape state) world).run.1.work = state.work + tickCost code publicData state := by
  cases stopped : state.machine.stopped with
  | some stop => simp only [tick, tickCost, stopped, State.work]; rfl
  | none =>
    cases selected : code[state.machine.pc]? with
    | none => simp only [tick, tickCost, stopped, selected, State.work]; rfl
    | some chosen =>
      cases chosen with
      | coin dst => simp only [tick, tickCost, stopped, selected, State.work]; rfl
      | base instruction =>
        simp only [tick, tickCost, stopped, selected, OracleProgram.run_bind, ObservationReplay.run_bind,
          OracleProgram.run, WriterT.run_pure, State.work]
        exact ClosedByteMachine.issue_work publicData state.machine instruction world

theorem tick_cursor_eq (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) (world : World) :
    (run (tick code publicData tape state) world).run.1.cursor = state.cursor + coinUse code state := by
  cases stopped : state.machine.stopped with
  | some stop => simp only [tick, coinUse, stopped]; rfl
  | none =>
    cases selected : code[state.machine.pc]? with
    | none => simp only [tick, coinUse, stopped, selected]; rfl
    | some chosen => cases chosen <;>
        simp only [tick, coinUse, stopped, selected, OracleProgram.run_bind, ObservationReplay.run_bind,
          OracleProgram.run, WriterT.run_pure] <;> rfl

theorem coinUse_cost (code : List Instruction) (publicData : Input) (state : State) :
    2 * coinUse code state ≤ tickCost code publicData state := by
  cases stopped : state.machine.stopped with
  | some stop => simp [coinUse, tickCost, stopped]
  | none =>
    cases selected : code[state.machine.pc]? with
    | none => simp [coinUse, tickCost, stopped, selected]
    | some chosen => cases chosen <;> simp [coinUse, tickCost, stopped, selected]

def take (code : List Instruction) (publicData : Input) (tape : Tape) : ℕ → State → Program State
  | 0, state => .pure state
  | fuel+1, state => bind (tick code publicData tape state) (take code publicData tape fuel)

theorem take_resume (code : List Instruction) (publicData : Input) (tape : Tape)
    (first later : ℕ) (state : State) :
    take code publicData tape (first+later) state = bind (take code publicData tape first state)
      (take code publicData tape later) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, take, OracleProgram.bind]
  | succ first ih =>
    simp only [Nat.succ_add, take, NativeProgramComposition.bind_assoc]
    congr 1
    funext next
    exact ih next

theorem stopped_take (code : List Instruction) (publicData : Input) (tape : Tape) (fuel : ℕ)
    (state : State) (stop : ClosedByteMachine.Stop) (stopped : state.machine.stopped = some stop) :
    take code publicData tape fuel state = .pure state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [take, tick, stopped, OracleProgram.bind, ih]

theorem take_work (code : List Instruction) (publicData : Input) (tape : Tape) (fuel : ℕ) (state : State) (world : World) :
    state.work ≤ (run (take code publicData tape fuel state) world).run.1.work := by
  induction fuel generalizing state with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [take, OracleProgram.run_bind, ObservationReplay.run_bind]
    exact (Nat.le_add_right _ _).trans ((tick_work_eq code publicData tape state world).symm ▸ ih _)

theorem work_prefix (code : List Instruction) (publicData : Input) (tape : Tape)
    (first later : ℕ) (bounded : first ≤ later) (state : State) (world : World) :
    (run (take code publicData tape first state) world).run.1.work ≤
      (run (take code publicData tape later state) world).run.1.work := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bounded
  rw [take_resume, OracleProgram.run_bind, ObservationReplay.run_bind]
  exact take_work _ _ _ _ _ _

theorem take_coinWork (code : List Instruction) (publicData : Input) (tape : Tape) (fuel : ℕ)
    (state : State) (paid : 2*state.cursor ≤ state.work) (world : World) :
    2*(run (take code publicData tape fuel state) world).run.1.cursor ≤
      (run (take code publicData tape fuel state) world).run.1.work := by
  induction fuel generalizing state with
  | zero => exact paid
  | succ fuel ih =>
    rw [take, OracleProgram.run_bind, ObservationReplay.run_bind]
    apply ih
    rw [tick_work_eq, tick_cursor_eq]
    have cost := coinUse_cost code publicData state
    omega

/-- A single instruction inspects at most its current private coordinate.
This proof bound is not a prepayment or an instruction's work charge. -/
theorem tick_finiteResult (code : List Instruction) (publicData : Input) (state : State) :
    PrivateCoinMachine.FiniteResult (fun tape => run (tick code publicData tape state)) := by
  intro tape world
  refine ⟨state.cursor+1, ?_⟩
  intro other same
  have byte := same ⟨state.cursor, Nat.lt_succ_self _⟩
  have equal : tick code publicData other state = tick code publicData tape state := by
    unfold tick
    cases state.machine.stopped with
    | some stop => rfl
    | none =>
      cases code[state.machine.pc]? with
      | none => rfl
      | some chosen => cases chosen <;> simp only [byte]
  change (run (tick code publicData other state) world).run =
    (run (tick code publicData tape state) world).run
  rw [equal]

theorem take_finiteResult (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) :
    PrivateCoinMachine.FiniteResult (fun tape => run (take code publicData tape fuel state)) := by
  induction fuel generalizing state with
  | zero =>
    intro tape world
    exact ⟨0, fun _ _ => rfl⟩
  | succ fuel ih =>
    simpa only [PrivateCoinMachine.FiniteResult, take, OracleProgram.run_bind] using
      PrivateCoinMachine.bind_finiteResult (tick_finiteResult code publicData state) (fun next => ih next)
end
end FormalProof4FHE.HasteBoots.PrivateCoinByteMachine
