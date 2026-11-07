module
public import FormalProof4FHE.HasteBoots.OracleMachine
@[expose] public section

/-! Closed byte instructions with silent local steps. Programs contain finite
syntax, never Lean functions or response continuations. The interpreter builds
its own oracle continuations and retains all tapes, work and status. This is a
specified byte-work model; its refinement to native attacker/verifier execution
and physical work is a separate obligation. Public setup is immutable and is
not charged as attacker initialization. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachine
open InputIndexedOracle (Byte Input World)
open OracleProgram (Program)
open NativeTranscript (Observation)

abbrev Register := Fin 4
abbrev Tape := Fin 4

inductive Instruction where
  | constant (dst : Register) (value : Byte)
  | copy (dst src : Register)
  | add (dst left right : Register)
  | push (dst : Tape) (src : Register)
  | pop (src : Tape) (dst : Register)
  | branchZero (src : Register) (target : ℕ)
  | jump (target : ℕ)
  | publicCopy (dst : Tape)
  | start (src : Tape)
  | read (src dst : Tape) (offset count : ℕ)
  | readTape (src dst offset count : Tape)
  | hash (src dst : Tape)
  | halt
  | reject
  deriving DecidableEq

/-- Size of the finite instruction encoding, including integer operands. -/
def Instruction.size : Instruction → ℕ
  | .constant _ _ => 3
  | .copy _ _ => 3
  | .add _ _ _ => 4
  | .push _ _ | .pop _ _ => 3
  | .branchZero _ target => 2+target.size
  | .jump target => 1+target.size
  | .publicCopy _ | .start _ => 2
  | .read _ _ offset count => 3+offset.size+count.size
  | .readTape _ _ _ _ => 5
  | .hash _ _ => 3
  | .halt | .reject => 1

inductive Stop where | halt | reject | abort
  deriving DecidableEq

structure State where
  registers : Register → Byte
  tapes : Tape → Input
  pc : ℕ
  stopped : Option Stop
  work : ℕ

/-- Attacker-owned finite code and private data are installed once. Immutable
public data is not included in this initialization charge. -/
def initialise (code : List Instruction) (privateData : Tape → Input) : State :=
  ⟨fun _ => 0,privateData,0,none,
    4+(code.map Instruction.size).sum+(List.ofFn (fun tape : Tape => (privateData tape).length)).sum⟩

def setRegister (state : State) (dst : Register) (value : Byte) : State :=
  {state with registers := Function.update state.registers dst value}

def setTape (state : State) (dst : Tape) (values : Input) : State :=
  {state with tapes := Function.update state.tapes dst values}

def charge (state : State) (amount : ℕ) : State :=
  {state with pc := state.pc+1,work := state.work+amount}

/-- Byte-work allowance for decoding an unbounded little-endian integer.
Its physical implementation still needs refinement, as does oracle pricing. -/
def decodeWork (values : Input) : ℕ := values.length*(values.length+1)

/-- Every issued instruction, including failed/terminal ones, has positive
work. Byte-consuming oracle and public-copy operations account for their
input/output lengths. Silent stack/register instructions remain real steps.
No native cycle count or cryptographic primitive pricing is asserted here. -/
def price (publicData : Input) (state : State) : Instruction → ℕ
  | .publicCopy _ => 1+publicData.length
  | .start src => 1+(state.tapes src).length
  | .read src _ offset count => 1+(state.tapes src).length+offset.size+count
  | .readTape src _ offset count =>
      1+(state.tapes src).length+decodeWork (state.tapes offset)+decodeWork (state.tapes count)+
        TranscriptFrame.fromLittleEndian (state.tapes count)
  | .hash src _ => 1+(state.tapes src).length+64
  | _ => 1

theorem price_pos (publicData : Input) (state : State) (instruction : Instruction) :
    0 < price publicData state instruction := by
  cases instruction <;> simp [price]

/-- The complete operational semantics of one finite instruction. There is no
user-supplied local evaluator, oracle callback, or world-valued operand. -/
def issue (publicData : Input) (state : State) (instruction : Instruction) : Program State :=
  let next := charge state (price publicData state instruction)
  match instruction with
  | .constant dst value => .pure (setRegister next dst value)
  | .copy dst src => .pure (setRegister next dst (state.registers src))
  | .add dst left right => .pure (setRegister next dst (state.registers left+state.registers right))
  | .push dst src => .pure (setTape next dst (state.registers src :: state.tapes dst))
  | .pop src dst => match state.tapes src with
    | [] => .pure {next with stopped := some .abort}
    | value :: tail => .pure (setRegister (setTape next src tail) dst value)
  | .branchZero src target => .pure {next with pc := if state.registers src = 0 then target else next.pc}
  | .jump target => .pure {next with pc := target}
  | .publicCopy dst => .pure (setTape next dst publicData)
  | .start src => .start (state.tapes src) (.pure next)
  | .read src dst offset count => .read (state.tapes src) offset count (fun values => .pure (setTape next dst values))
  | .readTape src dst offset count =>
      .read (state.tapes src) (TranscriptFrame.fromLittleEndian (state.tapes offset))
        (TranscriptFrame.fromLittleEndian (state.tapes count)) (fun values => .pure (setTape next dst values))
  | .hash src dst => .hash (state.tapes src) (fun digest => .pure (setTape next dst (List.ofFn digest)))
  | .halt => .pure {next with stopped := some .halt}
  | .reject => .pure {next with stopped := some .reject}

theorem issue_work (publicData : Input) (state : State) (instruction : Instruction) (world : World) :
    (OracleProgram.run (issue publicData state instruction) world).run.1.work =
      state.work+price publicData state instruction := by
  cases instruction with
  | pop src dst => cases h : state.tapes src <;> simp only [issue,h] <;> rfl
  | _ => rfl

/-- Falling outside finite code aborts and pays for that attempted instruction.
Terminal states then stutter without further work or fabricated observations. -/
def tick (code : List Instruction) (publicData : Input) (state : State) : Program State :=
  match state.stopped with
  | some _ => .pure state
  | none => match code[state.pc]? with
    | none => .pure {charge state 1 with stopped := some .abort}
    | some instruction => issue publicData state instruction

/-- Work of the next instruction, independent of its future oracle result. -/
def tickCost (code : List Instruction) (publicData : Input) (state : State) : ℕ :=
  match state.stopped with
  | some _ => 0
  | none => match code[state.pc]? with
    | none => 1
    | some chosen => price publicData state chosen

theorem tick_work_eq (code : List Instruction) (publicData : Input) (state : State) (world : World) :
    (OracleProgram.run (tick code publicData state) world).run.1.work =
      state.work+tickCost code publicData state := by
  cases stopped : state.stopped with
  | some stop => simp only [tick,tickCost,stopped]; rfl
  | none =>
    cases selected : code[state.pc]? with
    | none => simp only [tick,tickCost,stopped,selected]; rfl
    | some chosen => simpa only [tick,tickCost,stopped,selected] using issue_work publicData state chosen world

theorem tickCost_pos (code : List Instruction) (publicData : Input) (state : State)
    (active : state.stopped = none) : 0 < tickCost code publicData state := by
  simp only [tickCost,active]
  split
  · exact Nat.zero_lt_one
  · exact price_pos _ _ _

theorem tick_work (code : List Instruction) (publicData : Input) (state : State) (world : World) :
    state.work ≤ (OracleProgram.run (tick code publicData state) world).run.1.work := by
  unfold tick
  split
  · exact le_rfl
  · split
    · change state.work ≤ state.work+1
      omega
    · rw [issue_work]
      omega

theorem tick_active_work (code : List Instruction) (publicData : Input) (state : State) (world : World)
    (active : state.stopped = none) :
    state.work < (OracleProgram.run (tick code publicData state) world).run.1.work := by
  simp only [tick,active]
  split
  · change state.work < state.work+1
    omega
  · rw [issue_work]
    exact Nat.lt_add_of_pos_right (price_pos publicData state _)

/-- Fuel counts interpreter instruction steps, including silent local operations.
It is an analysis prefix, not a limit on the lifetime execution. -/
def take (code : List Instruction) (publicData : Input) : ℕ → State → Program State
  | 0,state => .pure state
  | fuel+1,state => OracleProgram.bind (tick code publicData state) (take code publicData fuel)

private theorem bind_assoc {A B C : Type} (program : Program A) (next : A → Program B) (last : B → Program C) :
    OracleProgram.bind program (fun value => OracleProgram.bind (next value) last) =
      OracleProgram.bind (OracleProgram.bind program next) last := by
  induction program with
  | pure value => rfl
  | start input tail ih => simpa only [OracleProgram.bind] using congrArg (Program.start input) ih
  | read input offset count tail ih =>
    simp only [OracleProgram.bind]
    congr 1
    funext values
    exact ih values
  | hash input tail ih =>
    simp only [OracleProgram.bind]
    congr 1
    funext digest
    exact ih digest

theorem take_resume (code : List Instruction) (publicData : Input) (first later : ℕ) (state : State) :
    take code publicData (first+later) state =
      OracleProgram.bind (take code publicData first state) (take code publicData later) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add,take,OracleProgram.bind]
  | succ first ih =>
    simp only [Nat.succ_add,take]
    calc
      _ = OracleProgram.bind (tick code publicData state)
          (fun value => OracleProgram.bind (take code publicData first value) (take code publicData later)) := by
        congr 1
        funext value
        exact ih value
      _ = _ := bind_assoc _ _ _

theorem take_one_work (code : List Instruction) (publicData : Input) (state : State) (world : World) :
    (OracleProgram.run (take code publicData 1 state) world).run.1.work = state.work+tickCost code publicData state := by
  rw [take,OracleProgram.run_bind,ObservationReplay.run_bind]
  change (OracleProgram.run (tick code publicData state) world).run.1.work = _
  exact tick_work_eq _ _ _ _

theorem take_succ_work (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) (world : World) :
    (OracleProgram.run (take code publicData (fuel+1) state) world).run.1.work =
      (OracleProgram.run (take code publicData fuel state) world).run.1.work+
        tickCost code publicData (OracleProgram.run (take code publicData fuel state) world).run.1 := by
  rw [take_resume,OracleProgram.run_bind,ObservationReplay.run_bind]
  exact take_one_work _ _ _ _

/-- Exact accounting over actual interpreter steps, not observation count. -/
theorem take_work_sum (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) (world : World) :
    state.work + ∑ index ∈ Finset.range fuel,
      tickCost code publicData (OracleProgram.run (take code publicData index state) world).run.1 =
        (OracleProgram.run (take code publicData fuel state) world).run.1.work := by
  induction fuel with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,Nat.add_zero]; rfl
  | succ fuel ih =>
    rw [Finset.sum_range_succ,← Nat.add_assoc,ih]
    exact (take_succ_work _ _ _ _ _).symm

theorem take_work (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) (world : World) :
    state.work ≤ (OracleProgram.run (take code publicData fuel state) world).run.1.work := by
  induction fuel generalizing state with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [take,OracleProgram.run_bind,ObservationReplay.run_bind]
    exact (tick_work code publicData state world).trans (ih _)

theorem work_prefix (code : List Instruction) (publicData : Input) (first later : ℕ)
    (bounded : first ≤ later) (state : State) (world : World) :
    (OracleProgram.run (take code publicData first state) world).run.1.work ≤
      (OracleProgram.run (take code publicData later state) world).run.1.work := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bounded
  rw [take_resume,OracleProgram.run_bind,ObservationReplay.run_bind]
  exact take_work _ _ _ _ _

theorem stopped_take (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State)
    (stop : Stop) (stopped : state.stopped = some stop) :
    take code publicData fuel state = .pure state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [take,tick,stopped,OracleProgram.bind,ih]

theorem tick_log_length (code : List Instruction) (publicData : Input) (state : State) (world : World) :
    (OracleProgram.run (tick code publicData state) world).run.2.length ≤ 1 := by
  unfold tick
  split
  · exact Nat.zero_le 1
  · split
    · exact Nat.zero_le 1
    · rename_i instruction _
      cases instruction with
      | pop src dst =>
        cases h : state.tapes src <;> simp only [issue,h] <;> exact Nat.zero_le 1
      | _ => first | exact Nat.zero_le 1 | exact Nat.le_refl 1

theorem prefix_replay (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) :
    ObservationReplay.Replayable (OracleProgram.run (take code publicData fuel state)) :=
  OracleProgram.run_replay _

theorem log_prefix (code : List Instruction) (publicData : Input) (first later : ℕ)
    (bounded : first ≤ later) (state : State) (world : World) :
    (OracleProgram.run (take code publicData first state) world).run.2.IsPrefix
      (OracleProgram.run (take code publicData later state) world).run.2 := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bounded
  rw [take_resume,OracleProgram.run_bind,ObservationReplay.run_bind]
  exact ⟨_,rfl⟩
end FormalProof4FHE.HasteBoots.ClosedByteMachine
