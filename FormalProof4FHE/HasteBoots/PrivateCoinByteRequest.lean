module
public import FormalProof4FHE.HasteBoots.InstructionClock
public import FormalProof4FHE.HasteBoots.PrivateCoinByteEmbedding
public import FormalProof4FHE.HasteBoots.ClosedByteMachineRequest
@[expose] public section

/-! Exact single-instruction requests for runtime private coins. Coin/local
instructions return their next state without an oracle request. The instruction
clock resumes them; they do not terminate the whole machine. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteRequest
open InputIndexedOracle (Input World)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction State tick take)
open CausalStreamExposure (seen firstRead)

def lift (cursor : ℕ) : OracleMachine.Command ClosedByteMachine.State ClosedByteMachine.State → OracleMachine.Command State State
  | .done next => .done ⟨next, cursor⟩
  | .start input next => .start input ⟨next, cursor⟩
  | .read input offset count next => .read input offset count (fun value => ⟨next value, cursor⟩)
  | .hash input next => .hash input (fun value => ⟨next value, cursor⟩)

theorem lift_exact (cursor : ℕ) (command : OracleMachine.Command ClosedByteMachine.State ClosedByteMachine.State) :
    OracleProgram.bind (ClosedByteMachineRequest.single command) (fun next => .pure (⟨next, cursor⟩ : State)) =
      InstructionClock.single (lift cursor command) := by
  cases command <;> rfl

def command (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) : OracleMachine.Command State State :=
  match state.machine.stopped with
  | some _ => .done state
  | none => match code[state.machine.pc]? with
    | none => .done ⟨{ClosedByteMachine.charge state.machine 1 with stopped := some .abort}, state.cursor⟩
    | some (.base instruction) => lift state.cursor (ClosedByteMachineRequest.instruction publicData state.machine instruction)
    | some (.coin dst) => .done ⟨ClosedByteMachine.setRegister (ClosedByteMachine.charge state.machine 2)
        dst (tape state.cursor), state.cursor+1⟩

theorem command_exact (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) :
    tick code publicData tape state = InstructionClock.single (command code publicData tape state) := by
  cases stopped : state.machine.stopped with
  | some stop => simp only [tick, command, stopped, InstructionClock.single]
  | none =>
    cases selected : code[state.machine.pc]? with
    | none => simp only [tick, command, stopped, selected, InstructionClock.single]
    | some chosen =>
      cases chosen with
      | coin dst => simp only [tick, command, stopped, selected, InstructionClock.single]
      | base instruction =>
        simp only [tick, command, stopped, selected, ClosedByteMachineRequest.instruction_exact, lift_exact]

theorem take_exact (code : List Instruction) (publicData : Input) (tape : Tape) (fuel : ℕ) (state : State) :
    take code publicData tape fuel state = InstructionClock.take (command code publicData tape) fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [take, InstructionClock.take, command_exact]
    congr 1
    funext next
    exact ih next

theorem tick_log_length (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) (world : World) :
    (OracleProgram.run (tick code publicData tape state) world).run.2.length ≤ 1 := by
  rw [command_exact]
  exact InstructionClock.single_log_length _ _

theorem firstRead_of_tick (code : List Instruction) (publicData : Input) (tape : Tape) (state : State)
    (before : List NativeTranscript.Observation) (world : World) (input : Input)
    (unseen : seen before input = false)
    (hit : seen (before ++ (OracleProgram.run (tick code publicData tape state) world).run.2) input = true) :
    firstRead (command code publicData tape) (.inl state, before) = some input := by
  rw [CausalStreamCoverage.seen_append, unseen, command_exact] at hit
  cases chosen : command code publicData tape state with
  | done next =>
    rw [chosen, Bool.false_or] at hit
    change seen [] input = true at hit
    simp [seen] at hit
  | start key next =>
    rw [chosen, Bool.false_or] at hit
    change seen [.start key] input = true at hit
    simp [seen, CausalStreamExposure.touches] at hit
  | hash key next =>
    rw [chosen, Bool.false_or] at hit
    change seen [.hash key (List.ofFn (InputIndexedOracle.sha512 world key))] input = true at hit
    simp [seen, CausalStreamExposure.touches] at hit
  | read key offset count next =>
    rw [chosen, Bool.false_or] at hit
    change seen [.output key offset (InputIndexedOracle.bytes world key offset count)] input = true at hit
    have info : key = input ∧ 0 < count := by
      simpa only [seen, List.any_cons, List.any_nil, Bool.or_false, CausalStreamExposure.touches,
        InputIndexedOracle.bytes_length, decide_eq_true_eq] using hit
    rcases info with ⟨rfl, positive⟩
    simp only [firstRead, CausalSeedExposure.request, chosen, positive, unseen, and_self, ite_true]
end FormalProof4FHE.HasteBoots.PrivateCoinByteRequest
