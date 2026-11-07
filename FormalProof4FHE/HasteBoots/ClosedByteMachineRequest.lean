module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineHistory
@[expose] public section

/-! Exact next-request classification for the closed interpreter. A local
instruction is represented as `done next` for this single-instruction view;
it does not terminate the whole interpreter. Oracle requests retain their
actual next state. This lets the existing conditional first-read laws consume
the actual closed-machine request without treating local steps as exposures. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineRequest
open InputIndexedOracle (Input World)
open ClosedByteMachine (Instruction State price charge setRegister setTape)
open OracleProgram (Program)
open NativeTranscript (Observation)
open CausalStreamExposure (seen firstRead)

def instruction (publicData : Input) (state : State) (instruction : Instruction) : OracleMachine.Command State State :=
  let next := charge state (price publicData state instruction)
  match instruction with
  | .constant dst value => .done (setRegister next dst value)
  | .copy dst src => .done (setRegister next dst (state.registers src))
  | .add dst left right => .done (setRegister next dst (state.registers left+state.registers right))
  | .push dst src => .done (setTape next dst (state.registers src :: state.tapes dst))
  | .pop src dst => match state.tapes src with
    | [] => .done {next with stopped := some .abort}
    | value :: tail => .done (setRegister (setTape next src tail) dst value)
  | .branchZero src target => .done {next with pc := if state.registers src = 0 then target else next.pc}
  | .jump target => .done {next with pc := target}
  | .publicCopy dst => .done (setTape next dst publicData)
  | .start src => .start (state.tapes src) next
  | .read src dst offset count => .read (state.tapes src) offset count (fun values => setTape next dst values)
  | .readTape src dst offset count =>
      .read (state.tapes src) (TranscriptFrame.fromLittleEndian (state.tapes offset))
        (TranscriptFrame.fromLittleEndian (state.tapes count)) (fun values => setTape next dst values)
  | .hash src dst => .hash (state.tapes src) (fun digest => setTape next dst (List.ofFn digest))
  | .halt => .done {next with stopped := some .halt}
  | .reject => .done {next with stopped := some .reject}

def command (code : List Instruction) (publicData : Input) (state : State) : OracleMachine.Command State State :=
  match state.stopped with
  | some _ => .done state
  | none => match code[state.pc]? with
    | none => .done {charge state 1 with stopped := some .abort}
    | some chosen => instruction publicData state chosen

def single : OracleMachine.Command State State → Program State
  | .done state => .pure state
  | .start input next => .start input (.pure next)
  | .read input offset count next => .read input offset count (fun values => .pure (next values))
  | .hash input next => .hash input (fun digest => .pure (next digest))

theorem instruction_exact (publicData : Input) (state : State) (chosen : Instruction) :
    ClosedByteMachine.issue publicData state chosen = single (instruction publicData state chosen) := by
  cases chosen with
  | pop src dst => cases h : state.tapes src <;> simp only [ClosedByteMachine.issue,instruction,h] <;> rfl
  | _ => rfl

theorem command_exact (code : List Instruction) (publicData : Input) (state : State) :
    ClosedByteMachine.tick code publicData state = single (command code publicData state) := by
  cases stopped : state.stopped with
  | some stop => simp only [ClosedByteMachine.tick,command,stopped,single]
  | none =>
    cases selected : code[state.pc]? with
    | none => simp only [ClosedByteMachine.tick,command,stopped,selected,single]
    | some chosen =>
      simpa only [ClosedByteMachine.tick,command,stopped,selected] using instruction_exact publicData state chosen

theorem firstRead_of_tick (code : List Instruction) (publicData : Input) (state : State)
    (before : List Observation) (world : World) (input : Input)
    (unseen : seen before input = false)
    (hit : seen (before ++ (OracleProgram.run (ClosedByteMachine.tick code publicData state) world).run.2) input = true) :
    firstRead (command code publicData) (.inl state,before) = some input := by
  rw [CausalStreamCoverage.seen_append,unseen,command_exact] at hit
  cases chosen : command code publicData state with
  | done next =>
    rw [chosen,Bool.false_or] at hit
    change seen [] input = true at hit; simp [seen] at hit
  | start key next =>
    rw [chosen,Bool.false_or] at hit
    change seen [.start key] input = true at hit
    simp [seen,CausalStreamExposure.touches] at hit
  | hash key next =>
    rw [chosen,Bool.false_or] at hit
    change seen [.hash key (List.ofFn (InputIndexedOracle.sha512 world key))] input = true at hit
    simp [seen,CausalStreamExposure.touches] at hit
  | read key offset count next =>
    rw [chosen,Bool.false_or] at hit
    change seen [.output key offset (InputIndexedOracle.bytes world key offset count)] input = true at hit
    have info : key = input ∧ 0 < count := by
      simpa only [seen,List.any_cons,List.any_nil,Bool.or_false,CausalStreamExposure.touches,
        InputIndexedOracle.bytes_length,decide_eq_true_eq] using hit
    rcases info with ⟨rfl,positive⟩
    simp only [firstRead,CausalSeedExposure.request,chosen,positive,unseen,and_self,ite_true]
/-- An actual first positive instruction read supplies both the existing
conditional-law selector and the exact earlier full source history. -/
theorem coverage (past : World → NativeTranscript.Execution State) (code : List Instruction) (publicData : Input)
    (fuel : ℕ) (world : World) (input : Input)
    (touched : seen (ClosedByteMachineHistory.history past code publicData fuel world).run.2 input = true) :
    seen (past world).run.2 input = true ∨ ∃ index < fuel,
      firstRead (command code publicData)
        (.inl (ClosedByteMachineHistory.history past code publicData index world).run.1,
          (ClosedByteMachineHistory.history past code publicData index world).run.2) = some input ∧
      CausalFirstStreamPrefix.recover input (ClosedByteMachineHistory.history past code publicData fuel world).run.2 =
        some (ClosedByteMachineHistory.history past code publicData index world).run.2 := by
  cases inherited : seen (past world).run.2 input with
  | true => exact Or.inl rfl
  | false =>
    obtain ⟨index,bound,unseen,hit⟩ := ClosedByteMachineHistory.first_flip past code publicData fuel world input inherited touched
    have stepHit : seen ((ClosedByteMachineHistory.history past code publicData index world).run.2 ++
        (OracleProgram.run (ClosedByteMachine.tick code publicData
          (ClosedByteMachineHistory.history past code publicData index world).run.1) world).run.2) input = true := by
      simpa only [ClosedByteMachineHistory.history_succ] using hit
    exact Or.inr ⟨index,bound,firstRead_of_tick code publicData _ _ world input unseen stepHit,
      (ClosedByteMachineHistory.recover_at_flip past code publicData fuel index world input bound unseen hit).1⟩
end FormalProof4FHE.HasteBoots.ClosedByteMachineRequest
