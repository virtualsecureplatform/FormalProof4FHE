module

public import FormalProof4FHE.HasteBoots.NativeScalarBatchUpdate
public import FormalProof4FHE.HasteBoots.NativeGoldLookupProducer

@[expose] public section

/-!
# Online native independent scalar-batch verifier

The actual ordered proof messages are checked, bound and interpolated with
one common challenge per round. Candidate rejection and receipt state are
retained across analysis prefixes; no runtime retry cap is introduced.
Returned subclaims are unauthenticated, exactly as in native `batch::verify`.
Internal precondition failures are explicit checked-model failures; proving
them unreachable from accepted preflight is separate from Rust refinement.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarBatchVerifier

open InputIndexedOracle (World)
open NativeTranscript (Transcript Observation)
open OracleProgram (Program bind run)
open NativeFields NativeGoldExtensionArithmetic NativeScalarBatchWire NativeScalarBatchPreflight

structure SubClaim where
  point : List Word
  expected : Word

inductive Error where
  | reject (reason : NativeScalarBatchPreflight.Error)
  | invalidRound | invalidPacket | invalidCoefficients | invalidInterpolation
  deriving DecidableEq

structure State where
  round : ℕ
  expected : List Word
  point : List Word
  transcript : Transcript

/-- Retained analysis history; this does not add native transcript messages. -/
structure CompletedRound where
  packet : RoundPacket
  challenge : Word
  coefficients : NativeFieldVector.State
  priorExpected : List Word
  expected : List Word

inductive Control where
  | ready
  | sampling (packet : RoundPacket) (field : NativeFieldVector.State)
  | finished (claims : List SubClaim)
  | failed (error : Error)

structure Machine where
  control : Control
  state : State
  completed : List CompletedRound

def initial (transcript : Transcript) (statement : Statement) (proof : Proof) : Machine :=
  match beginVerify transcript statement proof with
  | .error error => ⟨.failed (.reject error), ⟨0, statement.claims.val, [], transcript⟩, []⟩
  | .ok bound => ⟨.ready, ⟨0, statement.claims.val, [], bound⟩, []⟩

def fail (machine : Machine) (error : Error) : Machine := { machine with control := .failed error }

/-- Pure native guards precede round binding and the shared challenge request.
The explicit usize/access failures concern violated internal preconditions. -/
def prepare (statement : Statement) (proof : Proof) (machine : Machine) : Machine ⊕ (Machine × RoundPacket) :=
  match statement.infos.val.head? with
  | none => .inl (fail machine .invalidRound)
  | some first =>
      if machine.state.round < first.numVariables.val then
        if fits : machine.state.round < 2 ^ 64 then
          match NativeScalarBatchRoundPacket.packet ⟨machine.state.round, fits⟩ proof with
          | none => .inl (fail machine .invalidPacket)
          | some packet =>
              match bindCheckedRound machine.state.transcript packet machine.state.expected with
              | .error error => .inl (fail machine (.reject error))
              | .ok transcript => .inr ({ machine with state.transcript := transcript }, packet)
        else .inl (fail machine .invalidRound)
      else .inl { machine with control := .finished (machine.state.expected.map (fun value => ⟨machine.state.point, value⟩)) }

/-- Decode the completed canonical three-coordinate scalar, update the actual
expected vector in native zip order, then append the shared point coordinate. -/
def afterField (machine : Machine) (packet : RoundPacket) : NativeFieldVector.Status → Machine
  | .suspended field => { machine with control := .sampling packet field }
  | .finished coefficients transcript =>
      let received := { machine with state.transcript := transcript }
      match NativeGoldLookupProducer.decode coefficients.values with
      | none => fail received .invalidCoefficients
      | some challenge =>
          match NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
          | none => fail received .invalidInterpolation
          | some expected =>
              ⟨.ready, ⟨machine.state.round + 1, expected, machine.state.point ++ [challenge], transcript⟩,
                machine.completed ++ [⟨packet, challenge, coefficients, machine.state.expected, expected⟩]⟩

def tick (statement : Statement) (proof : Proof) (machine : Machine) : Program Machine :=
  match machine.control with
  | .finished _ | .failed _ => .pure machine
  | .ready =>
      match prepare statement proof machine with
      | .inl stopped => .pure stopped
      | .inr (bound, packet) =>
          bind (TypedFieldRequest.beginScalar goldilocksModulus 3 7 bound.state.transcript challengeLabel)
            (fun field => .pure { bound with control := .sampling packet field })
  | .sampling packet field =>
      bind (NativeFieldVector.drive goldilocksModulus 1 field)
        (fun result => .pure (afterField machine packet result))

def tickExecute (statement : Statement) (proof : Proof) (machine : Machine) (world : World) :
    Machine × List Observation :=
  match machine.control with
  | .finished _ | .failed _ => (machine, [])
  | .ready =>
      match prepare statement proof machine with
      | .inl stopped => (stopped, [])
      | .inr (bound, packet) =>
          let started := TypedFieldRequest.beginExecute goldilocksModulus 3 7 bound.state.transcript challengeLabel
          ({ bound with control := .sampling packet started.1 }, started.2)
  | .sampling packet field =>
      let trial := NativeFieldVector.driveExecute goldilocksModulus 1 field world
      (afterField machine packet trial.1, trial.2)

theorem run_tick (statement : Statement) (proof : Proof) (machine : Machine) (world : World) :
    (run (tick statement proof machine) world).run = tickExecute statement proof machine world := by
  cases control : machine.control with
  | finished claims => simp only [tick, tickExecute, control, OracleProgram.run, CanonicalTranscriptSampler.run_pure]
  | failed error => simp only [tick, tickExecute, control, OracleProgram.run, CanonicalTranscriptSampler.run_pure]
  | ready =>
    cases prepared : prepare statement proof machine with
    | inl stopped => simp only [tick, tickExecute, control, prepared, OracleProgram.run, CanonicalTranscriptSampler.run_pure]
    | inr bound =>
      rcases bound with ⟨bound, packet⟩
      simp only [tick, tickExecute, control, prepared, OracleProgram.run_bind, ObservationReplay.run_bind,
        TypedFieldRequest.run_beginScalar, OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]
  | sampling packet field =>
    simp only [tick, tickExecute, control, OracleProgram.run_bind, ObservationReplay.run_bind,
      NativeFieldVector.run_drive, OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]

def steps (statement : Statement) (proof : Proof) : ℕ → Machine → Program Machine
  | 0, machine => .pure machine
  | fuel + 1, machine => bind (tick statement proof machine) (steps statement proof fuel)

def execute (statement : Statement) (proof : Proof) : ℕ → Machine → World → Machine × List Observation
  | 0, machine, _ => (machine, [])
  | fuel + 1, machine, world =>
      let trial := tickExecute statement proof machine world
      let later := execute statement proof fuel trial.1 world
      (later.1, trial.2 ++ later.2)

theorem run_steps (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World) :
    (run (steps statement proof fuel machine) world).run = execute statement proof fuel machine world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih => simp only [steps, execute, OracleProgram.run_bind, ObservationReplay.run_bind, run_tick, ih]

theorem execute_add (statement : Statement) (proof : Proof) (first extra : ℕ) (machine : Machine) (world : World) :
    execute statement proof (first + extra) machine world =
      let earlier := execute statement proof first machine world
      let later := execute statement proof extra earlier.1 world
      (later.1, earlier.2 ++ later.2) := by
  induction first generalizing machine with
  | zero => simp only [Nat.zero_add, execute, List.nil_append]
  | succ first ih => simp only [Nat.succ_add, execute, ih, List.append_assoc]

theorem steps_replay (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) :
    ObservationReplay.Replayable (run (steps statement proof fuel machine)) := OracleProgram.run_replay _

def verifyPrefix (fuel : ℕ) (transcript : Transcript) (statement : Statement) (proof : Proof) : Program Machine :=
  steps statement proof fuel (initial transcript statement proof)

theorem execute_terminal (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World)
    (terminal : (∃ claims, machine.control = .finished claims) ∨ ∃ error, machine.control = .failed error) :
    execute statement proof fuel machine world = (machine, []) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rcases terminal with ⟨claims, finished⟩ | ⟨error, failed⟩
    · simp only [execute, tickExecute, finished, ih, List.nil_append]
    · simp only [execute, tickExecute, failed, ih, List.nil_append]

theorem initial_success (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (accepted : beginVerify transcript statement proof = .ok result) :
    initial transcript statement proof = ⟨.ready, ⟨0, statement.claims.val, [], result⟩, []⟩ := by
  rw [initial, accepted]

theorem initial_failure (transcript : Transcript) (statement : Statement) (proof : Proof)
    (error : NativeScalarBatchPreflight.Error) (rejected : beginVerify transcript statement proof = .error error) :
    initial transcript statement proof = ⟨.failed (.reject error), ⟨0, statement.claims.val, [], transcript⟩, []⟩ := by
  rw [initial, rejected]

end FormalProof4FHE.HasteBoots.NativeScalarBatchVerifier
