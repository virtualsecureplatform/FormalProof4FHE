module

public import FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler

@[expose] public section

/-!
# Resumable native coefficient collection and receipt finalization

One analysis step attempts one canonical candidate. Rejection keeps the
coefficient index fixed; acceptance advances it. The field reader and all
raw chunks survive suspension. A receipt is emitted only after collecting
the requested number of coefficients. This models `field_values`' scalar
collection; typed field conversion/basis grouping and Rust refinement are
separate obligations. Native callers still establish modulus and machine-word request-count bounds.
-/

namespace FormalProof4FHE.HasteBoots.NativeFieldVector

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript FieldPhase Observation Execution)
open OracleProgram (Program bind run)

structure State where
  phase : FieldPhase
  remaining : ℕ
  values : List ℕ
  chunks : List Input

def initial (phase : FieldPhase) (count : ℕ) : State := ⟨phase, count, [], []⟩

def advance (p : ℕ) (state : State) (trial : CanonicalTranscriptSampler.Outcome) : State :=
  match trial.accepted with
  | none => { state with phase := trial.phase, chunks := state.chunks ++ trial.chunks }
  | some raw =>
      ⟨trial.phase, state.remaining - 1,
        state.values ++ [CanonicalTranscriptSampler.candidate p raw], state.chunks ++ trial.chunks⟩

def collect (p : ℕ) : ℕ → State → Program State
  | 0, state => .pure state
  | fuel + 1, state =>
      if state.remaining = 0 then .pure state
      else bind (CanonicalTranscriptSampler.samplePrefix p 1 state.phase)
        (fun trial => collect p fuel (advance p state trial))

def execute (p : ℕ) : ℕ → State → World → State × List Observation
  | 0, state, _ => (state, [])
  | fuel + 1, state, world =>
      if state.remaining = 0 then (state, [])
      else
        let trial := CanonicalTranscriptSampler.executePrefix p 1 state.phase world
        let tail := execute p fuel (advance p state trial.1) world
        (tail.1, trial.2 ++ tail.2)

theorem run_collect (p fuel : ℕ) (state : State) (world : World) :
    (run (collect p fuel state) world).run = execute p fuel state world := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [collect, execute]
    split
    · rfl
    · simp only [OracleProgram.run_bind, ObservationReplay.run_bind,
        CanonicalTranscriptSampler.run_samplePrefix, ih]

theorem execute_complete (p fuel : ℕ) (state : State) (world : World) (complete : state.remaining = 0) :
    execute p fuel state world = (state, []) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [execute, complete]

/-- The global candidate budget resumes at the current coefficient and byte
cursor. No rejected candidate or previously accepted value is replayed. -/
theorem execute_add (p first extra : ℕ) (state : State) (world : World) :
    execute p (first + extra) state world =
      let earlier := execute p first state world
      let later := execute p extra earlier.1 world
      (later.1, earlier.2 ++ later.2) := by
  induction first generalizing state with
  | zero => simp [execute]
  | succ first ih =>
    rw [Nat.succ_add]
    by_cases complete : state.remaining = 0
    · simp [execute, complete, execute_complete p extra state world complete]
    · simp only [execute, complete, ite_false, ih]
      simp only [List.append_assoc]

theorem advance_count (p : ℕ) (state : State) (trial : CanonicalTranscriptSampler.Outcome)
    (pending : state.remaining ≠ 0) :
    (advance p state trial).remaining + (advance p state trial).values.length =
      state.remaining + state.values.length := by
  cases found : trial.accepted with
  | none => simp [advance, found]
  | some raw => simp only [advance, found, List.length_append, List.length_singleton]; omega

theorem count_invariant (p fuel : ℕ) (state : State) (world : World) :
    (execute p fuel state world).1.remaining + (execute p fuel state world).1.values.length =
      state.remaining + state.values.length := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simp [execute, complete]
    · simp only [execute, complete, ite_false]
      exact (ih _).trans (advance_count _ _ _ complete)

theorem completed_length (p fuel count : ℕ) (phase : FieldPhase) (world : World)
    (complete : (execute p fuel (initial phase count) world).1.remaining = 0) :
    (execute p fuel (initial phase count) world).1.values.length = count := by
  have total := count_invariant p fuel (initial phase count) world
  rw [complete] at total
  simpa only [initial, List.length_nil, zero_add, add_zero] using total

def ValuesValid (p : ℕ) (state : State) : Prop := ∀ value ∈ state.values, value < p

theorem advance_valid (p : ℕ) (state : State) (world : World) (valid : ValuesValid p state) :
    ValuesValid p (advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1) := by
  cases found : (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1.accepted with
  | none => simpa only [ValuesValid, advance, found] using valid
  | some raw =>
    have bound := CanonicalTranscriptSampler.accepted_below p 1 state.phase world raw found
    simp only [ValuesValid, advance, found, List.mem_append, List.mem_singleton, or_imp,
      forall_and, forall_eq]
    exact ⟨valid, bound⟩

theorem values_valid (p fuel : ℕ) (state : State) (world : World) (valid : ValuesValid p state) :
    ValuesValid p (execute p fuel state world).1 := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simpa only [execute, complete, ite_true] using valid
    · simpa only [execute, complete, ite_false] using ih _ (advance_valid p state world valid)

def Retains (origin : Input) (state : State) : Prop :=
  state.phase.consumed = origin ++ state.chunks.flatten

theorem advance_retains (p : ℕ) (origin : Input) (state : State) (world : World)
    (retained : Retains origin state) :
    Retains origin (advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1) := by
  have kept := CanonicalTranscriptSampler.phase_retains_chunks p 1 state.phase world
  cases found : (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1.accepted <;>
    simp only [Retains, advance, found, kept, List.flatten_append]
  all_goals exact retained ▸ List.append_assoc _ _ _

theorem retains (p fuel : ℕ) (origin : Input) (state : State) (world : World)
    (retained : Retains origin state) : Retains origin (execute p fuel state world).1 := by
  induction fuel generalizing state with
  | zero => exact retained
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simpa only [execute, complete, ite_true] using retained
    · simpa only [execute, complete, ite_false] using ih _ (advance_retains p origin state world retained)

theorem advance_header (p : ℕ) (state : State) (world : World) :
    let next := advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1
    next.phase.pending = state.phase.pending ∧ next.phase.label = state.phase.label := by
  have kept := CanonicalTranscriptSampler.phase_retains_chunks p 1 state.phase world
  cases found : (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1.accepted <;>
    simp [advance, found, kept]

/-- Neither resumption nor rejected candidates can change the original
request header or the label under which its receipt is absorbed. -/
theorem header_preserved (p fuel : ℕ) (state : State) (world : World) :
    (execute p fuel state world).1.phase.pending = state.phase.pending ∧
      (execute p fuel state world).1.phase.label = state.phase.label := by
  induction fuel generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simp [execute, complete]
    · simp only [execute, complete, ite_false]
      have later := ih (advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1)
      have earlier := advance_header p state world
      exact ⟨later.1.trans earlier.1, later.2.trans earlier.2⟩

theorem advance_coherent (p : ℕ) (state : State) (world : World)
    (coherent : NativeTranscript.Coherent world state.phase) :
    NativeTranscript.Coherent world
      (advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1).phase := by
  have next := CanonicalTranscriptSampler.final_coherent p 1 state.phase world coherent
  cases found : (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1.accepted <;>
    simpa only [advance, found] using next

theorem coherent (p fuel : ℕ) (state : State) (world : World)
    (initialCoherent : NativeTranscript.Coherent world state.phase) :
    NativeTranscript.Coherent world (execute p fuel state world).1.phase := by
  induction fuel generalizing state with
  | zero => exact initialCoherent
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simpa only [execute, complete, ite_true] using initialCoherent
    · simpa only [execute, complete, ite_false] using ih _ (advance_coherent p state world initialCoherent)

inductive Status where
  | suspended (state : State)
  | finished (state : State) (transcript : Transcript)

def stateOf : Status → State
  | .suspended state => state
  | .finished state _ => state

def finalize (state : State) : Program Status :=
  if state.remaining = 0 then bind (NativeTranscriptProgram.finishField state.phase)
    (fun transcript => .pure (.finished state transcript))
  else .pure (.suspended state)

def drive (p fuel : ℕ) (state : State) : Program Status := bind (collect p fuel state) finalize

def request (p fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) : Program Status :=
  bind (NativeTranscriptProgram.beginField transcript label p count)
    (fun phase => drive p fuel (initial phase count))

/-- A completed request cannot emit its receipt a second time on resumption. -/
def resume (p extra : ℕ) : Status → Program Status
  | .suspended state => drive p extra state
  | .finished state transcript => .pure (.finished state transcript)

def finishExecute (world : World) (state : State) : Status × List Observation :=
  if state.remaining = 0 then
    let finished := (NativeTranscript.finishField world state.phase).run
    (.finished state finished.1, finished.2)
  else (.suspended state, [])

def driveExecute (p fuel : ℕ) (state : State) (world : World) : Status × List Observation :=
  let collected := execute p fuel state world
  let finished := finishExecute world collected.1
  (finished.1, collected.2 ++ finished.2)

def resumeExecute (p extra : ℕ) (status : Status) (world : World) : Status × List Observation :=
  match status with
  | .suspended state => driveExecute p extra state world
  | .finished state transcript => (.finished state transcript, [])

theorem run_finalize (world : World) (state : State) :
    (run (finalize state) world).run = finishExecute world state := by
  by_cases complete : state.remaining = 0
  · simp only [finalize, finishExecute, complete, ite_true, OracleProgram.run_bind,
      NativeTranscriptProgram.run_finishField, ObservationReplay.run_bind, OracleProgram.run,
      CanonicalTranscriptSampler.run_pure, List.append_nil]
  · simp only [finalize, finishExecute, complete, ite_false, OracleProgram.run,
      CanonicalTranscriptSampler.run_pure]

theorem run_drive (p fuel : ℕ) (state : State) (world : World) :
    (run (drive p fuel state) world).run = driveExecute p fuel state world := by
  simp only [drive, driveExecute, OracleProgram.run_bind, ObservationReplay.run_bind, run_collect, run_finalize]

theorem run_resume (p extra : ℕ) (status : Status) (world : World) :
    (run (resume p extra status) world).run = resumeExecute p extra status world := by
  cases status with
  | suspended state => exact run_drive _ _ _ _
  | finished state transcript => rfl

theorem run_request (p fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) (world : World) :
    (run (request p fuel transcript label count) world).run =
      let started := (NativeTranscript.beginField transcript label p count).run
      let finished := driveExecute p fuel (initial started.1 count) world
      (finished.1, started.2 ++ finished.2) := by
  simp only [request, OracleProgram.run_bind, ObservationReplay.run_bind,
    NativeTranscriptProgram.run_beginField, run_drive]

theorem finish_state (world : World) (state : State) :
    stateOf (finishExecute world state).1 = state := by
  by_cases complete : state.remaining = 0 <;> simp [finishExecute, complete, stateOf]

def StatusValid : Status → Prop
  | .suspended state => state.remaining ≠ 0
  | .finished state _ => state.remaining = 0

theorem finish_status (world : World) (state : State) : StatusValid (finishExecute world state).1 := by
  by_cases complete : state.remaining = 0 <;> simp [finishExecute, complete, StatusValid]

theorem request_status (p fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) (world : World) :
    StatusValid (run (request p fuel transcript label count) world).run.1 := by
  simp only [run_request, driveExecute]
  exact finish_status _ _

theorem request_count (p fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) (world : World) :
    let result := stateOf (run (request p fuel transcript label count) world).run.1
    result.remaining + result.values.length = count := by
  simp only [run_request, driveExecute, finish_state]
  simpa only [initial, List.length_nil, add_zero] using
    count_invariant p fuel (initial (NativeTranscript.beginField transcript label p count).run.1 count) world

theorem request_values_valid (p fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) (world : World) :
    ValuesValid p (stateOf (run (request p fuel transcript label count) world).run.1) := by
  simp only [run_request, driveExecute, finish_state]
  apply values_valid
  simp [ValuesValid, initial]

theorem request_finished_length (p fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ)
    (world : World) (state : State) (result : Transcript)
    (finished : (run (request p fuel transcript label count) world).run.1 = .finished state result) :
    state.values.length = count := by
  have total := request_count p fuel transcript label count world
  have done := request_status p fuel transcript label count world
  rw [finished] at total done
  change state.remaining + state.values.length = count at total
  change state.remaining = 0 at done
  omega

theorem drive_add (p first extra : ℕ) (state : State) (world : World) :
    driveExecute p (first + extra) state world =
      let earlier := driveExecute p first state world
      let later := resumeExecute p extra earlier.1 world
      (later.1, earlier.2 ++ later.2) := by
  unfold driveExecute
  rw [execute_add]
  by_cases complete : (execute p first state world).1.remaining = 0
  · have stopped := execute_complete p extra (execute p first state world).1 world complete
    simp only [stopped, finishExecute, complete, ite_true, resumeExecute, List.append_nil]
  · simp only [finishExecute, complete, ite_false, resumeExecute, driveExecute, List.append_nil,
      List.append_assoc]

/-- Resumption keeps the original field request and emits the eventual
receipt once. It never starts a second request for the remaining slots. -/
theorem request_add (p first extra : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) (world : World) :
    (run (request p (first + extra) transcript label count) world).run =
      let earlier := (run (request p first transcript label count) world).run
      let later := (run (resume p extra earlier.1) world).run
      (later.1, earlier.2 ++ later.2) := by
  simp only [run_request, drive_add, run_resume, List.append_assoc]

/-- A zero-count request still creates its field reader and binds the empty
raw-prefix receipt, even with zero candidate-analysis budget. -/
theorem request_zero (p fuel : ℕ) (transcript : Transcript) (label : Input) (world : World) :
    (run (request p fuel transcript label 0) world).run =
      let phase := (NativeTranscript.beginField transcript label p 0).run.1
      let receipt := (NativeTranscript.finishField world phase).run
      (.finished (initial phase 0) receipt.1, [.start phase.pending.input] ++ receipt.2) := by
  rw [run_request]
  unfold driveExecute
  dsimp only
  rw [execute_complete p fuel _ world (by rfl)]
  rfl

/-- Prime-vector prelude from `ClassicalTranscript::challenge_prime`.
The returned coefficients are canonical naturals; typed conversion is pending. -/
def primeRequest (p fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) : Program Status :=
  request p fuel (NativeTranscript.appendBytes transcript
    (NativeTranscript.utf8 "field challenge kind") (NativeTranscript.utf8 "prime vector")) label count

theorem no_premature_receipt (world : World) (state : State) (pending : state.remaining ≠ 0) :
    (run (finalize state) world).run = (.suspended state, []) := by
  rw [run_finalize]
  simp [finishExecute, pending]

theorem finished_resume (p extra : ℕ) (state : State) (transcript : Transcript) (world : World) :
    (run (resume p extra (.finished state transcript)) world).run = (.finished state transcript, []) := rfl

theorem request_replay (p fuel : ℕ) (transcript : Transcript) (label : Input) (count : ℕ) :
    ObservationReplay.Replayable (run (request p fuel transcript label count)) := OracleProgram.run_replay _

end FormalProof4FHE.HasteBoots.NativeFieldVector
