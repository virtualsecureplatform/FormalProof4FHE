module

public import FormalProof4FHE.HasteBoots.NativeLookupChallenge
public import FormalProof4FHE.HasteBoots.NativeUsizeMessage

@[expose] public section

/-!
# Ordered shared lookup challenge requests and repetitions

This is the control of `shared::all_challenges` before helper commitments.
Each request index is absorbed even for zero repetitions. Every repetition
finishes its reciprocal rejection loop before the next starts. Analysis
exhaustion retains the full active reader, receipts, draws, completed jobs
and transcript. Helper commitments, inverse representation, native preflight,
whole-body linking, and checked Rust correspondence remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupBatch

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript Observation utf8 appendBytes)
open OracleProgram (Program bind run)

noncomputable section

structure Request (p : ℕ) where
  width : ℕ
  rows : List (List (ZMod p))
  repetitions : ℕ

structure Job (p : ℕ) where
  ordinal : NativeUsizeMessage.Usize
  repetition : ℕ
  request : Request p

inductive Action (p : ℕ) where
  | request (ordinal : NativeUsizeMessage.Usize)
  | sample (job : Job p)

/-- Registry order, followed by native repetition order. The explicit
64-bit bound prevents ordinal truncation or aliasing. -/
def schedule {p count : ℕ} (fits : count ≤ 2 ^ 64) (requests : Fin count → Request p) : List (Action p) :=
  (List.ofFn (fun index : Fin count =>
    let ordinal : NativeUsizeMessage.Usize := ⟨index.val, lt_of_lt_of_le index.isLt fits⟩
    Action.request ordinal :: List.ofFn (fun repetition : Fin (requests index).repetitions =>
      Action.sample ⟨ordinal, repetition.val, requests index⟩))).flatten

def requestLabel : Input := utf8 "shared lookup challenge request"

structure Completed (p : ℕ) (K : Type) where
  job : Job p
  selection : NativeLookupChallenge.Machine K

inductive Control (p : ℕ) (K : Type) where
  | ready (todo : List (Action p)) (transcript : Transcript)
  | sampling (job : Job p) (todo : List (Action p)) (selection : NativeLookupChallenge.Machine K)
  | finished (transcript : Transcript)

structure Machine (p : ℕ) (K : Type) where
  control : Control p K
  done : List (Action p)
  completed : List (Completed p K)

def initial {p : ℕ} {K : Type} (actions : List (Action p)) (transcript : Transcript) : Machine p K :=
  ⟨.ready actions transcript, [], []⟩

def afterSample {p : ℕ} {K : Type} (machine : Machine p K) (job : Job p) (todo : List (Action p))
    (selection : NativeLookupChallenge.Machine K) : Machine p K :=
  match selection.control with
  | .finished _ _ _ _ transcript =>
      ⟨.ready todo transcript, machine.done ++ [.sample job], machine.completed ++ [⟨job, selection⟩]⟩
  | _ => { machine with control := .sampling job todo selection }

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

def tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ) (machine : Machine p K) :
    Program (Machine p K) :=
  match machine.control with
  | .finished _ => .pure machine
  | .ready [] transcript => .pure { machine with control := .finished transcript }
  | .ready (.request ordinal :: todo) transcript =>
      .pure { machine with
        control := .ready todo (appendBytes transcript requestLabel (NativeUsizeMessage.encode ordinal))
        done := machine.done ++ [.request ordinal] }
  | .ready (.sample job :: todo) transcript =>
      bind (NativeLookupChallenge.initial p degree w transcript) (fun selection =>
        .pure { machine with control := .sampling job todo selection })
  | .sampling job todo selection =>
      bind (NativeLookupChallenge.tick basis w job.request.width job.request.rows selection)
        (fun updated => .pure (afterSample machine job todo updated))

def tickExecute (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : Machine p K) (world : World) : Machine p K × List Observation :=
  match machine.control with
  | .finished _ => (machine, [])
  | .ready [] transcript => ({ machine with control := .finished transcript }, [])
  | .ready (.request ordinal :: todo) transcript =>
      ({ machine with
        control := .ready todo (appendBytes transcript requestLabel (NativeUsizeMessage.encode ordinal))
        done := machine.done ++ [.request ordinal] }, [])
  | .ready (.sample job :: todo) transcript =>
      let started := NativeLookupChallenge.initialExecute p degree w transcript
      ({ machine with control := .sampling job todo started.1 }, started.2)
  | .sampling job todo selection =>
      let trial := NativeLookupChallenge.tickExecute basis w job.request.width job.request.rows selection world
      (afterSample machine job todo trial.1, trial.2)

theorem run_tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : Machine p K) (world : World) :
    (run (tick basis w machine) world).run = tickExecute basis w machine world := by
  rcases machine with ⟨control, done, completed⟩
  cases control with
  | finished => rfl
  | ready todo transcript =>
    cases todo with
    | nil => rfl
    | cons action todo =>
      cases action with
      | request ordinal => rfl
      | sample job =>
        simp only [tick, tickExecute, OracleProgram.run_bind, ObservationReplay.run_bind,
          NativeLookupChallenge.run_initial, OracleProgram.run, CanonicalTranscriptSampler.run_pure,
          List.append_nil]
  | sampling job todo selection =>
    simp only [tick, tickExecute, OracleProgram.run_bind, ObservationReplay.run_bind,
      NativeLookupChallenge.run_tick, OracleProgram.run, CanonicalTranscriptSampler.run_pure,
      List.append_nil]

def steps (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ) : ℕ → Machine p K → Program (Machine p K)
  | 0, machine => .pure machine
  | fuel + 1, machine => bind (tick basis w machine) (steps basis w fuel)

def execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ) :
    ℕ → Machine p K → World → Machine p K × List Observation
  | 0, machine, _ => (machine, [])
  | fuel + 1, machine, world =>
      let trial := tickExecute basis w machine world
      let later := execute basis w fuel trial.1 world
      (later.1, trial.2 ++ later.2)

theorem run_steps (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : Machine p K) (world : World) :
    (run (steps basis w fuel machine) world).run = execute basis w fuel machine world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih => simp only [steps, execute, OracleProgram.run_bind, ObservationReplay.run_bind, run_tick, ih]

theorem execute_add (basis : Module.Basis (Fin degree) (ZMod p) K) (w first extra : ℕ)
    (machine : Machine p K) (world : World) :
    execute basis w (first + extra) machine world =
      let earlier := execute basis w first machine world
      let later := execute basis w extra earlier.1 world
      (later.1, earlier.2 ++ later.2) := by
  induction first generalizing machine with
  | zero => simp [execute]
  | succ first ih => simp only [Nat.succ_add, execute, ih, List.append_assoc]

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
def pending (control : Control p K) : List (Action p) :=
  match control with
  | .ready todo _ => todo
  | .sampling job todo _ => .sample job :: todo
  | .finished _ => []

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
def Progress (actions : List (Action p)) (machine : Machine p K) : Prop :=
  machine.done ++ pending machine.control = actions

theorem tick_progress (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (actions : List (Action p)) (machine : Machine p K) (world : World) (valid : Progress actions machine) :
    Progress actions (tickExecute basis w machine world).1 := by
  rcases machine with ⟨control, done, completed⟩
  cases control with
  | finished => exact valid
  | ready todo transcript =>
    cases todo with
    | nil => exact valid
    | cons action todo =>
      cases action with
      | request ordinal => simpa only [tickExecute, Progress, pending, List.append_assoc, List.singleton_append] using valid
      | sample job => exact valid
  | sampling job todo selection =>
    simp only [tickExecute, afterSample]
    split <;> simpa only [Progress, pending, List.append_assoc, List.singleton_append] using valid

theorem execute_progress (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (actions : List (Action p)) (machine : Machine p K) (world : World) (valid : Progress actions machine) :
    Progress actions (execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick_progress basis w actions machine world valid)

theorem steps_replay (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ) (machine : Machine p K) :
    ObservationReplay.Replayable (run (steps basis w fuel machine)) := OracleProgram.run_replay _

/-- Full field-state and public-table invariants for one active or retained job. -/
def GoodSelection (basis : Module.Basis (Fin degree) (ZMod p) K) (job : Job p)
    (selection : NativeLookupChallenge.Machine K) : Prop :=
  NativeLookupChallenge.MachineValid basis selection ∧
    NativeLookupChallenge.SelectionValid job.request.width job.request.rows selection ∧
    NativeLookupChallenge.CountsValid selection

def Terminal (selection : NativeLookupChallenge.Machine K) : Prop :=
  match selection.control with
  | .finished _ _ _ _ _ => True
  | _ => False

def Valid (basis : Module.Basis (Fin degree) (ZMod p) K) (machine : Machine p K) : Prop :=
  (match machine.control with
    | .sampling job _ selection => GoodSelection basis job selection
    | _ => True) ∧
  ∀ completed ∈ machine.completed,
    GoodSelection basis completed.job completed.selection ∧ Terminal completed.selection

theorem initial_valid (basis : Module.Basis (Fin degree) (ZMod p) K)
    (actions : List (Action p)) (transcript : Transcript) : Valid basis (initial actions transcript) := by
  exact ⟨True.intro, by simp [initial]⟩

theorem afterSample_valid (basis : Module.Basis (Fin degree) (ZMod p) K)
    (machine : Machine p K) (job : Job p) (todo : List (Action p))
    (selection : NativeLookupChallenge.Machine K) (valid : Valid basis machine)
    (good : GoodSelection basis job selection) : Valid basis (afterSample machine job todo selection) := by
  cases controlEq : selection.control with
  | compression field =>
    simpa only [afterSample, controlEq, Valid] using (show GoodSelection basis job selection ∧
      (∀ completed ∈ machine.completed, GoodSelection basis completed.job completed.selection ∧ Terminal completed.selection) from ⟨good, valid.2⟩)
  | reciprocal y weights table field =>
    simpa only [afterSample, controlEq, Valid] using (show GoodSelection basis job selection ∧
      (∀ completed ∈ machine.completed, GoodSelection basis completed.job completed.selection ∧ Terminal completed.selection) from ⟨good, valid.2⟩)
  | finished y r weights table transcript =>
    simp only [afterSample, controlEq, Valid]
    refine ⟨True.intro, ?_⟩
    intro completed member
    rcases List.mem_append.mp member with prior | added
    · exact valid.2 completed prior
    · have same := List.mem_singleton.mp added
      subst completed
      exact ⟨good, by simp only [Terminal, controlEq]⟩

theorem tick_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : Machine p K) (world : World) (valid : Valid basis machine) :
    Valid basis (tickExecute basis w machine world).1 := by
  rcases machine with ⟨control, done, completed⟩
  cases control with
  | finished transcript => exact valid
  | ready todo transcript =>
    cases todo with
    | nil => exact valid
    | cons action todo =>
      cases action with
      | request ordinal => exact valid
      | sample job =>
        exact ⟨⟨NativeLookupChallenge.initial_valid basis w transcript, True.intro, ⟨rfl, rfl⟩⟩, valid.2⟩
  | sampling job todo selection =>
    apply afterSample_valid basis _ job todo _ valid
    exact ⟨NativeLookupChallenge.tick_valid basis w job.request.width job.request.rows selection world valid.1.1,
      NativeLookupChallenge.tick_selection basis w job.request.width job.request.rows selection world valid.1.2.1,
      NativeLookupChallenge.tick_counts basis w job.request.width job.request.rows selection world valid.1.2.2⟩

theorem execute_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : Machine p K) (world : World) (valid : Valid basis machine) :
    Valid basis (execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick_valid basis w machine world valid)

/-- Every retained accepted offset avoids zero and the poles of its own
request's public table, compressed with its own retained y. -/
theorem completed_allowed (basis : Module.Basis (Fin degree) (ZMod p) K)
    (machine : Machine p K) (valid : Valid basis machine) (completed : Completed p K)
    (member : completed ∈ machine.completed) (y r : K) (weights table : List K) (transcript : Transcript)
    (finished : completed.selection.control = .finished y r weights table transcript) :
    r ≠ 0 ∧ ∀ value ∈ NativeLookupChallenge.tableAt completed.job.request.rows completed.job.request.width y,
      r + value ≠ 0 := by
  have selected := (valid.2 completed member).1.2.1
  unfold NativeLookupChallenge.SelectionValid at selected
  rw [finished] at selected
  have source : table = NativeLookupChallenge.tableAt completed.job.request.rows completed.job.request.width y := by
    rw [selected.2.1, selected.1]
    rfl
  have allowed := (NativeLookupChallenge.allowed_iff table r).mp selected.2.2
  rwa [source] at allowed

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
def jobs (actions : List (Action p)) : List (Job p) :=
  actions.filterMap (fun action => match action with | .request _ => none | .sample job => some job)

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
def Ordered (machine : Machine p K) : Prop :=
  machine.completed.map (fun completed => completed.job) = jobs machine.done

theorem tick_ordered (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : Machine p K) (world : World) (ordered : Ordered machine) :
    Ordered (tickExecute basis w machine world).1 := by
  rcases machine with ⟨control, done, completed⟩
  cases control with
  | finished transcript => exact ordered
  | ready todo transcript =>
    cases todo with
    | nil => exact ordered
    | cons action todo =>
      cases action with
      | request ordinal => simpa only [tickExecute, Ordered, jobs, List.filterMap_append,
          List.filterMap_cons, List.filterMap_nil, List.append_nil] using ordered
      | sample job => exact ordered
  | sampling job todo selection =>
    simp only [tickExecute, afterSample]
    split <;> simp only [Ordered, List.map_append, List.map_cons, List.map_nil,
      jobs, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    · exact congrArg (fun prior => prior ++ [job]) ordered
    all_goals exact ordered

theorem execute_ordered (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : Machine p K) (world : World) (ordered : Ordered machine) :
    Ordered (execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact ordered
  | succ fuel ih => exact ih _ (tick_ordered basis w machine world ordered)

/-- A completed batch returns every scheduled job in exact order, with
neither omitted repetitions nor cross-request substitution. -/
theorem finished_jobs (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (actions : List (Action p)) (transcript : Transcript) (world : World) (final : Transcript)
    (finished : (execute basis w fuel (initial actions transcript) world).1.control = .finished final) :
    (execute basis w fuel (initial actions transcript) world).1.completed.map (fun completed => completed.job) =
      jobs actions := by
  have ordered := execute_ordered basis w fuel (initial actions transcript) world rfl
  have progress := execute_progress basis w fuel actions (initial actions transcript) world rfl
  unfold Progress at progress
  rw [finished] at progress
  simp only [pending, List.append_nil] at progress
  rw [ordered, progress]

theorem execute_finished (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : Machine p K) (world : World) (transcript : Transcript)
    (finished : machine.control = .finished transcript) :
    execute basis w fuel machine world = (machine, []) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [execute, tickExecute, finished, ih, List.nil_append]

def request {count : ℕ} (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (fits : count ≤ 2 ^ 64) (requests : Fin count → Request p) (transcript : Transcript) : Program (Machine p K) :=
  steps basis w fuel (initial (schedule fits requests) transcript)

/-- Splitting the analysis budget preserves all active and completed jobs,
raw rejected draws, byte cursors, receipts and observations exactly. -/
theorem request_add {count : ℕ} (basis : Module.Basis (Fin degree) (ZMod p) K) (w first extra : ℕ)
    (fits : count ≤ 2 ^ 64) (requests : Fin count → Request p) (transcript : Transcript) (world : World) :
    (run (request basis w (first + extra) fits requests transcript) world).run =
      let earlier := (run (request basis w first fits requests transcript) world).run
      let later := (run (steps basis w extra earlier.1) world).run
      (later.1, earlier.2 ++ later.2) := by
  simp only [request, run_steps, execute_add]

theorem request_valid {count : ℕ} (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (fits : count ≤ 2 ^ 64) (requests : Fin count → Request p) (transcript : Transcript) (world : World) :
    Valid basis (run (request basis w fuel fits requests transcript) world).run.1 := by
  rw [request, run_steps]
  exact execute_valid basis w fuel _ world (initial_valid basis _ transcript)

theorem request_progress {count : ℕ} (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (fits : count ≤ 2 ^ 64) (requests : Fin count → Request p) (transcript : Transcript) (world : World) :
    Progress (schedule fits requests) (run (request basis w fuel fits requests transcript) world).run.1 := by
  rw [request, run_steps]
  exact execute_progress basis w fuel _ _ world rfl

theorem request_ordered {count : ℕ} (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (fits : count ≤ 2 ^ 64) (requests : Fin count → Request p) (transcript : Transcript) (world : World) :
    Ordered (run (request basis w fuel fits requests transcript) world).run.1 := by
  rw [request, run_steps]
  exact execute_ordered basis w fuel _ world rfl

theorem request_replay {count : ℕ} (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (fits : count ≤ 2 ^ 64) (requests : Fin count → Request p) (transcript : Transcript) :
    ObservationReplay.Replayable (run (request basis w fuel fits requests transcript)) := OracleProgram.run_replay _

/-- Actual native challenge extensions; this compiler stops before inverse
representation and helper commitment construction. -/
def goldilocks {count : ℕ} (fuel : ℕ) (fits : count ≤ 2 ^ 64)
    (requests : Fin count → Request NativeFields.goldilocksModulus) (transcript : Transcript) :
    Program (Machine NativeFields.goldilocksModulus NativeExtensionFields.Goldilocks3) := by
  classical
  exact request NativeExtensionFields.goldilocksBasis 7 fuel fits requests transcript

def babyBear {count : ℕ} (fuel : ℕ) (fits : count ≤ 2 ^ 64)
    (requests : Fin count → Request NativeFields.babyBearModulus) (transcript : Transcript) :
    Program (Machine NativeFields.babyBearModulus NativeExtensionFields.BabyBear6) := by
  classical
  exact request NativeExtensionFields.babyBearBasis 31 fuel fits requests transcript

end

end FormalProof4FHE.HasteBoots.NativeLookupBatch
