module

public import FormalProof4FHE.HasteBoots.TypedFieldRequest

@[expose] public section

/-!
# Online compilation of native lookup challenge selection

This compiles one `packed_extension_lookup::challenges` repetition through
its accepted reciprocal offset. One analysis step drives one canonical
coefficient candidate. Inner rejection retains the reader; a completed
forbidden offset retains its whole draw and receipt before starting the
next scalar request. Exhaustion is a resumable analysis state, not native
rejection. Repetitions, inverse-table representation, the rest of the child
body, whole-history probability/work bounds and Rust refinement remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupChallenge

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript Observation utf8)
open OracleProgram (Program bind run)

noncomputable section

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

def powersFrom (y : K) : ℕ → K → List K
  | 0, _ => []
  | n + 1, value => value :: powersFrom y n (value * y)

def powers (y : K) (width : ℕ) : List K := powersFrom y width 1

/-- Literal native zip/fold, retaining truncation for malformed public shapes.
The trusted rectangular table contract is a separate caller obligation. -/
def compress (weights : List K) (row : List (ZMod p)) : K :=
  (row.zip weights).foldl (fun out pair => out + pair.2 * algebraMap (ZMod p) K pair.1) 0

def tableAt (rows : List (List (ZMod p))) (width : ℕ) (y : K) : List K :=
  rows.map (compress (powers y width))

def allowed (table : List K) (r : K) : Bool :=
  decide (r ≠ 0) && table.all (fun value => decide (r + value ≠ 0))

theorem allowed_iff (table : List K) (r : K) :
    allowed table r = true ↔ r ≠ 0 ∧ ∀ value ∈ table, r + value ≠ 0 := by
  simp [allowed]

structure Draw (K : Type) where
  value : K
  coefficients : NativeFieldVector.State

inductive Control (K : Type) where
  | compression (field : NativeFieldVector.State)
  | reciprocal (y : K) (weights table : List K) (field : NativeFieldVector.State)
  | finished (y r : K) (weights table : List K) (transcript : Transcript)

structure Machine (K : Type) where
  control : Control K
  draws : List (Draw K)
  rejected : ℕ

def hashLabel : Input := utf8 "extension tuple hash challenge"
def reciprocalLabel : Input := utf8 "extension tuple reciprocal challenge"

def initial (p degree w : ℕ) (transcript : Transcript) : Program (Machine K) :=
  bind (TypedFieldRequest.beginScalar p degree w transcript hashLabel)
    (fun field => .pure ⟨.compression field, [], 0⟩)

def initialExecute (p degree w : ℕ) (transcript : Transcript) : Machine K × List Observation :=
  let started := TypedFieldRequest.beginExecute p degree w transcript hashLabel
  (⟨.compression started.1, [], 0⟩, started.2)

def tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) : Program (Machine K) :=
  match machine.control with
  | .finished _ _ _ _ _ => .pure machine
  | .compression field =>
    bind (NativeFieldVector.drive p 1 field) (fun result => match result with
      | .suspended field => .pure { machine with control := .compression field }
      | .finished field transcript =>
        let y := TypedFieldRequest.scalarValue basis field.values
        let weights := powers y width
        let table := rows.map (compress weights)
        bind (TypedFieldRequest.beginScalar p degree w transcript reciprocalLabel) (fun next =>
          .pure ⟨.reciprocal y weights table next, machine.draws ++ [⟨y, field⟩], machine.rejected⟩))
  | .reciprocal y weights table field =>
    bind (NativeFieldVector.drive p 1 field) (fun result => match result with
      | .suspended field => .pure { machine with control := .reciprocal y weights table field }
      | .finished field transcript =>
        let r := TypedFieldRequest.scalarValue basis field.values
        let draws := machine.draws ++ [⟨r, field⟩]
        if allowed table r then
          .pure { machine with control := .finished y r weights table transcript, draws := draws }
        else bind (TypedFieldRequest.beginScalar p degree w transcript reciprocalLabel) (fun next =>
          .pure ⟨.reciprocal y weights table next, draws, machine.rejected + 1⟩))

def tickExecute (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) : Machine K × List Observation :=
  match machine.control with
  | .finished _ _ _ _ _ => (machine, [])
  | .compression field =>
    let trial := NativeFieldVector.driveExecute p 1 field world
    match trial.1 with
    | .suspended field => ({ machine with control := .compression field }, trial.2)
    | .finished field transcript =>
      let y := TypedFieldRequest.scalarValue basis field.values
      let weights := powers y width
      let table := rows.map (compress weights)
      let next := TypedFieldRequest.beginExecute p degree w transcript reciprocalLabel
      (⟨.reciprocal y weights table next.1, machine.draws ++ [⟨y, field⟩], machine.rejected⟩, trial.2 ++ next.2)
  | .reciprocal y weights table field =>
    let trial := NativeFieldVector.driveExecute p 1 field world
    match trial.1 with
    | .suspended field => ({ machine with control := .reciprocal y weights table field }, trial.2)
    | .finished field transcript =>
      let r := TypedFieldRequest.scalarValue basis field.values
      let draws := machine.draws ++ [⟨r, field⟩]
      if allowed table r then
        ({ machine with control := .finished y r weights table transcript, draws := draws }, trial.2)
      else
        let next := TypedFieldRequest.beginExecute p degree w transcript reciprocalLabel
        (⟨.reciprocal y weights table next.1, draws, machine.rejected + 1⟩, trial.2 ++ next.2)

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem run_initial (p degree w : ℕ) (transcript : Transcript) (world : World) :
    (run (initial (K := K) p degree w transcript) world).run = initialExecute p degree w transcript := by
  rfl

theorem run_tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) :
    (run (tick basis w width rows machine) world).run = tickExecute basis w width rows machine world := by
  rcases machine with ⟨control, draws, rejected⟩
  cases control with
  | finished => rfl
  | compression field =>
    simp only [tick, tickExecute, OracleProgram.run_bind, ObservationReplay.run_bind, NativeFieldVector.run_drive]
    split <;> simp only [OracleProgram.run_bind, ObservationReplay.run_bind, TypedFieldRequest.run_beginScalar,
      OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]
  | reciprocal y weights table field =>
    simp only [tick, tickExecute, OracleProgram.run_bind, ObservationReplay.run_bind, NativeFieldVector.run_drive]
    split
    · simp only [OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]
    · split <;> simp only [OracleProgram.run_bind, ObservationReplay.run_bind, TypedFieldRequest.run_beginScalar,
        OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]

def steps (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ) (rows : List (List (ZMod p))) :
    ℕ → Machine K → Program (Machine K)
  | 0, machine => .pure machine
  | fuel + 1, machine => bind (tick basis w width rows machine) (steps basis w width rows fuel)

def execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ) (rows : List (List (ZMod p))) :
    ℕ → Machine K → World → Machine K × List Observation
  | 0, machine, _ => (machine, [])
  | fuel + 1, machine, world =>
    let trial := tickExecute basis w width rows machine world
    let later := execute basis w width rows fuel trial.1 world
    (later.1, trial.2 ++ later.2)

theorem run_steps (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) :
    (run (steps basis w width rows fuel machine) world).run = execute basis w width rows fuel machine world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih => simp only [steps, execute, OracleProgram.run_bind, ObservationReplay.run_bind, run_tick, ih]

/-- The same complete reader state, rejected draws and ordered log are
preserved by every split of the analysis budget. -/
theorem execute_add (basis : Module.Basis (Fin degree) (ZMod p) K) (w width first extra : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) :
    execute basis w width rows (first + extra) machine world =
      let earlier := execute basis w width rows first machine world
      let later := execute basis w width rows extra earlier.1 world
      (later.1, earlier.2 ++ later.2) := by
  induction first generalizing machine with
  | zero => simp [execute]
  | succ first ih => simp only [Nat.succ_add, execute, ih, List.append_assoc]

def request (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (transcript : Transcript) : Program (Machine K) :=
  bind (initial p degree w transcript) (steps basis w width rows fuel)

theorem run_request (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (transcript : Transcript) (world : World) :
    (run (request basis w width fuel rows transcript) world).run =
      let started := initialExecute p degree w transcript
      let result := execute basis w width rows fuel started.1 world
      (result.1, started.2 ++ result.2) := by
  simp only [request, OracleProgram.run_bind, ObservationReplay.run_bind, run_initial, run_steps]

theorem request_add (basis : Module.Basis (Fin degree) (ZMod p) K) (w width first extra : ℕ)
    (rows : List (List (ZMod p))) (transcript : Transcript) (world : World) :
    (run (request basis w width (first + extra) rows transcript) world).run =
      let earlier := (run (request basis w width first rows transcript) world).run
      let later := (run (steps basis w width rows extra earlier.1) world).run
      (later.1, earlier.2 ++ later.2) := by
  simp only [run_request, run_steps, execute_add, List.append_assoc]

def MachineValid (basis : Module.Basis (Fin degree) (ZMod p) K) (machine : Machine K) : Prop :=
  (match machine.control with
    | .compression field | .reciprocal _ _ _ field => TypedFieldRequest.FieldValid p degree field
    | .finished _ _ _ _ _ => True) ∧
  ∀ draw ∈ machine.draws, draw.coefficients.values.length = degree ∧
    NativeFieldVector.ValuesValid p draw.coefficients ∧
    draw.value = TypedFieldRequest.scalarValue basis draw.coefficients.values

omit [DecidableEq K] in
theorem append_draw_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (draws : List (Draw K))
    (completed : NativeFieldVector.State)
    (old : ∀ draw ∈ draws, draw.coefficients.values.length = degree ∧
      NativeFieldVector.ValuesValid p draw.coefficients ∧
      draw.value = TypedFieldRequest.scalarValue basis draw.coefficients.values)
    (length : completed.values.length = degree) (valid : NativeFieldVector.ValuesValid p completed) :
    ∀ draw ∈ draws ++ [⟨TypedFieldRequest.scalarValue basis completed.values, completed⟩],
      draw.coefficients.values.length = degree ∧ NativeFieldVector.ValuesValid p draw.coefficients ∧
      draw.value = TypedFieldRequest.scalarValue basis draw.coefficients.values := by
  intro draw member
  rcases List.mem_append.mp member with before | added
  · exact old draw before
  · have same := List.mem_singleton.mp added
    subst draw
    exact ⟨length, valid, rfl⟩

omit [DecidableEq K] in
theorem initial_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ) (transcript : Transcript) :
    MachineValid basis (initialExecute p degree w transcript).1 := by
  exact ⟨TypedFieldRequest.begin_valid p degree w transcript hashLabel, by simp [initialExecute]⟩

theorem tick_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (valid : MachineValid basis machine) :
    MachineValid basis (tickExecute basis w width rows machine world).1 := by
  rcases machine with ⟨control, draws, rejected⟩
  cases control with
  | finished => exact valid
  | compression field =>
    cases resultEq : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      have updated := TypedFieldRequest.drive_valid p degree 1 world field valid.1
      rw [resultEq] at updated
      simp only [tickExecute, resultEq, MachineValid]
      exact ⟨updated, valid.2⟩
    | finished completed transcript =>
      have complete := TypedFieldRequest.drive_finished_length p degree 1 world field completed transcript valid.1 resultEq
      simp only [tickExecute, resultEq, MachineValid]
      exact ⟨TypedFieldRequest.begin_valid p degree w transcript reciprocalLabel,
        append_draw_valid basis draws completed valid.2 complete.1 complete.2⟩
  | reciprocal y weights table field =>
    cases resultEq : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      have updated := TypedFieldRequest.drive_valid p degree 1 world field valid.1
      rw [resultEq] at updated
      simp only [tickExecute, resultEq, MachineValid]
      exact ⟨updated, valid.2⟩
    | finished completed transcript =>
      have complete := TypedFieldRequest.drive_finished_length p degree 1 world field completed transcript valid.1 resultEq
      have added := append_draw_valid basis draws completed valid.2 complete.1 complete.2
      by_cases accepts : allowed table (TypedFieldRequest.scalarValue basis completed.values) = true
      · simp only [tickExecute, resultEq, accepts, ite_true, MachineValid]
        exact ⟨True.intro, added⟩
      · simp only [tickExecute, resultEq, accepts, MachineValid]
        exact ⟨TypedFieldRequest.begin_valid p degree w transcript reciprocalLabel, added⟩

theorem execute_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (valid : MachineValid basis machine) :
    MachineValid basis (execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick_valid basis w width rows machine world valid)

theorem request_valid (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (transcript : Transcript) (world : World) :
    MachineValid basis (run (request basis w width fuel rows transcript) world).run.1 := by
  rw [run_request]
  exact execute_valid basis w width fuel rows _ world (initial_valid basis w transcript)

omit [DecidableEq K] in
theorem draw_coordinate (basis : Module.Basis (Fin degree) (ZMod p) K) (machine : Machine K)
    (valid : MachineValid basis machine) (draw : Draw K) (member : draw ∈ machine.draws) (i : Fin degree) :
    (basis.equivFun draw.value i).val = draw.coefficients.values[i.val]'(by
      have length := (valid.2 draw member).1
      omega) := by
  have information := valid.2 draw member
  rw [information.2.2]
  exact TypedFieldRequest.scalar_coordinate basis draw.coefficients.values information.1 information.2.1 i

/-- Frozen public compression data and the literal native exclusion check. -/
def SelectionValid (width : ℕ) (rows : List (List (ZMod p))) (machine : Machine K) : Prop :=
  match machine.control with
  | .compression _ => True
  | .reciprocal y weights table _ => weights = powers y width ∧ table = rows.map (compress weights)
  | .finished y r weights table _ =>
    weights = powers y width ∧ table = rows.map (compress weights) ∧ allowed table r = true

theorem tick_selection (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (valid : SelectionValid width rows machine) :
    SelectionValid width rows (tickExecute basis w width rows machine world).1 := by
  rcases machine with ⟨control, draws, rejected⟩
  cases control with
  | finished => exact valid
  | compression field =>
    simp only [tickExecute]
    split <;> simp only [SelectionValid, and_self]
  | reciprocal y weights table field =>
    simp only [tickExecute]
    split
    · exact valid
    · split
      next accepted => exact ⟨valid.1, valid.2, accepted⟩
      next => exact valid

theorem execute_selection (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (valid : SelectionValid width rows machine) :
    SelectionValid width rows (execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick_selection basis w width rows machine world valid)

/-- An actually completed online request excludes zero and every pole in
its own public table, with no assumed independent field draw. -/
theorem returned_allowed (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (transcript : Transcript) (world : World)
    (y r : K) (weights table : List K) (result : Transcript)
    (finished : (run (request basis w width fuel rows transcript) world).run.1.control =
      .finished y r weights table result) : r ≠ 0 ∧ ∀ value ∈ tableAt rows width y, r + value ≠ 0 := by
  have valid : SelectionValid width rows (run (request basis w width fuel rows transcript) world).run.1 := by
    rw [run_request]
    exact execute_selection basis w width fuel rows _ world True.intro
  change (match (run (request basis w width fuel rows transcript) world).run.1.control with
    | .compression _ => True
    | .reciprocal y weights table _ => weights = powers y width ∧ table = rows.map (compress weights)
    | .finished y r weights table _ => weights = powers y width ∧ table = rows.map (compress weights) ∧ allowed table r = true) at valid
  rw [finished] at valid
  have source : table = tableAt rows width y := by rw [valid.2.1, valid.1]; rfl
  have conditions := (allowed_iff table r).mp valid.2.2
  rw [source] at conditions
  exact conditions

theorem execute_finished (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World)
    (y r : K) (weights table : List K) (transcript : Transcript)
    (finished : machine.control = .finished y r weights table transcript) :
    execute basis w width rows fuel machine world = (machine, []) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [execute, tickExecute, finished, ih, List.nil_append]

def CountsValid (machine : Machine K) : Prop :=
  match machine.control with
  | .compression _ => machine.draws = [] ∧ machine.rejected = 0
  | .reciprocal _ _ _ _ => machine.draws.length = 1 + machine.rejected
  | .finished _ _ _ _ _ => machine.draws.length = 2 + machine.rejected

theorem tick_counts (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (valid : CountsValid machine) :
    CountsValid (tickExecute basis w width rows machine world).1 := by
  rcases machine with ⟨control, draws, rejected⟩
  cases control with
  | finished => exact valid
  | compression field =>
    simp only [CountsValid] at valid
    cases resultEq : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next => simpa only [tickExecute, resultEq, CountsValid] using valid
    | finished completed transcript =>
      simp only [tickExecute, resultEq, CountsValid, List.length_append, List.length_singleton]
      rw [valid.1, valid.2]
      rfl
  | reciprocal y weights table field =>
    simp only [CountsValid] at valid
    simp only [tickExecute]
    split
    · exact valid
    · split <;> simp only [CountsValid, List.length_append, List.length_singleton] <;> omega

theorem execute_counts (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (valid : CountsValid machine) :
    CountsValid (execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick_counts basis w width rows machine world valid)

theorem request_counts (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (transcript : Transcript) (world : World) :
    CountsValid (run (request basis w width fuel rows transcript) world).run.1 := by
  rw [run_request]
  exact execute_counts basis w width fuel rows _ world ⟨rfl, rfl⟩

def Pending (machine : Machine K) : Prop :=
  match machine.control with
  | .compression field | .reciprocal _ _ _ field => field.remaining ≠ 0
  | .finished _ _ _ _ _ => True

theorem tick_pending (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (positive : degree ≠ 0) :
    Pending (tickExecute basis w width rows machine world).1 := by
  rcases machine with ⟨control, draws, rejected⟩
  cases control with
  | finished => trivial
  | compression field =>
    simp only [tickExecute]
    split
    next next resultEq =>
      have status := NativeFieldVector.finish_status world (NativeFieldVector.execute p 1 field world).1
      change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute p 1 field world).1 at status
      rw [resultEq] at status
      exact status
    next => exact positive
  | reciprocal y weights table field =>
    simp only [tickExecute]
    split
    next next resultEq =>
      have status := NativeFieldVector.finish_status world (NativeFieldVector.execute p 1 field world).1
      change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute p 1 field world).1 at status
      rw [resultEq] at status
      exact status
    next => split
            · trivial
            · exact positive

theorem execute_pending (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (positive : degree ≠ 0)
    (pending : Pending machine) : Pending (execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact pending
  | succ fuel ih => exact ih _ (tick_pending basis w width rows machine world positive)

theorem request_pending (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (transcript : Transcript) (world : World) (positive : degree ≠ 0) :
    Pending (run (request basis w width fuel rows transcript) world).run.1 := by
  rw [run_request]
  exact execute_pending basis w width fuel rows _ world positive positive

theorem request_replay (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (transcript : Transcript) :
    ObservationReplay.Replayable (run (request basis w width fuel rows transcript)) := OracleProgram.run_replay _

/-- Native challenge fields; inverse-table serialization and the remaining
lookup body are not replaced by these challenge-selection entry points. -/
def goldilocks (width fuel : ℕ) (rows : List (List NativeFields.Goldilocks)) (transcript : Transcript) :
    Program (Machine NativeExtensionFields.Goldilocks3) := by
  classical
  exact request NativeExtensionFields.goldilocksBasis 7 width fuel rows transcript

def babyBear (width fuel : ℕ) (rows : List (List NativeFields.BabyBear)) (transcript : Transcript) :
    Program (Machine NativeExtensionFields.BabyBear6) := by
  classical
  exact request NativeExtensionFields.babyBearBasis 31 width fuel rows transcript

end

end FormalProof4FHE.HasteBoots.NativeLookupChallenge
