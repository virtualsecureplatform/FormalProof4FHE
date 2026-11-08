module
public import FormalProof4FHE.HasteBoots.NativeByteSliceIndex
@[expose] public section

/-! Concrete checked operations used by a mutable byte drop traversal.
The recursive measure is the remaining slice extent. This is not yet a source
loop, Rust lifetime or compiler refinement, and supplies no physical-work law. -/
namespace FormalProof4FHE.HasteBoots.NativeByteDropTraversal
open NativeReferenceMachine (State)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteSliceIndex (Slice)

inductive Iteration where
  | value (pointer : Pointer) (world : State)
  | invalid (world : State)
  deriving DecidableEq

def Iteration.world : Iteration → State
  | .value _ world | .invalid world => world

/-- A source-shaped iteration reborrows the whole slice, indexes a byte,
recovers its raw pointer and explicitly closes its temporary leases. -/
def iteration (world : State) (slice : Slice) (offset : Word) : Iteration :=
  match NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte with
  | none => .invalid world
  | some (value, borrowed) => match value with
    | .reference true reference length => match NativeByteSliceIndex.index borrowed ⟨reference, length⟩ offset with
      | .invalid next => .invalid next
      | .value child next => match NativeByteSliceIndex.rawByte next child with
        | none => .invalid next
        | some pointer =>
          let cleaned := NativeReferenceCleanup.closeScope world next
          if cleaned.pending.isEmpty then .value pointer cleaned.world else .invalid cleaned.world
    | _ => .invalid borrowed

structure Result where
  world : State
  cursor : Nat
  last : Option Pointer
  complete : Bool
  deriving DecidableEq

/-- The cursor is bounded by the original slice extent. Its successor never
wraps, even though the corresponding source addition uses wrapping usize. -/
def runFrom (slice : Slice) (cursor : Nat) (_bounded : cursor ≤ slice.length.val)
    (world : State) (last : Option Pointer) : Result :=
  if remaining : cursor < slice.length.val then
    match iteration world slice ⟨cursor, Nat.lt_trans remaining slice.length.isLt⟩ with
    | .invalid next => ⟨next, cursor, last, false⟩
    | .value pointer next => runFrom slice (cursor + 1) (by omega) next (some pointer)
  else ⟨world, cursor, last, true⟩
termination_by slice.length.val - cursor

def run (world : State) (slice : Slice) : Result := runFrom slice 0 (Nat.zero_le _) world none

/-- Unbounded operational control: stop at the slice extent, retain a failed
iteration, or execute one iteration and continue at the next cursor. -/
inductive Executes (slice : Slice) : Nat → State → Option Pointer → Result → Prop where
  | stop (cursor : Nat) (world : State) (last : Option Pointer) (done : cursor = slice.length.val) :
      Executes slice cursor world last ⟨world, cursor, last, true⟩
  | fail (cursor : Nat) (world next : State) (last : Option Pointer)
      (before : cursor < slice.length.val)
      (failed : iteration world slice ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ = .invalid next) :
      Executes slice cursor world last ⟨next, cursor, last, false⟩
  | next (cursor : Nat) (world next : State) (last : Option Pointer) (pointer : Pointer) (result : Result)
      (before : cursor < slice.length.val)
      (actual : iteration world slice ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ = .value pointer next)
      (later : Executes slice (cursor + 1) next (some pointer) result) :
      Executes slice cursor world last result

theorem runFrom_executes (slice : Slice) (cursor : Nat) (bounded : cursor ≤ slice.length.val)
    (world : State) (last : Option Pointer) :
    Executes slice cursor world last (runFrom slice cursor bounded world last) := by
  rw [runFrom]
  split
  · rename_i before
    cases actual : iteration world slice ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ with
    | invalid next => exact .fail cursor world next last before actual
    | value pointer next =>
      exact .next cursor world next last pointer _ before actual (runFrom_executes slice (cursor + 1) _ next (some pointer))
  · exact .stop cursor world last (by omega)
termination_by slice.length.val - cursor

theorem executes_result (slice : Slice) (cursor : Nat) (world : State) (last : Option Pointer) (result : Result)
    (executed : Executes slice cursor world last result) (bounded : cursor ≤ slice.length.val) :
    result = runFrom slice cursor bounded world last := by
  induction executed with
  | stop cursor world last done =>
    rw [runFrom]
    split
    · omega
    · rfl
  | fail cursor world next last before failed =>
    rw [runFrom]
    simp only [before, ↓reduceDIte, failed]
  | next cursor world next last pointer result before actual later ih =>
    rw [runFrom]
    simpa only [before, ↓reduceDIte, actual] using ih (Nat.succ_le_of_lt before)

theorem executes_deterministic (slice : Slice) (cursor : Nat) (world : State) (last : Option Pointer)
    (left right : Result) (first : Executes slice cursor world last left) (second : Executes slice cursor world last right)
    (bounded : cursor ≤ slice.length.val) : left = right :=
  (executes_result slice cursor world last left first bounded).trans
    (executes_result slice cursor world last right second bounded).symm

theorem run_executes (world : State) (slice : Slice) : Executes slice 0 world none (run world slice) :=
  runFrom_executes slice 0 (Nat.zero_le _) world none

theorem cursor_increment (length cursor : Word) (before : cursor.val < length.val) :
    (cursor.val + 1) % (2 ^ 64) = cursor.val + 1 := by
  apply Nat.mod_eq_of_lt
  have bound := length.isLt
  omega

theorem iteration_projects (world : State) (slice : Slice) (offset : Word) :
    NativeReferenceMachine.Runs world (iteration world slice offset).world := by
  cases actual : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte with
  | none => simp only [iteration, actual, Iteration.world]; exact .refl _
  | some output =>
    rcases output with ⟨value, borrowed⟩
    have first := NativeSliceLLBC.issue_projects world borrowed true _ value actual
    obtain ⟨length, same⟩ := NativeSliceLLBC.issue_returned_tag world borrowed true _ value actual
    subst value
    simp only [iteration, actual]
    cases indexed : NativeByteSliceIndex.index borrowed ⟨⟨world.nextTag⟩, length⟩ offset with
    | invalid next =>
      have second := NativeByteSliceIndex.index_projects borrowed ⟨⟨world.nextTag⟩, length⟩ offset
      rw [indexed] at second
      exact NativeReferenceMachine.runs_trans _ _ _ first second
    | value child next =>
      simp only []
      have second := NativeByteSliceIndex.index_projects borrowed ⟨⟨world.nextTag⟩, length⟩ offset
      rw [indexed] at second
      have priorRun := NativeReferenceMachine.runs_trans _ _ _ first second
      cases recovered : NativeByteSliceIndex.rawByte next child with
      | none => exact priorRun
      | some pointer =>
        simp only []
        split <;> exact NativeReferenceMachine.runs_trans _ _ _ priorRun (NativeReferenceCleanup.closeScope_projects world next)

theorem issue_reference_heap (world borrowed : State) (slice : Slice) (value : NativeSliceLLBC.Value)
    (issued : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte = some (value, borrowed)) :
    borrowed.pointers.heap = world.pointers.heap := by
  simp only [NativeSliceLLBC.issue, Option.bind_eq_some_iff] at issued
  obtain ⟨lease, _, issued⟩ := issued
  split at issued
  · rename_i checked
    obtain ⟨next, actual, same⟩ := Option.map_eq_some_iff.mp issued
    cases same
    simp only [NativeReferenceMachine.execute, checked.2.1, checked.2.2, Option.bind] at actual
    obtain ⟨_, _, _, pointers, _⟩ := NativeReferenceMachine.grant_success _ _ _ _ _ _ actual
    exact congrArg NativePointerMachine.State.heap pointers
  · cases issued

theorem iteration_heap_frame (world : State) (slice : Slice) (offset : Word) :
    (iteration world slice offset).world.pointers.heap = world.pointers.heap := by
  cases actual : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte with
  | none => simp only [iteration, actual, Iteration.world]
  | some output =>
    rcases output with ⟨value, borrowed⟩
    have first := issue_reference_heap world borrowed slice value actual
    obtain ⟨length, same⟩ := NativeSliceLLBC.issue_returned_tag world borrowed true _ value actual
    subst value
    simp only [iteration, actual]
    cases indexed : NativeByteSliceIndex.index borrowed ⟨⟨world.nextTag⟩, length⟩ offset with
    | invalid next =>
      have second := NativeByteSliceIndex.index_heap_frame borrowed ⟨⟨world.nextTag⟩, length⟩ offset
      rw [indexed] at second
      exact second.trans first
    | value child next =>
      simp only []
      have second := NativeByteSliceIndex.index_heap_frame borrowed ⟨⟨world.nextTag⟩, length⟩ offset
      rw [indexed] at second
      cases recovered : NativeByteSliceIndex.rawByte next child with
      | none => exact second.trans first
      | some pointer =>
        simp only []
        have frame := NativeReferenceCleanup.release_frame next (NativeReferenceCleanup.scopeTags world next)
        have heap := congrArg (fun state : State => state.pointers.heap) frame
        split <;> exact heap.trans (second.trans first)

theorem runFrom_heap_frame (slice : Slice) (cursor : Nat) (bounded : cursor ≤ slice.length.val)
    (world : State) (last : Option Pointer) :
    (runFrom slice cursor bounded world last).world.pointers.heap = world.pointers.heap := by
  rw [runFrom]
  split
  · rename_i remaining
    cases actual : iteration world slice ⟨cursor, Nat.lt_trans remaining slice.length.isLt⟩ with
    | invalid next =>
      simpa only [actual, Iteration.world] using iteration_heap_frame world slice ⟨cursor, Nat.lt_trans remaining slice.length.isLt⟩
    | value pointer next =>
      have first := iteration_heap_frame world slice ⟨cursor, Nat.lt_trans remaining slice.length.isLt⟩
      rw [actual] at first
      exact (runFrom_heap_frame slice (cursor + 1) _ next (some pointer)).trans first
  · rfl
termination_by slice.length.val - cursor

theorem run_heap_frame (world : State) (slice : Slice) :
    (run world slice).world.pointers.heap = world.pointers.heap := runFrom_heap_frame slice 0 (Nat.zero_le _) world none

theorem runFrom_projects (slice : Slice) (cursor : Nat) (bounded : cursor ≤ slice.length.val)
    (world : State) (last : Option Pointer) :
    NativeReferenceMachine.Runs world (runFrom slice cursor bounded world last).world := by
  rw [runFrom]
  split
  · rename_i remaining
    cases actual : iteration world slice ⟨cursor, Nat.lt_trans remaining slice.length.isLt⟩ with
    | invalid next =>
      exact (by simpa only [actual, Iteration.world] using iteration_projects world slice ⟨cursor, Nat.lt_trans remaining slice.length.isLt⟩)
    | value pointer next =>
      have first := iteration_projects world slice ⟨cursor, Nat.lt_trans remaining slice.length.isLt⟩
      rw [actual] at first
      exact NativeReferenceMachine.runs_trans _ _ _ first (runFrom_projects slice (cursor + 1) _ next (some pointer))
  · exact .refl _
termination_by slice.length.val - cursor

theorem run_projects (world : State) (slice : Slice) : NativeReferenceMachine.Runs world (run world slice).world :=
  runFrom_projects slice 0 (Nat.zero_le _) world none

theorem runFrom_cursor (slice : Slice) (cursor : Nat) (bounded : cursor ≤ slice.length.val)
    (world : State) (last : Option Pointer) :
    cursor ≤ (runFrom slice cursor bounded world last).cursor ∧
    (runFrom slice cursor bounded world last).cursor ≤ slice.length.val ∧
    ((runFrom slice cursor bounded world last).complete = true →
      (runFrom slice cursor bounded world last).cursor = slice.length.val) := by
  rw [runFrom]
  split
  · rename_i remaining
    cases actual : iteration world slice ⟨cursor, Nat.lt_trans remaining slice.length.isLt⟩ with
    | invalid next => exact ⟨Nat.le_refl _, bounded, by intro impossible; cases impossible⟩
    | value pointer next =>
      obtain ⟨lower, upper, complete⟩ := runFrom_cursor slice (cursor + 1) _ next (some pointer)
      exact ⟨Nat.le_trans (Nat.le_succ cursor) lower, upper, complete⟩
  · have same : cursor = slice.length.val := by omega
    exact ⟨Nat.le_refl _, bounded, fun _ => same⟩
termination_by slice.length.val - cursor

theorem run_complete_cursor (world : State) (slice : Slice) (complete : (run world slice).complete = true) :
    (run world slice).cursor = slice.length.val :=
  (runFrom_cursor slice 0 (Nat.zero_le _) world none).2.2 complete

theorem run_wellFormed (world : State) (valid : NativeReferenceMachine.WellFormed world) (slice : Slice) :
    NativeReferenceMachine.WellFormed (run world slice).world :=
  NativeSliceLLBC.reference_runs_wellFormed _ _ valid (run_projects world slice)

theorem run_reachable (world : State) (reachable : NativeReferenceMachine.Reachable world) (slice : Slice) :
    NativeReferenceMachine.Reachable (run world slice).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (run_projects world slice)

end FormalProof4FHE.HasteBoots.NativeByteDropTraversal
