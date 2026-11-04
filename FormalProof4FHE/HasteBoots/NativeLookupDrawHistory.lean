module

public import FormalProof4FHE.HasteBoots.NativeLookupBatch

@[expose] public section

/-!
# Compression, rejected offsets and accepted offset in retained draw order

The complete draw records are retained. The first draw supplies y, the
middle draws are exactly the rejected offsets, and the final draw supplies
r. Suspension changes none of these positions. This is an invariant of the
existing execution, not a replacement sampler or a filtered draw history.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupDrawHistory

open NativeLookupChallenge
open InputIndexedOracle (World)

noncomputable section

variable {p degree : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

def Roles (machine : Machine K) : Prop :=
  match machine.control with
  | .compression _ => machine.draws = [] ∧ machine.rejected = 0
  | .reciprocal y _ table _ =>
      ∃ first middle, machine.draws = first :: middle ∧ first.value = y ∧
        middle.length = machine.rejected ∧ ∀ draw ∈ middle, allowed table draw.value = false
  | .finished y r _ table _ =>
      ∃ first middle last, machine.draws = first :: (middle ++ [last]) ∧
        first.value = y ∧ last.value = r ∧ middle.length = machine.rejected ∧
        (∀ draw ∈ middle, allowed table draw.value = false) ∧ allowed table r = true

omit [Algebra (ZMod p) K] in
theorem initial_roles (w : ℕ) (transcript : NativeTranscript.Transcript) :
    Roles (initialExecute (K := K) p degree w transcript).1 := ⟨rfl, rfl⟩

theorem tick_roles (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (valid : Roles machine) :
    Roles (tickExecute basis w width rows machine world).1 := by
  rcases machine with ⟨control, draws, rejected⟩
  cases control with
  | finished => exact valid
  | compression field =>
    change draws = [] ∧ rejected = 0 at valid
    cases resultEq : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next => simpa only [tickExecute, resultEq, Roles] using valid
    | finished completed transcript =>
      simp only [tickExecute, resultEq, Roles]
      rw [valid.1, valid.2]
      exact ⟨⟨TypedFieldRequest.scalarValue basis completed.values, completed⟩, [], rfl, rfl, rfl, by simp⟩
  | reciprocal y weights table field =>
    obtain ⟨first, middle, history, firstValue, count, rejectedOffsets⟩ := valid
    change draws = first :: middle at history
    change middle.length = rejected at count
    cases resultEq : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      simpa only [tickExecute, resultEq, Roles] using
        (show Roles ⟨.reciprocal y weights table field, draws, rejected⟩ from
          ⟨first, middle, history, firstValue, count, rejectedOffsets⟩)
    | finished completed transcript =>
      cases accepts : allowed table (TypedFieldRequest.scalarValue basis completed.values) with
      | true =>
        simp only [tickExecute, resultEq, accepts, ite_true, Roles]
        refine ⟨first, middle, ⟨TypedFieldRequest.scalarValue basis completed.values, completed⟩, ?_, firstValue, rfl, count, rejectedOffsets, True.intro⟩
        rw [history, List.cons_append]
      | false =>
        simp only [tickExecute, resultEq, accepts, Bool.false_eq_true, ite_false, Roles]
        refine ⟨first, middle ++ [⟨TypedFieldRequest.scalarValue basis completed.values, completed⟩], ?_, firstValue, ?_, ?_⟩
        · rw [history, List.cons_append]
        · simp only [List.length_append, List.length_singleton, count]
        · intro draw member
          rcases List.mem_append.mp member with prior | added
          · exact rejectedOffsets draw prior
          · have same := List.mem_singleton.mp added
            subst draw
            exact accepts

theorem execute_roles (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (machine : Machine K) (world : World) (valid : Roles machine) :
    Roles (execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick_roles basis w width rows machine world valid)

theorem request_roles (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (transcript : NativeTranscript.Transcript) (world : World) :
    Roles (OracleProgram.run (request basis w width fuel rows transcript) world).run.1 := by
  rw [run_request]
  exact execute_roles basis w width fuel rows _ world (initial_roles w transcript)

/-- Independent invariant for every active or completed batch job. -/
def BatchRoles (machine : NativeLookupBatch.Machine p K) : Prop :=
  (match machine.control with
    | .sampling _ _ selection => Roles selection
    | _ => True) ∧
  ∀ completed ∈ machine.completed, Roles completed.selection

omit [Algebra (ZMod p) K] in
theorem initial_batch (actions : List (NativeLookupBatch.Action p)) (transcript : NativeTranscript.Transcript) :
    BatchRoles (NativeLookupBatch.initial (K := K) actions transcript) := ⟨True.intro, by simp [NativeLookupBatch.initial]⟩

omit [Algebra (ZMod p) K] in
theorem afterSample_batch (machine : NativeLookupBatch.Machine p K) (job : NativeLookupBatch.Job p)
    (todo : List (NativeLookupBatch.Action p)) (selection : Machine K)
    (valid : BatchRoles machine) (good : Roles selection) :
    BatchRoles (NativeLookupBatch.afterSample machine job todo selection) := by
  cases controlEq : selection.control with
  | compression field =>
    simpa only [NativeLookupBatch.afterSample, controlEq, BatchRoles] using
      (show Roles selection ∧ (∀ completed ∈ machine.completed, Roles completed.selection) from ⟨good, valid.2⟩)
  | reciprocal y weights table field =>
    simpa only [NativeLookupBatch.afterSample, controlEq, BatchRoles] using
      (show Roles selection ∧ (∀ completed ∈ machine.completed, Roles completed.selection) from ⟨good, valid.2⟩)
  | finished y r weights table transcript =>
    simp only [NativeLookupBatch.afterSample, controlEq, BatchRoles]
    refine ⟨True.intro, ?_⟩
    intro completed member
    rcases List.mem_append.mp member with prior | added
    · exact valid.2 completed prior
    · have same := List.mem_singleton.mp added
      subst completed
      exact good

theorem tick_batch (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (valid : BatchRoles machine) :
    BatchRoles (NativeLookupBatch.tickExecute basis w machine world).1 := by
  rcases machine with ⟨control, done, completed⟩
  cases control with
  | finished transcript => exact valid
  | ready todo transcript =>
    cases todo with
    | nil => exact valid
    | cons action todo =>
      cases action with
      | request ordinal => exact valid
      | sample job => exact ⟨initial_roles w transcript, valid.2⟩
  | sampling job todo selection =>
    apply afterSample_batch _ job todo _ valid
    exact tick_roles basis w job.request.width job.request.rows selection world valid.1

theorem execute_batch (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World) (valid : BatchRoles machine) :
    BatchRoles (NativeLookupBatch.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick_batch basis w machine world valid)

theorem completed_roles (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (actions : List (NativeLookupBatch.Action p)) (transcript : NativeTranscript.Transcript) (world : World)
    (completed : NativeLookupBatch.Completed p K)
    (member : completed ∈ (NativeLookupBatch.execute basis w fuel
      (NativeLookupBatch.initial actions transcript) world).1.completed) : Roles completed.selection :=
  (execute_batch basis w fuel _ world (initial_batch actions transcript)).2 completed member

end

end FormalProof4FHE.HasteBoots.NativeLookupDrawHistory
