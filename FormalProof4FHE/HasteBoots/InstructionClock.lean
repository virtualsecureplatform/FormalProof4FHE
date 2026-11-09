module
public import FormalProof4FHE.HasteBoots.OracleMachine
public import FormalProof4FHE.HasteBoots.CausalFirstStreamPrefix
public import FormalProof4FHE.HasteBoots.NativeProgramComposition
@[expose] public section

/-! An instruction clock that resumes after silent local commands. A done
command returns one instruction's next state; it does not halt iteration.
Full mixed prequery histories are retained at every instruction boundary. -/
namespace FormalProof4FHE.HasteBoots.InstructionClock
open InputIndexedOracle (Input World)
open NativeTranscript (Execution Observation)
open OracleProgram (Program)
open CausalStreamExposure (seen touches)
noncomputable section
variable {S : Type}

def single : OracleMachine.Command S S → Program S
  | .done state => .pure state
  | .start input next => .start input (.pure next)
  | .read input offset count next => .read input offset count (fun value => .pure (next value))
  | .hash input next => .hash input (fun value => .pure (next value))

theorem single_log_length (command : OracleMachine.Command S S) (world : World) :
    (OracleProgram.run (single command) world).run.2.length ≤ 1 := by
  cases command <;> first | exact Nat.zero_le 1 | exact Nat.le_refl 1

def take (step : S → OracleMachine.Command S S) : ℕ → S → Program S
  | 0, state => .pure state
  | fuel+1, state => OracleProgram.bind (single (step state)) (take step fuel)

theorem take_resume (step : S → OracleMachine.Command S S) (first later : ℕ) (state : S) :
    take step (first+later) state = OracleProgram.bind (take step first state) (take step later) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, take, OracleProgram.bind]
  | succ first ih =>
    simp only [Nat.succ_add, take, NativeProgramComposition.bind_assoc]
    congr 1
    funext next
    exact ih next

def history (past : World → Execution S) (step : S → OracleMachine.Command S S)
    (fuel : ℕ) (world : World) : Execution S :=
  past world >>= fun state => OracleProgram.run (take step fuel state) world

theorem history_replay {past : World → Execution S} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S S) (fuel : ℕ) :
    ObservationReplay.Replayable (history past step fuel) :=
  ObservationReplay.bind_replay replay (fun state => OracleProgram.run_replay (take step fuel state))

theorem history_zero (past : World → Execution S) (step : S → OracleMachine.Command S S) (world : World) :
    (history past step 0 world).run = (past world).run := by
  rw [history,ObservationReplay.run_bind]
  exact Prod.ext rfl (List.append_nil _)

theorem history_resume (past : World → Execution S) (step : S → OracleMachine.Command S S)
    (first later : ℕ) (world : World) :
    (history past step (first+later) world).run =
      ((OracleProgram.run (take step later (history past step first world).run.1) world).run.1,
        (history past step first world).run.2 ++
          (OracleProgram.run (take step later (history past step first world).run.1) world).run.2) := by
  simp only [history,ObservationReplay.run_bind,take_resume,OracleProgram.run_bind,List.append_assoc]

theorem history_prefix (past : World → Execution S) (step : S → OracleMachine.Command S S)
    (first later : ℕ) (bounded : first ≤ later) (world : World) :
    (history past step first world).run.2.IsPrefix (history past step later world).run.2 := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bounded
  rw [history_resume]
  exact ⟨_,rfl⟩

theorem history_succ (past : World → Execution S) (step : S → OracleMachine.Command S S)
    (fuel : ℕ) (world : World) :
    (history past step (fuel+1) world).run =
      ((OracleProgram.run (single (step (history past step fuel world).run.1)) world).run.1,
        (history past step fuel world).run.2 ++
          (OracleProgram.run (single (step (history past step fuel world).run.1)) world).run.2) := by
  rw [history_resume]
  simp only [take,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,WriterT.run_pure]
  change (_, _ ++ (_ ++ [])) = (_, _ ++ _)
  rw [List.append_nil]
  rfl

/-- A newly exposed stream has an actual first instruction boundary, even
when arbitrarily many earlier local steps produced no oracle observations. -/
theorem first_flip (past : World → Execution S) (step : S → OracleMachine.Command S S)
    (fuel : ℕ) (world : World) (input : Input)
    (unseen : seen (past world).run.2 input = false)
    (touched : seen (history past step fuel world).run.2 input = true) :
    ∃ index < fuel,
      seen (history past step index world).run.2 input = false ∧
      seen (history past step (index+1) world).run.2 input = true := by
  let test : ℕ → Prop := fun n => seen (history past step n world).run.2 input = true
  have existsTest : ∃ n, test n := ⟨fuel,touched⟩
  let first := Nat.find existsTest
  have hit : test first := Nat.find_spec existsTest
  have bound : first ≤ fuel := Nat.find_min' existsTest touched
  have positive : 0 < first := by
    by_contra notPositive
    have zero : first = 0 := by omega
    have atZero : seen (past world).run.2 input = true := by
      simpa only [test,zero,history_zero] using hit
    rw [unseen] at atZero
    contradiction
  refine ⟨first-1,by omega,?_,?_⟩
  · cases h : seen (history past step (first-1) world).run.2 input with
    | false => rfl
    | true => exact False.elim (Nat.find_min existsTest (by omega) h)
  · have equal : first-1+1 = first := by omega
    simpa only [equal] using hit

/-- Recovery at an actual first-exposure instruction boundary. -/
theorem recover_at_flip (past : World → Execution S) (step : S → OracleMachine.Command S S)
    (fuel index : ℕ) (world : World) (input : Input) (bound : index < fuel)
    (unseen : seen (history past step index world).run.2 input = false)
    (hit : seen (history past step (index+1) world).run.2 input = true) :
    CausalFirstStreamPrefix.recover input (history past step fuel world).run.2 =
        some (history past step index world).run.2 ∧
      ∃ offset values after, values ≠ [] ∧
        (history past step fuel world).run.2 =
          (history past step index world).run.2 ++ .output input offset values :: after := by
  have split := congrArg Prod.snd (history_succ past step index world)
  let tail := (OracleProgram.run (single (step (history past step index world).run.1)) world).run.2
  have length : tail.length ≤ 1 := single_log_length _ _
  have tailSeen : seen tail input = true := by
    rw [split,CausalStreamCoverage.seen_append,unseen] at hit
    exact hit
  cases shape : tail with
  | nil => simp [shape,seen] at tailSeen
  | cons entry rest =>
    have empty : rest = [] := by
      rw [shape,List.length_cons] at length
      exact List.length_eq_zero_iff.mp (by omega)
    have touch : touches input entry = true := by
      simpa only [shape,empty,seen,List.any_cons,List.any_nil,Bool.or_false] using tailSeen
    have nextLog : (history past step (index+1) world).run.2 =
        (history past step index world).run.2 ++ [entry] := by
      change (history past step (index+1) world).run.2 =
        (history past step index world).run.2 ++ tail at split
      simpa only [shape,empty] using split
    obtain ⟨after,full⟩ := history_prefix past step (index+1) fuel (by omega) world
    rw [nextLog,List.append_assoc,List.singleton_append] at full
    have recovered := CausalFirstStreamPrefix.recover_at input
      (history past step index world).run.2 after entry unseen touch
    refine ⟨?_,?_⟩
    · rw [← full]
      exact recovered
    · cases entry with
      | start key => simp [touches] at touch
      | hash key digest => simp [touches] at touch
      | output key offset values =>
        have info : key = input ∧ 0 < values.length := of_decide_eq_true touch
        rcases info with ⟨rfl,positive⟩
        exact ⟨offset,values,after,List.ne_nil_of_length_pos positive,full.symm⟩

/-- The first instruction boundary recovers the exact earlier full history.
In particular, observation count is not substituted for instruction count. -/
theorem coverage (past : World → Execution S) (step : S → OracleMachine.Command S S)
    (fuel : ℕ) (world : World) (input : Input)
    (touched : seen (history past step fuel world).run.2 input = true) :
    seen (past world).run.2 input = true ∨ ∃ index < fuel,
      CausalFirstStreamPrefix.recover input (history past step fuel world).run.2 =
        some (history past step index world).run.2 ∧
      ∃ offset values after, values ≠ [] ∧
        (history past step fuel world).run.2 =
          (history past step index world).run.2 ++ .output input offset values :: after := by
  cases inherited : seen (past world).run.2 input with
  | true => exact Or.inl rfl
  | false =>
    obtain ⟨index,bound,unseen,hit⟩ := first_flip past step fuel world input inherited touched
    exact Or.inr ⟨index,bound,recover_at_flip past step fuel index world input bound unseen hit⟩

end
end FormalProof4FHE.HasteBoots.InstructionClock
