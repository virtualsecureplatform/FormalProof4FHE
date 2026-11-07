module
public import FormalProof4FHE.HasteBoots.ClosedByteMachine
public import FormalProof4FHE.HasteBoots.CausalFirstStreamPrefix
@[expose] public section

/-! Physical-prefix lineage for the closed instruction interpreter. Silent
instructions advance the instruction clock without inserting observations.
The first exposure is located by that clock, never by a log index. All mixed
prequery history and actual residual local state are retained. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineHistory
open InputIndexedOracle (Input World)
open NativeTranscript (Execution Observation)
open ClosedByteMachine (Instruction State take tick)
open CausalStreamExposure (seen touches)
noncomputable section

def history (past : World → Execution State) (code : List Instruction) (publicData : Input)
    (fuel : ℕ) (world : World) : Execution State :=
  past world >>= fun state => OracleProgram.run (take code publicData fuel state) world

theorem history_replay {past : World → Execution State} (replay : ObservationReplay.Replayable past)
    (code : List Instruction) (publicData : Input) (fuel : ℕ) :
    ObservationReplay.Replayable (history past code publicData fuel) :=
  ObservationReplay.bind_replay replay (fun state => ClosedByteMachine.prefix_replay code publicData fuel state)

theorem history_zero (past : World → Execution State) (code : List Instruction) (publicData : Input) (world : World) :
    (history past code publicData 0 world).run = (past world).run := by
  rw [history,ObservationReplay.run_bind]
  exact Prod.ext rfl (List.append_nil _)

theorem history_resume (past : World → Execution State) (code : List Instruction) (publicData : Input)
    (first later : ℕ) (world : World) :
    (history past code publicData (first+later) world).run =
      ((OracleProgram.run (take code publicData later (history past code publicData first world).run.1) world).run.1,
        (history past code publicData first world).run.2 ++
          (OracleProgram.run (take code publicData later (history past code publicData first world).run.1) world).run.2) := by
  simp only [history,ObservationReplay.run_bind,ClosedByteMachine.take_resume,OracleProgram.run_bind,List.append_assoc]

theorem history_prefix (past : World → Execution State) (code : List Instruction) (publicData : Input)
    (first later : ℕ) (bounded : first ≤ later) (world : World) :
    (history past code publicData first world).run.2.IsPrefix (history past code publicData later world).run.2 := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bounded
  rw [history_resume]
  exact ⟨_,rfl⟩

theorem history_succ (past : World → Execution State) (code : List Instruction) (publicData : Input)
    (fuel : ℕ) (world : World) :
    (history past code publicData (fuel+1) world).run =
      ((OracleProgram.run (tick code publicData (history past code publicData fuel world).run.1) world).run.1,
        (history past code publicData fuel world).run.2 ++
          (OracleProgram.run (tick code publicData (history past code publicData fuel world).run.1) world).run.2) := by
  rw [history_resume]
  simp only [take,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,WriterT.run_pure]
  change (_, _ ++ (_ ++ [])) = (_, _ ++ _)
  rw [List.append_nil]
  rfl

/-- A newly exposed stream has an actual first instruction boundary, even
when arbitrarily many earlier local steps produced no oracle observations. -/
theorem first_flip (past : World → Execution State) (code : List Instruction) (publicData : Input)
    (fuel : ℕ) (world : World) (input : Input)
    (unseen : seen (past world).run.2 input = false)
    (touched : seen (history past code publicData fuel world).run.2 input = true) :
    ∃ index < fuel,
      seen (history past code publicData index world).run.2 input = false ∧
      seen (history past code publicData (index+1) world).run.2 input = true := by
  let test : ℕ → Prop := fun n => seen (history past code publicData n world).run.2 input = true
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
  · cases h : seen (history past code publicData (first-1) world).run.2 input with
    | false => rfl
    | true => exact False.elim (Nat.find_min existsTest (by omega) h)
  · have equal : first-1+1 = first := by omega
    simpa only [equal] using hit

/-- Recovery at an actual first-exposure instruction boundary. -/
theorem recover_at_flip (past : World → Execution State) (code : List Instruction) (publicData : Input)
    (fuel index : ℕ) (world : World) (input : Input) (bound : index < fuel)
    (unseen : seen (history past code publicData index world).run.2 input = false)
    (hit : seen (history past code publicData (index+1) world).run.2 input = true) :
    CausalFirstStreamPrefix.recover input (history past code publicData fuel world).run.2 =
        some (history past code publicData index world).run.2 ∧
      ∃ offset values after, values ≠ [] ∧
        (history past code publicData fuel world).run.2 =
          (history past code publicData index world).run.2 ++ .output input offset values :: after := by
  have split := congrArg Prod.snd (history_succ past code publicData index world)
  let tail := (OracleProgram.run (tick code publicData (history past code publicData index world).run.1) world).run.2
  have length : tail.length ≤ 1 := ClosedByteMachine.tick_log_length _ _ _ _
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
    have nextLog : (history past code publicData (index+1) world).run.2 =
        (history past code publicData index world).run.2 ++ [entry] := by
      change (history past code publicData (index+1) world).run.2 =
        (history past code publicData index world).run.2 ++ tail at split
      simpa only [shape,empty] using split
    obtain ⟨after,full⟩ := history_prefix past code publicData (index+1) fuel (by omega) world
    rw [nextLog,List.append_assoc,List.singleton_append] at full
    have recovered := CausalFirstStreamPrefix.recover_at input
      (history past code publicData index world).run.2 after entry unseen touch
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
theorem coverage (past : World → Execution State) (code : List Instruction) (publicData : Input)
    (fuel : ℕ) (world : World) (input : Input)
    (touched : seen (history past code publicData fuel world).run.2 input = true) :
    seen (past world).run.2 input = true ∨ ∃ index < fuel,
      CausalFirstStreamPrefix.recover input (history past code publicData fuel world).run.2 =
        some (history past code publicData index world).run.2 ∧
      ∃ offset values after, values ≠ [] ∧
        (history past code publicData fuel world).run.2 =
          (history past code publicData index world).run.2 ++ .output input offset values :: after := by
  cases inherited : seen (past world).run.2 input with
  | true => exact Or.inl rfl
  | false =>
    obtain ⟨index,bound,unseen,hit⟩ := first_flip past code publicData fuel world input inherited touched
    exact Or.inr ⟨index,bound,recover_at_flip past code publicData fuel index world input bound unseen hit⟩

end
end FormalProof4FHE.HasteBoots.ClosedByteMachineHistory
