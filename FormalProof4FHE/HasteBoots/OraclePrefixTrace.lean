module

public import FormalProof4FHE.HasteBoots.OracleExecutionLaw

@[expose] public section

/-!
# Chronological one-step extension of causal mixed-oracle prefixes

A completed result stays completed. A paused result executes its next
primitive and retains its residual program. No prefix discards earlier
observations; fuel indexes proof approximations rather than runtime caps.
-/

namespace FormalProof4FHE.HasteBoots.OraclePrefixTrace

open InputIndexedOracle (World)
open NativeTranscript (Execution)
open OracleProgram (Program runPrefix)

/-- One further primitive, or an idle step after completion. -/
def advance {A : Type} : Program A ⊕ A → World → Execution (Program A ⊕ A)
  | .inl program, world => runPrefix 1 program world
  | .inr value, _ => pure (.inr value)

theorem advance_replay {A : Type} (result : Program A ⊕ A) :
    ObservationReplay.Replayable (advance result) := by
  cases result with
  | inl program => exact OracleProgram.prefix_replay 1 program
  | inr value => exact ObservationReplay.pure_replay _

/-- Extending a prefix follows its actual retained continuation. -/
theorem runPrefix_succ {A : Type} (depth : ℕ) (program : Program A) (world : World) :
    runPrefix (depth + 1) program world =
      (runPrefix depth program world >>= fun result => advance result world) := by
  induction depth generalizing program with
  | zero => cases program <;> simp [runPrefix, advance]
  | succ depth ih =>
    cases program with
    | pure value => simp [runPrefix, advance]
    | start input next => simp only [runPrefix, ih, bind_assoc]
    | read input offset count next => simp only [runPrefix, ih, bind_assoc]
    | hash input next => simp only [runPrefix, ih, bind_assoc]

theorem runPrefix_succ_run {A : Type} (depth : ℕ) (program : Program A) (world : World) :
    (runPrefix (depth + 1) program world).run =
      ((advance (runPrefix depth program world).run.1 world).run.1,
        (runPrefix depth program world).run.2 ++
          (advance (runPrefix depth program world).run.1 world).run.2) := by
  rw [runPrefix_succ, ObservationReplay.run_bind]

/-- All previous observations remain in every longer prefix. -/
theorem log_prefix {A : Type} (depth : ℕ) (program : Program A) (world : World) :
    (runPrefix depth program world).run.2.IsPrefix (runPrefix (depth + 1) program world).run.2 := by
  rw [runPrefix_succ_run]
  exact ⟨_, rfl⟩

/-- Every completed inductive program is represented exactly by one of
its chronological prefixes. This is not an assertion that an unbounded
native rejection sampler terminates or has already been compiled. -/
theorem eventual_completion {A : Type} (program : Program A) (world : World) :
    ∃ depth, (runPrefix depth program world).run =
      (.inr (OracleProgram.run program world).run.1, (OracleProgram.run program world).run.2) := by
  induction program with
  | pure value => exact ⟨0, rfl⟩
  | start input next ih =>
    obtain ⟨depth, same⟩ := ih
    refine ⟨depth + 1, ?_⟩
    simp only [runPrefix, OracleProgram.run, ObservationReplay.run_bind]
    rw [same]
  | read input offset count next ih =>
    obtain ⟨depth, same⟩ := ih (InputIndexedOracle.bytes world input offset count)
    refine ⟨depth + 1, ?_⟩
    simp only [runPrefix, OracleProgram.run, ObservationReplay.run_bind]
    rw [show (ObservationReplay.read world input offset count).run.1 =
      InputIndexedOracle.bytes world input offset count from rfl, same]
  | hash input next ih =>
    obtain ⟨depth, same⟩ := ih (InputIndexedOracle.sha512 world input)
    refine ⟨depth + 1, ?_⟩
    simp only [runPrefix, OracleProgram.run, ObservationReplay.run_bind]
    rw [show (ObservationReplay.hash world input).run.1 = InputIndexedOracle.sha512 world input from rfl, same]

end FormalProof4FHE.HasteBoots.OraclePrefixTrace
