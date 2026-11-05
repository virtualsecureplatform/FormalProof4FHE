module

public import FormalProof4FHE.HasteBoots.OracleMachine
public import FormalProof4FHE.HasteBoots.NativeProgramPrefix
@[expose] public section

/-! Exact causal-machine interpretation of native programs. Finite prefixes
retain the actual continuation; completion depth depends on the executed
path. No uniform retry bound or physical cost claim is introduced. -/
namespace FormalProof4FHE.HasteBoots.OracleProgramMachine
open InputIndexedOracle (World)
open OracleProgram (Program run)

def step {A : Type} : Program A → OracleMachine.Command (Program A) A
  | .pure value => .done value
  | .start input next => .start input next
  | .read input offset count next => .read input offset count next
  | .hash input next => .hash input next

theorem take_program {A : Type} (fuel : ℕ) (program : Program A) :
    OracleMachine.take step fuel program = NativeProgramPrefix.take fuel program := by
  induction fuel generalizing program with
  | zero => cases program <;> rfl
  | succ fuel ih => cases program <;> simp only [OracleMachine.take,step,NativeProgramPrefix.take,ih]

theorem take_run {A : Type} (fuel : ℕ) (program : Program A) (world : World) :
    run (OracleMachine.take step fuel program) world = OracleProgram.runPrefix fuel program world := by
  rw [take_program,NativeProgramPrefix.take_run]

/-- Completion depth is path-dependent; this is no uniform native retry cap. -/
theorem prefix_complete {A : Type} (program : Program A) (world : World) :
    ∃ fuel, (OracleProgram.runPrefix fuel program world).run =
      (.inr (run program world).run.1,(run program world).run.2) := by
  induction program with
  | pure value => exact ⟨0,rfl⟩
  | start input next ih =>
    obtain ⟨fuel,finished⟩ := ih
    refine ⟨fuel+1,?_⟩
    change ((OracleProgram.runPrefix fuel next world).run.1,
      [NativeTranscript.Observation.start input] ++ (OracleProgram.runPrefix fuel next world).run.2) = _
    rw [finished]
    rfl
  | read input offset count next ih =>
    obtain ⟨fuel,finished⟩ := ih (InputIndexedOracle.bytes world input offset count)
    refine ⟨fuel+1,?_⟩
    change ((OracleProgram.runPrefix fuel (next (InputIndexedOracle.bytes world input offset count)) world).run.1,
      [NativeTranscript.Observation.output input offset (InputIndexedOracle.bytes world input offset count)] ++
        (OracleProgram.runPrefix fuel (next (InputIndexedOracle.bytes world input offset count)) world).run.2) = _
    rw [finished]
    rfl
  | hash input next ih =>
    obtain ⟨fuel,finished⟩ := ih (InputIndexedOracle.sha512 world input)
    refine ⟨fuel+1,?_⟩
    change ((OracleProgram.runPrefix fuel (next (InputIndexedOracle.sha512 world input)) world).run.1,
      [NativeTranscript.Observation.hash input (List.ofFn (InputIndexedOracle.sha512 world input))] ++
        (OracleProgram.runPrefix fuel (next (InputIndexedOracle.sha512 world input)) world).run.2) = _
    rw [finished]
    rfl

theorem complete {A : Type} (program : Program A) (world : World) :
    ∃ fuel, (run (OracleMachine.take step fuel program) world).run =
      (.inr (run program world).run.1,(run program world).run.2) := by
  simpa only [take_run] using prefix_complete program world


/-- Every finite machine prefix is a prefix of the same complete native program run. -/
theorem log_prefix_run {A : Type} (fuel : ℕ) (program : Program A) (world : World) :
    (run (OracleMachine.take step fuel program) world).run.2.IsPrefix (run program world).run.2 := by
  rw [take_program]
  have same := congrArg (fun p => (run p world).run.2) (NativeProgramPrefix.take_resume fuel program)
  rw [OracleProgram.run_bind,ObservationReplay.run_bind] at same
  exact ⟨_,same⟩

end FormalProof4FHE.HasteBoots.OracleProgramMachine
