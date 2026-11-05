module

public import FormalProof4FHE.HasteBoots.OracleProgram

@[expose] public section

/-! A finite analysis prefix retains the actual residual native program.
Resuming it is an exact identity, so fuel imposes no retry limit. -/
namespace FormalProof4FHE.HasteBoots.NativeProgramPrefix

open OracleProgram (Program)

def take {A : Type} : ℕ → Program A → Program (Program A ⊕ A)
  | 0, .pure value => .pure (.inr value)
  | 0, program => .pure (.inl program)
  | _+1, .pure value => .pure (.inr value)
  | fuel+1, .start input next => .start input (take fuel next)
  | fuel+1, .read input offset count next =>
    .read input offset count (fun answer => take fuel (next answer))
  | fuel+1, .hash input next => .hash input (fun answer => take fuel (next answer))

def resume {A : Type} : Program A ⊕ A → Program A
  | .inl program => program
  | .inr value => .pure value

/-- The syntactic prefix runs the existing native finite-prefix semantics. -/
theorem take_run {A : Type} (fuel : ℕ) (program : Program A) (world : InputIndexedOracle.World) :
    OracleProgram.run (take fuel program) world = OracleProgram.runPrefix fuel program world := by
  induction fuel generalizing program with
  | zero => cases program <;> rfl
  | succ fuel ih =>
    cases program <;> simp only [take,OracleProgram.run,OracleProgram.runPrefix,ih]

/-- Prefix plus its actual continuation is the complete original program. -/
theorem take_resume {A : Type} (fuel : ℕ) (program : Program A) :
    OracleProgram.bind (take fuel program) resume = program := by
  induction fuel generalizing program with
  | zero => cases program <;> rfl
  | succ fuel ih =>
    cases program with
    | pure value => rfl
    | start input next =>
      simp only [take,OracleProgram.bind,ih]
    | read input offset count next =>
      simp only [take,OracleProgram.bind]
      congr 1
      funext answer
      exact ih (next answer)
    | hash input next =>
      simp only [take,OracleProgram.bind]
      congr 1
      funext answer
      exact ih (next answer)

end FormalProof4FHE.HasteBoots.NativeProgramPrefix
