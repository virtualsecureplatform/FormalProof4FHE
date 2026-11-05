module

public import FormalProof4FHE.HasteBoots.OracleProgram

@[expose] public section

namespace FormalProof4FHE.HasteBoots.NativeProgramComposition

/-- Factor native stages without changing any oracle action or branch. -/
theorem bind_assoc {A B C : Type} (first : OracleProgram.Program A)
    (next : A → OracleProgram.Program B) (last : B → OracleProgram.Program C) :
    OracleProgram.bind (OracleProgram.bind first next) last =
      OracleProgram.bind first (fun value => OracleProgram.bind (next value) last) := by
  induction first with
  | pure value => rfl
  | start input tail ih => exact congrArg (OracleProgram.Program.start input) ih
  | read input offset count tail ih =>
    simp only [OracleProgram.bind]
    congr 1
    funext answer
    exact ih answer
  | hash input tail ih =>
    simp only [OracleProgram.bind]
    congr 1
    funext answer
    exact ih answer

end FormalProof4FHE.HasteBoots.NativeProgramComposition
