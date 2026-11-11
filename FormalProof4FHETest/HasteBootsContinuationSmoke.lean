module
import all FormalProof4FHE.HasteBoots.InterpreterScalarLifetime
import all FormalProof4FHETest.HasteBootsFactorFiberSmoke

namespace FormalProof4FHE.HasteBoots.ContinuationSmoke
open OracleProgram (Program bind run runPrefix)
open HasteBootsSamplerAncestrySmoke (worldZero)
noncomputable section

def next (_ : Unit) : Program Bool := .read FactorFiberSmoke.input 0 1 (fun _ => .pure true)
def extended := bind FactorFiberSmoke.program next
def first := ProgramContinuationPrefix.first FactorFiberSmoke.first next

/-- A continuation with a different result type retains the original far
read after the start, empty read and hash. -/
theorem original_position : first.position = 3 ∧ first.offset = 999 ∧ first.count = 1 := ⟨rfl,rfl,rfl⟩

/-- The later same-key read does not replace the original positive read. -/
theorem original_output : (run extended worldZero).run.2[3]? = some (.output FactorFiberSmoke.input 999 [0]) := first.outputAt

/-- Appending the continuation retains both the original branch's start
and the later positive read. -/
theorem later_output : (run extended worldZero).run.2[5]? = some (.output FactorFiberSmoke.input 0 [0]) := by rfl

/-- The selecting prefix's log is unchanged although its future continuation
and final result type have changed. -/
theorem prefix_preserved : (runPrefix 3 extended worldZero).run.2 = (runPrefix 3 FactorFiberSmoke.program worldZero).run.2 :=
  congrArg Prod.snd (ProgramContinuationPrefix.active_bind FactorFiberSmoke.program next 3 worldZero _ FactorFiberSmoke.first.active)

end
end FormalProof4FHE.HasteBoots.ContinuationSmoke
