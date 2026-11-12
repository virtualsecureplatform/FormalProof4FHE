module
import all FormalProof4FHE.HasteBoots.EqualityLogWork

namespace HasteBootsEqualityWorkSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix)
noncomputable section

def world : World := fun _ => 0
def input : Input := [4,5,6]
def program : Program Unit := .read input 0 0 (fun _ => .read input 0 1 (fun _ => .read input 1 1 (fun _ => .pure ())))

theorem empty_read_zero : EqualityPositionKernel.charge program 0 world = 0 := by
  have selected : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix 0 program world).run = none := rfl
  change EqualityPositionKernel.score _ = _
  rw [EqualityPositionKernel.score,selected]

theorem first_positive_score : EqualityPositionKernel.charge program 1 world = (3 : ENNReal)*EqualityPositionKernel.rate := by
  have selected : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix 1 program world).run = some input := by decide +kernel
  change EqualityPositionKernel.score _ = _
  rw [EqualityPositionKernel.score,selected]
  rfl

theorem repeated_read_zero : EqualityPositionKernel.charge program 2 world = 0 := by
  have selected : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix 2 program world).run = none := by decide +kernel
  change EqualityPositionKernel.score _ = _
  rw [EqualityPositionKernel.score,selected]

theorem halt_zero : EqualityPositionKernel.charge program 3 world = 0 := by
  have selected : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix 3 program world).run = none := by decide +kernel
  change EqualityPositionKernel.score _ = _
  rw [EqualityPositionKernel.score,selected]

/-- Both positive reads remain in logged work, although the repeat has no
new equality charge. Empty reads remain present but carry zero byte weight. -/
theorem original_log_bytes : (run program world).run.2.length = 3 ∧ ScalarLogWork.bytes (run program world).run.2 = 6 := by decide +kernel

end
end HasteBootsEqualityWorkSmoke
