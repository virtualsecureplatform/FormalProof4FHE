module
import all FormalProof4FHE.HasteBoots.EqualityContinuation

namespace HasteBootsEqualityContinuationSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix bind)
noncomputable section

def world : World := fun _ => 0
def input : Input := [4,5,6]
def original : Program Unit := .read input 0 1 (fun _ => .pure ())
def continued : Program Unit := bind original (fun _ =>
  .read input 1 1 (fun _ => .read [7,8] 0 1 (fun _ => .pure ())))

/-- Continuation retains the original positive first read at its old position. -/
theorem original_prefix : (runPrefix 0 continued world).run.2 = (runPrefix 0 original world).run.2 := rfl

theorem original_charge : EqualityPositionKernel.charge continued 0 world =
    (3 : ENNReal)*EqualityPositionKernel.rate := by
  have selected : CausalStreamExposure.firstRead OracleProgramMachine.step
      (runPrefix 0 continued world).run = some input := by decide +kernel
  change EqualityPositionKernel.score _ = _
  rw [EqualityPositionKernel.score,selected]
  rfl

/-- A subsequent offset on the same input is charged as work, not a fresh class. -/
theorem repeated_charge : EqualityPositionKernel.charge continued 1 world = 0 := by
  have selected : CausalStreamExposure.firstRead OracleProgramMachine.step
      (runPrefix 1 continued world).run = none := by decide +kernel
  change EqualityPositionKernel.score _ = _
  rw [EqualityPositionKernel.score,selected]

theorem new_input_charge : EqualityPositionKernel.charge continued 2 world =
    (2 : ENNReal)*EqualityPositionKernel.rate := by
  have selected : CausalStreamExposure.firstRead OracleProgramMachine.step
      (runPrefix 2 continued world).run = some [7,8] := by decide +kernel
  change EqualityPositionKernel.score _ = _
  rw [EqualityPositionKernel.score,selected]
  rfl

theorem continued_log_work : (run continued world).run.2.length = 3 ∧
    ScalarLogWork.bytes (run continued world).run.2 = 8 := by decide +kernel

end
end HasteBootsEqualityContinuationSmoke
