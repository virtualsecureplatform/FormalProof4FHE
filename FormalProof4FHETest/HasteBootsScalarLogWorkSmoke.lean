module
import all FormalProof4FHE.HasteBoots.ByteScalarLogWork
import all FormalProof4FHETest.HasteBootsScalarRecoverySmoke

namespace FormalProof4FHE.HasteBoots.ScalarLogWorkSmoke
open HasteBootsSamplerAncestrySmoke (worldZero)
noncomputable section

def code : List ClosedByteMachine.Instruction := [.constant 0 0,.read 0 1 999 1,.read 0 2 0 1,.halt]
def initial : ClosedByteMachine.State := ClosedByteMachine.initialise code (fun _ => ScalarReplaySmoke.target)

/-- The local constant consumes an instruction but emits no observation. -/
theorem silent_instruction : (OracleProgram.run (ClosedByteMachine.take code [] 1 initial) worldZero).run.2 = [] := by rfl

/-- Observation position zero already selects the read after that local step. -/
theorem different_clocks : CausalStreamExposure.firstRead OracleProgramMachine.step
    (OracleProgram.runPrefix 0 (ClosedByteMachine.take code [] 3 initial) worldZero).run = some ScalarReplaySmoke.target := by rfl

/-- Both positive reads are retained in the intermediate log bound, even
though the security charge only selects their key once. -/
theorem repeated_log : ScalarLogWork.bytes
    (OracleProgram.run (ClosedByteMachine.take code [] 3 initial) worldZero).run.2 = 2*ScalarReplaySmoke.target.length := by
  change ScalarLogWork.bytes [.output ScalarReplaySmoke.target 999 [0],.output ScalarReplaySmoke.target 0 [0]] = _
  simp [ScalarLogWork.bytes,ScalarLogWork.weight,Nat.two_mul]

/-- Starts, hashes and empty reads add no positive-read byte potential. -/
theorem no_positive_read (input : InputIndexedOracle.Input) :
    ScalarLogWork.bytes [.start input,.hash input [],.output input 123 []] = 0 := by
  simp [ScalarLogWork.bytes,ScalarLogWork.weight]

end
end FormalProof4FHE.HasteBoots.ScalarLogWorkSmoke
