module
import all FormalProof4FHE.HasteBoots.OriginalBatchJointProbability
import all FormalProof4FHETest.HasteBootsScalarLogWorkSmoke
import all FormalProof4FHETest.HasteBootsPrivateCoinScalarSmoke

namespace FormalProof4FHE.HasteBoots.OpeningClockSmoke
open OracleProgram (run runPrefix)
open HasteBootsSamplerAncestrySmoke (worldZero)
noncomputable section

def code := ScalarLogWorkSmoke.code.map PrivateCoinByteMachine.Instruction.base
def initial : PrivateCoinByteMachine.State := ⟨ScalarLogWorkSmoke.initial,0⟩
def program := PrivateCoinByteMachine.take code [] PrivateCoinScalarSmoke.zero 3 initial

/-- One raw observation occurs after two instructions: the silent constant
is retained in the actual clock used for the original PCS witness. -/
theorem first_observation : (runPrefix 1 program worldZero).run.2 =
    (run (PrivateCoinByteMachine.take code [] PrivateCoinScalarSmoke.zero 2 initial) worldZero).run.2 := by rfl

/-- Repeated reads at different offsets appear at the same exact native log
in the raw-prefix and actual-instruction views, even after completion. -/
theorem completed_prefix : (runPrefix 100 program worldZero).run.2 =
    (run (PrivateCoinByteMachine.take code [] PrivateCoinScalarSmoke.zero 3 initial) worldZero).run.2 := by rfl

/-- A consumed runtime coin changes local state but adds no observation to
be manufactured by a PCS analysis prefix. -/
theorem coin_is_silent :
    let state := PrivateCoinByteMachine.initialise PrivateCoinScalarSmoke.code (fun _ => [])
    let executed := (run (PrivateCoinByteMachine.take PrivateCoinScalarSmoke.code [] PrivateCoinScalarSmoke.zero 1 state) worldZero).run
    executed.1.cursor = 1 ∧ executed.2 = (run (PrivateCoinByteMachine.take PrivateCoinScalarSmoke.code [] PrivateCoinScalarSmoke.zero 0 state) worldZero).run.2 := by
  exact ⟨rfl,rfl⟩

end
end FormalProof4FHE.HasteBoots.OpeningClockSmoke
