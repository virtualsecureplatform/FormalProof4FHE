module
import all FormalProof4FHE.HasteBoots.PrivateCoinScalarProbability
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace FormalProof4FHE.HasteBoots.PrivateCoinScalarSmoke
open PrivateCoinByteMachine (Instruction take initialise)
open HasteBootsSamplerAncestrySmoke (worldZero)
open InputIndexedOracle (Byte)
noncomputable section

def code : List Instruction := [.coin 0,.coin 1,.base .halt]
def zero : PrivateCoinReplay.Tape := fun _ => 0
def changed : PrivateCoinReplay.Tape := Function.update zero 1 1

/-- A future coin does not change the whole earlier prefix program, even
though the infinite original tape is different. -/
theorem unused_coin : take code [] changed 1 (initialise code (fun _ => [])) =
    take code [] zero 1 (initialise code (fun _ => [])) := by
  apply PrivateCoinProgramPrefix.take_agrees
  intro index lower upper
  change index < 0+1 at upper
  have same : index = 0 := by omega
  subst index
  rfl

/-- When the next coin instruction executes, that byte becomes observable
in local state and the finite strategies cease to be equal. -/
theorem consumed_coin : take code [] changed 2 (initialise code (fun _ => [])) ≠
    take code [] zero 2 (initialise code (fun _ => [])) := by
  intro equal
  have byte := congrArg (fun program => (OracleProgram.run program worldZero).run.1.machine.registers 1) equal
  change (1 : Byte) = 0 at byte
  contradiction

/-- A resumed nonzero cursor does not inspect an earlier tape coordinate. -/
theorem earlier_coin :
    let state := {initialise code (fun _ => []) with cursor := 17}
    take code [] (Function.update zero 16 1) 1 state = take code [] zero 1 state := by
  dsimp only
  apply PrivateCoinProgramPrefix.take_agrees
  intro index lower upper
  change 17 ≤ index at lower
  have different : index ≠ 16 := by omega
  simp [Function.update,different]

end
end FormalProof4FHE.HasteBoots.PrivateCoinScalarSmoke
