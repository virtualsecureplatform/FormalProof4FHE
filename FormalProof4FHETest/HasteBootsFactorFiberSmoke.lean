module
import all FormalProof4FHE.HasteBoots.FirstReadFiber
import all FormalProof4FHE.HasteBoots.FactorPosteriorMismatch
import all FormalProof4FHE.HasteBoots.FactorFiberUniform
import all FormalProof4FHE.HasteBoots.AllocatedFactorSamples
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace FormalProof4FHE.HasteBoots.FactorFiberSmoke
open HasteBootsSamplerAncestrySmoke (worldZero)
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix)
open ProgramFirstStreamRead (First)
noncomputable section

def input : Input := [17]
def resume (values : Input) : Program Unit :=
  if values = [0] then .start [1] (.pure ()) else .start [2] (.pure ())
def program : Program Unit := .start input (.read input 9000 0 (fun _ => .hash input (fun _ => .read input 999 1 resume)))
def changed : World := Function.update worldZero (.inl (input,999)) 1

def first : First program worldZero input :=
  ⟨3,999,1,resume,rfl,rfl,by decide +kernel,by decide,rfl⟩

/-- Hashing the same key does not expose its SHAKE byte; starts and an empty
read do not expose it either. The prefix is unchanged after this update. -/
theorem same_prefix : (runPrefix first.position program changed).run = (runPrefix first.position program worldZero).run := by
  apply OracleProgram.prefix_update_unobserved
  exact CausalStreamExposure.unseen_coordinates _ _ first.fresh 999

def transported : First program changed input := FirstReadFiber.transport first changed same_prefix

example : transported.position = 3 ∧ transported.offset = 999 ∧ transported.count = 1 := ⟨rfl,rfl,rfl⟩

/-- The actual next observation uses the changed world's byte. -/
theorem changed_output : (run program changed).run.2[3]? =
    some (NativeTranscript.Observation.output input 999 [1]) := by
  have present := transported.outputAt
  change (run program changed).run.2[3]? = some (.output input 999 (InputIndexedOracle.bytes changed input 999 1)) at present
  have values : InputIndexedOracle.bytes changed input 999 1 = [1] := rfl
  rw [values] at present
  exact present

/-- Prefix replay is sufficient even when the later branch and full raw
execution log differ. -/
theorem future_differs : (run program changed).run.2 ≠ (run program worldZero).run.2 := by
  intro equal
  have observations := congrArg (fun history : List NativeTranscript.Observation => history[3]?) equal
  have original := first.outputAt
  change (run program worldZero).run.2[3]? = some (.output input 999 [0]) at original
  rw [changed_output,original] at observations
  have values := (NativeTranscript.Observation.output.inj (Option.some.inj observations)).2.2
  change [1] = [0] at values
  contradiction

theorem unique_position (otherFirst : First program changed input) : otherFirst.position = first.position :=
  FirstReadFiber.position_on_fiber first otherFirst same_prefix

end
end FormalProof4FHE.HasteBoots.FactorFiberSmoke
