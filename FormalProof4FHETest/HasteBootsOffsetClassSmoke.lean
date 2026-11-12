module
import all FormalProof4FHE.HasteBoots.CallerLookupClassCoverage
import all FormalProof4FHE.HasteBoots.PrivateCoinOffsetClassProbability

namespace HasteBootsOffsetClassSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (Program)
noncomputable section

def emptyRead (key : Input) : Program Unit :=
  .start key (.read key 99 0 (fun _ => .pure ()))

/-- Starts and zero-byte reads cannot manufacture an attained reciprocal
class, at any analysis position, even if the stream key was named. -/
theorem no_class_from_empty_read (key : Input) (dummy : NativeRootMessage.Digest) (world : World) :
    ¬OffsetClassKernel.Lifetime (emptyRead key) dummy world := by
  rintro ⟨position,input,ordinal,cost,⟨candidate,_⟩⟩
  have first := candidate.val.source.first
  have never (position : ℕ) : CausalStreamExposure.firstRead OracleProgramMachine.step
      (OracleProgram.runPrefix position (emptyRead key) world).run = none := by
    cases position with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => cases n <;> rfl
  have selected := first.selected
  rw [never first.position] at selected
  contradiction

def laterRead (key : Input) : Program Unit :=
  .start key (.read key 99 0 (fun _ => .read key 7 1 (fun _ => .pure ())))

/-- The original earliest positive read remains at the literal observation
ordinal after a start and an empty read, including its arbitrary byte offset. -/
theorem actual_positive_read (key : Input) (world : World) :
    ∃ first : ProgramFirstStreamRead.First (laterRead key) world key,
      first.position = 2 ∧ first.offset = 7 ∧ first.count = 1 := by
  refine ⟨⟨2,7,1,fun _ => .pure (),rfl,rfl,?_,by decide,rfl⟩,rfl,rfl,rfl⟩
  change CausalStreamExposure.seen [.start key,.output key 99 (InputIndexedOracle.bytes world key 99 0)] key = false
  simp [CausalStreamExposure.seen,CausalStreamExposure.touches,InputIndexedOracle.bytes_length]

end
end HasteBootsOffsetClassSmoke
