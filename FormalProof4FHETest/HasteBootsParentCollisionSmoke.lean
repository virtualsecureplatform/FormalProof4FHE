module
import all FormalProof4FHE.HasteBoots.AllocatedParentPrefix
import all FormalProof4FHETest.HasteBootsParentCompletionSmoke

namespace FormalProof4FHE.HasteBoots.ParentCollisionSmoke
open ParentCompletionSmoke (program past candidates)
open HasteBootsParentStateSmoke (parentInput parent_parsed world)
open HasteBootsLifetimeLineageSmoke (descendantInput descendant_parsed descendant_quote)
open OracleProgram (run runPrefix)
noncomputable section

theorem apart : parentInput ≠ descendantInput := by decide +kernel

theorem earlier : ParentSeedCandidates.inputs (runPrefix 2 program world).run.2 = {parentInput} := by
  change ParentSeedCandidates.inputs [NativeTranscript.Observation.start parentInput,.output parentInput 999 [9]] = _
  simp [ParentSeedCandidates.inputs,List.filterMap_nil,ParentSeedCandidates.candidate,NativeParentCoverage.observationInput,parent_parsed]

/-- An empty read names a new recognized parent, even before any byte of its
seed has been physically queried. This is not receipt-read eligibility. -/
theorem selected : ParentSeedCollisionRisk.select OracleProgramMachine.step (runPrefix 2 program world).run = some descendantInput := by
  change (ParentSeedCollisionRisk.candidate (.read descendantInput 0 0)).bind (fun raw =>
    if raw ∈ ParentSeedCandidates.inputs (runPrefix 2 program world).run.2 then none else some raw) = _
  simp [ParentSeedCollisionRisk.candidate,ParentSeedCollisionRisk.requestInput,ParentSeedCandidates.candidate,
    NativeParentCoverage.observationInput,descendant_parsed,earlier,apart.symm]

theorem actual_hit : ParentSeedCollisionRisk.event OracleProgramMachine.step (runPrefix 2 program world).run world := by
  simp only [ParentSeedCollisionRisk.event,selected,earlier,Finset.mem_singleton]
  exact ⟨parentInput,rfl,rfl⟩

theorem exact_charge : ParentSeedCollisionRisk.risk OracleProgramMachine.step (runPrefix 2 program world).run = 1/(2 : ENNReal)^512 := by
  simp only [ParentSeedCollisionRisk.risk,selected,earlier,Finset.card_singleton,Nat.cast_one]

theorem repeated_none : ParentSeedCollisionRisk.select OracleProgramMachine.step (runPrefix 1 program world).run = none := by
  change (ParentSeedCollisionRisk.candidate (.read parentInput 999 1)).bind (fun raw =>
    if raw ∈ ParentSeedCandidates.inputs [NativeTranscript.Observation.start parentInput] then none else some raw) = none
  simp [ParentSeedCollisionRisk.candidate,ParentSeedCollisionRisk.requestInput,ParentSeedCandidates.candidate,
    ParentSeedCandidates.inputs,NativeParentCoverage.observationInput,parent_parsed]

theorem final_collision : ParentSeedCollisionRisk.Collision (run program world).run.2 world := by
  refine ⟨parentInput,?_,descendantInput,?_,apart,rfl⟩
  · change parentInput ∈ ParentSeedCandidates.inputs (past world).run.2
    rw [candidates]
    simp
  · change descendantInput ∈ ParentSeedCandidates.inputs (past world).run.2
    rw [candidates]
    simp

theorem covered : ProgramParentSeedCollision.Bad program world := ProgramParentSeedCollision.covers program world final_collision

/-- Two actual matches need not be the same parent. The collision branch
of the coupling theorem retains that case explicitly. -/
theorem matching_covered : ProgramParentSeedCollision.Bad program world := by
  have namedLeft : parentInput ∈ ParentSeedCandidates.inputs (runPrefix 3 program world).run.2 := by
    change parentInput ∈ ParentSeedCandidates.inputs (past world).run.2
    rw [candidates]
    simp
  have namedRight : descendantInput ∈ ParentSeedCandidates.inputs (runPrefix 3 program world).run.2 := by
    change descendantInput ∈ ParentSeedCandidates.inputs (past world).run.2
    rw [candidates]
    simp
  rcases ParentMatchFixation.on_fiber program 3 world world descendantInput parentInput descendantInput namedLeft namedRight
      descendant_quote descendant_quote rfl with same | bad
  · exact False.elim (apart same.symm)
  · exact bad

end
end FormalProof4FHE.HasteBoots.ParentCollisionSmoke
