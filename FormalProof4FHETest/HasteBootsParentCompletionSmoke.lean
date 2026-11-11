module
import all FormalProof4FHE.HasteBoots.ParentFactorFiber
import all FormalProof4FHETest.HasteBootsLifetimeLineageSmoke
import all FormalProof4FHETest.HasteBootsScalarInputSmoke

namespace FormalProof4FHE.HasteBoots.ParentCompletionSmoke
open HasteBootsParentStateSmoke (parentInput parentFrames parent_parsed context helper world seed)
open HasteBootsLifetimeLineageSmoke (descendantInput descendantFrames descendant_parsed descendant_quote)
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (Program run)
noncomputable section

def program : Program Unit := .start parentInput (.read parentInput 999 1 (fun _ => .read descendantInput 0 0 (fun _ => .pure ())))
def past (world : World) := run program world
def changed : World := Function.update world (.inl (parentInput,17)) 10

theorem candidates : ParentSeedCandidates.inputs (past world).run.2 = {parentInput,descendantInput} := by
  change ParentSeedCandidates.inputs [Observation.start parentInput,.output parentInput 999 [9],.output descendantInput 0 []] = _
  simp [ParentSeedCandidates.inputs,List.filterMap_nil,ParentSeedCandidates.candidate,
    NativeParentCoverage.observationInput,parent_parsed,descendant_parsed]

/-- The refinement retains multiple full matches rather than selecting one
parent based on a partial cache. The all-nine fixture has two such matches. -/
theorem matching_parents : ParentSeedCompletion.matching (past world).run.2 world seed = {parentInput,descendantInput} := by
  unfold ParentSeedCompletion.matching
  rw [candidates]
  have equal (input : Input) : InputIndexedOracle.block world input 0 64 = seed := rfl
  simp only [equal,Finset.filter_true]

/-- A byte inside the seed block was not exposed by the far-offset read. -/
theorem seed_unobserved : (.inl (parentInput,17) : InputIndexedOracle.Coordinate) ∉ ObservationReplay.footprint (past world).run.2 := by
  intro member
  obtain ⟨entry,present,coordinate⟩ := Finset.mem_biUnion.mp member
  have inLog := List.mem_toFinset.mp present
  change entry ∈ [Observation.start parentInput,.output parentInput 999 [9],.output descendantInput 0 []] at inLog
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inLog
  rcases inLog with rfl | rfl | rfl
  · simp only [ObservationReplay.coordinates,Finset.notMem_empty] at coordinate
  · have position := (NativeShakeProjection.output_coordinate _ _ _ _).mp coordinate
    omega
  · simp only [ObservationReplay.coordinates,List.length_nil,Finset.range_zero,Finset.image_empty,Finset.notMem_empty] at coordinate

theorem same_raw : (past changed).run = (past world).run :=
  ObservationReplay.update_unobserved (OracleProgram.run_replay program) world _ 10 seed_unobserved

/-- Completing named parents distinguishes worlds that the old raw packet
could not distinguish, without silently authenticating partial seeds. -/
theorem completion_differs : (ParentSeedCompletion.extend past changed).run ≠ (ParentSeedCompletion.extend past world).run := by
  intro same
  have equal := ParentSeedCompletion.seed_on_fiber (past := past) (OracleProgram.run_replay program) world changed parentInput (by rw [candidates]; simp) same
  have atByte := congrFun equal (⟨17,by decide⟩ : Fin 64)
  change (10 : InputIndexedOracle.Byte) = 9 at atByte
  contradiction

theorem known : NativeParentLineage.Known world (past world).run.2 descendantInput context := by
  have direct : NativeParentLineage.Known world [Observation.start parentInput] parentInput context :=
    .direct [] (.start parentInput) parentFrames parent_parsed context helper
  have earlier := NativeParentLineage.Known.later [Observation.start parentInput] [.output parentInput 999 [9]] parentInput context direct
  exact .inherit _ (.output descendantInput 0 []) descendantFrames descendant_parsed parentInput context earlier descendant_quote

/-- Semantic helper ancestry is replayed on the completed parent fiber. -/
theorem known_replay (other : World)
    (same : (ParentSeedCompletion.extend past other).run = (ParentSeedCompletion.extend past world).run) :
    NativeParentLineage.Known other (past other).run.2 descendantInput context :=
  (ParentMetadataReplay.on_fiber (OracleProgram.run_replay program) world other descendantInput (.helper context) same).mpr known

/-- An actual typed scalar input is rejected by the parent-seed parser. -/
theorem scalar_separated : NativeParentInputView.parseParent ScalarInputSmoke.phase.pending.input = none :=
  ScalarParentSeparation.rejected _ _ ScalarInputSmoke.parsed

end
end FormalProof4FHE.HasteBoots.ParentCompletionSmoke
