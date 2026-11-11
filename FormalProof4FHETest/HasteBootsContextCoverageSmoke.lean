module
import all FormalProof4FHE.HasteBoots.AllocatedFirstContextCoverage
import all FormalProof4FHETest.HasteBootsContextAssociationSmoke
import all FormalProof4FHETest.HasteBootsParentBindingsSmoke

namespace FormalProof4FHE.HasteBoots.ContextCoverageSmoke
open InputIndexedOracle (Input World law)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open OracleProgram (Program run runPrefix)
open NativeTranscript (Observation)
open ContextAssociationSmoke (base world base_context)
open HasteBootsBatchMeaningSmoke (root)
open scoped Classical
noncomputable section

def binding : NativeCanonicalLookupWire.Binding :=
  ⟨HasteBootsRegistryAncestrySmoke.config,root,⟨[],by decide⟩⟩
def frame := ParentBindingTrace.frame binding
def naming : Input := TranscriptFrame.encodeMany [frame]

theorem valid : ∀ entry ∈ [frame], TranscriptFrame.Valid entry := by
  intro entry member
  obtain rfl := List.mem_singleton.mp member
  constructor <;> decide +kernel

theorem mentioned : ContextDigestTargets.fromInput naming = [root] := by
  unfold ContextDigestTargets.fromInput NativeParentLedger.direct NativeParentLedger.helpers NativeParentLedger.frames naming
  rw [NativeRootInputView.raw_complete _ valid,TranscriptFrame.decodeAll_encodeMany _ valid]
  simp only [Option.getD_some,NativeRootInputView.mentions,List.filterMap_cons,List.filterMap_nil]
  rw [show NativeRootInputView.frameSources frame = some [] from NativeRootInputView.binding_complete binding,
    show NativeParentInputView.frameHelper frame = some root from NativeParentInputView.frameHelper_complete binding]
  rfl

def program : Program Unit := .start naming (.read naming 91 0 (fun _ =>
  .hash (GoldContextInput.bytes base) (fun _ => .hash (GoldContextInput.bytes base) (fun _ => .pure ()))))

theorem start_targets : ContextDigestTargets.targets (runPrefix 1 program world).run.2 = {root} := by
  change ContextDigestTargets.targets [.start naming] = {root}
  simp only [ContextDigestTargets.targets,List.flatMap_cons,List.flatMap_nil,NativeParentCoverage.observationInput,mentioned,List.append_nil,
    List.toFinset_cons,List.toFinset_nil,Finset.insert_empty]

theorem empty_read_targets : ContextDigestTargets.targets (runPrefix 2 program world).run.2 = {root} := by
  change ContextDigestTargets.targets [.start naming,.output naming 91 []] = {root}
  simp only [ContextDigestTargets.targets,List.flatMap_cons,List.flatMap_nil,NativeParentCoverage.observationInput,mentioned,List.append_nil,
    List.singleton_append,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.insert_eq_of_mem,Finset.mem_singleton_self]

theorem selected : ContextTargetRisk.select OracleProgramMachine.step (runPrefix 2 program world).run = some (GoldContextInput.bytes base) := rfl

theorem exact_risk : ContextTargetRisk.risk OracleProgramMachine.step (runPrefix 2 program world).run = 1/(2 : ENNReal)^512 := by
  rw [ContextTargetRisk.risk,selected,empty_read_targets,Finset.card_singleton,Nat.cast_one]


theorem conditional_risk :
    (law[|{other | (runPrefix 2 program other).run = (runPrefix 2 program world).run}])
      {other | ContextTargetRisk.event OracleProgramMachine.step (runPrefix 2 program other).run other} = 1/(2 : ENNReal)^512 := by
  rw [ContextTargetRisk.conditional_event OracleProgramMachine.step (OracleProgram.prefix_replay 2 program) world,exact_risk]

/-- A repeat hash is ineligible even though its digest remains a target. -/
theorem repeat_ineligible : ContextTargetRisk.select OracleProgramMachine.step (runPrefix 3 program world).run = none := by
  change (if ContextTargetRisk.seen [.start naming,.output naming 91 [],
    .hash (GoldContextInput.bytes base) (List.ofFn root)] (GoldContextInput.bytes base) = false then some (GoldContextInput.bytes base) else none) = none
  simp only [ContextTargetRisk.seen,List.any_cons,ContextTargetRisk.touches,List.any_nil,decide_true,Bool.false_or,Bool.true_or,Bool.true_eq_false,ite_false]

/-- The actual late hash hit is covered by the one program lifetime ledger. -/
theorem late_bad : ProgramContextTarget.Bad program world := by
  refine ⟨2,?_⟩
  simp only [ContextTargetRisk.event,selected,empty_read_targets,Finset.mem_singleton]
  rfl

theorem full : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row base) world).run.2.Sublist (run program world).run.2 := by
  rw [GoldContextCollision.context_run]
  change [Observation.hash (GoldContextInput.bytes base) (List.ofFn root)].Sublist
    [.start naming,.output naming 91 [],.hash (GoldContextInput.bytes base) (List.ofFn root),.hash (GoldContextInput.bytes base) (List.ofFn root)]
  exact List.singleton_sublist.mpr (by simp)

theorem prefix_missing : ¬(run (NativeBrakedownContext.context NativeGoldBlockCode.description.row base) world).run.2.Sublist (runPrefix 1 program world).run.2 := by
  rw [GoldContextCollision.context_run]
  change ¬[Observation.hash (GoldContextInput.bytes base) (List.ofFn root)].Sublist [.start naming]
  simp only [List.singleton_sublist,List.mem_singleton]
  intro impossible
  cases impossible

/-- Full execution does not justify old observation: the coverage theorem
must take the explicit late-target branch in this fixture. -/
theorem coverage_branch : ProgramContextTarget.Bad program world := by
  have named : root ∈ ContextDigestTargets.targets (runPrefix 1 program world).run.2 := by rw [start_targets]; exact Finset.mem_singleton_self _
  exact (ProgramContextTarget.context_observed_or_bad program world 1 base root base_context full named).resolve_left prefix_missing


/-- All original slots are observed in actual preparation, including the
unused distinct-context slot and the duplicate source. -/
theorem native_registry_slots : ∀ slot : Fin HasteBootsRegistryAncestrySmoke.registry.val.length,
    (run (NativeBrakedownContext.context HasteBootsRegistryAncestrySmoke.description
      (HasteBootsRegistryAncestrySmoke.registry.val.get slot).parameters) HasteBootsRegistryAncestrySmoke.world).run.2.Sublist
      HasteBootsRegistryAncestrySmoke.preparation.2 := by
  intro slot
  obtain ⟨geometry,success⟩ := HasteBootsRegistryAncestrySmoke.prepared_exists
  exact (RegistryContextObservation.contexts _ _ _ _ HasteBootsRegistryAncestrySmoke.contexts_computed _ (List.get_mem _ _)).trans
    (RegistryContextObservation.prepare _ _ _ _ _ _ geometry success)

end
end FormalProof4FHE.HasteBoots.ContextCoverageSmoke
