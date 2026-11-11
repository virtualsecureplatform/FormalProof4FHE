module
import all FormalProof4FHE.HasteBoots.AllocatedParentData
import all FormalProof4FHE.HasteBoots.GoldContextFiber
import all FormalProof4FHETest.HasteBootsRegistryAncestrySmoke
import all FormalProof4FHETest.HasteBootsContextAssociationSmoke

namespace FormalProof4FHE.HasteBoots.SharedParentDataSmoke
open HasteBootsRegistryAncestrySmoke (frames framed expected packet producer registered preflightParent description registry world contexts_computed)
open SharedParentInputView (View registryFrame groupedFrame flatFrame forkFrame requestFrame)
open OracleProgram (run)
noncomputable section

def view : View := ⟨frames,expected,NativeLookupMultiplicityWire.grouped packet,NativeLookupMultiplicityWire.flattened packet⟩
theorem valid : ∀ frame ∈ view.frames, TranscriptFrame.Valid frame :=
  SharedParentInputView.valid view framed.1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem actual_parsed : SharedParentInputView.parse producer = some view := by
  unfold producer
  rw [registered,SharedParentInputView.native_frames preflightParent frames framed.2 expected packet]
  exact SharedParentInputView.parse_native view valid

/-- The final registry retains the duplicate original slot and the unused
slot with a different context, although the request uses only slot 1. -/
theorem original_slots : view.sources.val.length = 3 ∧ view.sources.val[0]? = view.sources.val[1]? ∧
    view.sources.val[0]?.map Prod.fst ≠ view.sources.val[2]?.map Prod.fst := by
  exact ⟨rfl,rfl,by decide +kernel⟩

theorem unused_slot : ∃ source, view.sources.val[2]? = some source ∧
    (run (NativeBrakedownContext.context description registry.val[2].parameters) world).run.1 = some source.1 ∧
      source.2 = registry.val[2].root :=
  OriginalSharedParent.slot description registry world view contexts_computed ⟨2,by decide⟩

def emptySources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source := ⟨[],by decide⟩
def decoy : View := {view with before := registryFrame emptySources :: frames}

theorem decoy_valid : ∀ frame ∈ decoy.frames, TranscriptFrame.Valid frame := by
  apply SharedParentInputView.valid
  · intro frame member
    rcases List.mem_cons.mp member with rfl | old
    · constructor <;> decide +kernel
    · exact framed.1 frame old
  all_goals decide +kernel

/-- An earlier empty registry frame is retained in the prefix and cannot
replace the actual adjacent final registry. -/
theorem decoy_parsed : SharedParentInputView.parse (TranscriptFrame.encodeMany decoy.frames) = some decoy :=
  SharedParentInputView.parse_native decoy decoy_valid

theorem decoy_sources : decoy.sources = expected := rfl

/-- Swapping the adjacent grouped and flat frames is rejected even when the
final registry itself is valid and exactly decodes. -/
theorem swapped_rejected : SharedParentInputView.readParts requestFrame forkFrame (groupedFrame view.grouped)
    (flatFrame view.flat) (registryFrame expected) frames.reverse = none := by
  have apart : groupedFrame view.grouped ≠ flatFrame (groupedFrame view.grouped).message := by
    intro equal
    have labels := congrArg TranscriptFrame.Frame.label equal
    change NativeSharedLookupChild.groupedLabel = NativeSharedLookupChild.flatLabel at labels
    have different : NativeSharedLookupChild.groupedLabel ≠ NativeSharedLookupChild.flatLabel := by decide +kernel
    exact different labels
  simp only [SharedParentInputView.readParts,registryFrame,NativeExactCodec.read_encode,Option.bind_some]
  apply ite_eq_right
  intro accepted
  exact apart accepted.2.2.1

def otherWorld : InputIndexedOracle.World
  | .inl _ => 1
  | .inr _ => 0

theorem context_same : (run ContextAssociationSmoke.program otherWorld).run =
    (run ContextAssociationSmoke.program ContextAssociationSmoke.world).run := by
  simp only [ContextAssociationSmoke.program,OracleProgram.run_bind,ObservationReplay.run_bind,GoldContextCollision.context_run]
  rfl

/-- Equal observed digests of distinct full parameter records across worlds
enter the existing shared hash bad event, not a new per-slot exception. -/
theorem context_bad : NativeRootFamilyLifetime.Bad HasteBootsBatchMeaningSmoke.root ContextAssociationSmoke.history := by
  have computed : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ContextAssociationSmoke.other) otherWorld).run.1 =
      some HasteBootsBatchMeaningSmoke.root := by rw [GoldContextCollision.context_run]; rfl
  have observed : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ContextAssociationSmoke.other) otherWorld).run.2.Sublist
      (run ContextAssociationSmoke.program otherWorld).run.2 := by
    rw [context_same]
    have equal : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ContextAssociationSmoke.other) otherWorld).run.2 =
        (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ContextAssociationSmoke.other) ContextAssociationSmoke.world).run.2 := by
      simp only [GoldContextCollision.context_run]
      rfl
    rw [equal]
    exact ContextAssociationSmoke.other_observed
  exact (GoldContextFiber.parameters_or_bad (OracleProgram.run_replay ContextAssociationSmoke.program) ContextAssociationSmoke.world otherWorld
    ContextAssociationSmoke.base ContextAssociationSmoke.other HasteBootsBatchMeaningSmoke.root HasteBootsBatchMeaningSmoke.root
    ContextAssociationSmoke.base_context computed ContextAssociationSmoke.base_observed observed context_same).resolve_left ContextAssociationSmoke.different

end
end FormalProof4FHE.HasteBoots.SharedParentDataSmoke
