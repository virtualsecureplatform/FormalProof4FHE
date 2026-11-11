module
import all FormalProof4FHE.HasteBoots.FamilyPosteriorMismatch
import all FormalProof4FHE.HasteBoots.AllocatedFirstParentFamily
import all FormalProof4FHETest.HasteBootsContextAssociationSmoke
import all FormalProof4FHETest.HasteBootsParentBindingsSmoke

namespace FormalProof4FHE.HasteBoots.OriginalFamilySmoke
open InputIndexedOracle (Input World)
open NativeGoldBlockCode (description)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
open ContextAssociationSmoke (base other world different)
open HasteBootsBatchMeaningSmoke (root usize)
noncomputable section

def left : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored) :=
  ⟨[⟨base,root⟩,⟨base,root⟩,⟨other,root⟩],by decide⟩
def right : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored) :=
  ⟨[⟨other,root⟩,⟨base,root⟩,⟨other,root⟩],by decide⟩
def sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source := ⟨[(root,root),(root,root),(root,root)],by decide⟩
def binding : NativeCanonicalLookupWire.Binding := ⟨HasteBootsRegistryAncestrySmoke.config,root,⟨[(root,root)],by decide⟩⟩
def view : SharedParentInputView.View := ⟨[ParentBindingTrace.frame binding],sources,[],[]⟩
def input := TranscriptFrame.encodeMany view.frames

theorem valid : ∀ frame ∈ view.frames, TranscriptFrame.Valid frame := by
  apply SharedParentInputView.valid
  · intro frame member
    obtain rfl := List.mem_singleton.mp member
    constructor <;> decide +kernel
  all_goals decide +kernel

theorem parsed : SharedParentInputView.parse input = some view := SharedParentInputView.parse_native view valid

theorem parent_parsed : NativeParentInputView.parseParent input = some view.frames := by
  rw [NativeParentInputView.parseParent,input,TranscriptFrame.decodeAll_encodeMany _ valid,Option.bind_some]
  have seed : NativeParentInputView.isSeedFrames view.frames := by
    exact ⟨rfl,rfl,rfl,rfl⟩
  exact ite_eq_left seed

def program : Program Unit := .hash (GoldContextInput.bytes base) (fun _ => .hash (GoldContextInput.bytes other) (fun _ => .start input (.pure ())))

theorem known : NativeParentLineage.Known world (runPrefix 3 program world).run.2 input root := by
  change NativeParentLineage.Known world ([.hash (GoldContextInput.bytes base) (List.ofFn root),
    .hash (GoldContextInput.bytes other) (List.ofFn root)] ++ [.start input]) input root
  apply NativeParentLineage.Known.direct _ (.start input) view.frames parent_parsed root
  change root ∈ NativeParentLedger.helpers input
  simp only [NativeParentLedger.helpers,NativeParentLedger.frames,input,TranscriptFrame.decodeAll_encodeMany _ valid,Option.getD_some]
  apply List.mem_filterMap.mpr
  exact ⟨ParentBindingTrace.frame binding,by simp [view,SharedParentInputView.View.frames],NativeParentInputView.frameHelper_complete binding⟩

theorem left_computed : (run (NativeSharedLookupParent.contexts description.row left.val) world).run.1 = some sources.val := by
  simp only [left,NativeSharedLookupParent.contexts,OracleProgram.run_bind,ObservationReplay.run_bind,GoldContextCollision.context_run]
  rfl

theorem right_computed : (run (NativeSharedLookupParent.contexts description.row right.val) world).run.1 = some sources.val := by
  simp only [right,NativeSharedLookupParent.contexts,OracleProgram.run_bind,ObservationReplay.run_bind,GoldContextCollision.context_run]
  rfl

theorem full (parameters : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored) (member : parameters = base ∨ parameters = other) :
    (run (NativeBrakedownContext.context description.row parameters) world).run.2.Sublist (run program world).run.2 := by
  rw [GoldContextCollision.context_run]
  change [Observation.hash (GoldContextInput.bytes parameters) (List.ofFn root)].Sublist
    [.hash (GoldContextInput.bytes base) (List.ofFn root),.hash (GoldContextInput.bytes other) (List.ofFn root),.start input]
  apply List.singleton_sublist.mpr
  rcases member with rfl | rfl <;> simp

/-- Changing only an unused slot's full parameter record does not change
the literal context/root vector in this deliberately colliding world. -/
theorem distinct_registry : left ≠ right := by
  intro same
  have entry := OriginalPackedFamily.entry_eq left right same ⟨0,by decide⟩ ⟨0,by decide⟩ rfl
  exact different (congrArg NativeSharedLookupParent.Oracle.parameters entry)

/-- Whole-registry coupling retains its explicit shared exception instead
of identifying distinct unused original records through their digest. -/
theorem exception_retained : NativeRootFamilyLifetime.Bad root (runPrefix 3 program world).run.2 ∨
    ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program world := by
  apply (OriginalRegistryFiber.registry program 3 world world left right input root root view known parsed left_computed right_computed ?_ ?_ rfl).resolve_left distinct_registry
  · intro slot
    apply full
    fin_cases slot <;> first | exact Or.inl rfl | exact Or.inr rfl
  · intro slot
    apply full
    fin_cases slot <;> first | exact Or.inl rfl | exact Or.inr rfl

def slots : LookupOriginalSlots.Slots 3 HasteBootsRegistryAncestrySmoke.request.toModel := ⟨fun _ => ⟨1,by decide⟩,rfl⟩

theorem slots_unique (candidate : LookupOriginalSlots.Slots 3 HasteBootsRegistryAncestrySmoke.request.toModel) : candidate.slot = slots.slot :=
  eq_of_heq (OriginalPackedFamily.slots rfl rfl candidate slots)

/-- Equal digest/root pairs at slots 0 and 1 cannot justify swapping the
original request address from 1 to 0. -/
theorem alias_forbidden (candidate : LookupOriginalSlots.Slots 3 HasteBootsRegistryAncestrySmoke.request.toModel) : (candidate.slot ⟨0,by decide⟩).val ≠ 0 := by
  rw [slots_unique candidate]
  decide

def padded : NativeGoldBatchPcsProgram.Context :=
  {HasteBootsBatchMeaningSmoke.ctx with parameters := {base with width := usize 4}}
def changed : NativeGoldBatchPcsProgram.Context := {padded with fieldFuel := 0,queries := ⟨[],by decide⟩}

theorem capacity : GoldCommonSourceTable.Capacity padded.parameters := by decide +kernel
theorem geometry : GoldHistorySourceTable.Geometry padded.parameters := by constructor <;> decide +kernel

/-- Complete four-lane tables are equal under changes to unrelated call
fields. The fourth packing lane has no zero-padding assumption. -/
theorem padding_retained (history : List Observation) (radius : ℕ) :
    HEq (ScalarPublicSourceModel.publicPacked padded root root root history radius capacity geometry (padding := 1) rfl)
      (ScalarPublicSourceModel.publicPacked changed root root root history radius capacity geometry (padding := 1) rfl) :=
  PackedContextCongruence.packed padded changed rfl root root root root root rfl rfl history history rfl radius capacity capacity geometry geometry rfl rfl

end
end FormalProof4FHE.HasteBoots.OriginalFamilySmoke
