module
public import FormalProof4FHE.HasteBoots.ParentSeedCompletion
@[expose] public section

/-! Completing recognized parent seeds fixes semantic source/helper ancestry
on the refined raw-history fiber. All compatible parents remain represented;
this does not assert unique parents or full parameter authentication. -/
namespace FormalProof4FHE.HasteBoots.ParentMetadataReplay
open InputIndexedOracle (Input World)
open NativeTranscript (Observation Execution)
noncomputable section

theorem source_transfer (world other : World) {history : List Observation} {input : Input} {key : NativeCanonicalLookupWire.Source}
    (known : NativeSourceLineage.Known world history input key)
    (seeds : ∀ parent ∈ ParentSeedCandidates.inputs history,
      InputIndexedOracle.block other parent 0 64 = InputIndexedOracle.block world parent 0 64) :
    NativeSourceLineage.Known other history input key := by
  revert seeds
  induction known with
  | direct before entry frames parsed key source =>
    intro _
    exact .direct before entry frames parsed key source
  | inherit before entry frames parsed parent key earlier quoted ih =>
    intro seeds
    have included := List.sublist_append_left before [entry]
    have inherited := ih (fun input named => seeds input (ParentSeedCandidates.mono _ _ included named))
    apply NativeSourceLineage.Known.inherit before entry frames parsed parent key inherited
    rw [seeds parent (ParentSeedCandidates.mono _ _ included (ParentSeedCandidates.source_known earlier))]
    exact quoted
  | later before later input key earlier ih =>
    intro seeds
    exact .later before later input key (ih (fun parent named => seeds parent (ParentSeedCandidates.mono _ _ (List.sublist_append_left _ _) named)))

theorem helper_transfer (world other : World) {history : List Observation} {input : Input} {context : NativeRootMessage.Digest}
    (known : NativeParentLineage.Known world history input context)
    (seeds : ∀ parent ∈ ParentSeedCandidates.inputs history,
      InputIndexedOracle.block other parent 0 64 = InputIndexedOracle.block world parent 0 64) :
    NativeParentLineage.Known other history input context := by
  revert seeds
  induction known with
  | direct before entry frames parsed context helper =>
    intro _
    exact .direct before entry frames parsed context helper
  | inherit before entry frames parsed parent context earlier quoted ih =>
    intro seeds
    have included := List.sublist_append_left before [entry]
    have inherited := ih (fun input named => seeds input (ParentSeedCandidates.mono _ _ included named))
    apply NativeParentLineage.Known.inherit before entry frames parsed parent context inherited
    rw [seeds parent (ParentSeedCandidates.mono _ _ included (ParentSeedCandidates.helper_known earlier))]
    exact quoted
  | later before later input context earlier ih =>
    intro seeds
    exact .later before later input context (ih (fun parent named => seeds parent (ParentSeedCandidates.mono _ _ (List.sublist_append_left _ _) named)))

theorem on_fiber {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world other : World) (input : Input) (fact : NativeSeedAncestry.Fact)
    (same : (ParentSeedCompletion.extend past other).run = (ParentSeedCompletion.extend past world).run) :
    NativeSeedAncestry.Known other (past other).run.2 input fact ↔ NativeSeedAncestry.Known world (past world).run.2 input fact := by
  have old := ParentSeedCompletion.old_packet past world other same
  have forward : ∀ parent ∈ ParentSeedCandidates.inputs (past world).run.2,
      InputIndexedOracle.block other parent 0 64 = InputIndexedOracle.block world parent 0 64 :=
    fun parent named => ParentSeedCompletion.seed_on_fiber replay world other parent named same
  rw [old]
  cases fact with
  | source key =>
    exact ⟨fun known => source_transfer other world known (fun parent named => (forward parent named).symm),
      fun known => source_transfer world other known forward⟩
  | helper context =>
    exact ⟨fun known => helper_transfer other world known (fun parent named => (forward parent named).symm),
      fun known => helper_transfer world other known forward⟩

end
end FormalProof4FHE.HasteBoots.ParentMetadataReplay
