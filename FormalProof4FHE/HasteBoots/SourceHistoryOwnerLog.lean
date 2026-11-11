module
public import FormalProof4FHE.HasteBoots.SourceSnapshotLogIdentity
@[expose] public section

/-! Select the immutable source owner log by full context/root from the whole
public history. Once recorded, later observations cannot change the result.
For an unrecorded key the existing selector's fallback is still the current
hash log; no stability assertion is made before a snapshot exists. -/
namespace FormalProof4FHE.HasteBoots.SourceHistoryOwnerLog
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeRootFamilySourceSelection (Log)
open NativeGoldBatchFamilyAvailability (reconstructed)
open StoredSourceVectorReadCost (sourceView)
open StoredGoldPublicSource (viewLog)
noncomputable section

def key (context root : Digest) : StoredSourceVectorReadCost.Source := (Vector.ofFn context,Vector.ofFn root)

theorem key_view (context root : Digest) : sourceView (key context root) = (context,root) := by
  have get : ∀ {n : ℕ} (f : Fin n → InputIndexedOracle.Byte) (i : Fin n), (Vector.ofFn f).get i = f i := by
    intro n f i
    simp [Vector.get]
    exact congrArg f (Fin.ext rfl)
  apply Prod.ext <;> funext i <;> exact get _ i

def selected (history : List Observation) (context root : Digest) : Log :=
  viewLog (StoredSourceSnapshotSelection.run history (key context root)).value

/-- Whole-history lookup returns the exact original recorded log, rather than
any later cumulative hash log. Snapshot existence is essential. -/
theorem of_snapshot (dummy : Digest) (history : List Observation) (context root : Digest)
    (height : NativeMerkleShapeFamily.Height) (sourceLog : Log)
    (present : ⟨(context,height),⟨root,sourceLog⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints) :
    selected history context root = sourceLog := by
  have stored := (SourceSnapshotLogIdentity.snapshots_perm dummy history).mem_iff.mpr present
  obtain ⟨mark,member,markKey,markLog⟩ :=
    (StoredSourceSnapshotSelection.checkpoint_iff _ (context,root) height sourceLog).mp ⟨_,stored,rfl,rfl,rfl⟩
  let state := (StoredSourceSnapshotHistory.reconstruct history).value
  have sameKey : sourceView mark.source = sourceView (key context root) := markKey.trans (key_view context root).symm
  cases found : (StoredSourceSnapshotSelection.find (key context root) state.snapshots).value with
  | none => exact False.elim ((StoredSourceSnapshotSelection.find_none _ _ found mark member) sameKey)
  | some chosen =>
    obtain ⟨chosenMember,chosenKey⟩ := StoredSourceSnapshotSelection.find_some _ _ _ found
    have same := StoredSourceSnapshotSelection.unique_source _ (StoredSourceSnapshotSelection.reconstruct_distinct history)
      chosen mark chosenMember member (chosenKey.trans sameKey.symm)
    change viewLog (StoredSourceSnapshotSelection.select state (key context root)).value = sourceLog
    simp only [StoredSourceSnapshotSelection.select,found]
    exact (congrArg (fun value : StoredSourceSnapshotHistory.Snapshot => viewLog value.log) same).trans markLog

theorem batch_recovered (dummy : Digest) (history : List Observation) (field : NativeGoldBatchFieldInputView.View)
    (parsed : NativeGoldBatchFieldInputView.parse (NativeGoldBatchFirstFieldSource.input field) = some field)
    (sourceLog : Log) (recovered : NativeGoldBatchFirstFieldSource.recover dummy history field = some sourceLog) :
    selected history field.data.context field.data.root = sourceLog :=
  of_snapshot dummy history field.data.context field.data.root 0 sourceLog
    (NativeGoldBatchFirstFieldSource.recover_snapshot dummy history field parsed sourceLog recovered 0)

theorem single_recovered (dummy : Digest) (history : List Observation) (field : SingleOpeningFieldInputView.View)
    (parsed : SingleOpeningFieldInputView.parse (SingleOpeningFirstFieldSource.input field) = some field)
    (sourceLog : Log) (recovered : SingleOpeningFirstFieldSource.recover dummy history field = some sourceLog) :
    selected history field.data.context field.data.root = sourceLog :=
  of_snapshot dummy history field.data.context field.data.root 0 sourceLog
    (SingleOpeningFirstFieldSource.recover_snapshot dummy history field parsed sourceLog recovered 0)

/-- The reference table may be read from the complete later history without
moving the original snapshot. An unseen key is deliberately excluded. -/
theorem selected_append (dummy : Digest) (before after : List Observation) (context root : Digest)
    (height : NativeMerkleShapeFamily.Height) (sourceLog : Log)
    (present : ⟨(context,height),⟨root,sourceLog⟩⟩ ∈ (reconstructed dummy before).checkpoints.checkpoints) :
    selected (before++after) context root = selected before context root := by
  have retained := NativeRootFamilyHistory.fold_retains NativeGoldColumnAuthentication.encoding dummy
    (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy before) after (context,height) ⟨root,sourceLog⟩ present
  have later : ⟨(context,height),⟨root,sourceLog⟩⟩ ∈ (reconstructed dummy (before++after)).checkpoints.checkpoints := by
    simpa only [reconstructed,NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial,List.foldl_append] using retained
  exact (of_snapshot dummy (before++after) context root height sourceLog later).trans
    (of_snapshot dummy before context root height sourceLog present).symm

end
end FormalProof4FHE.HasteBoots.SourceHistoryOwnerLog
