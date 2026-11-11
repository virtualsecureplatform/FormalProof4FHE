module
public import FormalProof4FHE.HasteBoots.StoredSourceSnapshotSelection
public import FormalProof4FHE.HasteBoots.SingleOpeningFirstFieldSource
@[expose] public section

/-! The causal owner freezes each full context/root key only once. Thus any
canonical single or batch field read for that key recovers the same exact old
log in a common history, even if the reads and nonces differ. This is a replay
invariant and introduces no cryptographic bad event. -/
namespace FormalProof4FHE.HasteBoots.SourceSnapshotLogIdentity
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeRootFamilySourceSelection (Log)
open NativeGoldBatchFamilyAvailability (reconstructed)
open NativeMerkleShapeFamily (Height)
open StoredSourceSnapshotHistory (snapshotView)
noncomputable section

/-- The compact stored snapshots and actual native checkpoints have the same
members, although their order within each 64-height expansion can differ. -/
theorem snapshots_perm (dummy : Digest) (history : List Observation) :
    (snapshotView (StoredSourceSnapshotHistory.reconstruct history).value.snapshots).Perm
      (reconstructed dummy history).checkpoints.checkpoints := by
  have stored := congrArg (fun state : ExecutableSourceHistory.State => state.snapshots)
    (StoredSourceSnapshotHistory.reconstruct_value history)
  have native := congrArg (fun state : ExecutableSourceHistory.State => state.snapshots)
    (ExecutableSourceHistory.reconstruct_eq NativeGoldColumnAuthentication.encoding dummy history)
  have related := (CompactSourceHistory.reconstruct_related history).snapshots
  change (snapshotView (StoredSourceSnapshotHistory.reconstruct history).value.snapshots) = _ at stored
  change (ExecutableSourceHistory.reconstruct history).snapshots =
    (reconstructed dummy history).checkpoints.checkpoints at native
  rw [stored,← native]
  exact related

/-- Even a single supported height identifies the original log for a complete
context/root key. Uniqueness is derived from replay, not assumed of input. -/
theorem snapshot_log_unique (dummy : Digest) (history : List Observation) (context root : Digest)
    (height : Height) (first last : Log)
    (firstIn : ⟨(context,height),⟨root,first⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints)
    (lastIn : ⟨(context,height),⟨root,last⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints) : first = last := by
  have perm := snapshots_perm dummy history
  have firstStored := perm.mem_iff.mpr firstIn
  have lastStored := perm.mem_iff.mpr lastIn
  obtain ⟨firstMark,firstMember,firstKey,firstLog⟩ :=
    (StoredSourceSnapshotSelection.checkpoint_iff _ (context,root) height first).mp
      ⟨_,firstStored,rfl,rfl,rfl⟩
  obtain ⟨lastMark,lastMember,lastKey,lastLog⟩ :=
    (StoredSourceSnapshotSelection.checkpoint_iff _ (context,root) height last).mp
      ⟨_,lastStored,rfl,rfl,rfl⟩
  have same := StoredSourceSnapshotSelection.unique_source _
    (StoredSourceSnapshotSelection.reconstruct_distinct history) firstMark lastMark firstMember lastMember (firstKey.trans lastKey.symm)
  exact firstLog.symm.trans ((congrArg (fun mark : StoredSourceSnapshotHistory.Snapshot => StoredGoldPublicSource.viewLog mark.log) same).trans lastLog)

theorem batches (dummy : Digest) (history : List Observation) (first last : NativeGoldBatchFieldInputView.View)
    (firstParsed : NativeGoldBatchFieldInputView.parse (NativeGoldBatchFirstFieldSource.input first) = some first)
    (lastParsed : NativeGoldBatchFieldInputView.parse (NativeGoldBatchFirstFieldSource.input last) = some last)
    (context : first.data.context = last.data.context) (root : first.data.root = last.data.root)
    (firstLog lastLog : Log)
    (firstRecovered : NativeGoldBatchFirstFieldSource.recover dummy history first = some firstLog)
    (lastRecovered : NativeGoldBatchFirstFieldSource.recover dummy history last = some lastLog) : firstLog = lastLog := by
  have firstIn := NativeGoldBatchFirstFieldSource.recover_snapshot dummy history first firstParsed firstLog firstRecovered 0
  have lastIn := NativeGoldBatchFirstFieldSource.recover_snapshot dummy history last lastParsed lastLog lastRecovered 0
  rw [context,root] at firstIn
  exact snapshot_log_unique dummy history last.data.context last.data.root 0 firstLog lastLog firstIn lastIn

theorem singles (dummy : Digest) (history : List Observation) (first last : SingleOpeningFieldInputView.View)
    (firstParsed : SingleOpeningFieldInputView.parse (SingleOpeningFirstFieldSource.input first) = some first)
    (lastParsed : SingleOpeningFieldInputView.parse (SingleOpeningFirstFieldSource.input last) = some last)
    (context : first.data.context = last.data.context) (root : first.data.root = last.data.root)
    (firstLog lastLog : Log)
    (firstRecovered : SingleOpeningFirstFieldSource.recover dummy history first = some firstLog)
    (lastRecovered : SingleOpeningFirstFieldSource.recover dummy history last = some lastLog) : firstLog = lastLog := by
  have firstIn := SingleOpeningFirstFieldSource.recover_snapshot dummy history first firstParsed firstLog firstRecovered 0
  have lastIn := SingleOpeningFirstFieldSource.recover_snapshot dummy history last lastParsed lastLog lastRecovered 0
  rw [context,root] at firstIn
  exact snapshot_log_unique dummy history last.data.context last.data.root 0 firstLog lastLog firstIn lastIn

theorem single_batch (dummy : Digest) (history : List Observation)
    (single : SingleOpeningFieldInputView.View) (batch : NativeGoldBatchFieldInputView.View)
    (singleParsed : SingleOpeningFieldInputView.parse (SingleOpeningFirstFieldSource.input single) = some single)
    (batchParsed : NativeGoldBatchFieldInputView.parse (NativeGoldBatchFirstFieldSource.input batch) = some batch)
    (context : single.data.context = batch.data.context) (root : single.data.root = batch.data.root)
    (singleLog batchLog : Log)
    (singleRecovered : SingleOpeningFirstFieldSource.recover dummy history single = some singleLog)
    (batchRecovered : NativeGoldBatchFirstFieldSource.recover dummy history batch = some batchLog) : singleLog = batchLog := by
  have singleIn := SingleOpeningFirstFieldSource.recover_snapshot dummy history single singleParsed singleLog singleRecovered 0
  have batchIn := NativeGoldBatchFirstFieldSource.recover_snapshot dummy history batch batchParsed batchLog batchRecovered 0
  rw [context,root] at singleIn
  exact snapshot_log_unique dummy history batch.data.context batch.data.root 0 singleLog batchLog singleIn batchIn

end
end FormalProof4FHE.HasteBoots.SourceSnapshotLogIdentity
