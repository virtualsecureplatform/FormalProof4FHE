module
import all FormalProof4FHE.HasteBoots.UsizeVectorCost
import all FormalProof4FHE.HasteBoots.BytePrefixCost
import all FormalProof4FHE.HasteBoots.IntegerPrefixCost
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Data.Fintype.Defs
import all FormalProof4FHE.HasteBoots.NativeGoldBatchPrelude
import all FormalProof4FHE.HasteBoots.NativeLookupRequestWire
import all FormalProof4FHE.HasteBoots.NativeGoldPcsWire
import all FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
import all FormalProof4FHE.HasteBoots.ExecutableSourceSelection
import all FormalProof4FHE.HasteBoots.ExecutableSourceHistory
import all FormalProof4FHE.HasteBoots.ExecutableParentLedger
import all FormalProof4FHE.HasteBoots.ExecutableParentInputView
import all FormalProof4FHE.HasteBoots.NativeRootInputView
import all FormalProof4FHE.HasteBoots.NativeChildSeedView
import all FormalProof4FHE.HasteBoots.NativeCanonicalLookupWire
import all FormalProof4FHE.HasteBoots.NativeExactCodec
import all FormalProof4FHE.HasteBoots.NativeByteCodec
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeIntegerPrefix
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all FormalProof4FHE.HasteBoots.NativeShakeCache
import all FormalProof4FHE.HasteBoots.JointHashCache
import all FormalProof4FHE.HasteBoots.CausalFirstStreamPrefix
import all FormalProof4FHE.HasteBoots.CausalStreamCoverage
import all FormalProof4FHE.HasteBoots.CausalStreamExposure
import all FormalProof4FHE.HasteBoots.NativeGoldBatchFieldInputView
import all FormalProof4FHE.HasteBoots.NativeGoldBatchExposure
import all FormalProof4FHE.HasteBoots.NativeGoldBatchMessage
import all FormalProof4FHE.HasteBoots.TypedFieldRequest
import all FormalProof4FHE.HasteBoots.NativeFields
open FormalProof4FHE.HasteBoots
open NativeTranscript (Observation)
open InputIndexedOracle (Input)
private def digest (value : Fin 256) : NativeRootMessage.Digest := fun _ => value
private def key : NativeCanonicalLookupWire.Source := (digest 1,digest 2)
private def registry (context : NativeRootMessage.Digest) (aliasByte : Fin 256) : Input :=
  TranscriptFrame.encodeMany [⟨1,NativeCanonicalLookupWire.registryLabel,
    NativeCanonicalLookupWire.sourcesCodec.encode ⟨[(context,digest 2)],by change 1 < 2^64; decide⟩⟩,⟨0,[aliasByte],[]⟩]
private def firstHash : Observation := .hash [71] (List.ofFn (digest 11))
private def laterHash : Observation := .hash [72] (List.ofFn (digest 12))
private def earlyLog : ExecutableSourceHistory.Log := [⟨[71],digest 11⟩]
private def bothLogs : ExecutableSourceHistory.Log := earlyLog ++ [⟨[72],digest 12⟩]

-- An earlier unused alias owns the immutable snapshot for the complete pair.
/-- info: true -/
#guard_msgs in
#eval let history := [firstHash,.output (registry (digest 1) 0) 17 [9],laterHash,.output (registry (digest 1) 1) 0 [8]]
      let state := ExecutableSourceHistory.reconstruct history
      decide (ExecutableSourceSelection.select state key = earlyLog ∧ state.snapshots.length = 64)

-- Starts and empty reads discover metadata but do not freeze a source.
/-- info: true -/
#guard_msgs in
#eval let history := [firstHash,.start (registry (digest 1) 0),.output (registry (digest 1) 0) 0 [],
        laterHash,.output (registry (digest 1) 1) 0 [8]]
      decide (ExecutableSourceSelection.select (ExecutableSourceHistory.reconstruct history) key = bothLogs)

-- The same root under a different complete context has its own later snapshot.
/-- info: true -/
#guard_msgs in
#eval let state := ExecutableSourceHistory.reconstruct [firstHash,.output (registry (digest 1) 0) 0 [9],
        laterHash,.output (registry (digest 3) 0) 0 [8]]
      decide (ExecutableSourceSelection.select state key = earlyLog ∧
        ExecutableSourceSelection.select state (digest 3,digest 2) = bothLogs ∧ state.snapshots.length = 128)

-- Repeated hash observations remain in the current log, including non-role bytes.
/-- info: true -/
#guard_msgs in
#eval let state := ExecutableSourceHistory.reconstruct [firstHash,firstHash,laterHash]
      decide (ExecutableSourceSelection.select state key = earlyLog ++ bothLogs)

private def parents : NativeParentLedger.State :=
  ⟨[⟨[10],[key],[]⟩,⟨[11],[(digest 3,digest 2)],[]⟩],∅⟩
private def child (value : Fin 256) : Input :=
  TranscriptFrame.encodeMany (NativeChildSeedView.seededFrames (digest 0) [] []
    (fun pos => if pos = 17 then value else 0))

-- Unknown bytes retain every compatible parent. One known byte excludes only conflicts.
/-- info: true -/
#guard_msgs in
#eval let cache := ExecutableSourceHistory.writeBytes NativeShakeCache.empty [10] 17 [9]
      decide ((ExecutableParentLedger.active parents NativeShakeCache.empty (child 8)).length = 2 ∧
        (ExecutableParentLedger.active parents cache (child 8)).length = 1 ∧
        (ExecutableParentLedger.active parents cache (child 9)).length = 2)

private def field : NativeGoldBatchFieldInputView.View :=
  ⟨[],⟨digest 1,digest 2,⟨[],by decide⟩,⟨[],by decide⟩⟩,1⟩
private def fieldInput : Input := TranscriptFrame.encodeMany field.frames

-- Recover the old alias's snapshot from a later full field history, across partial reads.
/-- info: true -/
#guard_msgs in
#eval let history := [firstHash,.output (registry (digest 1) 0) 0 [9],laterHash,
        .start fieldInput,.output fieldInput 0 [],.output fieldInput 999 [7],.hash [73] (List.ofFn (digest 13)),
        .output fieldInput 0 [6]]
      decide (ExecutableSourceSelection.recover history field = some earlyLog)

/-- info: true -/
#guard_msgs in
#eval (ExecutableSourceSelection.recover [.start fieldInput,.output fieldInput 0 []] field).isNone
