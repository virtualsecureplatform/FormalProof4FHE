module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchRootMentions
import all FormalProof4FHE.HasteBoots.NativeGoldBatchRawAvailability
import all FormalProof4FHE.HasteBoots.NativeGoldLookupProgramDomain
import all FormalProof4FHETest.HasteBootsBatchPcsSmoke
open FormalProof4FHE.HasteBoots
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)
open OracleSpec OracleComp
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsSourceGroupsSmoke (nativePrefix nativeContextDigest nativeRootBytes)
namespace HasteBootsBatchExposureSmoke
noncomputable section

def keyBytes (key : NativeCanonicalLookupWire.Source) : Input × Input := (List.ofFn key.1,List.ofFn key.2)
def data : NativeGoldBatchMessage.Data := ⟨HasteBootsSourceGroupsSmoke.nativeDigest,HasteBootsSourceGroupsSmoke.nativeRoot,
  HasteBootsSourceGroupsSmoke.queries,HasteBootsSourceGroupsSmoke.values⟩
def frame : TranscriptFrame.Frame := ⟨1,NativeTranscript.utf8 "mw batched row-code v1",NativeGoldBatchMessage.codec.encode data⟩

-- Golden bytes came from the real pinned Rust batch verifier, including a lazy query entry.
example : (NativeRootInputView.raw nativePrefix).map (List.map keyBytes) = some [(nativeContextDigest,nativeRootBytes)] := by decide +kernel
example : (NativeRootInputView.raw HasteBootsBatchPcsSmoke.Accepted.start0).map (List.map keyBytes) = some [(nativeContextDigest,nativeRootBytes)] := by decide +kernel
example : (NativeRootInputView.raw HasteBootsBatchPcsSmoke.Accepted.start2).map (List.map keyBytes) = some [(nativeContextDigest,nativeRootBytes)] := by decide +kernel
example : (NativeExactCodec.read NativeGoldBatchMessage.codec frame.message).map (fun data => data.queries.val.length) = some 4 := by decide +kernel
example : (NativeExactCodec.read NativeGoldBatchMessage.codec (frame.message++[0])).isNone = true := by decide +kernel
example : (NativeRootInputView.frameSources {frame with message := frame.message++[0]}).isNone = true := by decide +kernel
example : (NativeRootInputView.frameSources {frame with kind := 0}).isNone = true := by decide +kernel
example : (NativeRootInputView.frameSources {frame with label := NativeTranscript.utf8 "unrecognized batch"}).isNone = true := by decide +kernel

-- Even a native-invalid empty batch is a raw/off-path context/root mention.
def empty : NativeGoldBatchMessage.Data := {data with queries := ⟨[],by decide⟩,values := ⟨[],by decide⟩}
example : (NativeRootInputView.frameSources {frame with message := NativeGoldBatchMessage.codec.encode empty}).map (List.map keyBytes) =
    some [(nativeContextDigest,nativeRootBytes)] := by decide +kernel
example : NativeGoldBatchBinding.check HasteBootsSourceGroupsSmoke.batchParameters empty.queries empty.values = false := by decide +kernel

def dummy : Digest := fun _ => 0
def height (_ : Digest) : ℕ := 5
def input := HasteBootsBatchPcsSmoke.Accepted.start0
def first : List NativeTranscript.Observation := [
  .hash HasteBootsBatchPcsSmoke.Accepted.hashInput0 HasteBootsBatchPcsSmoke.Accepted.hashOutput0,
  .output input 7 [0]]
def state (history : List NativeTranscript.Observation) := NativeGoldBatchRawAvailability.reconstructed dummy height history

def snapshots (history : List NativeTranscript.Observation) := (state history).checkpoints.checkpoints.map
  (fun checkpoint => (List.ofFn checkpoint.1,List.ofFn checkpoint.2.root,checkpoint.2.cumulativeLog.length))

-- No verifier declaration or stream start precedes this raw one-byte read at offset 7.
example : snapshots first = [(nativeContextDigest,nativeRootBytes,1)] := by decide +kernel
example : (state [.start input]).checkpoints.checkpoints.length = 0 := by decide +kernel
example : (state [.output input 7 []]).checkpoints.checkpoints.length = 0 := by decide +kernel
example : (state [.output input 7 [0]]).checkpoints.checkpoints.length = 1 := by decide +kernel

-- Later hashes and later reads grow the real cache, without resetting the snapshot.
def later : List NativeTranscript.Observation := first++[.hash [9] (List.replicate 64 42),.output input 0 [1,2,3,4,5,6,7,8]]
example : snapshots later = [(nativeContextDigest,nativeRootBytes,1)] := by decide +kernel
example : (state later).hash.log.length = 2 := by decide +kernel
example : (state first).hash.log.length = 1 := by decide +kernel

example (history : List NativeTranscript.Observation) : (state history).hash = JointHashCache.project history :=
  NativeGoldBatchRawAvailability.reconstructed_hash dummy height history

-- Actual captured native columns become one raw request each, independent of
-- the number of grouped responses. Their leaf hash bytes are unchanged.
def capturedJobs (openingBytes stream : Input) : Option (List NativeGoldColumnWorker.Job) := do
  let opening ← (NativeGoldBatchOpening.codec.read openingBytes).map Prod.fst
  pure (((NativeIndexRequest.ordered 32 1 stream).zip opening.columns.val).map (fun pair => ⟨pair.1,pair.2⟩))
def capturedRequests (rootBytes openingBytes stream : Input) :=
  (capturedJobs openingBytes stream).bind (NativeGoldRawRequests.entries height HasteBootsSourceGroupsSmoke.nativeDigest
    (fun index => rootBytes[index.val]?.getD 0))
def acceptedRequests := capturedRequests HasteBootsBatchPcsSmoke.Accepted.rootBytes HasteBootsBatchPcsSmoke.Accepted.openingBytes
  HasteBootsBatchPcsSmoke.Accepted.stream2
def rejectedRequests := capturedRequests HasteBootsBatchPcsSmoke.SecondResponse.rootBytes HasteBootsBatchPcsSmoke.SecondResponse.openingBytes
  HasteBootsBatchPcsSmoke.SecondResponse.stream2
example : acceptedRequests.map List.length = some 1 := by decide +kernel
example : acceptedRequests.map (fun entries => entries.map (fun entry => NativeGoldColumnAuthentication.leafInput entry.2.payload)) =
    some [HasteBootsBatchPcsSmoke.Accepted.hashInput1] := by decide +kernel
example : rejectedRequests.map (fun entries => entries.map (fun entry => NativeGoldColumnAuthentication.leafInput entry.2.payload)) =
    some [HasteBootsBatchPcsSmoke.SecondResponse.hashInput1] := by decide +kernel

def replay (history : List NativeTranscript.Observation) (request : NativeGoldRawRequests.Request height) :=
  simulateQ (JointHashCache.project history).cache.toPartialImpl
    (NativeMerkleVerifier.verifyPayload NativeGoldColumnAuthentication.encoding (height request.tag) request.position.val request.payload request.leaf request.root request.siblings)
example : acceptedRequests.map (fun entries => entries.map (fun entry => replay HasteBootsBatchPcsSmoke.Accepted.expected entry.2)) = some [some true] := by decide +kernel
example : rejectedRequests.map (fun entries => entries.map (fun entry => replay HasteBootsBatchPcsSmoke.SecondResponse.expected entry.2)) = some [some true] := by decide +kernel
end
end HasteBootsBatchExposureSmoke
