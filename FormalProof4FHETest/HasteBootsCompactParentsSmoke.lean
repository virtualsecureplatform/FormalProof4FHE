module
import all FormalProof4FHE.HasteBoots.CompactSourceHistory
import all FormalProof4FHE.HasteBoots.CompactParentLedger
import all FormalProof4FHE.HasteBoots.CompactParentHistory
import all Mathlib.Data.List.Defs
import all Mathlib.Data.Finset.Defs
import all Mathlib.Data.Finset.Card
import all FormalProof4FHE.HasteBoots.NativeRootMessage
import all FormalProof4FHE.HasteBoots.NativeLookupEquality
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
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
private def digest (value : Fin 256) : NativeRootMessage.Digest := fun _ => value
private def key : NativeCanonicalLookupWire.Source := (digest 1,digest 2)
private def parentInput : Input := TranscriptFrame.encodeMany
  (NativeChildSeedView.seededFrames (digest 0) [] [] (digest 0) ++
    [⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode ⟨[key],by decide⟩⟩,
     ⟨6,[],[]⟩,⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩])

-- Reference inheritance doubles the newest source list; compaction retains its key once.
/-- info: true -/
#guard_msgs in
#eval let history := List.replicate 6 (Observation.start parentInput)
      let compact := CompactParentHistory.reconstruct history
      let reference := ExecutableSourceHistory.reconstruct history
      decide (compact.1.parents.length = 6 ∧ compact.1.parents[0]?.map (fun p => p.sources.length) = some 1 ∧
        reference.ledger.parents[0]?.map (fun p => p.sources.length) = some 32 ∧
        CompactParentLedger.metadataSize compact.1 = 6)

-- A longer chain stays compact without constructing the exponential reference list.
/-- info: true -/
#guard_msgs in
#eval let compact := CompactParentHistory.reconstruct (List.replicate 20 (Observation.start parentInput))
      decide (compact.1.parents.length = 20 ∧ CompactParentLedger.metadataSize compact.1 = 20)

/-- info: true -/
#guard_msgs in
#eval let history := List.replicate 5 (Observation.start parentInput) ++ [Observation.output parentInput 999 [7]]
      let compact := CompactParentHistory.reconstruct history
      let reference := ExecutableSourceHistory.reconstruct history
      decide (compact.1.frozen = reference.ledger.frozen ∧ compact.1.frozen.card = 1)

private def parents : NativeParentLedger.State :=
  ⟨[⟨[10],[key,key],[]⟩,⟨[11],[(digest 3,digest 2),(digest 3,digest 2)],[]⟩],∅⟩
private def child (value : Fin 256) : Input := TranscriptFrame.encodeMany
  (NativeChildSeedView.seededFrames (digest 0) [] [] (fun pos => if pos = 17 then value else 0))

-- Both compatible parents survive; a conflicting observed byte excludes only its parent.
/-- info: true -/
#guard_msgs in
#eval let cache := ExecutableSourceHistory.writeBytes NativeShakeCache.empty [10] 17 [9]
      let both := CompactParentLedger.prepare parents cache (child 9)
      let one := CompactParentLedger.prepare parents cache (child 8)
      decide (both.requests.length = 2 ∧ key ∈ both.requests ∧ (digest 3,digest 2) ∈ both.requests ∧
        one.requests = [(digest 3,digest 2)])

-- Source and helper duplicates are removed from each newly stored parent.
private def helpersInput : Input := TranscriptFrame.encodeMany
  (NativeChildSeedView.seededFrames (digest 0) [] [] (digest 0) ++
    [⟨1,NativeLookupEquality.rootsLabel,NativeRootMessage.encode [digest 4] (by decide)⟩,
     ⟨6,[],[]⟩,⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩])
private def repeatedHelpers : NativeParentLedger.State := ⟨[⟨[10],[key,key],[digest 3,digest 3]⟩],∅⟩
/-- info: true -/
#guard_msgs in
#eval let next := CompactParentLedger.discover repeatedHelpers NativeShakeCache.empty helpersInput
      match next.parents[0]? with
      | none => false
      | some parent => decide (parent.sources.length = 2 ∧ key ∈ parent.sources ∧ (digest 3,digest 4) ∈ parent.sources ∧
          parent.helpers = [digest 3])

private def reorderedRegistry : Input := TranscriptFrame.encodeMany
  [⟨1,NativeCanonicalLookupWire.registryLabel,
    NativeCanonicalLookupWire.sourcesCodec.encode ⟨[key,(digest 3,digest 4),key],by decide⟩⟩]

-- Deduplication changes checkpoint-entry order, but not candidate-log order or selection.
/-- info: true -/
#guard_msgs in
#eval let history := [Observation.hash [71] (List.ofFn (digest 11)),Observation.output reorderedRegistry 0 [9],
        Observation.hash [72] (List.ofFn (digest 12))]
      let compact := CompactSourceHistory.reconstruct history
      let reference := ExecutableSourceHistory.reconstruct history
      let frozen : ExecutableSourceHistory.Log := [⟨[71],digest 11⟩]
      decide (compact.snapshots[0]?.map (fun entry => entry.1.1) = some (digest 3) ∧
        reference.snapshots[0]?.map (fun entry => entry.1.1) = some (digest 1) ∧
        compact.snapshots.map (fun entry => entry.2.cumulativeLog) = reference.snapshots.map (fun entry => entry.2.cumulativeLog) ∧
        ExecutableSourceSelection.select compact key = frozen ∧
        ExecutableSourceSelection.select compact (digest 3,digest 4) = frozen)

private def field : NativeGoldBatchFieldInputView.View :=
  ⟨[],⟨digest 1,digest 2,⟨[],by decide⟩,⟨[],by decide⟩⟩,1⟩
private def fieldInput : Input := TranscriptFrame.encodeMany field.frames
/-- info: true -/
#guard_msgs in
#eval let history := List.replicate 6 (Observation.start parentInput) ++
        [Observation.hash [71] (List.ofFn (digest 11)),Observation.output reorderedRegistry 0 [9],
         Observation.hash [72] (List.ofFn (digest 12)),Observation.output fieldInput 999 [7],Observation.output fieldInput 0 [8]]
      decide (CompactSourceHistory.recover history field = some [⟨[71],digest 11⟩])
