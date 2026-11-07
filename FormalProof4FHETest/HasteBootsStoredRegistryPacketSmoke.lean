module
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.StoredRegistryPacketCost
import all FormalProof4FHE.HasteBoots.StoredRegistrySourcesCost
import all FormalProof4FHE.HasteBoots.StoredSourceVectorCost
import all FormalProof4FHE.HasteBoots.StoredSourceVectorReadCost
import all FormalProof4FHE.HasteBoots.StoredDigestView
import all FormalProof4FHE.HasteBoots.FixedByteReadCost
import all FormalProof4FHE.HasteBoots.BytePrefixMatchCost
import all FormalProof4FHE.HasteBoots.BytePrefixCost
import all FormalProof4FHE.HasteBoots.RowEncodingCost
import all FormalProof4FHE.HasteBoots.IntegerEncodingCost
import all FormalProof4FHE.HasteBoots.IntegerPrefixCost
import all FormalProof4FHE.HasteBoots.NativeIntegerPrefix
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.NativeCanonicalLookupWire
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeByteCodec
import all FormalProof4FHE.HasteBoots.ParentSeedRequestCost
import all FormalProof4FHE.HasteBoots.TranscriptFrameStreamCost
import all FormalProof4FHE.HasteBoots.TranscriptFrameCost
import all FormalProof4FHE.HasteBoots.SizedFrameCost
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all FormalProof4FHE.HasteBoots.StoredRegistryOwnerCost
import all FormalProof4FHE.HasteBoots.StoredMetadataCost

namespace FormalProof4FHETest.HasteBootsStoredRegistryPacketSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte)
private def root (value : Nat) : Vector Byte 64 := Vector.replicate 64 (Fin.ofNat 256 value)
private def pair (context rootId : Nat) : StoredSourceVectorReadCost.Source := (root context,root rootId)
private def sources : StoredSourceVectorReadCost.Sources :=
  ⟨[pair 1 9,pair 2 9,pair 1 9,pair 1 10,pair 2 9],by decide⟩
private def packet (values : StoredSourceVectorReadCost.Sources) : TranscriptFrame.Frame :=
  ⟨1,NativeCanonicalLookupWire.registryLabel,(StoredSourceVectorCost.encode values).value⟩
private def empty : StoredSourceVectorReadCost.Sources := ⟨[],by decide⟩
private def input := TranscriptFrame.encodeMany [packet empty,packet sources]
private def ids (values : StoredSourceVectorReadCost.Sources) :=
  values.val.map (fun key => ((key.1.get 0).val,(key.2.get 0).val))

-- A preceding registry must neither merge into nor displace the terminal packet.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredRegistryPacketCost.decode input).value.map ids =
  some [(1,9),(2,9),(1,9),(1,10),(2,9)]) &&
  decide ((StoredRegistryPacketCost.decode input).cost ≤
    1797*input.length+6*StoredRegistrySourcesCost.label.length+1787)

-- Aliases keep their original positions; equal roots with different contexts differ.
/-- info: true -/
#guard_msgs in
#eval match (StoredRegistryPacketCost.decode input).value with
  | none => false
  | some values => (List.finRange values.val.length).all (fun index =>
      decide ((StoredRegistryOwnerCost.owner values index).value = [0,1,0,3,1][index.val]?))

-- An empty terminal packet is authoritative even after a nonempty registry.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredRegistryPacketCost.decode (TranscriptFrame.encodeMany [packet sources,packet empty])).value.map ids = some [])

-- No fallback to an earlier valid registry after a wrong role or label.
/-- info: true -/
#guard_msgs in
#eval [⟨2,NativeCanonicalLookupWire.registryLabel,(packet sources).message⟩,
       ⟨1,[],(packet sources).message⟩].all (fun last =>
  (StoredRegistryPacketCost.decode (TranscriptFrame.encodeMany [packet sources,last])).value.isNone)

-- Truncated, trailing and noncanonical source payloads fail at the terminal packet.
/-- info: true -/
#guard_msgs in
#eval [(packet sources).message.dropLast,(packet sources).message++[0],[251,0,0]].all (fun bytes =>
  (StoredRegistryPacketCost.decode (TranscriptFrame.encodeMany
    [packet sources,⟨1,NativeCanonicalLookupWire.registryLabel,bytes⟩])).value.isNone)

-- Whole-stream framing rejects raw trailing garbage and incomplete final frames.
/-- info: true -/
#guard_msgs in
#eval [[],input++[255],input.dropLast].all (fun bytes => (StoredRegistryPacketCost.decode bytes).value.isNone)
end FormalProof4FHETest.HasteBootsStoredRegistryPacketSmoke
