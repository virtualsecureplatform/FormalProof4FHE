module
public import FormalProof4FHE.HasteBoots.StoredRegistryPacketCost
public import FormalProof4FHE.HasteBoots.StoredGoldRegistryAssociation
@[expose] public section

/-! Owner association from decoding the actual initialized parent transcript,
with all original registry slots retained. Native framing/allocation and the
selected claim key remain explicit until the enclosing dispatcher is refined. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldRegistryPacketAssociation
open InputIndexedOracle (Input Byte World)
open NativeSharedLookupParent (Oracle)
open NativePrefixCodec (Vector)
open NativeTranscript (Transcript Observation)
open StoredSourceVectorReadCost (Sources view)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem initialized_sources (registry : Vector (Oracle NativeGoldBlockCode.Stored)) (parent : Transcript)
    (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (before : List TranscriptFrame.Frame) (parentBytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (labelFits : NativeCanonicalLookupWire.registryLabel.length < TranscriptFrame.lengthLimit)
    (messageFits : (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources).length < TranscriptFrame.lengthLimit)
    (sources : Sources) (decoded : (StoredRegistryPacketCost.decode initialized.parent.input).value = some sources) :
    view sources = initialized.sources := by
  have origin := NativeSourceRegistry.initialized_origin NativeGoldBlockCode.description.row registry parent world initialized executed
  rw [origin.2.2.1] at decoded
  exact StoredRegistryPacketCost.decoded_native_sources parent initialized.sources sources before parentBytes valid labelFits messageFits decoded

theorem extraction_original (registry : Vector (Oracle NativeGoldBlockCode.Stored)) (parent : Transcript)
    (world : World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.1 = some initialized)
    (before : List TranscriptFrame.Frame) (parentBytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (labelFits : NativeCanonicalLookupWire.registryLabel.length < TranscriptFrame.lengthLimit)
    (messageFits : (NativeCanonicalLookupWire.sourcesCodec.encode initialized.sources).length < TranscriptFrame.lengthLimit)
    (sources : Sources) (decoded : (StoredRegistryPacketCost.decode initialized.parent.input).value = some sources)
    (index : Fin sources.val.length) (history : List Observation)
    (included : (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row registry parent) world).run.2.Sublist history)
    (input : Input) (dummy : Vector Byte 64) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (key : output.1.data.source = sources.val.get index)
    (truthful : ObservationReplay.Agrees world history)
    (safe : ¬NativeRootFamilyLifetime.Bad dummy.get history) :
    ∃ original : Fin registry.val.length,
      (StoredRegistryOwnerCost.owner sources index).value = some original.val ∧ original.val ≤ index.val ∧
      ctx.parameters = (registry.val.get original).parameters ∧
      (registry.val.get original).root = output.1.data.source.2.get :=
  StoredGoldRegistryAssociation.extraction_original_parameters registry parent world initialized executed sources
    (initialized_sources registry parent world initialized executed before parentBytes valid labelFits messageFits sources decoded)
    index history included input dummy ctx radius output accepted key truthful
    (StoredGoldRegistryAssociation.no_collision_of_not_bad dummy.get history safe)

end
end FormalProof4FHE.HasteBoots.StoredGoldRegistryPacketAssociation
