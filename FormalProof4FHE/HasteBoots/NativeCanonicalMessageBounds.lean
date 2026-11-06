module

public import FormalProof4FHE.HasteBoots.NativeRegistryAncestry
public import FormalProof4FHE.HasteBoots.NativeTranscriptFraming
import all Init.Data.String.Defs
@[expose] public section

/-! Static bounds for canonical bind and original registry frames. Digest
contents do not affect their serialized sizes, including repeated/unused slots. -/
namespace FormalProof4FHE.HasteBoots.NativeCanonicalMessageBounds
open NativeCanonicalLookupWire (Source Binding)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription Parameters)
open NativeTranscript (Transcript)
open NativeTranscriptExtension (Extends)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem sources_length (sources : Vector Source) :
    (NativeCanonicalLookupWire.sourcesCodec.encode sources).length ≤ 9 + 128 * sources.val.length := by
  have flat : (sources.val.flatMap (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2)).length = 128 * sources.val.length := by
    induction sources.val with
    | nil => rfl
    | cons entry tail ih => simp only [List.flatMap_cons,List.length_append,List.length_ofFn,List.length_cons,ih]; omega
  rw [NativeCanonicalLookupWire.sources_encode,List.length_append,flat]
  exact Nat.add_le_add_right (NativeUsizeMessage.encode_length _) _

theorem payload_length (binding : Binding) :
    (NativeCanonicalLookupWire.payload binding).length ≤
      (NativeLookupRequestWire.configCodec.encode binding.config).length + 65 + (9 + 128 * binding.sources.val.length) := by
  have sourceBound := sources_length binding.sources
  have degree : (NativeUsizeMessage.encode ⟨3,by decide⟩).length = 1 := rfl
  simp only [NativeCanonicalLookupWire.payload,List.length_append,degree,NativeByteCodec.digest_encode,List.length_ofFn]
  omega

theorem contexts_length {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (world : World)
    (sources : List Source) (executed : (run (NativeSharedLookupParent.contexts row registry) world).run.1 = some sources) :
    sources.length = registry.length := (NativeRegistryAncestry.contexts_order row registry world sources executed).length_eq.symm

theorem registry_extension (parent : Transcript) (sources : Vector Source)
    (fits : 9 + 128 * sources.val.length < TranscriptFrame.lengthLimit) :
    Extends parent (NativeCanonicalLookupWire.registry parent sources) :=
  NativeTranscriptExtension.absorb parent 1 NativeCanonicalLookupWire.registryLabel _
    ⟨by change NativeCanonicalLookupWire.registryLabel.length < _; decide +kernel,lt_of_le_of_lt (sources_length sources) fits⟩

theorem bind_extension (parent : Transcript) (binding : Binding)
    (fits : (NativeLookupRequestWire.configCodec.encode binding.config).length + 65 + (9 + 128 * binding.sources.val.length) < TranscriptFrame.lengthLimit) :
    Extends parent (NativeCanonicalLookupWire.bind parent binding) :=
  NativeTranscriptExtension.absorb parent 1 NativeCanonicalLookupWire.label _
    ⟨by change NativeCanonicalLookupWire.label.length < _; decide +kernel,lt_of_le_of_lt (payload_length binding) fits⟩
end
end FormalProof4FHE.HasteBoots.NativeCanonicalMessageBounds
