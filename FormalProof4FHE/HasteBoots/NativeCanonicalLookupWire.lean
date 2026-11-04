module

public import FormalProof4FHE.HasteBoots.NativeLookupRequestWire
public import FormalProof4FHE.HasteBoots.NativeByteCodec
import all Init.Data.String.Defs

@[expose] public section

/-! The canonical bind tuple and Brakedown registry message. Source entries
retain original order and repetitions, and may have different contexts. -/
namespace FormalProof4FHE.HasteBoots.NativeCanonicalLookupWire

open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativePrefixCodec (Codec product vector transport)

abbrev Source := Digest × Digest

def sourcesCodec : Codec (NativePrefixCodec.Vector Source) := vector (product NativeByteCodec.digest NativeByteCodec.digest)

structure Binding where
  config : NativeLookupRequestWire.Config
  helper : Digest
  sources : NativePrefixCodec.Vector Source

/-- The fixed extension degree is an actual serialized usize, not a vector
header, and follows the complete configuration. -/
def payload (binding : Binding) : Input := NativeLookupRequestWire.configCodec.encode binding.config ++
  NativeUsizeMessage.encode ⟨3,by decide⟩ ++ NativeByteCodec.digest.encode binding.helper ++ sourcesCodec.encode binding.sources

def label : Input := NativeTranscript.utf8 "packed canonical backend extension tuple lookup v1"
def registryLabel : Input := NativeTranscript.utf8 "packed deferred opening registry v1"

def bind (parent : NativeTranscript.Transcript) (binding : Binding) : NativeTranscript.Transcript :=
  NativeTranscript.appendBytes parent label (payload binding)

def registry (parent : NativeTranscript.Transcript) (sources : NativePrefixCodec.Vector Source) : NativeTranscript.Transcript :=
  NativeTranscript.appendBytes parent registryLabel (sourcesCodec.encode sources)

theorem sources_encode (sources : NativePrefixCodec.Vector Source) : sourcesCodec.encode sources =
    NativeUsizeMessage.encode ⟨sources.val.length,sources.property⟩ ++
      sources.val.flatMap (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2) := rfl

theorem sources_prefix (sources : NativePrefixCodec.Vector Source) (suffix : Input) :
    sourcesCodec.read (sourcesCodec.encode sources ++ suffix) = some (sources,suffix) := sourcesCodec.read_encode _ _

theorem payload_injective (left right : Binding) (same : payload left = payload right) : left = right := by
  have cfg := NativeLookupRequestWire.configCodec.prefix_injective left.config right.config _ _
    (by simpa only [payload,List.append_assoc] using same)
  have rest := List.append_cancel_left cfg.2
  have helper := NativeByteCodec.digest.prefix_injective left.helper right.helper _ _ rest
  have sources := sourcesCodec.encode_injective helper.2
  cases left; cases right
  simp only [Binding.mk.injEq] at *
  exact ⟨cfg.1,helper.1,sources⟩

theorem bind_input (parent : NativeTranscript.Transcript) (binding : Binding) :
    (bind parent binding).input = parent.input ++ TranscriptFrame.encode ⟨1,label,payload binding⟩ := rfl

theorem registry_input (parent : NativeTranscript.Transcript) (sources : NativePrefixCodec.Vector Source) :
    (registry parent sources).input = parent.input ++ TranscriptFrame.encode ⟨1,registryLabel,sourcesCodec.encode sources⟩ := rfl

/-- Byte-frame allocation domains are retained instead of assumed collision
resistance of the transcript checkpoint. -/
theorem append_injective (parent : NativeTranscript.Transcript) (messageLabel left right : Input)
    (labelFits : messageLabel.length < TranscriptFrame.lengthLimit)
    (leftFits : left.length < TranscriptFrame.lengthLimit) (rightFits : right.length < TranscriptFrame.lengthLimit)
    (same : (NativeTranscript.appendBytes parent messageLabel left).input = (NativeTranscript.appendBytes parent messageLabel right).input) : left = right := by
  have encoded := List.append_cancel_left same
  have frames := TranscriptFrame.encodeMany_injective [⟨1,messageLabel,left⟩] [⟨1,messageLabel,right⟩]
    (by intro frame member; obtain rfl := List.mem_singleton.mp member; exact ⟨labelFits,leftFits⟩)
    (by intro frame member; obtain rfl := List.mem_singleton.mp member; exact ⟨labelFits,rightFits⟩)
    (by simpa only [TranscriptFrame.encodeMany,List.append_nil] using encoded)
  exact congrArg TranscriptFrame.Frame.message (List.cons.inj frames).1

theorem bind_injective (parent : NativeTranscript.Transcript) (left right : Binding)
    (leftFits : (payload left).length < TranscriptFrame.lengthLimit) (rightFits : (payload right).length < TranscriptFrame.lengthLimit)
    (same : (bind parent left).input = (bind parent right).input) : left = right :=
  payload_injective left right (append_injective parent label (payload left) (payload right) (by decide +kernel) leftFits rightFits same)

theorem registry_injective (parent : NativeTranscript.Transcript) (left right : NativePrefixCodec.Vector Source)
    (leftFits : (sourcesCodec.encode left).length < TranscriptFrame.lengthLimit)
    (rightFits : (sourcesCodec.encode right).length < TranscriptFrame.lengthLimit)
    (same : (registry parent left).input = (registry parent right).input) : left = right :=
  sourcesCodec.encode_injective (append_injective parent registryLabel _ _ (by decide +kernel) leftFits rightFits same)

end FormalProof4FHE.HasteBoots.NativeCanonicalLookupWire
