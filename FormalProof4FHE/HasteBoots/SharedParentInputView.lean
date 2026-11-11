module
public import FormalProof4FHE.HasteBoots.NativeRegistryAncestry
public import FormalProof4FHE.HasteBoots.NativeExactCodec
public import FormalProof4FHE.HasteBoots.SingleOpeningExposure
import all Init.Data.String.Defs
@[expose] public section

/-! Strict adjacent-frame recovery of the original registered source vector
and multiplicity bytes from a shared lookup parent-seed input. Earlier frames
with the same labels are retained as a prefix, never substituted for the
actual final registry, grouped/flat data, fork and seed request. -/
namespace FormalProof4FHE.HasteBoots.SharedParentInputView
open InputIndexedOracle (Input)
open NativePrefixCodec (Vector)
open NativeCanonicalLookupWire (Source)
open TranscriptFrame (Frame encodeMany)
open NativeTranscript (Transcript)

structure View where
  before : List Frame
  sources : Vector Source
  grouped : Input
  flat : Input

def registryFrame (sources : Vector Source) : Frame := ⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩
def groupedFrame (bytes : Input) : Frame := ⟨1,NativeSharedLookupChild.groupedLabel,bytes⟩
def flatFrame (bytes : Input) : Frame := ⟨1,NativeSharedLookupChild.flatLabel,bytes⟩
def forkFrame : Frame := ⟨6,NativeSharedLookupChild.childLabel,NativeSharedLookupChild.childContext⟩
def requestFrame : Frame := ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩
def View.frames (view : View) : List Frame :=
  view.before ++ [registryFrame view.sources,groupedFrame view.grouped,flatFrame view.flat,forkFrame,requestFrame]

def readParts (request fork flat grouped registry : Frame) (rest : List Frame) : Option View :=
  (NativeExactCodec.read NativeCanonicalLookupWire.sourcesCodec registry.message).bind fun sources =>
    if request = requestFrame ∧ fork = forkFrame ∧ flat = flatFrame flat.message ∧
        grouped = groupedFrame grouped.message ∧ registry = registryFrame sources then
      some ⟨rest.reverse,sources,grouped.message,flat.message⟩ else none

def readFrames : List Frame → Option View
  | request :: fork :: flat :: grouped :: registry :: rest => readParts request fork flat grouped registry rest
  | _ => none

def parse (input : Input) : Option View := (TranscriptFrame.decodeAll input).bind (fun frames => readFrames frames.reverse)

theorem readParts_native (view : View) :
    readParts requestFrame forkFrame (flatFrame view.flat) (groupedFrame view.grouped) (registryFrame view.sources) view.before.reverse = some view := by
  simp only [readParts,registryFrame,NativeExactCodec.read_encode,Option.bind_some,flatFrame,groupedFrame,and_self,ite_true,List.reverse_reverse]

theorem readParts_sound (request fork flat grouped registry : Frame) (rest : List Frame) (view : View)
    (parsed : readParts request fork flat grouped registry rest = some view) :
    request :: fork :: flat :: grouped :: registry :: rest = view.frames.reverse := by
  obtain ⟨sources,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  split at parsed
  next valid =>
    obtain rfl := Option.some.inj parsed
    simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.reverse_reverse]
    rw [valid.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2]
    rfl
  next => contradiction

theorem readFrames_sound (frames : List Frame) (view : View) (parsed : readFrames frames = some view) : frames = view.frames.reverse := by
  unfold readFrames at parsed
  split at parsed
  next request fork flat grouped registry rest => exact readParts_sound request fork flat grouped registry rest view parsed
  next => contradiction

theorem parse_native (view : View) (valid : ∀ frame ∈ view.frames, TranscriptFrame.Valid frame) :
    parse (encodeMany view.frames) = some view := by
  rw [parse,TranscriptFrame.decodeAll_encodeMany _ valid,Option.bind_some]
  simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,readFrames]
  exact readParts_native view

theorem parse_sound (input : Input) (view : View) (parsed : parse input = some view) :
    input = encodeMany view.frames ∧ ∀ frame ∈ view.frames, TranscriptFrame.Valid frame := by
  obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp parsed
  have same := congrArg List.reverse (readFrames_sound frames.reverse view read)
  simp only [List.reverse_reverse] at same
  obtain ⟨valid,encoded⟩ := TranscriptFrame.decodeAll_sound input frames decoded
  rw [same] at valid encoded
  exact ⟨encoded,valid⟩

theorem valid (view : View) (before : ∀ frame ∈ view.before, TranscriptFrame.Valid frame)
    (sources : (NativeCanonicalLookupWire.sourcesCodec.encode view.sources).length < TranscriptFrame.lengthLimit)
    (grouped : view.grouped.length < TranscriptFrame.lengthLimit) (flat : view.flat.length < TranscriptFrame.lengthLimit) :
    ∀ frame ∈ view.frames, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [View.frames,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with old | rfl | rfl | rfl | rfl | rfl
  · exact before frame old
  · exact ⟨by change NativeCanonicalLookupWire.registryLabel.length < _; unfold NativeCanonicalLookupWire.registryLabel NativeTranscript.utf8; decide +kernel,sources⟩
  · exact ⟨by change NativeSharedLookupChild.groupedLabel.length < _; unfold NativeSharedLookupChild.groupedLabel NativeTranscript.utf8; decide +kernel,grouped⟩
  · exact ⟨by change NativeSharedLookupChild.flatLabel.length < _; unfold NativeSharedLookupChild.flatLabel NativeTranscript.utf8; decide +kernel,flat⟩
  · constructor
    · change NativeSharedLookupChild.childLabel.length < _
      unfold NativeSharedLookupChild.childLabel NativeTranscript.utf8
      decide +kernel
    · change NativeSharedLookupChild.childContext.length < _
      unfold NativeSharedLookupChild.childContext NativeTranscript.utf8
      decide +kernel
  · constructor
    · change (NativeTranscript.utf8 "classical child seed").length < _
      unfold NativeTranscript.utf8
      decide +kernel
    · change (TranscriptFrame.littleEndian 8 64).length < _
      rw [TranscriptFrame.littleEndian_length]
      decide

/-- The native final registry and multiplicity suffix has exactly this form,
without requiring equality of any earlier parent transcript. -/
theorem native_frames (parent : Transcript) (before : List Frame) (bytes : parent.input = encodeMany before)
    (sources : Vector Source) (packet : NativeLookupMultiplicityWire.Packet) :
    NativeForkAncestry.seedInput (NativeSharedLookupChild.prepare (NativeCanonicalLookupWire.registry parent sources) packet)
      NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext =
    encodeMany (View.mk before sources (NativeLookupMultiplicityWire.grouped packet) (NativeLookupMultiplicityWire.flattened packet)).frames := by
  simp only [NativeForkAncestry.seedInput,NativeTranscript.requestInput,NativeTranscript.absorb,
    NativeSharedLookupChild.prepare_input,NativeCanonicalLookupWire.registry_input,bytes,View.frames,
    SingleOpeningExposure.encodeMany_append,TranscriptFrame.encodeMany,registryFrame,groupedFrame,flatFrame,forkFrame,requestFrame,
    List.append_nil,List.append_assoc]

end FormalProof4FHE.HasteBoots.SharedParentInputView
