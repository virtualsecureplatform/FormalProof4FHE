module
public import FormalProof4FHE.HasteBoots.ScalarRoundChallengeMeaning
public import FormalProof4FHE.HasteBoots.SingleOpeningExposure
import all Init.Data.String.Defs
@[expose] public section

/-! Strict adjacent-frame recovery of the actual outer scalar challenge's
round packet. No scanning for an earlier matching label and no canonicalizing
of raw message words is performed. Parsing alone is not application ownership. -/
namespace FormalProof4FHE.HasteBoots.ScalarChallengeInputView
open InputIndexedOracle (Input)
open NativeTranscript (Transcript utf8)
open NativeRootMessage (Digest)
open NativeScalarBatchWire (RoundPacket roundCodec roundLabel challengeLabel)
open TranscriptFrame (Frame encodeMany littleEndian)

structure View where
  before : List Frame
  packet : RoundPacket

def roundFrame (packet : RoundPacket) : Frame := ⟨1,roundLabel,roundCodec.encode packet⟩
def typedFrame : Frame := ⟨1,utf8 "typed request kind",TypedFieldRequest.kindBytes .scalar⟩
def extensionFrame : Frame := ⟨1,utf8 "field challenge kind",utf8 "extension vector"⟩
def basisFrame : Frame := ⟨1,utf8 "extension basis",NativeExtensionDescriptor.descriptor 3 7⟩
def fieldFrame : Frame := ⟨4,challengeLabel,littleEndian 16 NativeFields.goldilocksModulus ++ littleEndian 8 3⟩
def View.frames (view : View) := view.before ++ [roundFrame view.packet,typedFrame,extensionFrame,basisFrame,fieldFrame]
def View.phase (view : View) (profile : Digest) := ScalarRoundChallengeMeaning.phase ⟨encodeMany view.before,profile⟩ view.packet

def readRound (frame : Frame) : Option RoundPacket :=
  (roundCodec.read frame.message).bind (fun (packet,tail) =>
    if frame = roundFrame packet ∧ tail = [] then some packet else none)

theorem readRound_native (packet : RoundPacket) : readRound (roundFrame packet) = some packet := by
  have encoded := NativeScalarBatchWire.round_roundtrip packet []
  rw [List.append_nil] at encoded
  simp only [readRound,roundFrame,encoded,Option.bind_some,and_self,ite_true]

theorem readRound_sound (frame : Frame) (packet : RoundPacket) (parsed : readRound frame = some packet) : frame = roundFrame packet := by
  unfold readRound at parsed
  obtain ⟨⟨value,tail⟩,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  dsimp only at parsed
  split at parsed
  next valid => cases Option.some.inj parsed; exact valid.1
  next => contradiction

def readParts (field basis extension typed round : Frame) (rest : List Frame) : Option View :=
  if field = fieldFrame ∧ basis = basisFrame ∧ extension = extensionFrame ∧ typed = typedFrame then
    (readRound round).map (fun packet => ⟨rest.reverse,packet⟩)
  else none

def readFrames : List Frame → Option View
  | field :: basis :: extension :: typed :: round :: rest => readParts field basis extension typed round rest
  | _ => none

def parse (input : Input) : Option View := (TranscriptFrame.decodeAll input).bind (fun frames => readFrames frames.reverse)

theorem readParts_native (before : List Frame) (packet : RoundPacket) :
    readParts fieldFrame basisFrame extensionFrame typedFrame (roundFrame packet) before.reverse = some ⟨before,packet⟩ := by
  simp only [readParts,and_self,ite_true,readRound_native,Option.map_some,List.reverse_reverse]

theorem readParts_sound (field basis extension typed round : Frame) (rest : List Frame) (view : View)
    (parsed : readParts field basis extension typed round rest = some view) :
    field :: basis :: extension :: typed :: round :: rest = view.frames.reverse := by
  unfold readParts at parsed
  split at parsed
  next kinds =>
    obtain ⟨packet,decoded,same⟩ := Option.map_eq_some_iff.mp parsed
    subst view
    have roundEq := readRound_sound round packet decoded
    simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.reverse_reverse]
    rw [kinds.1,kinds.2.1,kinds.2.2.1,kinds.2.2.2,roundEq]
  next => contradiction

theorem readFrames_sound (frames : List Frame) (view : View) (parsed : readFrames frames = some view) : frames = view.frames.reverse := by
  unfold readFrames at parsed
  split at parsed
  next field basis extension typed round rest => exact readParts_sound field basis extension typed round rest view parsed
  next => contradiction

theorem phase_input (view : View) (profile : Digest) : (view.phase profile).pending.input = encodeMany view.frames := by
  rw [View.frames,SingleOpeningExposure.encodeMany_append]
  simp only [View.phase,ScalarRoundChallengeMeaning.phase,TypedFieldRequest.scalarPhase,TypedFieldRequest.prepare,
    NativeExtensionRequest.prepare,NativeScalarBatchWire.bindRound,NativeTranscript.beginField,NativeTranscript.appendBytes,
    NativeTranscript.absorb,encodeMany,roundFrame,typedFrame,extensionFrame,basisFrame,fieldFrame,List.append_nil,List.append_assoc]
  rfl

theorem parse_sound (input : Input) (view : View) (parsed : parse input = some view) (profile : Digest) :
    (view.phase profile).pending.input = input ∧ ∀ frame ∈ view.frames, TranscriptFrame.Valid frame := by
  obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp parsed
  have suffix := readFrames_sound frames.reverse view read
  have same : frames = view.frames := by
    have equal := congrArg List.reverse suffix
    simpa only [List.reverse_reverse] using equal
  obtain ⟨valid,encoded⟩ := TranscriptFrame.decodeAll_sound input frames decoded
  rw [same] at valid encoded
  exact ⟨by rw [phase_input,encoded],valid⟩

theorem parse_native (view : View) (profile : Digest) (valid : ∀ frame ∈ view.frames, TranscriptFrame.Valid frame) :
    parse (view.phase profile).pending.input = some view := by
  rw [phase_input,parse,TranscriptFrame.decodeAll_encodeMany _ valid,Option.bind_some]
  cases view with
  | mk before packet =>
    simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,readFrames]
    exact readParts_native before packet

theorem frames_valid (before : List Frame) (packet : RoundPacket) (prior : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (roundCodec.encode packet).length < TranscriptFrame.lengthLimit) :
    ∀ frame ∈ (View.mk before packet).frames, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [View.frames,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with old | rfl | rfl | rfl | rfl | rfl
  · exact prior frame old
  · exact ⟨by change roundLabel.length < TranscriptFrame.lengthLimit; decide +kernel,fits⟩
  all_goals constructor <;> decide +kernel

theorem rebuild_transcript (transcript : Transcript) (before : List Frame)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before) :
    (⟨encodeMany before,transcript.profile⟩ : Transcript) = transcript := by
  have inputEq := (TranscriptFrame.decodeAll_sound transcript.input before decoded).2
  cases transcript
  cases inputEq
  rfl

theorem actual_parse (transcript : Transcript) (before : List Frame) (packet : RoundPacket)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (fits : (roundCodec.encode packet).length < TranscriptFrame.lengthLimit) :
    parse (ScalarRoundChallengeMeaning.phase transcript packet).pending.input = some ⟨before,packet⟩ := by
  have valid := (TranscriptFrame.decodeAll_sound transcript.input before decoded).1
  have native := parse_native ⟨before,packet⟩ transcript.profile (frames_valid before packet valid fits)
  have restored := rebuild_transcript transcript before decoded
  change parse (ScalarRoundChallengeMeaning.phase ⟨encodeMany before,transcript.profile⟩ packet).pending.input = _ at native
  rw [restored] at native
  exact native

/-- One full challenge input has one adjacent original packet, even when
there are earlier round-label frames in the retained prefix. -/
theorem packet_unique (input : Input) (first second : View)
    (firstParsed : parse input = some first) (secondParsed : parse input = some second) : first.packet = second.packet :=
  congrArg View.packet (Option.some.inj (firstParsed.symm.trans secondParsed))

end FormalProof4FHE.HasteBoots.ScalarChallengeInputView
