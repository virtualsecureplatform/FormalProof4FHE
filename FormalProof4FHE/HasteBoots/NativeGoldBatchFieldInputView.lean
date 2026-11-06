module
public import FormalProof4FHE.HasteBoots.NativeIndexInputView
public import FormalProof4FHE.HasteBoots.NativeGoldBatchReadExposure
@[expose] public section

/-! Recover the native Goldilocks vector request and its immediate batch bind
from a complete pending input. The fixed suffix is checked rather than scanning
for an arbitrary earlier matching label. This is a structural view, not trusted
context identity, source availability or implementation refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFieldInputView
open InputIndexedOracle (Input)
open NativeTranscript (utf8)
open NativeUsizeMessage (Usize)
open TranscriptFrame (Frame encodeMany littleEndian)
open NativeGoldBatchMessage (Data)

def typedFrame : Frame := ⟨1,utf8 "typed request kind",TypedFieldRequest.kindBytes .vector⟩
def primeFrame : Frame := ⟨1,utf8 "field challenge kind",utf8 "prime vector"⟩
def fieldFrame (count : Usize) : Frame := ⟨4,NativeGoldBatchPrelude.randomLabel,
  littleEndian 16 NativeFields.goldilocksModulus ++ littleEndian 8 count.val⟩
def batchFrame (data : Data) : Frame := NativeGoldBatchExposure.frame data

def readCount (frame : Frame) : Option Usize := do
  let count ← NativeIndexInputView.readU64 (frame.message.drop 16)
  if frame = fieldFrame count ∧ 0 < count.val then some count else none

theorem readCount_native (count : Usize) (positive : 0 < count.val) : readCount (fieldFrame count) = some count := by
  have tail : (fieldFrame count).message.drop 16 = littleEndian 8 count.val := by
    change (littleEndian 16 NativeFields.goldilocksModulus ++ littleEndian 8 count.val).drop 16 = _
    have same : (littleEndian 16 NativeFields.goldilocksModulus ++ littleEndian 8 count.val).drop
        (littleEndian 16 NativeFields.goldilocksModulus).length = littleEndian 8 count.val := List.drop_left
    simpa only [TranscriptFrame.littleEndian_length] using same
  unfold readCount
  rw [tail,NativeIndexInputView.readU64_encode]
  simp only [Option.bind_eq_bind,Option.bind_some,positive,and_true,ite_true]

theorem readCount_sound (frame : Frame) (count : Usize) (parsed : readCount frame = some count) :
    frame = fieldFrame count ∧ 0 < count.val := by
  obtain ⟨value,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  split at parsed
  next valid =>
    have equal := Option.some.inj parsed
    subst count
    exact valid
  next => contradiction

def readBatch (frame : Frame) : Option Data :=
  if frame.kind = 1 ∧ frame.label = utf8 "mw batched row-code v1" then
    NativeExactCodec.read NativeGoldBatchMessage.codec frame.message else none

theorem readBatch_native (data : Data) : readBatch (batchFrame data) = some data := by
  simp only [readBatch,batchFrame,NativeGoldBatchExposure.frame,and_self,ite_true]
  exact NativeGoldBatchMessage.read_exact data

theorem readBatch_sound (frame : Frame) (data : Data) (parsed : readBatch frame = some data) : frame = batchFrame data := by
  unfold readBatch at parsed
  split at parsed
  next shape =>
    have message := NativeExactCodec.read_sound NativeGoldBatchMessage.codec frame.message data parsed
    cases frame
    simp only [batchFrame,NativeGoldBatchExposure.frame,Frame.mk.injEq]
    exact ⟨shape.1,shape.2,message.symm⟩
  next => contradiction

structure View where
  before : List Frame
  data : Data
  count : Usize

def View.frames (view : View) : List Frame := view.before ++ [batchFrame view.data,typedFrame,primeFrame,fieldFrame view.count]

def View.phase (view : View) (profile : NativeRootMessage.Digest) : NativeTranscript.FieldPhase :=
  NativePrimeRequest.phase NativeFields.goldilocksModulus
    (NativeGoldBatchBinding.appendBound ⟨encodeMany view.before,profile⟩ view.data.context view.data.root view.data.queries view.data.values)
    .vector NativeGoldBatchPrelude.randomLabel view.count

def readParts (field prime typed batch : Frame) (rest : List Frame) : Option View :=
  if prime = primeFrame ∧ typed = typedFrame then do
    let count ← readCount field
    let data ← readBatch batch
    pure ⟨rest.reverse,data,count⟩
  else none

def readFrames (frames : List Frame) : Option View :=
  match frames with
  | field :: prime :: typed :: batch :: rest => readParts field prime typed batch rest
  | _ => none

def parse (input : Input) : Option View := (TranscriptFrame.decodeAll input).bind (fun frames => readFrames frames.reverse)

theorem readParts_native (before : List Frame) (data : Data) (count : Usize) (positive : 0 < count.val) :
    readParts (fieldFrame count) primeFrame typedFrame (batchFrame data) before.reverse = some ⟨before,data,count⟩ := by
  simp only [readParts,and_self,ite_true,readCount_native count positive,readBatch_native,
    Option.bind_eq_bind,Option.bind_some,List.reverse_reverse]
  rfl

theorem readParts_sound (field prime typed batch : Frame) (rest : List Frame) (view : View)
    (parsed : readParts field prime typed batch rest = some view) :
    field :: prime :: typed :: batch :: rest = view.frames.reverse ∧ 0 < view.count.val := by
  unfold readParts at parsed
  split at parsed
  next kinds =>
    obtain ⟨count,readCount,parsed⟩ := Option.bind_eq_some_iff.mp parsed
    obtain ⟨data,readBatch,equal⟩ := Option.bind_eq_some_iff.mp parsed
    have equal : (⟨rest.reverse,data,count⟩ : View) = view := Option.some.inj equal
    subst view
    have fieldEq := readCount_sound field count readCount
    have batchEq := readBatch_sound batch data readBatch
    refine ⟨?_,fieldEq.2⟩
    simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.cons_append,List.reverse_reverse]
    rw [fieldEq.1,kinds.1,kinds.2,batchEq]
  next => contradiction

theorem readFrames_sound (frames : List Frame) (view : View) (parsed : readFrames frames = some view) :
    frames = view.frames.reverse ∧ 0 < view.count.val := by
  cases frames with
  | nil => cases parsed
  | cons field rest =>
    cases rest with
    | nil => cases parsed
    | cons prime rest =>
      cases rest with
      | nil => cases parsed
      | cons typed rest =>
        cases rest with
        | nil => cases parsed
        | cons batch rest => exact readParts_sound field prime typed batch rest view parsed

private theorem encodeMany_append (first later : List Frame) : encodeMany (first++later) = encodeMany first ++ encodeMany later := by
  induction first with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append,encodeMany,ih,List.append_assoc]

theorem phase_input (view : View) (profile : NativeRootMessage.Digest) : (view.phase profile).pending.input = encodeMany view.frames := by
  rw [View.frames,encodeMany_append]
  simp only [View.phase,NativePrimeRequest.phase,NativeTranscript.beginField,NativePrimeRequest.prepare,
    TypedFieldRequest.prepare,NativeGoldBatchBinding.appendBound,NativeTranscript.appendBytes,NativeTranscript.absorb,
    encodeMany,fieldFrame,primeFrame,typedFrame,batchFrame,NativeGoldBatchExposure.frame,List.append_nil,List.append_assoc]
  rw [NativeGoldBatchMessage.encode]
  rfl

theorem parse_sound (input : Input) (view : View) (parsed : parse input = some view) (profile : NativeRootMessage.Digest) :
    (view.phase profile).pending.input = input ∧ 0 < view.count.val ∧
      ∀ frame ∈ view.frames, TranscriptFrame.Valid frame := by
  obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp parsed
  have suffix := readFrames_sound frames.reverse view read
  have equal : frames = view.frames := by
    have same := congrArg List.reverse suffix.1
    simpa only [List.reverse_reverse] using same
  obtain ⟨valid,inputEq⟩ := TranscriptFrame.decodeAll_sound input frames decoded
  rw [equal] at valid inputEq
  exact ⟨by rw [phase_input,inputEq],suffix.2,valid⟩

theorem parse_native (view : View) (profile : NativeRootMessage.Digest) (positive : 0 < view.count.val)
    (framed : ∀ frame ∈ view.frames, TranscriptFrame.Valid frame) : parse (view.phase profile).pending.input = some view := by
  rw [phase_input,parse,TranscriptFrame.decodeAll_encodeMany _ framed,Option.bind_some]
  cases view with
  | mk before data count =>
    simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,readFrames]
    exact readParts_native before data count positive
end FormalProof4FHE.HasteBoots.NativeGoldBatchFieldInputView
