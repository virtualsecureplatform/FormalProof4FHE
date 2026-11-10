module
public import FormalProof4FHE.HasteBoots.SingleOpeningColumnLaw
public import FormalProof4FHE.HasteBoots.NativeIndexInputView
@[expose] public section

/-! Exact structural recovery of the original single-opening binding immediately
before its field request. Adjacent context/query frames and the complete fixed
field suffix are checked. This is an analysis view, not a Rust deserializer or
trusted parameter/source certificate. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFieldInputView
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (utf8)
open NativeUsizeMessage (Usize)
open TranscriptFrame (Frame encodeMany littleEndian)
noncomputable section

structure Data where
  context : Digest
  root : Digest
  query : NativeGoldPcsWire.Query
  claimed : NativeLookupRequestWire.Row

def contextFrame (data : Data) := SingleOpeningExposure.contextFrame data.context
def openingFrame (data : Data) := SingleOpeningExposure.openingFrame data.root data.query data.claimed

def typedFrame : Frame := ⟨1,utf8 "typed request kind",TypedFieldRequest.kindBytes .vector⟩
def primeFrame : Frame := ⟨1,utf8 "field challenge kind",utf8 "prime vector"⟩
def fieldFrame (count : Usize) : Frame := ⟨4,NativeGoldPcsPrelude.randomLabel,
  littleEndian 16 NativeFields.goldilocksModulus ++ littleEndian 8 count.val⟩

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

def readBinding (context opening : Frame) : Option Data :=
  if context.kind = 1 ∧ context.label = utf8 "mw brakedown row-code v2" ∧
      opening.kind = 1 ∧ opening.label = utf8 "mw commitment and query" then do
    let digest ← NativeExactCodec.read NativeByteCodec.digest context.message
    let packet ← NativeExactCodec.read NativeGoldPcsWire.openingCodec opening.message
    pure ⟨digest,packet.1,packet.2.1,packet.2.2⟩
  else none

theorem readBinding_native (data : Data) : readBinding (contextFrame data) (openingFrame data) = some data := by
  simp only [readBinding,contextFrame,openingFrame,SingleOpeningExposure.contextFrame,SingleOpeningExposure.openingFrame,and_self,ite_true,Option.bind_eq_bind]
  rw [show List.ofFn data.context = NativeByteCodec.digest.encode data.context from rfl,NativeExactCodec.read_encode,
    Option.bind_some,NativeGoldPcsWire.opening,NativeExactCodec.read_encode,Option.bind_some]
  rfl

theorem readBinding_sound (context opening : Frame) (data : Data) (parsed : readBinding context opening = some data) :
    context = contextFrame data ∧ opening = openingFrame data := by
  unfold readBinding at parsed
  split at parsed
  next shape =>
    obtain ⟨digest,readDigest,rest⟩ := Option.bind_eq_some_iff.mp parsed
    obtain ⟨packet,readPacket,same⟩ := Option.bind_eq_some_iff.mp rest
    cases same
    have contextBytes := NativeExactCodec.read_sound NativeByteCodec.digest context.message digest readDigest
    have openingBytes := NativeExactCodec.read_sound NativeGoldPcsWire.openingCodec opening.message packet readPacket
    constructor
    · cases context
      simp only [contextFrame,SingleOpeningExposure.contextFrame,Frame.mk.injEq]
      exact ⟨shape.1,shape.2.1,contextBytes.symm⟩
    · cases opening
      simp only [openingFrame,SingleOpeningExposure.openingFrame,NativeGoldPcsWire.opening,Frame.mk.injEq]
      exact ⟨shape.2.2.1,shape.2.2.2,openingBytes.symm⟩
  next => contradiction

structure View where
  before : List Frame
  data : Data
  count : Usize

def View.frames (view : View) := view.before ++ [contextFrame view.data,openingFrame view.data,typedFrame,primeFrame,fieldFrame view.count]

def View.phase (view : View) (profile : Digest) := NativePrimeRequest.phase NativeFields.goldilocksModulus
  (NativeGoldPcsBinding.appendBound ⟨encodeMany view.before,profile⟩ view.data.context view.data.root view.data.query view.data.claimed)
  .vector NativeGoldPcsPrelude.randomLabel view.count

def readParts (field prime typed opening context : Frame) (rest : List Frame) : Option View :=
  if prime = primeFrame ∧ typed = typedFrame then do
    let count ← readCount field
    let data ← readBinding context opening
    pure ⟨rest.reverse,data,count⟩
  else none

def readFrames : List Frame → Option View
  | field :: prime :: typed :: opening :: context :: rest => readParts field prime typed opening context rest
  | _ => none

def parse (input : Input) : Option View := (TranscriptFrame.decodeAll input).bind (fun frames => readFrames frames.reverse)

theorem readParts_native (before : List Frame) (data : Data) (count : Usize) (positive : 0 < count.val) :
    readParts (fieldFrame count) primeFrame typedFrame (openingFrame data) (contextFrame data) before.reverse = some ⟨before,data,count⟩ := by
  simp only [readParts,and_self,ite_true,readCount_native count positive,readBinding_native,
    Option.bind_eq_bind,Option.bind_some,List.reverse_reverse]
  rfl

theorem readParts_sound (field prime typed opening context : Frame) (rest : List Frame) (view : View)
    (parsed : readParts field prime typed opening context rest = some view) :
    field :: prime :: typed :: opening :: context :: rest = view.frames.reverse ∧ 0 < view.count.val := by
  unfold readParts at parsed
  split at parsed
  next kinds =>
    obtain ⟨count,countRead,parsed⟩ := Option.bind_eq_some_iff.mp parsed
    obtain ⟨data,bindingRead,equal⟩ := Option.bind_eq_some_iff.mp parsed
    have equal : (⟨rest.reverse,data,count⟩ : View) = view := Option.some.inj equal
    subst view
    have fieldEq := readCount_sound field count countRead
    have bindingEq := readBinding_sound context opening data bindingRead
    refine ⟨?_,fieldEq.2⟩
    simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.reverse_reverse]
    rw [fieldEq.1,kinds.1,kinds.2,bindingEq.1,bindingEq.2]
  next => contradiction

theorem readFrames_sound (frames : List Frame) (view : View) (parsed : readFrames frames = some view) :
    frames = view.frames.reverse ∧ 0 < view.count.val := by
  unfold readFrames at parsed
  split at parsed
  next field prime typed opening context rest => exact readParts_sound field prime typed opening context rest view parsed
  next => contradiction

theorem phase_input (view : View) (profile : Digest) : (view.phase profile).pending.input = encodeMany view.frames := by
  rw [View.frames,SingleOpeningExposure.encodeMany_append]
  simp only [View.phase,NativePrimeRequest.phase,NativeTranscript.beginField,NativePrimeRequest.prepare,
    TypedFieldRequest.prepare,NativeGoldPcsBinding.appendBound,NativeTranscript.appendBytes,NativeTranscript.absorb,
    encodeMany,fieldFrame,primeFrame,typedFrame,contextFrame,openingFrame,SingleOpeningExposure.contextFrame,
    SingleOpeningExposure.openingFrame,List.append_nil,List.append_assoc]
  rfl

theorem parse_sound (input : Input) (view : View) (parsed : parse input = some view) (profile : Digest) :
    (view.phase profile).pending.input = input ∧ 0 < view.count.val ∧ ∀ frame ∈ view.frames, TranscriptFrame.Valid frame := by
  obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp parsed
  have suffix := readFrames_sound frames.reverse view read
  have equal : frames = view.frames := by
    have same := congrArg List.reverse suffix.1
    simpa only [List.reverse_reverse] using same
  obtain ⟨valid,inputEq⟩ := TranscriptFrame.decodeAll_sound input frames decoded
  rw [equal] at valid inputEq
  exact ⟨by rw [phase_input,inputEq],suffix.2,valid⟩

theorem parse_native (view : View) (profile : Digest) (positive : 0 < view.count.val)
    (framed : ∀ frame ∈ view.frames, TranscriptFrame.Valid frame) : parse (view.phase profile).pending.input = some view := by
  rw [phase_input,parse,TranscriptFrame.decodeAll_encodeMany _ framed,Option.bind_some]
  cases view with
  | mk before data count =>
    simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,readFrames]
    exact readParts_native before data count positive

/-- The actual successful native sampler supplies its complete parse. Context
identity, both raw opening rows and the count are recovered, not assumed. -/
theorem receipt_parse {ctx : NativeGoldPcsExecution.Context} {world : World} {work : NativeGoldPcsWorkers.Prepared}
    {sample : NativeIndexRequest.Result} (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (OracleProgram.run ctx.prefix world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.transcript.input = encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit) :
    ∃ context : Digest,
      (OracleProgram.run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
      parse (SingleOpeningRandomLaw.phase receipt).pending.input =
        some ⟨before,⟨context,ctx.root,ctx.query,ctx.claimed⟩,work.geometry.randomCount⟩ := by
  obtain ⟨context,hashed,bound⟩ := SingleOpeningExposure.binding_origin ctx world receipt.bound receipt.binding
  let view : View := ⟨before,⟨context,ctx.root,ctx.query,ctx.claimed⟩,work.geometry.randomCount⟩
  have dims := SingleOpeningRectangularData.dimensions ctx world work prepared
  have positiveWidth : 0 < ctx.parameters.width.val := Nat.pos_of_ne_zero dims.1
  have positive : 0 < work.geometry.randomCount.val := by
    rw [SingleOpeningRandomLaw.count prepared,dims.2.2]
    positivity
  have framed : ∀ frame ∈ view.frames, TranscriptFrame.Valid frame := by
    change ∀ frame ∈ SingleOpeningExposure.frames before (SingleOpeningExposure.suffix work.geometry.randomCount)
      context ctx.root ctx.query ctx.claimed, TranscriptFrame.Valid frame
    exact SingleOpeningExposure.frames_valid ctx context before work.geometry.randomCount valid fits
  have pending : (SingleOpeningRandomLaw.phase receipt).pending.input = (view.phase ctx.transcript.profile).pending.input := by
    rw [SingleOpeningRandomLaw.phase,bound,SingleOpeningExposure.phase_input ctx context before work.geometry.randomCount parent,phase_input]
    rfl
  refine ⟨context,hashed,?_⟩
  rw [pending]
  exact parse_native view ctx.transcript.profile positive framed

end
end FormalProof4FHE.HasteBoots.SingleOpeningFieldInputView
