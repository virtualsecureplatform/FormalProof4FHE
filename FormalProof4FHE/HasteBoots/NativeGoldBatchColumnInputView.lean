module
public import FormalProof4FHE.HasteBoots.NativeIndexInputView
public import FormalProof4FHE.HasteBoots.NativeGoldBatchResponseBinding
public import FormalProof4FHE.HasteBoots.NativeExactCodec
@[expose] public section

/-! Recover every raw batch response from the complete pending column input.
The canonical response codec checks the full payload; authentication columns
are later data. The view does not assert trusted parameter identity, receipt
lineage, source ownership or Rust deserializer refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchColumnInputView
open InputIndexedOracle (Input)
open TranscriptFrame (Frame encodeMany)
open NativeGoldBatchOpening (Opening)
open NativeLookupRequestWire (Row rowCodec)
open NativePrefixCodec (Codec Vector product vector)

def responseCodec : Codec (Row × Vector Row) := product rowCodec (vector rowCodec)

def responseFrame (opening : Opening) : Frame :=
  ⟨1,NativeTranscript.utf8 "mw batch linear responses",NativeGoldBatchResponseBinding.payload opening⟩

/-- The nonce contains responses, not the later authenticated columns. -/
def responses (opening : Opening) : Opening := {opening with columns := ⟨[],by decide⟩}

def readResponse (frame : Frame) : Option Opening :=
  if frame.kind = 1 ∧ frame.label = NativeTranscript.utf8 "mw batch linear responses" then
    (NativeExactCodec.read responseCodec frame.message).map (fun pair => ⟨pair.1,pair.2,⟨[],by decide⟩⟩)
  else none

theorem readResponse_native (opening : Opening) : readResponse (responseFrame opening) = some (responses opening) := by
  simp only [readResponse,responseFrame,and_self,ite_true]
  change (NativeExactCodec.read responseCodec (responseCodec.encode (opening.test,opening.evaluations))).map _ = _
  rw [NativeExactCodec.read_encode]
  rfl

theorem readResponse_sound (frame : Frame) (opening : Opening) (parsed : readResponse frame = some opening) :
    frame = responseFrame opening ∧ opening.columns.val = [] := by
  unfold readResponse at parsed
  split at parsed
  next shape =>
    obtain ⟨pair,read,equal⟩ := Option.map_eq_some_iff.mp parsed
    subst opening
    have message := NativeExactCodec.read_sound responseCodec frame.message pair read
    constructor
    · cases frame
      simp only [responseFrame,Frame.mk.injEq]
      exact ⟨shape.1,shape.2,message.symm⟩
    · rfl
  next => contradiction

structure View where
  index : NativeIndexInputView.View
  opening : Opening

def readIndex (index : NativeIndexInputView.View) : Option View :=
  match index.before.reverse with
  | response :: _ => (readResponse response).map (fun opening => ⟨index,opening⟩)
  | [] => none

def parse (input : Input) : Option View := (NativeIndexInputView.parse input).bind readIndex

theorem readIndex_sound (index : NativeIndexInputView.View) (view : View) (parsed : readIndex index = some view) :
    view.index = index ∧ (∃ before, index.before = before ++ [responseFrame view.opening]) ∧ view.opening.columns.val = [] := by
  unfold readIndex at parsed
  split at parsed
  next response rest reversed =>
    obtain ⟨opening,read,equal⟩ := Option.map_eq_some_iff.mp parsed
    subst view
    obtain ⟨frame,columns⟩ := readResponse_sound response opening read
    refine ⟨rfl,⟨rest.reverse,?_⟩,columns⟩
    have same := congrArg List.reverse reversed
    simpa only [List.reverse_reverse,List.reverse_cons,frame] using same
  next => contradiction

/-- Every accepted view has the exact original complete SHAKE input, checked
index dimensions, and a canonical raw response frame in its preceding transcript. -/
theorem parse_sound (input : Input) (view : View) (parsed : parse input = some view) (profile : NativeRootMessage.Digest) :
    NativePrequeryIndexLaw.requestInput (view.index.request profile).transcript view.index.label view.index.domain view.index.count = input ∧
      NativeIndexRequest.check view.index.domain view.index.count = true ∧
      (∃ before, view.index.before = before ++ [responseFrame view.opening]) ∧ view.opening.columns.val = [] := by
  obtain ⟨index,read,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨same,before,columns⟩ := readIndex_sound index view parsed
  obtain ⟨inputEq,checked⟩ := NativeIndexInputView.parse_sound input index read profile
  rw [same]
  exact ⟨inputEq,checked,before,columns⟩

private theorem encodeMany_append (first later : List Frame) : encodeMany (first++later) = encodeMany first ++ encodeMany later := by
  induction first with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append,encodeMany,ih,List.append_assoc]

theorem parse_native (before : List Frame) (profile : NativeRootMessage.Digest) (label : Input)
    (domain count : NativeUsizeMessage.Usize) (opening : Opening)
    (valid : NativeIndexRequest.check domain count = true)
    (framed : ∀ frame ∈ NativeIndexInputView.View.frames ⟨before++[responseFrame opening],label,domain,count⟩,
      TranscriptFrame.Valid frame) :
    parse (NativeGoldBatchResponseBinding.input ⟨encodeMany before,profile⟩ label domain count opening) =
      some ⟨⟨before++[responseFrame opening],label,domain,count⟩,responses opening⟩ := by
  have input : NativeGoldBatchResponseBinding.input ⟨encodeMany before,profile⟩ label domain count opening =
      NativePrequeryIndexLaw.requestInput ⟨encodeMany (before++[responseFrame opening]),profile⟩ label domain count := by
    simp only [NativeGoldBatchResponseBinding.input,NativeGoldBatchOpening.bindResponses,NativeTranscript.appendBytes,
      NativeTranscript.absorb,encodeMany_append,encodeMany,List.append_nil,responseFrame]
    rfl
  rw [input,parse,NativeIndexInputView.parse_native _ _ _ _ _ valid framed,Option.bind_some]
  simp only [readIndex,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
  rw [readResponse_native]
  rfl
end FormalProof4FHE.HasteBoots.NativeGoldBatchColumnInputView
