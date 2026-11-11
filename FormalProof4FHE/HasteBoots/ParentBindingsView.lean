module
public import FormalProof4FHE.HasteBoots.ParentBindingTrace
public import FormalProof4FHE.HasteBoots.NativeRootInputView
public import FormalProof4FHE.HasteBoots.SingleOpeningExposure
import all Init.Data.String.Defs
@[expose] public section

/-! Recover the contiguous native canonical binding suffix and the original
request vector directly before it. A malformed binding is rejected, and an
earlier request frame cannot replace the adjacent native request vector. -/
namespace FormalProof4FHE.HasteBoots.ParentBindingsView
open InputIndexedOracle (Input)
open NativePrefixCodec (Vector)
open NativeCanonicalLookupWire (Binding)
open NativeLookupRequestWire (Request)
open TranscriptFrame (Frame encodeMany)
open ParentBindingTrace (frame)

structure View where
  before : List Frame
  requests : Vector Request
  bindings : List Binding

def requestFrame (requests : Vector Request) : Frame := ⟨1,NativeLookupRequestWire.requestsLabel,NativeLookupRequestWire.requestsCodec.encode requests⟩
def View.frames (view : View) := view.before ++ [requestFrame view.requests] ++ view.bindings.map frame

def readRequest (head : Frame) (rest : List Frame) : Option View :=
  (NativeExactCodec.read NativeLookupRequestWire.requestsCodec head.message).bind fun requests =>
    if head = requestFrame requests then some ⟨rest.reverse,requests,[]⟩ else none

def readFrames : List Frame → Option View
  | [] => none
  | head :: rest =>
    if head.kind = 1 ∧ head.label = NativeCanonicalLookupWire.label then
      (NativeExactCodec.read NativeRootInputView.bindingCodec head.message).bind fun binding =>
        if head = frame binding then (readFrames rest).map (fun view => {view with bindings := view.bindings ++ [binding]}) else none
    else readRequest head rest

def parse (input : Input) : Option View :=
  ((TranscriptFrame.decodeAll input).bind (fun frames => readFrames frames.reverse)).bind fun view =>
    if view.bindings.length = view.requests.val.length then some view else none

theorem labels_apart : NativeLookupRequestWire.requestsLabel ≠ NativeCanonicalLookupWire.label := by
  unfold NativeLookupRequestWire.requestsLabel NativeCanonicalLookupWire.label NativeTranscript.utf8
  decide +kernel

theorem readRequest_native (before : List Frame) (requests : Vector Request) :
    readRequest (requestFrame requests) before.reverse = some ⟨before,requests,[]⟩ := by
  simp only [readRequest,requestFrame,NativeExactCodec.read_encode,Option.bind_some,ite_true,List.reverse_reverse]

theorem binding_read_native (binding : Binding) :
    NativeExactCodec.read NativeRootInputView.bindingCodec (NativeCanonicalLookupWire.payload binding) = some binding := by
  change NativeExactCodec.read NativeRootInputView.bindingCodec (NativeRootInputView.bindingCodec.encode binding) = some binding
  exact NativeExactCodec.read_encode _ _

theorem readFrames_native (before : List Frame) (requests : Vector Request) (reversed : List Binding) :
    readFrames (reversed.map frame ++ requestFrame requests :: before.reverse) = some ⟨before,requests,reversed.reverse⟩ := by
  induction reversed with
  | nil =>
    simp only [List.map_nil,List.nil_append,readFrames,requestFrame,labels_apart,and_false,ite_false]
    exact readRequest_native before requests
  | cons binding rest ih =>
    simp only [List.map_cons,List.cons_append,readFrames,frame,and_self,ite_true,binding_read_native,Option.bind_some,ih,Option.map_some,List.reverse_cons]

theorem readRequest_sound (head : Frame) (rest : List Frame) (view : View)
    (parsed : readRequest head rest = some view) : head::rest = view.frames.reverse := by
  obtain ⟨requests,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  split at parsed
  next same =>
    obtain rfl := Option.some.inj parsed
    simp only [View.frames,List.map_nil,List.append_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.reverse_reverse]
    rw [same]
  next => contradiction

theorem readFrames_sound (frames : List Frame) (view : View) (parsed : readFrames frames = some view) : frames = view.frames.reverse := by
  induction frames generalizing view with
  | nil => contradiction
  | cons head rest ih =>
    unfold readFrames at parsed
    split at parsed
    next canonical =>
      obtain ⟨binding,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
      split at parsed
      next same =>
        obtain ⟨previous,prior,returned⟩ := Option.map_eq_some_iff.mp parsed
        subst view
        have older := ih previous prior
        simp only [View.frames,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
        rw [same,older]
        simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
      next => contradiction
    next other => exact readRequest_sound head rest view parsed

theorem parse_native (view : View) (valid : ∀ entry ∈ view.frames, TranscriptFrame.Valid entry)
    (count : view.bindings.length = view.requests.val.length) : parse (encodeMany view.frames) = some view := by
  rw [parse,TranscriptFrame.decodeAll_encodeMany _ valid,Option.bind_some]
  have reversed : view.frames.reverse = view.bindings.reverse.map frame ++ requestFrame view.requests :: view.before.reverse := by
    simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.map_reverse,List.cons_append]
  rw [reversed,readFrames_native]
  simp only [List.reverse_reverse,Option.bind_some,count,ite_true]

theorem parse_sound (input : Input) (view : View) (parsed : parse input = some view) :
    input = encodeMany view.frames ∧ (∀ entry ∈ view.frames, TranscriptFrame.Valid entry) ∧
      view.bindings.length = view.requests.val.length := by
  obtain ⟨candidate,prior,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  split at parsed
  next count =>
    obtain rfl := Option.some.inj parsed
    obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp prior
    have same := congrArg List.reverse (readFrames_sound frames.reverse candidate read)
    simp only [List.reverse_reverse] at same
    obtain ⟨valid,encoded⟩ := TranscriptFrame.decodeAll_sound input frames decoded
    rw [same] at valid encoded
    exact ⟨encoded,valid,count⟩
  next => contradiction

end FormalProof4FHE.HasteBoots.ParentBindingsView
