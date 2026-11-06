module
public import FormalProof4FHE.HasteBoots.NativeRootMessage
public import FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw
@[expose] public section

/-! Fail-closed structural recovery of a complete native index request from
its pending SHAKE input. Both suffix frames and fixed-width integers are
checked. The view carries no oracle values or future accepted work. This is
an analysis input view, not refinement of the Rust proof deserializer. -/
namespace FormalProof4FHE.HasteBoots.NativeIndexInputView
open InputIndexedOracle (Input)
open NativeTranscript (Transcript utf8)
open NativeUsizeMessage (Usize)
open TranscriptFrame (Frame encodeMany littleEndian)

/-- Fixed-width native u64, with no variable-integer aliases or trailing bytes. -/
def readU64 (input : Input) : Option Usize :=
  if size : input.length = 8 then
    some ⟨TranscriptFrame.fromLittleEndian input,by
      have bound := TranscriptFrame.fromLittleEndian_lt input
      rw [size] at bound
      exact bound⟩
  else none

theorem readU64_encode (value : Usize) : readU64 (littleEndian 8 value.val) = some value := by
  unfold readU64
  rw [dite_eq_left (TranscriptFrame.littleEndian_length 8 value.val)]
  congr 1
  apply Fin.ext
  exact TranscriptFrame.fromLittleEndian_littleEndian 8 value.val value.isLt

theorem readU64_sound (input : Input) (value : Usize) (parsed : readU64 input = some value) :
    input = littleEndian 8 value.val := by
  unfold readU64 at parsed
  split at parsed
  next size =>
    have equal := congrArg Fin.val (Option.some.inj parsed)
    rw [← equal,← size]
    exact (TranscriptFrame.littleEndian_fromLittleEndian input).symm
  next => contradiction

structure View where
  before : List Frame
  label : Input
  domain : Usize
  count : Usize

def View.request (view : View) (profile : NativeRootMessage.Digest) : NativePrequeryIndexLaw.Request :=
  ⟨⟨encodeMany view.before,profile⟩,view.label,view.domain,view.count⟩

def View.frames (view : View) : List Frame := view.before ++
  [⟨1,utf8 "index domain",littleEndian 8 view.domain.val⟩,
   ⟨2,view.label,littleEndian 8 (view.count.val*8)⟩]

/-- Read the last two frames, leaving the complete preceding transcript. -/
def readFrames : List Frame → Option View
  | request :: domain :: rest =>
    if request.kind = 2 ∧ domain.kind = 1 ∧ domain.label = utf8 "index domain" then do
      let bound ← readU64 domain.message
      let byteCount ← readU64 request.message
      if byteCount.val % 8 = 0 then
        let count : Usize := ⟨byteCount.val/8,lt_of_le_of_lt (Nat.div_le_self _ _) byteCount.isLt⟩
        if NativeIndexRequest.check bound count then some ⟨rest.reverse,request.label,bound,count⟩ else none
      else none
    else none
  | _ => none

def parse (input : Input) : Option View := (TranscriptFrame.decodeAll input).bind (fun frames => readFrames frames.reverse)

theorem readFrames_native (before : List Frame) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true) :
    readFrames (View.frames ⟨before,label,domain,count⟩).reverse = some ⟨before,label,domain,count⟩ := by
  have bounded := (NativeIndexRequest.check_iff domain count).mp valid
  let byteCount : Usize := ⟨count.val*8,bounded.2⟩
  have number : readU64 (littleEndian 8 (count.val*8)) = some byteCount := readU64_encode byteCount
  simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.cons_append,readFrames,and_self,ite_true,readU64_encode,number,Option.bind_eq_bind,Option.bind_some]
  have countEq : (⟨byteCount.val/8,lt_of_le_of_lt (Nat.div_le_self _ _) byteCount.isLt⟩ : Usize) = count := by
    apply Fin.ext
    simp [byteCount]
  have divisible : byteCount.val % 8 = 0 := by simp [byteCount]
  simp only [divisible,ite_true,List.reverse_reverse]
  rw [countEq,valid]
  rfl

/-- Every accepted view reconstructs the two complete canonical suffix frames. -/
theorem readFrames_sound (frames : List Frame) (view : View) (parsed : readFrames frames = some view) :
    frames = view.frames.reverse ∧ NativeIndexRequest.check view.domain view.count = true := by
  cases frames with
  | nil => cases parsed
  | cons request tail =>
    cases tail with
    | nil => cases parsed
    | cons domain rest =>
      simp only [readFrames,Option.bind_eq_bind] at parsed
      split at parsed
      next shape =>
        cases domainRead : readU64 domain.message with
        | none => simp [domainRead] at parsed
        | some bound =>
          cases countRead : readU64 request.message with
          | none => simp [domainRead,countRead] at parsed
          | some byteCount =>
            simp only [domainRead,countRead,Option.bind_some] at parsed
            split at parsed
            next divisible =>
              split at parsed
              next valid =>
                have equal := Option.some.inj parsed
                subst view
                refine ⟨?_,valid⟩
                have bytes := readU64_sound request.message byteCount countRead
                have boundBytes := readU64_sound domain.message bound domainRead
                have countEq : byteCount.val/8*8 = byteCount.val := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero divisible)
                simp only [View.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
                  List.cons_append,List.reverse_reverse]
                apply congrArg₂ List.cons
                · cases request
                  simp only [Frame.mk.injEq] at shape ⊢
                  exact ⟨shape.1,True.intro,by simpa only [countEq] using bytes⟩
                · apply congrArg₂ List.cons
                  · cases domain
                    simp only [Frame.mk.injEq] at shape ⊢
                    exact ⟨shape.2.1,shape.2.2,boundBytes⟩
                  · rfl
              next => contradiction
            next => contradiction
      next => contradiction

private theorem encodeMany_append (first later : List Frame) : encodeMany (first++later) = encodeMany first ++ encodeMany later := by
  induction first with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append,encodeMany,ih,List.append_assoc]

theorem parse_sound (input : Input) (view : View) (parsed : parse input = some view) (profile : NativeRootMessage.Digest) :
    NativePrequeryIndexLaw.requestInput (view.request profile).transcript view.label view.domain view.count = input ∧
      NativeIndexRequest.check view.domain view.count = true := by
  obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp parsed
  have suffix := readFrames_sound frames.reverse view read
  have equal : frames = view.frames := by
    have same := congrArg List.reverse suffix.1
    simpa only [List.reverse_reverse] using same
  have bytes := (TranscriptFrame.decodeAll_sound input frames decoded).2
  rw [equal] at bytes
  refine ⟨?_,suffix.2⟩
  rw [bytes,View.frames,encodeMany_append]
  simp only [NativePrequeryIndexLaw.requestInput,View.request,NativeIndexRequest.prepare,NativeTranscript.appendBytes,
    NativeTranscript.absorb,encodeMany,List.append_nil,List.append_assoc]

/-- Completeness requires the actual parent frames and native label to fit
framing lengths; rejection of malformed or wrapping streams is unconditional. -/
theorem parse_native (before : List Frame) (profile : NativeRootMessage.Digest) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true)
    (framed : ∀ frame ∈ View.frames ⟨before,label,domain,count⟩, TranscriptFrame.Valid frame) :
    parse (NativePrequeryIndexLaw.requestInput ⟨encodeMany before,profile⟩ label domain count) = some ⟨before,label,domain,count⟩ := by
  have input : NativePrequeryIndexLaw.requestInput ⟨encodeMany before,profile⟩ label domain count =
      encodeMany (View.frames ⟨before,label,domain,count⟩) := by
    rw [View.frames,encodeMany_append]
    simp only [NativePrequeryIndexLaw.requestInput,NativeIndexRequest.prepare,NativeTranscript.appendBytes,
      NativeTranscript.absorb,encodeMany,List.append_nil,List.append_assoc]
  rw [input,parse,TranscriptFrame.decodeAll_encodeMany _ framed,Option.bind_some]
  exact readFrames_native before label domain count valid
end FormalProof4FHE.HasteBoots.NativeIndexInputView
