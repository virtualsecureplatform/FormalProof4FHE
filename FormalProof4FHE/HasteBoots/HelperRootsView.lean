module
public import FormalProof4FHE.HasteBoots.NativeLookupEquality
public import FormalProof4FHE.HasteBoots.NativeExactCodec
public import FormalProof4FHE.HasteBoots.SingleOpeningExposure
import all Init.Data.String.Defs
@[expose] public section

/-! Strict recovery of the most recent helper-roots frame in complete framed
bytes. A malformed final roots frame is rejected without fallback. Original
root order and repetitions are retained by the exact vector codec. -/
namespace FormalProof4FHE.HasteBoots.HelperRootsView
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativePrefixCodec (Vector)
open TranscriptFrame (Frame encodeMany)

def tagged (frame : Frame) : Prop := frame.kind = 1 ∧ frame.label = NativeLookupEquality.rootsLabel
instance (frame : Frame) : Decidable (tagged frame) := inferInstanceAs (Decidable (_ ∧ _))
def Clean (frame : Frame) : Prop := ¬tagged frame

def codec := NativePrefixCodec.vector NativeByteCodec.digest
def rootFrame (roots : Vector Digest) : Frame := ⟨1,NativeLookupEquality.rootsLabel,codec.encode roots⟩

def readFrames : List Frame → Option (Vector Digest)
  | [] => none
  | frame :: rest => if tagged frame then NativeExactCodec.read codec frame.message else readFrames rest

def parse (input : Input) : Option (Vector Digest) :=
  (TranscriptFrame.decodeAll input).bind (fun frames => readFrames frames.reverse)

theorem read_native (roots : Vector Digest) (before : List Frame) : readFrames (rootFrame roots :: before) = some roots := by
  simp only [readFrames,tagged,rootFrame,and_self,ite_true,NativeExactCodec.read_encode]

theorem read_clean (frames : List Frame) (clean : ∀ frame ∈ frames, Clean frame) (before : List Frame) :
    readFrames (frames ++ before) = readFrames before := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
    rw [List.cons_append,readFrames,ite_eq_right (clean frame List.mem_cons_self)]
    exact ih (fun entry member => clean entry (List.mem_cons_of_mem _ member))

theorem parse_native (before after : List Frame) (roots : Vector Digest)
    (valid : ∀ frame ∈ before ++ rootFrame roots :: after, TranscriptFrame.Valid frame)
    (clean : ∀ frame ∈ after, Clean frame) :
    parse (encodeMany (before ++ rootFrame roots :: after)) = some roots := by
  rw [parse,TranscriptFrame.decodeAll_encodeMany _ valid,Option.bind_some,List.reverse_append,List.reverse_cons]
  rw [List.append_assoc,read_clean after.reverse (fun frame member => clean frame (List.mem_reverse.mp member))]
  exact read_native roots before.reverse


theorem read_sound (frames : List Frame) (roots : Vector Digest) (parsed : readFrames frames = some roots) :
    ∃ after before, frames = after ++ rootFrame roots :: before ∧ ∀ frame ∈ after, Clean frame := by
  induction frames with
  | nil => contradiction
  | cons frame rest ih =>
    unfold readFrames at parsed
    split at parsed
    next tag =>
      have payload := NativeExactCodec.read_sound codec frame.message roots parsed
      have same : frame = rootFrame roots := by
        cases frame with
        | mk kind label message =>
          obtain ⟨rfl,rfl⟩ := tag
          change codec.encode roots = message at payload
          rw [← payload]
          rfl
      exact ⟨[],rest,by rw [same]; rfl,by intro frame member; cases member⟩
    next clean =>
      obtain ⟨after,before,same,valid⟩ := ih parsed
      refine ⟨frame::after,before,by rw [same]; rfl,?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | tail
      · exact clean
      · exact valid entry tail

theorem parse_sound (input : Input) (roots : Vector Digest) (parsed : parse input = some roots) :
    ∃ before after, input = encodeMany (before ++ rootFrame roots :: after) ∧
      (∀ frame ∈ before ++ rootFrame roots :: after, TranscriptFrame.Valid frame) ∧ ∀ frame ∈ after, Clean frame := by
  obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨after,before,same,clean⟩ := read_sound frames.reverse roots read
  have actual := congrArg List.reverse same
  simp only [List.reverse_reverse,List.reverse_append,List.reverse_cons] at actual
  have arranged : frames = before.reverse ++ rootFrame roots :: after.reverse := by
    simpa only [List.append_assoc,List.singleton_append] using actual
  obtain ⟨valid,bytes⟩ := TranscriptFrame.decodeAll_sound input frames decoded
  rw [arranged] at valid bytes
  exact ⟨before.reverse,after.reverse,bytes,valid,fun frame member => clean frame (List.mem_reverse.mp member)⟩

theorem parse_bound (state : NativeTranscript.Transcript) (frames : List Frame)
    (bytes : state.input = encodeMany frames) (valid : ∀ frame ∈ frames, TranscriptFrame.Valid frame)
    (roots : Vector Digest) (fits : (NativeRootMessage.encode roots.val roots.property).length < TranscriptFrame.lengthLimit) :
    parse (NativeLookupEquality.bindRoots state roots.val roots.property).input = some roots := by
  have framed : (NativeLookupEquality.bindRoots state roots.val roots.property).input = encodeMany (frames ++ [rootFrame roots]) := by
    rw [NativeLookupEquality.bindRoots_input,bytes,SingleOpeningExposure.encodeMany_append]
    simp only [TranscriptFrame.encodeMany,List.append_nil]
    rfl
  rw [framed]
  apply parse_native frames [] roots
  · intro frame member
    rcases List.mem_append.mp member with old | added
    · exact valid frame old
    · obtain rfl := List.mem_singleton.mp added
      exact ⟨by change NativeLookupEquality.rootsLabel.length < _; unfold NativeLookupEquality.rootsLabel NativeTranscript.utf8; decide +kernel,fits⟩
  · intro frame member
    cases member

end FormalProof4FHE.HasteBoots.HelperRootsView
