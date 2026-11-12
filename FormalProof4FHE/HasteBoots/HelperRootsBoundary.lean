module
public import FormalProof4FHE.HasteBoots.EqualityFamilyCandidate
import all Init.Data.String.Defs
@[expose] public section

/-! Strict latest-roots parsing retains the transcript before the original
binder. Clean equality suffixes preserve this boundary; malformed last binders
are rejected rather than replaced by an earlier roots frame. -/
namespace FormalProof4FHE.HasteBoots.HelperRootsBoundary
open TranscriptFrame (Frame encodeMany)
open NativePrefixCodec (Vector)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)
open HelperRootsView (tagged Clean rootFrame codec)
noncomputable section

def readFrames : List Frame → Option (Vector Digest × List Frame)
  | [] => none
  | frame :: rest => if tagged frame then
      (NativeExactCodec.read codec frame.message).map (fun roots => (roots,rest.reverse)) else readFrames rest

def parse (input : Input) : Option (Vector Digest × List Frame) :=
  (TranscriptFrame.decodeAll input).bind (fun frames => readFrames frames.reverse)

theorem read_clean (frames : List Frame) (clean : ∀ frame ∈ frames, Clean frame) (before : List Frame) :
    readFrames (frames++before) = readFrames before := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
    rw [List.cons_append,readFrames,ite_eq_right (clean frame List.mem_cons_self)]
    exact ih (fun entry member => clean entry (List.mem_cons_of_mem _ member))

theorem native (before after : List Frame) (roots : Vector Digest)
    (valid : ∀ frame ∈ before ++ rootFrame roots :: after, TranscriptFrame.Valid frame)
    (clean : ∀ frame ∈ after, Clean frame) :
    parse (encodeMany (before ++ rootFrame roots :: after)) = some (roots,before) := by
  rw [parse,TranscriptFrame.decodeAll_encodeMany _ valid,Option.bind_some,List.reverse_append,List.reverse_cons]
  rw [List.append_assoc,read_clean after.reverse (fun frame member => clean frame (List.mem_reverse.mp member))]
  simp only [List.singleton_append,readFrames,tagged,rootFrame,and_self,ite_true,NativeExactCodec.read_encode,Option.map_some,List.reverse_reverse]

theorem bound (state : NativeTranscript.Transcript) (frames : List Frame)
    (bytes : state.input = encodeMany frames) (valid : ∀ frame ∈ frames, TranscriptFrame.Valid frame)
    (roots : Vector Digest) (fits : (NativeRootMessage.encode roots.val roots.property).length < TranscriptFrame.lengthLimit) :
    parse (NativeLookupEquality.bindRoots state roots.val roots.property).input = some (roots,frames) := by
  have framed : (NativeLookupEquality.bindRoots state roots.val roots.property).input = encodeMany (frames ++ [rootFrame roots]) := by
    rw [NativeLookupEquality.bindRoots_input,bytes,SingleOpeningExposure.encodeMany_append]
    simp only [encodeMany,List.append_nil]
    rfl
  rw [framed]
  apply native frames [] roots
  · intro frame member
    rcases List.mem_append.mp member with old | added
    · exact valid frame old
    · obtain rfl := List.mem_singleton.mp added
      exact ⟨by change NativeLookupEquality.rootsLabel.length < _; decide +kernel,fits⟩
  · simp

theorem preserved {before after : NativeTranscript.Transcript} (extension : RootSafeExtension.Extends before after)
    (frames : List Frame) (decoded : TranscriptFrame.decodeAll before.input = some frames) : parse after.input = parse before.input := by
  obtain ⟨suffix,valid,clean,bytes,_⟩ := extension
  obtain ⟨oldValid,oldBytes⟩ := TranscriptFrame.decodeAll_sound _ _ decoded
  have afterDecoded : TranscriptFrame.decodeAll after.input = some (frames++suffix) := by
    rw [bytes,oldBytes,← SingleOpeningExposure.encodeMany_append]
    apply TranscriptFrame.decodeAll_encodeMany
    intro frame member
    rcases List.mem_append.mp member with old | added
    · exact oldValid frame old
    · exact valid frame added
  simp only [parse,afterDecoded,decoded,Option.bind_some,List.reverse_append]
  exact read_clean suffix.reverse (fun frame member => clean frame (List.mem_reverse.mp member)) frames.reverse

theorem read_sound (frames : List Frame) (roots : Vector Digest) (before : List Frame)
    (parsed : readFrames frames = some (roots,before)) :
    ∃ after, frames = after ++ rootFrame roots :: before.reverse ∧ ∀ frame ∈ after, Clean frame := by
  induction frames with
  | nil => contradiction
  | cons frame rest ih =>
    unfold readFrames at parsed
    split at parsed
    next tag =>
      obtain ⟨selected,decoded,same⟩ := Option.map_eq_some_iff.mp parsed
      have rootEq : selected = roots := congrArg Prod.fst same
      subst selected
      have beforeEq : rest.reverse = before := congrArg Prod.snd same
      have payload := NativeExactCodec.read_sound codec frame.message roots decoded
      have frameEq : frame = rootFrame roots := by
        cases frame with
        | mk kind label message =>
          obtain ⟨rfl,rfl⟩ := tag
          change codec.encode roots = message at payload
          rw [← payload]
          rfl
      refine ⟨[],?_,by simp⟩
      simp only [List.nil_append]
      rw [frameEq,← beforeEq,List.reverse_reverse]
    next clean =>
      obtain ⟨after,same,valid⟩ := ih parsed
      refine ⟨frame::after,by rw [same]; rfl,?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | tail
      · exact clean
      · exact valid entry tail

theorem sound (input : Input) (roots : Vector Digest) (before : List Frame)
    (parsed : parse input = some (roots,before)) :
    ∃ after, input = encodeMany (before ++ rootFrame roots :: after) ∧
      ∀ frame ∈ before ++ rootFrame roots :: after, TranscriptFrame.Valid frame := by
  obtain ⟨frames,decoded,read⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨after,same,_⟩ := read_sound frames.reverse roots before read
  have actual := congrArg List.reverse same
  simp only [List.reverse_reverse,List.reverse_append,List.reverse_cons] at actual
  have arranged : frames = before ++ rootFrame roots :: after.reverse := by
    simpa only [List.append_assoc,List.singleton_append] using actual
  obtain ⟨valid,bytes⟩ := TranscriptFrame.decodeAll_sound input frames decoded
  rw [arranged] at valid bytes
  exact ⟨after.reverse,bytes,valid⟩

end
end FormalProof4FHE.HasteBoots.HelperRootsBoundary
