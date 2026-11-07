module
public import FormalProof4FHE.HasteBoots.NativeParentInputView
@[expose] public section

/-! Executable structural parent views. Compatibility checks only the 64
already observed seed bytes; it neither enumerates field elements nor requires
a complete seed. All compatible parents are retained by the ledger. -/
namespace FormalProof4FHE.HasteBoots.ExecutableParentInputView
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open TranscriptFrame (Frame)

def frameHelper (frame : Frame) : Option Digest :=
  if frame.kind = 1 ∧ frame.label = NativeCanonicalLookupWire.label then
    (NativeExactCodec.read NativeRootInputView.bindingCodec frame.message).map (fun binding => binding.helper)
  else none

def helperRoots (frame : Frame) : Option (List Digest) :=
  if frame.kind = 1 ∧ frame.label = NativeLookupEquality.rootsLabel then
    (NativeExactCodec.read (NativePrefixCodec.vector NativeByteCodec.digest) frame.message).map (fun roots => roots.val)
  else none

def compatible (cache : NativeShakeCache.Cache) (input : Input) (quote : Digest) : Bool :=
  (List.finRange 64).all (fun position => match cache (input,position.val) with
    | none => true
    | some value => decide (value = quote position))

theorem compatible_iff (cache : NativeShakeCache.Cache) (input : Input) (quote : Digest) :
    compatible cache input quote = true ↔ NativeParentInputView.compatible cache input quote := by
  simp only [compatible,List.all_eq_true]
  constructor
  · intro agrees position value known
    have here := agrees position (List.mem_finRange position)
    simpa only [known,decide_eq_true_eq] using here
  · intro agrees position _
    cases known : cache (input,position.val) with
    | none => rfl
    | some value => exact decide_eq_true (agrees position value known)

def seedFrames (frames : List Frame) : Bool :=
  match frames.reverse with
  | request :: fork :: _ => decide (request.kind = 2 ∧ request.label = NativeTranscript.utf8 "classical child seed" ∧
      request.message = TranscriptFrame.littleEndian 8 64 ∧ fork.kind = 6)
  | _ => false

theorem seedFrames_iff (frames : List Frame) : seedFrames frames = true ↔ NativeParentInputView.isSeedFrames frames := by
  unfold seedFrames NativeParentInputView.isSeedFrames
  split <;> simp_all

def parseParent (input : Input) : Option (List Frame) :=
  (TranscriptFrame.decodeAll input).bind (fun frames => if seedFrames frames then some frames else none)

theorem frameHelper_eq : frameHelper = NativeParentInputView.frameHelper := by
  funext frame
  unfold frameHelper NativeParentInputView.frameHelper
  rfl

theorem helperRoots_eq : helperRoots = NativeParentInputView.helperRoots := by
  funext frame
  unfold helperRoots NativeParentInputView.helperRoots
  rfl

theorem parseParent_eq : parseParent = NativeParentInputView.parseParent := by
  funext input
  unfold parseParent NativeParentInputView.parseParent
  congr 1
  funext frames
  by_cases yes : NativeParentInputView.isSeedFrames frames
  · have accepted := (seedFrames_iff frames).mpr yes
    simp only [accepted,ite_true,ite_eq_left yes]
  · have rejected : seedFrames frames ≠ true := (seedFrames_iff frames).not.mpr yes
    simp only [ite_eq_right rejected,ite_eq_right yes]
end FormalProof4FHE.HasteBoots.ExecutableParentInputView
