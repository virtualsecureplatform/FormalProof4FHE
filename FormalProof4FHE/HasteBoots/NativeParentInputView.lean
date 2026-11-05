module

public import FormalProof4FHE.HasteBoots.NativeRootInputView
public import FormalProof4FHE.HasteBoots.NativeChildSeedView
public import FormalProof4FHE.HasteBoots.NativeLookupEquality
@[expose] public section

/-! Native helper contexts, helper-root vectors and parent-seed input views.
Cache compatibility uses only previously observed bytes and includes the
actual seed after arbitrary partial reads. These structural views do not
authenticate ownership or trusted parameter identity. -/
namespace FormalProof4FHE.HasteBoots.NativeParentInputView
open InputIndexedOracle (Input Byte)
open NativeRootMessage (Digest)
open TranscriptFrame (Frame)
open scoped Classical
noncomputable section

def frameHelper (frame : Frame) : Option Digest :=
  if frame.kind = 1 ∧ frame.label = NativeCanonicalLookupWire.label then
    (NativeExactCodec.read NativeRootInputView.bindingCodec frame.message).map (fun binding => binding.helper)
  else none

def helperRoots (frame : Frame) : Option (List Digest) :=
  if frame.kind = 1 ∧ frame.label = NativeLookupEquality.rootsLabel then
    (NativeExactCodec.read (NativePrefixCodec.vector NativeByteCodec.digest) frame.message).map (fun roots => roots.val)
  else none

theorem frameHelper_complete (binding : NativeCanonicalLookupWire.Binding) :
    frameHelper ⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩ = some binding.helper := by
  simp only [frameHelper,and_self,ite_true]
  change (NativeExactCodec.read NativeRootInputView.bindingCodec (NativeRootInputView.bindingCodec.encode binding)).map _ = _
  rw [NativeExactCodec.read_encode]
  rfl

theorem helperRoots_complete (roots : List Digest) (fits : roots.length < 2^64) :
    helperRoots ⟨1,NativeLookupEquality.rootsLabel,NativeRootMessage.encode roots fits⟩ = some roots := by
  simp only [helperRoots,and_self,ite_true]
  change (NativeExactCodec.read (NativePrefixCodec.vector NativeByteCodec.digest)
    ((NativePrefixCodec.vector NativeByteCodec.digest).encode ⟨roots,fits⟩)).map _ = _
  rw [NativeExactCodec.read_encode]
  rfl

def compatible (cache : NativeShakeCache.Cache) (input : Input) (quote : Digest) : Prop :=
  ∀ position : Fin 64, ∀ value, cache (input,position.val) = some value → value = quote position

theorem compatible_empty (input : Input) (quote : Digest) : compatible NativeShakeCache.empty input quote := by
  intro position value known
  simp [NativeShakeCache.empty] at known

theorem compatible_observed (log : List NativeTranscript.Observation) (world : InputIndexedOracle.World) (input : Input) :
    compatible (NativeShakeKernel.observed log world) input (InputIndexedOracle.block world input 0 64) := by
  intro position value known
  unfold NativeShakeKernel.observed at known
  split at known
  · have same := Option.some.inj known
    simpa [InputIndexedOracle.block,InputIndexedOracle.shake] using same.symm
  · simp at known


def isSeedFrames (frames : List Frame) : Prop :=
  match frames.reverse with
  | request :: fork :: _ => request.kind = 2 ∧ request.label = NativeTranscript.utf8 "classical child seed" ∧
      request.message = TranscriptFrame.littleEndian 8 64 ∧ fork.kind = 6
  | _ => False

theorem isSeedFrames_native (before : List Frame) (label context : Input) :
    isSeedFrames (before++[⟨6,label,context⟩,
      ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩]) := by
  simp [isSeedFrames,List.reverse_append]

def parseParent (input : Input) : Option (List Frame) :=
  (TranscriptFrame.decodeAll input).bind (fun frames => if isSeedFrames frames then some frames else none)

theorem parseParent_complete (before : List Frame) (label context : Input)
    (valid : ∀ frame ∈ before++[⟨6,label,context⟩,
      ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩], TranscriptFrame.Valid frame) :
    parseParent (TranscriptFrame.encodeMany (before++[⟨6,label,context⟩,
      ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩])) =
    some (before++[⟨6,label,context⟩,
      ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩]) := by
  rw [parseParent,TranscriptFrame.decodeAll_encodeMany _ valid,Option.bind_some]
  exact ite_eq_left (isSeedFrames_native before label context)

private theorem encodeMany_append (first later : List Frame) :
    TranscriptFrame.encodeMany (first++later) =
      TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany later := by
  induction first with
  | nil => simp [TranscriptFrame.encodeMany]
  | cons frame rest ih => simp [TranscriptFrame.encodeMany,ih,List.append_assoc]

theorem parent_request_frames (state : NativeTranscript.Transcript) (before : List Frame)
    (bytes : state.input = TranscriptFrame.encodeMany before) (label context : Input) :
    NativeTranscript.requestInput (NativeTranscript.absorb state 6 label context)
      (NativeTranscript.utf8 "classical child seed") 64 =
    TranscriptFrame.encodeMany (before++[⟨6,label,context⟩,
      ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩]) := by
  simp only [NativeTranscript.requestInput,NativeTranscript.absorb,bytes,encodeMany_append,
    TranscriptFrame.encodeMany,List.append_nil,List.append_assoc]

theorem parseParent_request (state : NativeTranscript.Transcript) (before : List Frame)
    (bytes : state.input = TranscriptFrame.encodeMany before) (label context : Input)
    (valid : ∀ frame ∈ before++[⟨6,label,context⟩,
      ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩], TranscriptFrame.Valid frame) :
    parseParent (NativeTranscript.requestInput (NativeTranscript.absorb state 6 label context)
      (NativeTranscript.utf8 "classical child seed") 64) =
    some (before++[⟨6,label,context⟩,
      ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩]) := by
  rw [parent_request_frames state before bytes]
  exact parseParent_complete before label context valid

end
end FormalProof4FHE.HasteBoots.NativeParentInputView
