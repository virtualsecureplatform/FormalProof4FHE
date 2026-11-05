module

public import FormalProof4FHE.HasteBoots.NativeExactCodec
public import FormalProof4FHE.HasteBoots.NativeTranscript
public import FormalProof4FHE.HasteBoots.OracleMachineExposure
import all Init.Data.String.Defs
@[expose] public section

/-! Recover the immediate parent seed from the fixed native child-header
slot of a complete raw input. At most one candidate is collected per raw
observation; later frames with the same label do not add candidates. Every
raw observation remains in the underlying log. Root/parent association and
first-exposure registration remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeChildSeedView
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open TranscriptFrame (Frame)

def frameSeed (frame : Frame) : Option Digest :=
  if frame.kind = 1 ∧ frame.label = NativeTranscript.utf8 "parent seed" then
    NativeExactCodec.read NativeByteCodec.digest frame.message
  else none

def quote (input : Input) : Option Digest :=
  (TranscriptFrame.decodeAll input).bind (fun frames => frames[5]?.bind frameSeed)

theorem frameSeed_native (seed : Digest) :
    frameSeed ⟨1,NativeTranscript.utf8 "parent seed",List.ofFn seed⟩ = some seed := by
  simp only [frameSeed,and_self,ite_true]
  simpa only [NativeByteCodec.digest_encode] using NativeExactCodec.read_encode NativeByteCodec.digest seed


def seededFrames (profile : Digest) (label context : Input) (seed : Digest) : List Frame :=
  [⟨0,NativeTranscript.utf8 "protocol",NativeTranscript.utf8 "HasteBoots framed SHAKE256 v1"⟩,
   ⟨0,NativeTranscript.utf8 "application",NativeTranscript.utf8 "HasteBoots framed SHAKE256 child v1"⟩,
   ⟨0,NativeTranscript.utf8 "trusted profile",List.ofFn profile⟩,
   ⟨1,NativeTranscript.utf8 "child label",label⟩,
   ⟨1,NativeTranscript.utf8 "child context",context⟩,
   ⟨1,NativeTranscript.utf8 "parent seed",List.ofFn seed⟩]

theorem quote_complete (profile : Digest) (label context : Input) (seed : Digest) (suffix : List Frame)
    (valid : ∀ frame ∈ seededFrames profile label context seed ++ suffix, TranscriptFrame.Valid frame) :
    quote (TranscriptFrame.encodeMany (seededFrames profile label context seed ++ suffix)) = some seed := by
  rw [quote,TranscriptFrame.decodeAll_encodeMany _ valid,Option.bind_some]
  simp only [seededFrames,List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some]
  exact frameSeed_native seed

def candidate : NativeTranscript.Observation → Option Digest
  | .start _ => none
  | .output input _ values => if values = [] then none else quote input
  | .hash input _ => quote input

def guesses (log : List NativeTranscript.Observation) : Finset Digest := (log.filterMap candidate).toFinset

theorem guesses_card_le (log : List NativeTranscript.Observation) : (guesses log).card ≤ log.length := by
  exact (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem guesses_append (first later : List NativeTranscript.Observation) :
    guesses (first++later) = guesses first ∪ guesses later := by
  simp [guesses,List.filterMap_append,List.toFinset_append]


theorem forkChild_input (world : InputIndexedOracle.World) (parent : NativeTranscript.Transcript)
    (label context : Input) :
    (NativeTranscript.forkChild world parent label context).run.1.2.input =
      TranscriptFrame.encodeMany (seededFrames parent.profile label context
        (InputIndexedOracle.block world (NativeTranscript.requestInput
          (NativeTranscript.absorb parent 6 label context) (NativeTranscript.utf8 "classical child seed") 64) 0 64)) := by
  change (((NativeTranscript.new (NativeTranscript.utf8 "HasteBoots framed SHAKE256 child v1") parent.profile).input ++
    TranscriptFrame.encode ⟨1,NativeTranscript.utf8 "child label",label⟩) ++
    TranscriptFrame.encode ⟨1,NativeTranscript.utf8 "child context",context⟩) ++
    TranscriptFrame.encode ⟨1,NativeTranscript.utf8 "parent seed",_⟩ = _
  simp only [seededFrames,NativeTranscript.new,NativeTranscript.requestInput,NativeTranscript.absorb,TranscriptFrame.encodeMany,
    List.nil_append,List.append_nil,List.append_assoc,InputIndexedOracle.bytes]


theorem seededFrames_valid (profile : Digest) (label context : Input) (seed : Digest)
    (labelFits : label.length < TranscriptFrame.lengthLimit)
    (contextFits : context.length < TranscriptFrame.lengthLimit) :
    ∀ frame ∈ seededFrames profile label context seed, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [seededFrames,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> dsimp only <;> first
    | exact labelFits
    | exact contextFits
    | simpa only [List.length_ofFn] using (by decide +kernel : 64 < TranscriptFrame.lengthLimit)
    | decide +kernel

theorem quote_forkChild (world : InputIndexedOracle.World) (parent : NativeTranscript.Transcript)
    (label context : Input) (labelFits : label.length < TranscriptFrame.lengthLimit)
    (contextFits : context.length < TranscriptFrame.lengthLimit) :
    NativeChildSeedView.quote (NativeTranscript.forkChild world parent label context).run.1.2.input =
      some (InputIndexedOracle.block world (NativeTranscript.requestInput
        (NativeTranscript.absorb parent 6 label context) (NativeTranscript.utf8 "classical child seed") 64) 0 64) := by
  rw [forkChild_input]
  have complete := quote_complete parent.profile label context
    (InputIndexedOracle.block world (NativeTranscript.requestInput
      (NativeTranscript.absorb parent 6 label context) (NativeTranscript.utf8 "classical child seed") 64) 0 64) []
      (by simpa only [List.append_nil] using seededFrames_valid parent.profile label context _ labelFits contextFits)
  simpa only [List.append_nil] using complete



/-- Recognition is tied to the exact canonical parent-seed frame. -/
theorem frameSeed_sound (frame : Frame) (seed : Digest) (parsed : frameSeed frame = some seed) :
    frame.kind = 1 ∧ frame.label = NativeTranscript.utf8 "parent seed" ∧ frame.message = List.ofFn seed := by
  unfold frameSeed at parsed
  split at parsed
  · rename_i accepted
    refine ⟨accepted.1,accepted.2,?_⟩
    simpa only [NativeByteCodec.digest_encode] using
      (NativeExactCodec.read_sound NativeByteCodec.digest frame.message seed parsed).symm
  · simp at parsed

/-- A recognized quote comes from slot5 of the entire decoded input, not an arbitrary later label. -/
theorem quote_sound (input : Input) (seed : Digest) (parsed : quote input = some seed) :
    ∃ frames frame, TranscriptFrame.decodeAll input = some frames ∧ frames[5]? = some frame ∧
      frame.kind = 1 ∧ frame.label = NativeTranscript.utf8 "parent seed" ∧ frame.message = List.ofFn seed := by
  unfold quote at parsed
  cases decoded : TranscriptFrame.decodeAll input with
  | none => simp [decoded] at parsed
  | some frames =>
    simp only [decoded,Option.bind_some] at parsed
    cases selected : frames[5]? with
    | none => simp [selected] at parsed
    | some frame =>
      simp only [selected,Option.bind_some] at parsed
      exact ⟨frames,frame,rfl,selected,frameSeed_sound frame seed parsed⟩

/-- Unframed consumed-byte receipt calls remain raw observations, not child-header candidates. -/
theorem quote_receipt (consumed : Input) :
    NativeChildSeedView.quote (NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ consumed) = none := by
  simp [quote,NativeTranscript.receipt_decode_rejected]

private theorem encodeMany_append (first later : List Frame) :
    TranscriptFrame.encodeMany (first++later) =
      TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany later := by
  induction first with
  | nil => simp [TranscriptFrame.encodeMany]
  | cons entry rest ih => simp [TranscriptFrame.encodeMany,ih,List.append_assoc]

/-- A constructed native child header followed by valid absorbed frames. -/
def HasHeader (state : NativeTranscript.Transcript) (profile : Digest) (label context : Input) (seed : Digest) : Prop :=
  ∃ suffix : List Frame, (∀ frame ∈ seededFrames profile label context seed ++ suffix, TranscriptFrame.Valid frame) ∧
    state.input = TranscriptFrame.encodeMany (seededFrames profile label context seed ++ suffix)

theorem HasHeader.quote {state : NativeTranscript.Transcript} {profile : Digest} {label context : Input} {seed : Digest}
    (header : HasHeader state profile label context seed) : quote state.input = some seed := by
  obtain ⟨suffix,valid,bytes⟩ := header
  rw [bytes]
  exact quote_complete profile label context seed suffix valid

theorem HasHeader.absorb {state : NativeTranscript.Transcript} {profile : Digest} {label context : Input} {seed : Digest}
    (header : HasHeader state profile label context seed) (kind : Fin 9) (nextLabel message : Input)
    (valid : TranscriptFrame.Valid ⟨kind,nextLabel,message⟩) :
    HasHeader (NativeTranscript.absorb state kind nextLabel message) profile label context seed := by
  obtain ⟨suffix,oldValid,bytes⟩ := header
  refine ⟨suffix++[⟨kind,nextLabel,message⟩],?_,?_⟩
  · intro frame member
    have normalized : frame ∈ (seededFrames profile label context seed ++ suffix) ++ [⟨kind,nextLabel,message⟩] := by
      simpa only [List.append_assoc] using member
    rcases List.mem_append.mp normalized with old | added
    · exact oldValid frame old
    · obtain rfl := List.mem_singleton.mp added
      exact valid
  · change state.input ++ TranscriptFrame.encode ⟨kind,nextLabel,message⟩ = _
    rw [bytes]
    simp only [encodeMany_append,TranscriptFrame.encodeMany,List.append_nil,List.append_assoc]

theorem forkChild_header (world : InputIndexedOracle.World) (parent : NativeTranscript.Transcript)
    (label context : Input) (labelFits : label.length < TranscriptFrame.lengthLimit)
    (contextFits : context.length < TranscriptFrame.lengthLimit) :
    HasHeader (NativeTranscript.forkChild world parent label context).run.1.2 parent.profile label context
      (InputIndexedOracle.block world (NativeTranscript.requestInput (NativeTranscript.absorb parent 6 label context)
        (NativeTranscript.utf8 "classical child seed") 64) 0 64) := by
  refine ⟨[],?_,?_⟩
  · simpa only [List.append_nil] using seededFrames_valid parent.profile label context _ labelFits contextFits
  · simpa only [List.append_nil] using forkChild_input world parent label context



/-- Byte challenges retain the immediate parent seed under their added request frame. -/
theorem HasHeader.request {state : NativeTranscript.Transcript} {profile : Digest} {label context : Input} {seed : Digest}
    (header : HasHeader state profile label context seed) (nextLabel : Input) (count : ℕ)
    (labelFits : nextLabel.length < TranscriptFrame.lengthLimit) :
    NativeChildSeedView.quote (NativeTranscript.requestInput state nextLabel count) = some seed := by
  change NativeChildSeedView.quote (NativeTranscript.absorb state 2 nextLabel (TranscriptFrame.littleEndian 8 count)).input = _
  apply HasHeader.quote
  apply header.absorb
  exact ⟨labelFits,by simpa only [TranscriptFrame.littleEndian_length] using (by decide +kernel : 8 < TranscriptFrame.lengthLimit)⟩

/-- Field-reader inputs retain the same child header, including zero-length requests. -/
theorem HasHeader.beginField {state : NativeTranscript.Transcript} {profile : Digest} {label context : Input} {seed : Digest}
    (header : HasHeader state profile label context seed) (nextLabel : Input) (modulus count : ℕ)
    (labelFits : nextLabel.length < TranscriptFrame.lengthLimit) :
    NativeChildSeedView.quote (NativeTranscript.beginField state nextLabel modulus count).run.1.pending.input = some seed := by
  change NativeChildSeedView.quote (NativeTranscript.absorb state 4 nextLabel
    (TranscriptFrame.littleEndian 16 modulus ++ TranscriptFrame.littleEndian 8 count)).input = _
  apply HasHeader.quote
  apply header.absorb
  exact ⟨labelFits,by simpa only [List.length_append,TranscriptFrame.littleEndian_length] using
    (by decide +kernel : 16+8 < TranscriptFrame.lengthLimit)⟩

noncomputable section
open MeasureTheory ProbabilityTheory

theorem orphan_probability {S A : Type} (step : S → OracleMachine.Command S A) (fuel index : ℕ)
    (state : S) (world : InputIndexedOracle.World) (input : Input)
    (first : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel state) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some index) :
    (InputIndexedOracle.law[|{other | (OracleProgram.run (OracleMachine.take step index state) other).run =
      (OracleProgram.run (OracleMachine.take step index state) world).run}])
      {other | InputIndexedOracle.block other input 0 64 ∈
        guesses (OracleProgram.run (OracleMachine.take step index state) other).run.2} =
      ((guesses (OracleProgram.run (OracleMachine.take step index state) world).run.2).card : ENNReal)/(2 : ENNReal)^512 := by
  calc _ = (InputIndexedOracle.law[|{other | (OracleProgram.run (OracleMachine.take step index state) other).run =
      (OracleProgram.run (OracleMachine.take step index state) world).run}]) {other | InputIndexedOracle.block other input 0 64 ∈
        guesses (OracleProgram.run (OracleMachine.take step index state) world).run.2} := by
        apply NativeShakeProjection.conditional_event_congr (OracleProgram.run_replay _) world
        intro other same
        rw [congrArg Prod.snd same]
       _ = _ := OracleMachineExposure.pre_exposure_targets step fuel index state world input _ first

end

end FormalProof4FHE.HasteBoots.NativeChildSeedView
