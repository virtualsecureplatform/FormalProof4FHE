module

public import FormalProof4FHE.HasteBoots.NativeChildSeedView
public import FormalProof4FHE.HasteBoots.TypedFieldVector
public import FormalProof4FHE.HasteBoots.NativeParentLedger
import all Init.Data.String.Defs

@[expose] public section

/-! Native sampler extensions retain valid absorbed frames and profiles.
All candidate retries retain the exact pending transcript and field label;
suspension/resumption and finalization preserve header ancestry and earlier
helper roots. Label and descriptor allocation domains remain explicit.
No receipt entropy, freshness, work, or Rust refinement claim is made. -/
namespace FormalProof4FHE.HasteBoots.NativeTranscriptExtension
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript FieldPhase utf8)
open NativeRootMessage (Digest)
open OracleProgram (run)
noncomputable section

def Extends (before after : Transcript) : Prop :=
  ∃ suffix : List TranscriptFrame.Frame, (∀ frame ∈ suffix, TranscriptFrame.Valid frame) ∧
    after.input = before.input ++ TranscriptFrame.encodeMany suffix ∧ after.profile = before.profile

private theorem encodeMany_append (first later : List TranscriptFrame.Frame) :
    TranscriptFrame.encodeMany (first++later) = TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany later := by
  induction first with
  | nil => simp [TranscriptFrame.encodeMany]
  | cons frame rest ih => simp [TranscriptFrame.encodeMany,ih,List.append_assoc]

theorem Extends.refl (state : Transcript) : Extends state state := ⟨[],by simp,by simp [TranscriptFrame.encodeMany],rfl⟩

theorem Extends.trans {first middle last : Transcript} (earlier : Extends first middle) (later : Extends middle last) :
    Extends first last := by
  obtain ⟨left,leftValid,leftBytes,leftProfile⟩ := earlier
  obtain ⟨right,rightValid,rightBytes,rightProfile⟩ := later
  exact ⟨left++right,by
    intro frame member
    rcases List.mem_append.mp member with old | added
    · exact leftValid frame old
    · exact rightValid frame added,
    by rw [rightBytes,leftBytes,encodeMany_append,List.append_assoc],rightProfile.trans leftProfile⟩

theorem absorb (state : Transcript) (kind : Fin 9) (label message : Input)
    (valid : TranscriptFrame.Valid ⟨kind,label,message⟩) : Extends state (NativeTranscript.absorb state kind label message) :=
  ⟨[⟨kind,label,message⟩],by simpa using valid,by simp [NativeTranscript.absorb,TranscriptFrame.encodeMany],rfl⟩

theorem Extends.header {before after : Transcript} (extension : Extends before after)
    {profile : Digest} {label context : Input} {seed : Digest}
    (header : NativeChildSeedView.HasHeader before profile label context seed) :
    NativeChildSeedView.HasHeader after profile label context seed := by
  obtain ⟨suffix,valid,bytes⟩ := header
  obtain ⟨later,laterValid,laterBytes,_⟩ := extension
  refine ⟨suffix++later,?_,?_⟩
  · intro frame member
    rcases List.mem_append.mp (by simpa only [List.append_assoc] using member :
      frame ∈ (NativeChildSeedView.seededFrames profile label context seed ++ suffix) ++ later) with old | added
    · exact valid frame old
    · exact laterValid frame added
  · simp only [laterBytes,bytes,encodeMany_append,List.append_assoc]

theorem beginField (state : Transcript) (label : Input) (p count : ℕ)
    (labelFits : label.length < TranscriptFrame.lengthLimit) :
    Extends state (NativeTranscript.beginField state label p count).run.1.pending := by
  apply absorb state 4 label _
  exact ⟨labelFits,by simp only [List.length_append,TranscriptFrame.littleEndian_length]; decide +kernel⟩


theorem finishField (phase : FieldPhase) (world : World)
    (labelFits : phase.label.length < TranscriptFrame.lengthLimit) :
    Extends phase.pending (NativeTranscript.finishField world phase).run.1 := by
  apply absorb phase.pending 5 phase.label _
  exact ⟨labelFits,by simp only [List.length_append,TranscriptFrame.littleEndian_length,InputIndexedOracle.bytes,List.length_ofFn]; decide +kernel⟩

def StateExtends (base : Transcript) (state : NativeFieldVector.State) : Prop :=
  Extends base state.phase.pending ∧ state.phase.label.length < TranscriptFrame.lengthLimit

def StatusExtends (base : Transcript) : NativeFieldVector.Status → Prop
  | .suspended state => StateExtends base state
  | .finished state transcript => StateExtends base state ∧ Extends base transcript

private theorem advance_phase (p : ℕ) (state : NativeFieldVector.State) (trial : CanonicalTranscriptSampler.Outcome) :
    (NativeFieldVector.advance p state trial).phase = trial.phase := by
  unfold NativeFieldVector.advance
  split <;> rfl

/-- Every candidate retry keeps the exact pending transcript and label. -/
theorem execute_fields (p fuel : ℕ) (state : NativeFieldVector.State) (world : World) :
    (NativeFieldVector.execute p fuel state world).1.phase.pending = state.phase.pending ∧
    (NativeFieldVector.execute p fuel state world).1.phase.label = state.phase.label := by
  induction fuel generalizing state with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
    by_cases complete : state.remaining = 0
    · simp only [NativeFieldVector.execute,complete,ite_true,and_self]
    · have next := ih (NativeFieldVector.advance p state (CanonicalTranscriptSampler.executePrefix p 1 state.phase world).1)
      rw [advance_phase] at next
      have retained := CanonicalTranscriptSampler.phase_retains_chunks p 1 state.phase world
      rw [retained] at next
      simpa only [NativeFieldVector.execute,complete,ite_false] using next

theorem execute_state (base : Transcript) (p fuel : ℕ) (state : NativeFieldVector.State) (world : World)
    (valid : StateExtends base state) : StateExtends base (NativeFieldVector.execute p fuel state world).1 := by
  have fields := execute_fields p fuel state world
  exact ⟨by rw [fields.1]; exact valid.1,by rw [fields.2]; exact valid.2⟩

theorem finish_status (base : Transcript) (state : NativeFieldVector.State) (world : World)
    (valid : StateExtends base state) : StatusExtends base (NativeFieldVector.finishExecute world state).1 := by
  unfold NativeFieldVector.finishExecute
  split
  · exact ⟨valid,valid.1.trans (finishField state.phase world valid.2)⟩
  · exact valid

theorem drive_status (base : Transcript) (p fuel : ℕ) (state : NativeFieldVector.State) (world : World)
    (valid : StateExtends base state) : StatusExtends base (NativeFieldVector.driveExecute p fuel state world).1 :=
  finish_status base _ world (execute_state base p fuel state world valid)

theorem resume_status (base : Transcript) (p fuel : ℕ) (status : NativeFieldVector.Status) (world : World)
    (valid : StatusExtends base status) : StatusExtends base (run (NativeFieldVector.resume p fuel status) world).run.1 := by
  rw [NativeFieldVector.run_resume]
  cases status with
  | suspended state => exact drive_status base p fuel state world valid
  | finished state transcript => exact valid

theorem request_status (p fuel : ℕ) (state : Transcript) (label : Input) (count : ℕ) (world : World)
    (labelFits : label.length < TranscriptFrame.lengthLimit) :
    StatusExtends state (run (NativeFieldVector.request p fuel state label count) world).run.1 := by
  rw [NativeFieldVector.run_request]
  exact drive_status state p fuel _ world ⟨beginField state label p count labelFits,labelFits⟩

theorem extension_prepare (state : Transcript) (degree w : ℕ)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Extends state (NativeExtensionRequest.prepare state degree w) := by
  apply (absorb state 1 (utf8 "field challenge kind") (utf8 "extension vector") ⟨by decide +kernel,by decide +kernel⟩).trans
  exact absorb _ 1 (utf8 "extension basis") _ ⟨by change (utf8 "extension basis").length < _; decide +kernel,descriptorFits⟩

theorem typed_prepare (state : Transcript) (kind : TypedFieldRequest.Kind) :
    Extends state (TypedFieldRequest.prepare state kind) := by
  apply absorb state 1 (utf8 "typed request kind") _
  constructor
  · change (utf8 "typed request kind").length < _
    decide +kernel
  · cases kind <;> decide +kernel

theorem scalar_begin (p degree w : ℕ) (state : Transcript) (label : Input)
    (labelFits : label.length < TranscriptFrame.lengthLimit)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    StateExtends state (TypedFieldRequest.beginExecute p degree w state label).1 := by
  refine ⟨?_,labelFits⟩
  exact ((typed_prepare state .scalar).trans (extension_prepare _ degree w descriptorFits)).trans
    (beginField _ label p degree labelFits)

theorem vector_begin (p degree w count : ℕ) (state : Transcript) (label : Input)
    (labelFits : label.length < TranscriptFrame.lengthLimit)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    StateExtends state (TypedFieldVector.beginExecute p degree w count state label).1 := by
  refine ⟨?_,labelFits⟩
  exact ((typed_prepare state .vector).trans (extension_prepare _ degree w descriptorFits)).trans
    (beginField _ label p (count*degree) labelFits)

theorem StateExtends.trans {first middle : Transcript} {state : NativeFieldVector.State}
    (before : Extends first middle) (later : StateExtends middle state) : StateExtends first state :=
  ⟨before.trans later.1,later.2⟩

theorem StatusExtends.trans {first middle : Transcript} {status : NativeFieldVector.Status}
    (before : Extends first middle) (later : StatusExtends middle status) : StatusExtends first status := by
  cases status with
  | suspended state => exact StateExtends.trans before later
  | finished state transcript => exact ⟨StateExtends.trans before later.1,before.trans later.2⟩

theorem typed_request_status (p degree w fuel : ℕ) (state : Transcript) (kind : TypedFieldRequest.Kind)
    (label : Input) (count : ℕ) (world : World)
    (labelFits : label.length < TranscriptFrame.lengthLimit)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    StatusExtends state (run (TypedFieldRequest.extension p degree w fuel state kind label count) world).run.1 := by
  exact StatusExtends.trans ((typed_prepare state kind).trans (extension_prepare _ degree w descriptorFits))
    (request_status p fuel _ label (count*degree) world labelFits)


theorem Extends.frames {before after : Transcript} (extension : Extends before after)
    (frames : List TranscriptFrame.Frame) (decoded : TranscriptFrame.decodeAll before.input = some frames) :
    ∃ suffix : List TranscriptFrame.Frame, TranscriptFrame.decodeAll after.input = some (frames++suffix) := by
  have beforeValid := TranscriptFrame.decodeAll_sound before.input frames decoded
  obtain ⟨suffix,valid,bytes,_⟩ := extension
  refine ⟨suffix,?_⟩
  rw [bytes,beforeValid.2,← encodeMany_append]
  apply TranscriptFrame.decodeAll_encodeMany
  intro frame member
  rcases List.mem_append.mp member with old | added
  · exact beforeValid.1 frame old
  · exact valid frame added

/-- Literal helper roots remain in the complete decoded input through all valid extensions. -/
theorem Extends.roots {before after : Transcript} (extension : Extends before after)
    (frames : List TranscriptFrame.Frame) (decoded : TranscriptFrame.decodeAll before.input = some frames) :
    (NativeParentLedger.roots before.input).Sublist (NativeParentLedger.roots after.input) := by
  obtain ⟨suffix,decodedAfter⟩ := extension.frames frames decoded
  simp only [NativeParentLedger.roots,NativeParentLedger.frames,decoded,decodedAfter,Option.getD_some,List.flatMap_append]
  exact List.sublist_append_left _ _

end
end FormalProof4FHE.HasteBoots.NativeTranscriptExtension

