module
public import FormalProof4FHE.HasteBoots.HelperRootsView
public import FormalProof4FHE.HasteBoots.NativeTranscriptExtension
import all Init.Data.String.Defs
@[expose] public section

/-! Native typed field sampling appends valid frames without appending a
helper-roots frame. Retry state, suspension and finalization retain this
stronger property without assumptions about earlier transcript labels. -/
namespace FormalProof4FHE.HasteBoots.RootSafeExtension
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript FieldPhase utf8)
open OracleProgram (run)
noncomputable section

def Extends (before after : Transcript) : Prop :=
  ∃ suffix : List TranscriptFrame.Frame, (∀ frame ∈ suffix, TranscriptFrame.Valid frame) ∧
    (∀ frame ∈ suffix, HelperRootsView.Clean frame) ∧
    after.input = before.input ++ TranscriptFrame.encodeMany suffix ∧ after.profile = before.profile

private theorem encodeMany_append (first later : List TranscriptFrame.Frame) :
    TranscriptFrame.encodeMany (first++later) = TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany later := by
  induction first with
  | nil => simp [TranscriptFrame.encodeMany]
  | cons frame rest ih => simp [TranscriptFrame.encodeMany,ih,List.append_assoc]

theorem Extends.refl (state : Transcript) : Extends state state := ⟨[],by simp,by simp,by simp [TranscriptFrame.encodeMany],rfl⟩

theorem Extends.trans {first middle last : Transcript} (earlier : Extends first middle) (later : Extends middle last) :
    Extends first last := by
  obtain ⟨left,leftValid,leftClean,leftBytes,leftProfile⟩ := earlier
  obtain ⟨right,rightValid,rightClean,rightBytes,rightProfile⟩ := later
  exact ⟨left++right,by
    intro frame member
    rcases List.mem_append.mp member with old | added
    · exact leftValid frame old
    · exact rightValid frame added,
    by
      intro frame member
      rcases List.mem_append.mp member with old | added
      · exact leftClean frame old
      · exact rightClean frame added,
    by rw [rightBytes,leftBytes,encodeMany_append,List.append_assoc],rightProfile.trans leftProfile⟩

theorem absorb (state : Transcript) (kind : Fin 9) (label message : Input)
    (valid : TranscriptFrame.Valid ⟨kind,label,message⟩) (clean : HelperRootsView.Clean ⟨kind,label,message⟩) : Extends state (NativeTranscript.absorb state kind label message) :=
  ⟨[⟨kind,label,message⟩],by simpa using valid,by simpa using clean,by simp [NativeTranscript.absorb,TranscriptFrame.encodeMany],rfl⟩

theorem beginField (state : Transcript) (label : Input) (p count : ℕ)
    (labelFits : label.length < TranscriptFrame.lengthLimit) :
    Extends state (NativeTranscript.beginField state label p count).run.1.pending := by
  apply absorb state 4 label _
  · exact ⟨labelFits,by simp only [List.length_append,TranscriptFrame.littleEndian_length]; decide +kernel⟩
  · intro tagged
    cases tagged.1


theorem finishField (phase : FieldPhase) (world : World)
    (labelFits : phase.label.length < TranscriptFrame.lengthLimit) :
    Extends phase.pending (NativeTranscript.finishField world phase).run.1 := by
  apply absorb phase.pending 5 phase.label _
  · exact ⟨labelFits,by simp only [List.length_append,TranscriptFrame.littleEndian_length,InputIndexedOracle.bytes,List.length_ofFn]; decide +kernel⟩
  · intro tagged
    cases tagged.1

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

theorem clean_label (label message : Input) (apart : label ≠ NativeLookupEquality.rootsLabel) : HelperRootsView.Clean ⟨1,label,message⟩ :=
  fun tagged => apart tagged.2

theorem extension_prepare (state : Transcript) (degree w : ℕ)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Extends state (NativeExtensionRequest.prepare state degree w) := by
  apply (absorb state 1 (utf8 "field challenge kind") (utf8 "extension vector") ⟨by decide +kernel,by decide +kernel⟩
    (clean_label _ _ (by decide +kernel))).trans
  exact absorb _ 1 (utf8 "extension basis") _ ⟨by change (utf8 "extension basis").length < _; decide +kernel,descriptorFits⟩ (clean_label _ _ (by decide +kernel))

theorem typed_prepare (state : Transcript) (kind : TypedFieldRequest.Kind) :
    Extends state (TypedFieldRequest.prepare state kind) := by
  apply absorb state 1 (utf8 "typed request kind") _
  · constructor
    · change (utf8 "typed request kind").length < _
      decide +kernel
    · cases kind <;> decide +kernel
  · exact clean_label _ _ (by decide +kernel)

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


theorem Extends.parse {before after : Transcript} (extension : Extends before after)
    (frames : List TranscriptFrame.Frame) (decoded : TranscriptFrame.decodeAll before.input = some frames) :
    HelperRootsView.parse after.input = HelperRootsView.parse before.input := by
  obtain ⟨suffix,valid,clean,bytes,_⟩ := extension
  obtain ⟨oldValid,oldBytes⟩ := TranscriptFrame.decodeAll_sound _ _ decoded
  have afterDecoded : TranscriptFrame.decodeAll after.input = some (frames++suffix) := by
    rw [bytes,oldBytes,← encodeMany_append]
    apply TranscriptFrame.decodeAll_encodeMany
    intro frame member
    rcases List.mem_append.mp member with old | added
    · exact oldValid frame old
    · exact valid frame added
  simp only [HelperRootsView.parse,afterDecoded,decoded,Option.bind_some,List.reverse_append]
  exact HelperRootsView.read_clean suffix.reverse (fun frame member => clean frame (List.mem_reverse.mp member)) frames.reverse

end
end FormalProof4FHE.HasteBoots.RootSafeExtension
