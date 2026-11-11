module
public import FormalProof4FHE.HasteBoots.ScalarPrefixProof
public import FormalProof4FHE.HasteBoots.ScalarReplayChallengeLaw
@[expose] public section

/-! Scalar replay configuration recovered from the selected original input.
The statement, preceding raw packets, certificate layout and parent bytes
are selected without a world or a future response. -/
namespace FormalProof4FHE.HasteBoots.ScalarRecoveredReplay
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativeScalarBatchVerifier (Machine)
open NativeScalarBatchPreflight (Proof)
open OracleProgram (Program bind run)

structure Configuration where
  view : ScalarTranscriptPrefix.View
  proof : Proof

def recover (input : Input) : Option Configuration :=
  (ScalarTranscriptPrefix.parse input).bind (fun view =>
    (ScalarPrefixProof.reconstruct view).map (fun proof => ⟨view,proof⟩))

def Configuration.parent (configuration : Configuration) (profile : Digest) : Transcript :=
  ⟨TranscriptFrame.encodeMany configuration.view.history.before,profile⟩
def Configuration.initial (configuration : Configuration) (profile : Digest) : Machine :=
  NativeScalarBatchVerifier.initial (configuration.parent profile) configuration.view.history.statement configuration.proof

theorem recover_sound (input : Input) (configuration : Configuration) (found : recover input = some configuration) :
    ScalarTranscriptPrefix.parse input = some configuration.view ∧
      ScalarPrefixProof.reconstruct configuration.view = some configuration.proof := by
  obtain ⟨view,parsed,found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨proof,built,same⟩ := Option.map_eq_some_iff.mp found
  cases same
  exact ⟨parsed,built⟩

/-- Native well-framed history encoding recovers its literal original data.
The reconstruction guard remains explicit and is evaluated before replay. -/
theorem recover_native (view : ScalarTranscriptPrefix.View) (profile : Digest)
    (valid : ∀ frame ∈ (ScalarChallengeInputView.View.mk view.history.frames view.packet).frames, TranscriptFrame.Valid frame)
    (lengths : ∀ pair ∈ view.history.rounds, pair.2.length = 80) (proof : Proof)
    (built : ScalarPrefixProof.reconstruct view = some proof) :
    recover (TranscriptFrame.encodeMany (ScalarChallengeInputView.View.mk view.history.frames view.packet).frames) = some ⟨view,proof⟩ := by
  have parsed := ScalarTranscriptPrefix.parse_native view profile valid lengths
  rw [ScalarChallengeInputView.phase_input] at parsed
  simp only [recover,parsed,Option.bind_some,built,Option.map_some]

theorem initialized (input : Input) (configuration : Configuration) (found : recover input = some configuration) (profile : Digest) :
    NativeScalarBatchPreflight.beginVerify (configuration.parent profile) configuration.view.history.statement configuration.proof =
      .ok (NativeScalarBatchWire.bindStatement (configuration.parent profile) configuration.view.history.statement) := by
  have preflight := ScalarPrefixProof.reconstruct_preflight configuration.view configuration.proof (recover_sound input configuration found).2
  exact (NativeScalarBatchPreflight.beginVerify_ok_iff _ _ _ _).mpr ⟨preflight.1,preflight.2,rfl⟩

/-- Missing/malformed prefix data fails without an oracle query. -/
def program (input : Input) (profile : Digest) (budget : ℕ) : Program (Option (Bool × Machine)) :=
  match recover input with
  | none => .pure none
  | some configuration =>
      bind (ScalarStoppedReplay.program input configuration.view.history.statement configuration.proof budget (configuration.initial profile))
        (fun result => .pure (some result))

theorem run_program (input : Input) (profile : Digest) (budget : ℕ) (configuration : Configuration)
    (found : recover input = some configuration) (world : World) :
    (run (program input profile budget) world).run =
      (some (ScalarStoppedReplay.execute input configuration.view.history.statement configuration.proof budget
        (configuration.initial profile) world).1,
        (ScalarStoppedReplay.execute input configuration.view.history.statement configuration.proof budget
        (configuration.initial profile) world).2) := by
  simp only [program,found,OracleProgram.run_bind,ObservationReplay.run_bind,ScalarStoppedReplay.run_program,
    OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem replayable (input : Input) (profile : Digest) (budget : ℕ) :
    ObservationReplay.Replayable (run (program input profile budget)) := OracleProgram.run_replay _

/-- Both failed recovery and every native replay outcome preserve selected
stream nonexposure. All preceding field receipt queries remain in the log. -/
theorem unseen (input : Input) (profile : Digest) (budget : ℕ) (world : World) :
    CausalStreamExposure.seen (run (program input profile budget) world).run.2 input = false := by
  cases found : recover input with
  | none => simp only [program,found]; rfl
  | some configuration =>
    rw [run_program input profile budget configuration found world]
    have parsed := ScalarTranscriptPrefix.parse_sound input configuration.view (recover_sound input configuration found).1
    exact ScalarStoppedReplay.unseen input _ parsed _ _ _ _ world

/-- The reconstructed initial state yields the actual native chain from the
recovered statement, without a separate statement/proof association premise. -/
theorem linked (input : Input) (profile : Digest) (budget : ℕ) (configuration : Configuration)
    (found : recover input = some configuration) (world : World) :
    NativeScalarBatchHistory.Linked configuration.view.history.statement configuration.proof
      (ScalarStoppedReplay.execute input configuration.view.history.statement configuration.proof budget
        (configuration.initial profile) world).1.2 :=
  ScalarStoppedReplay.initialized_linked input _ _ _ _ (initialized input configuration found profile) budget world

/-- The selected original packet is an actual getter in the recovered native
proof, with the exact original raw message words and ordinal. -/
theorem current_packet (input : Input) (configuration : Configuration) (found : recover input = some configuration) :
    NativeScalarBatchRoundPacket.packet configuration.view.packet.round configuration.proof = some configuration.view.packet := by
  have built := (recover_sound input configuration found).2
  have dims := (ScalarPrefixProof.reconstruct_preflight _ _ built).2
  obtain ⟨first,head,_,_,_⟩ := NativeScalarBatchPreflight.dimensions_success _ dims
  exact ScalarPrefixProof.reconstruct_current _ _ built first head

/-- An actual successful wrapper result derives its recovered configuration
and exact native prefix origin, including all primitive observations. -/
theorem origin (input : Input) (profile : Digest) (budget : ℕ) (world : World) (result : Bool × Machine)
    (returned : (run (program input profile budget) world).run.1 = some result) :
    ∃ configuration, recover input = some configuration ∧ ∃ used ≤ budget,
      (result.2,(run (program input profile budget) world).run.2) =
        NativeScalarBatchVerifier.execute configuration.view.history.statement configuration.proof used
          (configuration.initial profile) world := by
  cases found : recover input with
  | none =>
    simp only [program,found,OracleProgram.run] at returned
    change none = some result at returned
    contradiction
  | some configuration =>
    have actual := run_program input profile budget configuration found world
    rw [actual] at returned
    cases Option.some.inj returned
    obtain ⟨used,bound,same,_⟩ := ScalarStoppedReplay.origin input configuration.view.history.statement
      configuration.proof budget (configuration.initial profile) world
    refine ⟨configuration,rfl,used,bound,?_⟩
    rw [actual]
    exact same

theorem prior_packet (input : Input) (configuration : Configuration) (found : recover input = some configuration)
    (index : ℕ) (pair : NativeScalarBatchWire.RoundPacket × Input)
    (atIndex : configuration.view.history.rounds[index]? = some pair) :
    NativeScalarBatchRoundPacket.packet pair.1.round configuration.proof = some pair.1 := by
  have built := (recover_sound input configuration found).2
  have dims := (ScalarPrefixProof.reconstruct_preflight _ _ built).2
  obtain ⟨first,head,_,_,_⟩ := NativeScalarBatchPreflight.dimensions_success _ dims
  exact ScalarPrefixProof.reconstruct_prior _ _ built first head index pair atIndex

noncomputable section
open MeasureTheory ProbabilityTheory
open NativeExtensionFields (Goldilocks3)
open scoped Classical
local instance : SampleableType Goldilocks3 := SampleableType.ofFintype _

/-- Recovered framing supplies the selected phase as well as the native
replay inputs. Only the trusted profile is supplied separately. -/
def Configuration.phase (configuration : Configuration) (profile : Digest) : NativeTranscript.FieldPhase :=
  (ScalarChallengeInputView.View.mk configuration.view.history.frames configuration.view.packet).phase profile

theorem phase_input (input : Input) (configuration : Configuration) (found : recover input = some configuration) (profile : Digest) :
    (configuration.phase profile).pending.input = input := by
  have parsed := ScalarTranscriptPrefix.parse_sound input configuration.view (recover_sound input configuration found).1
  exact (ScalarChallengeInputView.parse_sound input _ parsed profile).1

/-- Adaptive polynomial selection now uses a native replay configuration
recovered from the original selected input, rather than supplied statement,
proof, parent transcript or initial machine associations. -/
theorem eventual_agreement_bound {S A : Type} {past : World → NativeTranscript.Execution (S ⊕ A)}
    (replay : ObservationReplay.Replayable past) (step : S → OracleMachine.Command S A) (world : World)
    (dummy profile : Digest) (input : Input) (configuration : Configuration)
    (found : recover input = some configuration)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input) (budget : ℕ)
    (sent honest : Machine → Polynomial Goldilocks3) (degree : ℕ)
    (different : ∀ state, sent state ≠ honest state)
    (sentDegree : ∀ state, (sent state).natDegree ≤ degree)
    (honestDegree : ∀ state, (honest state).natDegree ≤ degree) :
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, ScalarReplayChallengeLaw.event input configuration.view.history.statement configuration.proof budget
        (configuration.initial profile) fuel (configuration.phase profile)
        (fun state value => (sent state).eval value = (honest state).eval value) other} ≤
          (degree : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have parsed := ScalarTranscriptPrefix.parse_sound input configuration.view (recover_sound input configuration found).1
  exact ScalarReplayChallengeLaw.eventual_agreement_bound replay step world dummy input _ parsed selected
    configuration.view.history.statement configuration.proof budget (configuration.initial profile)
    (configuration.phase profile) (phase_input input configuration found profile) sent honest degree different sentDegree honestDegree

end

end FormalProof4FHE.HasteBoots.ScalarRecoveredReplay
