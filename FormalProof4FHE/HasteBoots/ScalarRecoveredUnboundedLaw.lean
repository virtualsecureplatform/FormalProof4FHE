module
public import FormalProof4FHE.HasteBoots.ScalarUnboundedReplayLaw
@[expose] public section

/-! One causal scalar input selects its reconstructed replay and an eventual
prior-dependent test over all auxiliary and collector budgets. Original
active samplers supply this event through the derived stopped-prior identity. -/
namespace FormalProof4FHE.HasteBoots.ScalarRecoveredUnboundedLaw
open InputIndexedOracle (Input World law)
open NativeTranscript (Transcript Execution)
open NativeRootMessage (Digest)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)
open NativeExtensionFields (Goldilocks3)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open scoped Classical
noncomputable section
local instance : SampleableType Goldilocks3 := SampleableType.ofFintype _

abbrev Prior := List NativeGoldExtensionArithmetic.Word × List NativeGoldExtensionArithmetic.Word × List NativeScalarBatchVerifier.CompletedRound

def event (input : Input) (configuration : ScalarRecoveredReplay.Configuration) (profile : Digest)
    (bad : Prior → Goldilocks3 → Prop) (world : World) : Prop :=
  ScalarUnboundedReplayLaw.eventual input configuration.view.history.statement configuration.proof
    (configuration.initial profile) (configuration.phase profile) (fun state value => bad (ScalarPriorStability.prior state) value) world

theorem measurable {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (input : Input) (configuration : ScalarRecoveredReplay.Configuration) (profile : Digest)
    (bad : Prior → Goldilocks3 → Prop) : MeasurableSet {world | event input configuration profile bad world} :=
  ScalarUnboundedReplayLaw.eventual_measurable replay input configuration.view.history.statement configuration.proof
    (configuration.initial profile) (configuration.phase profile) _

/-- The all-budget bound consumes only the causally recovered configuration.
Side conditions concern eligible priors of matched replay states. -/
theorem agreement_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S A) (world : World) (dummy profile : Digest)
    (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (eligible : Prior → Prop) (sent honest : Prior → Polynomial Goldilocks3) (degree : ℕ)
    (different : ∀ state, ScalarStoppedReplay.blocked input state = true → eligible (ScalarPriorStability.prior state) →
      sent (ScalarPriorStability.prior state) ≠ honest (ScalarPriorStability.prior state))
    (sentDegree : ∀ state, ScalarStoppedReplay.blocked input state = true → eligible (ScalarPriorStability.prior state) →
      (sent (ScalarPriorStability.prior state)).natDegree ≤ degree)
    (honestDegree : ∀ state, ScalarStoppedReplay.blocked input state = true → eligible (ScalarPriorStability.prior state) →
      (honest (ScalarPriorStability.prior state)).natDegree ≤ degree) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event input configuration profile
        (fun prior value => eligible prior ∧ (sent prior).eval value = (honest prior).eval value) other} ≤
          (degree : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have parsed := ScalarTranscriptPrefix.parse_sound input configuration.view
    (ScalarRecoveredReplay.recover_sound input configuration found).1
  exact ScalarUnboundedReplayLaw.agreement_bound replay step world dummy input _ parsed selected
    configuration.view.history.statement configuration.proof (configuration.initial profile)
    (configuration.phase profile) (ScalarRecoveredReplay.phase_input input configuration found profile)
    (fun state => eligible (ScalarPriorStability.prior state))
    (fun state => sent (ScalarPriorStability.prior state)) (fun state => honest (ScalarPriorStability.prior state))
    degree different sentDegree honestDegree

/-- Any actual original active sampler with this input contributes a guarded
all-budget event when the corresponding collector value satisfies its prior
test. The original proof, prior and common point need not have been supplied
to the causal selector. Collector completion is still an explicit premise. -/
theorem original_witness (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration)
    (transcript result : Transcript) (before : List TranscriptFrame.Frame) (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof)
    (budget : ℕ) (world : World) (packet : RoundPacket) (field : NativeFieldVector.State)
    (active : (NativeScalarBatchVerifier.execute statement proof budget
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling packet field)
    (sameInput : field.phase.pending.input = input)
    (fuel : ℕ) (value : Goldilocks3)
    (collected : GoldScalarChallengeLaw.values fuel (configuration.phase transcript.profile) world = some value)
    (bad : Prior → Goldilocks3 → Prop)
    (failed : bad (ScalarPriorStability.prior (NativeScalarBatchVerifier.execute statement proof budget
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1) value) :
    event input configuration transcript.profile bad world := by
  obtain ⟨recovered,recoverFound,statementEq,_,matched,priorEq⟩ := ScalarRecoveredStoppedAgreement.sampler_prior
    transcript result before statement proof decoded accepted statementFits domain budget world packet field active
  rw [sameInput] at recoverFound matched priorEq
  have same := Option.some.inj (recoverFound.symm.trans found)
  subst recovered
  change ∃ budget fuel, ScalarUnboundedReplayLaw.event input configuration.view.history.statement configuration.proof budget
    (configuration.initial transcript.profile) fuel (configuration.phase transcript.profile)
    (fun state value => bad (ScalarPriorStability.prior state) value) world
  refine ⟨budget,fuel,?_⟩
  have origin := ScalarStoppedReplay.origin input statement configuration.proof budget (configuration.initial transcript.profile) world
  obtain ⟨_,_,_,flag⟩ := origin
  have blocked : ScalarStoppedReplay.blocked input (ScalarStoppedReplay.execute input statement configuration.proof budget
      (configuration.initial transcript.profile) world).1.2 = true := flag.symm.trans matched
  unfold ScalarUnboundedReplayLaw.event ScalarReplayChallengeLaw.event
  rw [statementEq]
  rw [collected]
  exact ⟨blocked,by dsimp only; rw [priorEq]; exact failed⟩

end
end FormalProof4FHE.HasteBoots.ScalarRecoveredUnboundedLaw
