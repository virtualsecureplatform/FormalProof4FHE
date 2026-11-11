module
public import FormalProof4FHE.HasteBoots.ScalarStoppedReplay
public import FormalProof4FHE.HasteBoots.OracleProgramHistory
public import FormalProof4FHE.HasteBoots.OracleHistoryComposition
@[expose] public section

/-! Refine the attacker's actual first-exposure history by native scalar
replay which stops before reading that stream. The resulting prior machine
state can select the challenge test without an independence assumption. -/
namespace FormalProof4FHE.HasteBoots.ScalarReplayChallengeLaw
open InputIndexedOracle (Input World law)
open NativeTranscript (Execution FieldPhase)
open NativeScalarBatchWire (Statement)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)
open NativeExtensionFields (Goldilocks3)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open scoped Classical
noncomputable section
local instance : SampleableType Goldilocks3 := SampleableType.ofFintype _

def extended {A : Type} (past : World → Execution A) (target : Input) (statement : Statement)
    (proof : Proof) (budget : ℕ) (machine : Machine) :=
  OracleProgramHistory.extend past (fun _ => ScalarStoppedReplay.program target statement proof budget machine)

theorem run_extended {A : Type} (past : World → Execution A) (target : Input) (statement : Statement)
    (proof : Proof) (budget : ℕ) (machine : Machine) (world : World) :
    (extended past target statement proof budget machine world).run =
      (((past world).run,(ScalarStoppedReplay.execute target statement proof budget machine world).1),
       (past world).run.2 ++ (ScalarStoppedReplay.execute target statement proof budget machine world).2) := by
  simp only [extended, OracleProgramHistory.run_extend, ScalarStoppedReplay.run_program]

theorem extended_replay {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (target : Input) (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine) :
    ObservationReplay.Replayable (extended past target statement proof budget machine) := OracleProgramHistory.replay replay _

def event (target : Input) (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (fuel : ℕ) (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) (world : World) : Prop :=
  (GoldScalarChallengeLaw.values fuel phase world).elim False
    (bad (ScalarStoppedReplay.execute target statement proof budget machine world).1.2)

theorem event_measurable {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (target : Input) (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (fuel : ℕ) (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) :
    MeasurableSet {world | event target statement proof budget machine fuel phase bad world} := by
  have measurable := OracleProgramHistory.event_measurable (extended_replay replay target statement proof budget machine)
    (fun packet world => (GoldScalarChallengeLaw.values fuel phase world).elim False (bad packet.1.2.2))
    (fun packet => by
      simpa only [GoldScalarChallengeLaw.values, NativeFieldVectorLaw.program_values, Option.elim_map, Function.comp_def] using
        (OracleExecutionLaw.event_measurable
          (OracleProgram.run_replay (NativeFieldVectorProgram.program NativeFields.goldilocksModulus fuel 3 phase))
          (fun result => result.1.elim False (fun coefficients => bad packet.1.2.2 (GoldScalarChallengeLaw.assemble coefficients)))))
  simpa only [run_extended, event] using measurable

/-- Auxiliary replay fixes the actual prior native machine state on the
refined fiber, while all three coordinates of the selected challenge remain
jointly uniform. Completion mass still includes every rejected candidate. -/
theorem retained_uniform {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S A) (world : World) (dummy : NativeRootMessage.Digest)
    (target : Input) (view : ScalarChallengeInputView.View) (parsed : ScalarChallengeInputView.parse target = some view)
    (selected : CausalStreamExposure.firstRead step (past world).run = some target)
    (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (fuel : ℕ) (phase : FieldPhase) (input : phase.pending.input = target) (bad : Machine → Goldilocks3 → Prop) :
    (law[|{other | (extended past target statement proof budget machine other).run =
      (extended past target statement proof budget machine world).run}])
      {other | event target statement proof budget machine fuel phase bad other} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar NativeFields.goldilocksModulus 1) fuel 3 *
        Pr{let value ← $ᵗ Goldilocks3}[bad (ScalarStoppedReplay.execute target statement proof budget machine world).1.2 value] := by
  have notSeen : CausalStreamExposure.seen (past world).run.2 target = false := by
    unfold CausalStreamExposure.firstRead at selected
    split at selected <;> simp at selected
    obtain ⟨eligible,rfl⟩ := selected
    exact eligible.2
  have fresh := ScalarStoppedReplay.retained_fresh target view parsed statement proof budget machine world
    (past world).run.2 notSeen phase.consumed.length
  have native := NativeFieldVectorLaw.conditional_uniform (extended_replay replay target statement proof budget machine)
    world NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
    (NativeGoldBatchFamilyAvailability.reconstructed dummy (extended past target statement proof budget machine world).run.2)
    (NativeGoldBatchFamilyAvailability.reconstructed_hash dummy (extended past target statement proof budget machine world).run.2)
    NativeFields.goldilocksModulus (by decide +kernel) fuel 3 phase (by rw [input]; simpa only [run_extended] using fresh)
    (fun coefficients => bad (ScalarStoppedReplay.execute target statement proof budget machine world).1.2
      (GoldScalarChallengeLaw.assemble coefficients))
  rw [GoldScalarChallengeLaw.uniform_assembly] at native
  calc
    _ = (law[|{other | (extended past target statement proof budget machine other).run =
          (extended past target statement proof budget machine world).run}])
        {other | (GoldScalarChallengeLaw.values fuel phase other).elim False
          (bad (ScalarStoppedReplay.execute target statement proof budget machine world).1.2)} := by
      apply NativeShakeProjection.conditional_event_congr (extended_replay replay target statement proof budget machine) world
      intro other same
      have state := congrArg (fun packet => packet.1.2.2) same
      simp only [run_extended] at state
      simp only [event, state]
    _ = _ := by simpa only [GoldScalarChallengeLaw.values, Option.elim_map, Function.comp_def] using native

/-- Averaging the auxiliary states returns to the original attacker-history
posterior. No conditioning on successful replay or field collection occurs. -/
theorem conditional_uniform {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S A) (world : World) (dummy : NativeRootMessage.Digest)
    (target : Input) (view : ScalarChallengeInputView.View) (parsed : ScalarChallengeInputView.parse target = some view)
    (selected : CausalStreamExposure.firstRead step (past world).run = some target)
    (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (fuel : ℕ) (phase : FieldPhase) (input : phase.pending.input = target) (bad : Machine → Goldilocks3 → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event target statement proof budget machine fuel phase bad other} =
      ∫⁻ current, BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar NativeFields.goldilocksModulus 1) fuel 3 *
        Pr{let value ← $ᵗ Goldilocks3}[bad (ScalarStoppedReplay.execute target statement proof budget machine current).1.2 value]
        ∂law[|{other | (past other).run = (past world).run}] := by
  rw [OracleHistoryComposition.refinement_event replay (extended_replay replay target statement proof budget machine)
    (fun packet => packet.1.1) (fun _ => rfl) world _
    (event_measurable replay target statement proof budget machine fuel phase bad)]
  apply lintegral_congr_ae
  filter_upwards [ae_cond_mem (μ := law) (ObservationReplay.fiber_measurable replay world)] with current same
  have first : CausalStreamExposure.firstRead step (past current).run = some target := by rw [same]; exact selected
  exact retained_uniform replay step current dummy target view parsed first statement proof budget machine fuel phase input bad

/-- Uniform test bounds survive adaptive selection by stopped native state. -/
theorem conditional_le {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S A) (world : World) (dummy : NativeRootMessage.Digest)
    (target : Input) (view : ScalarChallengeInputView.View) (parsed : ScalarChallengeInputView.parse target = some view)
    (selected : CausalStreamExposure.firstRead step (past world).run = some target)
    (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (fuel : ℕ) (phase : FieldPhase) (input : phase.pending.input = target) (bad : Machine → Goldilocks3 → Prop)
    (risk : ENNReal) (bounded : ∀ state, Pr{let value ← $ᵗ Goldilocks3}[bad state value] ≤ risk) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event target statement proof budget machine fuel phase bad other} ≤ risk := by
  rw [conditional_uniform replay step world dummy target view parsed selected statement proof budget machine fuel phase input bad]
  calc
    _ ≤ ∫⁻ _ : World, risk ∂law[|{other | (past other).run = (past world).run}] := by
      apply lintegral_mono
      intro current
      exact (mul_le_of_le_one_left' (BudgetedUniformSequence.completion_le_one _ fuel 3)).trans (bounded _)
    _ ≤ risk := by
      rw [lintegral_const]
      exact mul_le_of_le_one_right' prob_le_one

/-- All analysis prefixes of the same sampler are included. The replay budget
is an auxiliary finite history, not a runtime bound on challenge retries. -/
theorem eventual_le {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S A) (world : World) (dummy : NativeRootMessage.Digest)
    (target : Input) (view : ScalarChallengeInputView.View) (parsed : ScalarChallengeInputView.parse target = some view)
    (selected : CausalStreamExposure.firstRead step (past world).run = some target)
    (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (phase : FieldPhase) (input : phase.pending.input = target) (bad : Machine → Goldilocks3 → Prop)
    (risk : ENNReal) (bounded : ∀ state, Pr{let value ← $ᵗ Goldilocks3}[bad state value] ≤ risk) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, event target statement proof budget machine fuel phase bad other} ≤ risk := by
  have monotone : Monotone (fun fuel => {other | event target statement proof budget machine fuel phase bad other}) := by
    intro first second ordered other member
    have native := NativeFieldVectorLaw.event_monotone NativeFields.goldilocksModulus 3 phase
      (fun coefficients => bad (ScalarStoppedReplay.execute target statement proof budget machine other).1.2
        (GoldScalarChallengeLaw.assemble coefficients)) ordered
    simp only [Set.mem_ofPred_eq, event, GoldScalarChallengeLaw.values, Option.elim_map, Function.comp_def] at member ⊢
    exact native member
  have union : {other | ∃ fuel, event target statement proof budget machine fuel phase bad other} =
      ⋃ fuel, {other | event target statement proof budget machine fuel phase bad other} := by ext other; simp
  rw [union, monotone.measure_iUnion]
  exact iSup_le (fun fuel => conditional_le replay step world dummy target view parsed selected
    statement proof budget machine fuel phase input bad risk bounded)

/-- Received/honest polynomial families may depend on the actual replayed
native machine state. The cubic-field root bound still holds in the original
attacker posterior and over every candidate prefix. -/
theorem eventual_agreement_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S A) (world : World) (dummy : NativeRootMessage.Digest)
    (target : Input) (view : ScalarChallengeInputView.View) (parsed : ScalarChallengeInputView.parse target = some view)
    (selected : CausalStreamExposure.firstRead step (past world).run = some target)
    (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (phase : FieldPhase) (input : phase.pending.input = target)
    (sent honest : Machine → Polynomial Goldilocks3) (degree : ℕ)
    (different : ∀ state, sent state ≠ honest state)
    (sentDegree : ∀ state, (sent state).natDegree ≤ degree)
    (honestDegree : ∀ state, (honest state).natDegree ≤ degree) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, event target statement proof budget machine fuel phase
        (fun state value => (sent state).eval value = (honest state).eval value) other} ≤
          (degree : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) :=
  eventual_le replay step world dummy target view parsed selected statement proof budget machine phase input _ _
    (fun state => GoldScalarChallengeLaw.agreement_probability _ _ degree (different state) (sentDegree state) (honestDegree state))

end
end FormalProof4FHE.HasteBoots.ScalarReplayChallengeLaw
