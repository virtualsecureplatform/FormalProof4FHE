module
public import FormalProof4FHE.HasteBoots.ScalarRecoveredStoppedAgreement
@[expose] public section

/-! One scalar exposure bounds successful stopped replay over every auxiliary
budget and every challenge-candidate prefix. A match guard is essential:
exhausted or missed guesses cannot select fresh tests at later budgets. -/
namespace FormalProof4FHE.HasteBoots.ScalarUnboundedReplayLaw
open InputIndexedOracle (Input World law)
open NativeTranscript (FieldPhase Execution)
open NativeScalarBatchWire (Statement)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)
open NativeExtensionFields (Goldilocks3)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open scoped Classical
noncomputable section
local instance : SampleableType Goldilocks3 := SampleableType.ofFintype _

def guarded (target : Input) (bad : Machine → Goldilocks3 → Prop) (state : Machine) (value : Goldilocks3) : Prop :=
  ScalarStoppedReplay.blocked target state = true ∧ bad state value

def event (target : Input) (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (fuel : ℕ) (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) (world : World) : Prop :=
  ScalarReplayChallengeLaw.event target statement proof budget machine fuel phase (guarded target bad) world

/-- Any guarded event has actually found its selected native reader. -/
theorem event_matched (target : Input) (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (fuel : ℕ) (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) (world : World)
    (yes : event target statement proof budget machine fuel phase bad world) :
    (ScalarStoppedReplay.execute target statement proof budget machine world).1.1 = true := by
  obtain ⟨_,_,_,flag⟩ := ScalarStoppedReplay.origin target statement proof budget machine world
  unfold event ScalarReplayChallengeLaw.event at yes
  cases values : GoldScalarChallengeLaw.values fuel phase world with
  | none => simp only [values,Option.elim_none] at yes
  | some value =>
    simp only [values,Option.elim_some,guarded] at yes
    exact flag.trans yes.1

/-- Successful replay tests are monotone in auxiliary budget because their
entire retained state becomes constant once a match is found. -/
theorem budget_monotone (target : Input) (statement : Statement) (proof : Proof) (machine : Machine)
    (fuel : ℕ) (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) :
    Monotone (fun budget => {world | event target statement proof budget machine fuel phase bad world}) := by
  intro first later ordered world member
  have matched := event_matched target statement proof first machine fuel phase bad world member
  have same := ScalarFirstMatch.stable target statement proof first later ordered machine world matched
  simpa only [Set.mem_ofPred_eq,event,ScalarReplayChallengeLaw.event,same] using member

theorem fuel_monotone (target : Input) (statement : Statement) (proof : Proof) (budget : ℕ) (machine : Machine)
    (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) :
    Monotone (fun fuel => {world | event target statement proof budget machine fuel phase bad world}) := by
  intro first later ordered world member
  have native := NativeFieldVectorLaw.event_monotone NativeFields.goldilocksModulus 3 phase
    (fun coefficients => guarded target bad (ScalarStoppedReplay.execute target statement proof budget machine world).1.2
      (GoldScalarChallengeLaw.assemble coefficients)) ordered
  simp only [Set.mem_ofPred_eq,event,ScalarReplayChallengeLaw.event,GoldScalarChallengeLaw.values,
    Option.elim_map,Function.comp_def] at member ⊢
  exact native member

def eventual (target : Input) (statement : Statement) (proof : Proof) (machine : Machine)
    (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) (world : World) : Prop :=
  ∃ budget fuel, event target statement proof budget machine fuel phase bad world

/-- Independent finite witnesses for both loops are covered by one increasing
diagonal. No union bound over budgets is paid. -/
theorem diagonal (target : Input) (statement : Statement) (proof : Proof) (machine : Machine)
    (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) :
    {world | eventual target statement proof machine phase bad world} =
      ⋃ bound, {world | event target statement proof bound machine bound phase bad world} := by
  ext world
  constructor
  · rintro ⟨budget,fuel,yes⟩
    have moreBudget := budget_monotone target statement proof machine fuel phase bad (Nat.le_max_left budget fuel) yes
    have moreFuel := fuel_monotone target statement proof (max budget fuel) machine phase bad (Nat.le_max_right budget fuel) moreBudget
    exact Set.mem_iUnion.mpr ⟨max budget fuel,moreFuel⟩
  · intro member
    obtain ⟨bound,yes⟩ := Set.mem_iUnion.mp member
    exact ⟨bound,bound,yes⟩

theorem diagonal_monotone (target : Input) (statement : Statement) (proof : Proof) (machine : Machine)
    (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) :
    Monotone (fun bound => {world | event target statement proof bound machine bound phase bad world}) := by
  intro first later ordered world member
  exact fuel_monotone target statement proof later machine phase bad ordered
    (budget_monotone target statement proof machine first phase bad ordered member)

theorem eventual_measurable {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (target : Input) (statement : Statement) (proof : Proof) (machine : Machine)
    (phase : FieldPhase) (bad : Machine → Goldilocks3 → Prop) :
    MeasurableSet {world | eventual target statement proof machine phase bad world} := by
  rw [diagonal]
  exact MeasurableSet.iUnion (fun bound => ScalarReplayChallengeLaw.event_measurable replay
    target statement proof bound machine bound phase (guarded target bad))

/-- The original attacker posterior bounds the union over all successful
auxiliary replay budgets and all native collector prefixes at one exposure. -/
theorem eventual_le {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S A) (world : World) (dummy : NativeRootMessage.Digest)
    (target : Input) (view : ScalarChallengeInputView.View) (parsed : ScalarChallengeInputView.parse target = some view)
    (selected : CausalStreamExposure.firstRead step (past world).run = some target)
    (statement : Statement) (proof : Proof) (machine : Machine)
    (phase : FieldPhase) (input : phase.pending.input = target) (bad : Machine → Goldilocks3 → Prop)
    (risk : ENNReal) (bounded : ∀ state, Pr{let value ← $ᵗ Goldilocks3}[guarded target bad state value] ≤ risk) :
    (law[|{other | (past other).run = (past world).run}])
      {other | eventual target statement proof machine phase bad other} ≤ risk := by
  rw [diagonal,(diagonal_monotone target statement proof machine phase bad).measure_iUnion]
  exact iSup_le (fun bound => ScalarReplayChallengeLaw.conditional_le replay step world dummy target view parsed selected
    statement proof bound machine bound phase input (guarded target bad) risk bounded)

/-- Polynomial side conditions are required only for matched eligible states.
Failed reconstruction guesses and exhausted prefixes cannot contribute roots. -/
theorem agreement_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (step : S → OracleMachine.Command S A) (world : World) (dummy : NativeRootMessage.Digest)
    (target : Input) (view : ScalarChallengeInputView.View) (parsed : ScalarChallengeInputView.parse target = some view)
    (selected : CausalStreamExposure.firstRead step (past world).run = some target)
    (statement : Statement) (proof : Proof) (machine : Machine)
    (phase : FieldPhase) (input : phase.pending.input = target) (eligible : Machine → Prop)
    (sent honest : Machine → Polynomial Goldilocks3) (degree : ℕ)
    (different : ∀ state, ScalarStoppedReplay.blocked target state = true → eligible state → sent state ≠ honest state)
    (sentDegree : ∀ state, ScalarStoppedReplay.blocked target state = true → eligible state → (sent state).natDegree ≤ degree)
    (honestDegree : ∀ state, ScalarStoppedReplay.blocked target state = true → eligible state → (honest state).natDegree ≤ degree) :
    (law[|{other | (past other).run = (past world).run}])
      {other | eventual target statement proof machine phase
        (fun state value => eligible state ∧ (sent state).eval value = (honest state).eval value) other} ≤
          (degree : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  apply eventual_le replay step world dummy target view parsed selected statement proof machine phase input
  intro state
  by_cases matched : ScalarStoppedReplay.blocked target state = true
  · by_cases allowed : eligible state
    · exact (prEvent_mono _ _ _ (fun _ yes => yes.2.2)).trans
        (GoldScalarChallengeLaw.agreement_probability _ _ degree (different state matched allowed)
          (sentDegree state matched allowed) (honestDegree state matched allowed))
    · exact (le_of_eq (prEvent_eq_zero_of_forall_not _ _ (fun _ yes => allowed yes.2.1))).trans zero_le
  · exact (le_of_eq (prEvent_eq_zero_of_forall_not _ _ (fun _ yes => matched yes.1))).trans zero_le

end
end FormalProof4FHE.HasteBoots.ScalarUnboundedReplayLaw
