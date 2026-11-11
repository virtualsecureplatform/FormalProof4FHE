module
import all FormalProof4FHE.HasteBoots.ScalarRecoveredUnboundedLaw
import all FormalProof4FHETest.HasteBootsScalarStoppedPriorSmoke

namespace FormalProof4FHE.HasteBoots.ScalarUnboundedSmoke
open HasteBootsSamplerAncestrySmoke (child worldZero worldReject)
open ScalarReplaySmoke (target)
open ScalarRecoverySmoke (recovered found)
open InputIndexedOracle (World)
open MeasureTheory ProbabilityTheory
noncomputable section

def phase := recovered.phase child.profile
def initial := recovered.initial child.profile
def statement := recovered.view.history.statement
def proof := recovered.proof

def detector (budget fuel : ℕ) (world : World) : Bool :=
  (ScalarStoppedReplay.execute target statement proof budget initial world).1.1 &&
    (GoldScalarChallengeLaw.values fuel phase world).isSome

/-- This Boolean regression predicate is precisely the guarded successful
replay/collector event with a trivial challenge test. -/
theorem detector_iff (budget fuel : ℕ) (world : World) :
    detector budget fuel world = true ↔ ScalarUnboundedReplayLaw.event target statement proof budget initial fuel phase (fun _ _ => True) world := by
  obtain ⟨_,_,_,flag⟩ := ScalarStoppedReplay.origin target statement proof budget initial world
  simp only [detector,flag,Bool.and_eq_true_iff,ScalarUnboundedReplayLaw.event,ScalarReplayChallengeLaw.event]
  cases values : GoldScalarChallengeLaw.values fuel phase world with
  | none => simp
  | some value => simp [ScalarUnboundedReplayLaw.guarded]

/-- Without the match guard, exhausted replay states can change the selected
test as the auxiliary budget grows; that event is not monotone. -/
example : ScalarReplayChallengeLaw.event target statement proof 2 initial 3 phase
      (fun state _ => state.state.point.length = 0) worldZero ∧
    ¬ ScalarReplayChallengeLaw.event target statement proof 4 initial 3 phase
      (fun state _ => state.state.point.length = 0) worldZero := by
  have completed : (GoldScalarChallengeLaw.values 3 phase worldZero).isSome = true := by decide +kernel
  unfold ScalarReplayChallengeLaw.event
  cases values : GoldScalarChallengeLaw.values 3 phase worldZero with
  | none => simp only [values,Option.isSome_none,Bool.false_eq_true] at completed
  | some value =>
    simp only [Option.elim_some]
    decide +kernel

/-- Completing hypothetical target bytes cannot turn a missed auxiliary match
into an event; likewise a matched reader with two coefficients is incomplete. -/
example : detector 2 3 worldZero = false ∧ detector 4 3 worldZero = false := by decide +kernel
example : detector 5 2 worldZero = false ∧ detector 5 3 worldZero = true := by decide +kernel
example : detector 8 3 worldReject = false := by decide +kernel

example : ScalarUnboundedReplayLaw.event target statement proof 5 initial 3 phase (fun _ _ => True) worldZero :=
  (detector_iff 5 3 worldZero).mp (by decide +kernel)

/-- Unequal auxiliary and collector witnesses are covered by one diagonal
index; no equality or finite runtime bound on those witnesses is assumed. -/
example : ScalarUnboundedReplayLaw.eventual target statement proof initial phase (fun _ _ => True) worldZero :=
  ⟨5,3,(detector_iff 5 3 worldZero).mp (by decide +kernel)⟩

example : worldZero ∈ ⋃ bound, {world | ScalarUnboundedReplayLaw.event target statement proof bound initial bound phase (fun _ _ => True) world} := by
  rw [← ScalarUnboundedReplayLaw.diagonal]
  exact ⟨5,3,(detector_iff 5 3 worldZero).mp (by decide +kernel)⟩

/-- Guarded event monotonicity comes from post-match state stability rather
than a claim that every intermediate exhausted state selects the same test. -/
example (first later fuel : ℕ) (ordered : first ≤ later) (world : World)
    (event : ScalarUnboundedReplayLaw.event target statement proof first initial fuel phase (fun _ _ => True) world) :
    ScalarUnboundedReplayLaw.event target statement proof later initial fuel phase (fun _ _ => True) world :=
  ScalarUnboundedReplayLaw.budget_monotone target statement proof initial fuel phase _ ordered event

example (budget fuel : ℕ) (world : World)
    (unmatched : (ScalarStoppedReplay.execute target statement proof budget initial world).1.1 = false) :
    ¬ ScalarUnboundedReplayLaw.event target statement proof budget initial fuel phase (fun _ _ => True) world := by
  intro yes
  have matched := ScalarUnboundedReplayLaw.event_matched target statement proof budget initial fuel phase _ world yes
  rw [unmatched] at matched
  contradiction

example : MeasurableSet {world | ScalarRecoveredUnboundedLaw.event target recovered child.profile (fun _ _ => True) world} :=
  ScalarRecoveredUnboundedLaw.measurable ScalarHealingSmoke.replay target recovered child.profile _

/-- Both unbounded loops preserve the one-exposure cubic root bound. The
polynomial constant term depends on the actual retained common point length. -/
example : (InputIndexedOracle.law[|{other | (ScalarHealingSmoke.past other).run = (ScalarHealingSmoke.past worldZero).run}])
    {other | ScalarRecoveredUnboundedLaw.event target recovered child.profile
      (fun prior value => True ∧
        (Polynomial.C (prior.2.1.length : NativeExtensionFields.Goldilocks3)).eval value =
        (Polynomial.X + Polynomial.C (prior.2.1.length : NativeExtensionFields.Goldilocks3)).eval value) other} ≤
          (1 : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have bound := ScalarRecoveredUnboundedLaw.agreement_bound ScalarHealingSmoke.replay ScalarReplaySmoke.step worldZero
    (fun _ => 0) child.profile target recovered found rfl (fun _ => True)
    (fun prior => Polynomial.C (prior.2.1.length : NativeExtensionFields.Goldilocks3))
    (fun prior => Polynomial.X + Polynomial.C (prior.2.1.length : NativeExtensionFields.Goldilocks3)) 1
    (by intro state _ _ same; have coefficient := congrArg (fun poly : Polynomial NativeExtensionFields.Goldilocks3 => poly.coeff 1) same; simp at coefficient)
    (by intro state _ _; simp) (by intro state _ _; exact (Polynomial.natDegree_add_le _ _).trans (by simp))
  simpa only [Nat.cast_one] using bound

/-- Side conditions are irrelevant for ineligible matched states. -/
example : (InputIndexedOracle.law[|{other | (ScalarHealingSmoke.past other).run = (ScalarHealingSmoke.past worldZero).run}])
    {other | ScalarRecoveredUnboundedLaw.event target recovered child.profile
      (fun _ value => False ∧ (Polynomial.X : Polynomial NativeExtensionFields.Goldilocks3).eval value = Polynomial.X.eval value) other} ≤
        (0 : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  simpa only [Nat.cast_zero] using (ScalarRecoveredUnboundedLaw.agreement_bound ScalarHealingSmoke.replay ScalarReplaySmoke.step worldZero
    (fun _ => 0) child.profile target recovered found rfl (fun _ => False) (fun _ => Polynomial.X) (fun _ => Polynomial.X) 0
    (by intro state _ impossible; contradiction) (by intro state _ impossible; contradiction) (by intro state _ impossible; contradiction))

/-- Any original active fixture supplies an all-budget event from a collected
value and its actual prior test. No stopped-prior equality is a premise. -/
example (budget fuel : ℕ) (world : World) (packet : NativeScalarBatchWire.RoundPacket) (field : NativeFieldVector.State)
    (active : (ScalarExecutionRecoverySmoke.execution budget world).1.control = .sampling packet field)
    (same : field.phase.pending.input = target) (value : NativeExtensionFields.Goldilocks3)
    (collected : GoldScalarChallengeLaw.values fuel phase world = some value)
    (bad : ScalarRecoveredUnboundedLaw.Prior → NativeExtensionFields.Goldilocks3 → Prop)
    (failed : bad (ScalarPriorStability.prior (ScalarExecutionRecoverySmoke.execution budget world).1) value) :
    ScalarRecoveredUnboundedLaw.event target recovered child.profile bad world :=
  ScalarRecoveredUnboundedLaw.original_witness target recovered found child
    (NativeScalarBatchWire.bindStatement child ScalarReplaySmoke.statement)
    ScalarExecutionRecoverySmoke.before ScalarReplaySmoke.statement ScalarReplaySmoke.proof
    ScalarExecutionRecoverySmoke.decoded rfl (by decide +kernel) ScalarExecutionRecoverySmoke.domain
    budget world packet field active same fuel value collected bad failed

end
end FormalProof4FHE.HasteBoots.ScalarUnboundedSmoke
