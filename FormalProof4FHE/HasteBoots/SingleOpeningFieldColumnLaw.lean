module
public import FormalProof4FHE.HasteBoots.SingleOpeningChallengeScope
public import FormalProof4FHE.HasteBoots.NativeIndexUnseenLaw
public import FormalProof4FHE.HasteBoots.OracleProgramHistory
@[expose] public section

/-! Posterior composition of actual single-opening Goldilocks field collection with the
ordered native column vector. The field result may determine every test
response. Full original histories and suspended outcomes are retained. This
is a sampling/composition law; source ownership and application soundness
must still supply the disagreement witness. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFieldColumnLaw
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeTranscript (Execution)
open SingleOpeningChallengeLink (View)
open NativeFieldVector (State)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def collected (profile : Digest) (fuel : ℕ) (view : View) (world : World) :=
  NativeFieldVector.execute NativeFields.goldilocksModulus fuel
    (NativeFieldVector.initial (view.field.phase profile) view.field.count.val) world

def extended {A : Type} (past : World → Execution A) (profile : Digest) (fuel : ℕ) (view : View) :=
  OracleProgramHistory.extend past (fun _ => NativeFieldVector.collect NativeFields.goldilocksModulus fuel
    (NativeFieldVector.initial (view.field.phase profile) view.field.count.val))

theorem run_extended {A : Type} (past : World → Execution A) (profile : Digest) (fuel : ℕ) (view : View) (world : World) :
    (extended past profile fuel view world).run =
      (((past world).run,(collected profile fuel view world).1),(past world).run.2++(collected profile fuel view world).2) := by
  simp only [extended,OracleProgramHistory.run_extend,NativeFieldVector.run_collect,collected]

theorem extended_replay {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (view : View) : ObservationReplay.Replayable (extended past profile fuel view) :=
  OracleProgramHistory.replay replay _

/-- First-read eligibility is checked on the original machine packet.
No certificate about the auxiliary collector's cache is an argument. -/
theorem unseen_extended {S A : Type} (past : World → Execution (S ⊕ A)) (profile : Digest) (fuel : ℕ)
    (view : View) (input : Input) (parsed : SingleOpeningChallengeLink.parse input = some view)
    (step : S → OracleMachine.Command S A) (world : World)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input) :
    CausalStreamExposure.seen (extended past profile fuel view world).run.2 input = false := by
  have unseen : CausalStreamExposure.seen (past world).run.2 input = false := by
    unfold CausalStreamExposure.firstRead at selected
    split at selected <;> simp at selected
    obtain ⟨eligible,rfl⟩ := selected
    exact eligible.2
  rw [run_extended]
  exact SingleOpeningChallengeScope.unseen_after_collect input view parsed profile fuel world _ unseen

def event (profile : Digest) (fuel : ℕ) (view : View) (bits : ℕ)
    (bad : State → (Fin view.column.index.count.val → Fin (2^bits)) → Prop) (world : World) : Prop :=
  (NativeIndexFirstReadLaw.values bits (view.column.index.request profile).transcript view.column.index.label
    view.column.index.domain view.column.index.count world).elim False (bad (collected profile fuel view world).1)

theorem event_measurable {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (view : View) (bits : ℕ)
    (bad : State → (Fin view.column.index.count.val → Fin (2^bits)) → Prop) :
    MeasurableSet {world | event profile fuel view bits bad world} := by
  have measurable := OracleProgramHistory.event_measurable (extended_replay replay profile fuel view)
    (fun packet world => (NativeIndexFirstReadLaw.values bits (view.column.index.request profile).transcript view.column.index.label
      view.column.index.domain view.column.index.count world).elim False (bad packet.1.2))
    (fun packet => OracleExecutionLaw.event_measurable
      (OracleProgram.run_replay (NativeIndexRequest.request (view.column.index.request profile).transcript
        view.column.index.label view.column.index.domain view.column.index.count))
      (fun result => (result.1.bind (fun sample => NativeGoldPcsDraws.typed bits view.column.index.count.val sample.draws)).elim False (bad packet.1.2)))
  simpa only [run_extended,event] using measurable

/-- The completed or suspended field state is fixed on the retained fiber;
its dependent test family still sees a jointly uniform ordered column vector. -/
theorem retained_uniform {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (view : View) (input : Input)
    (parsed : SingleOpeningChallengeLink.parse input = some view)
    (step : S → OracleMachine.Command S A) (world : World)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (bits : ℕ) (power : view.column.index.domain.val = 2^bits)
    (bad : State → (Fin view.column.index.count.val → Fin (2^bits)) → Prop) :
    (law[|{other | (extended past profile fuel view other).run = (extended past profile fuel view world).run}])
      {other | event profile fuel view bits bad other} =
      Pr{let draw ← $ᵗ (Fin view.column.index.count.val → Fin (2^bits))}[bad (collected profile fuel view world).1 draw] := by
  have linked := SingleOpeningChallengeLink.parse_sound input view parsed profile
  have column := SingleOpeningColumnInputView.parse_sound input view.column linked.1 profile
  have unseen := unseen_extended past profile fuel view input parsed step world selected
  rw [← column.1] at unseen
  calc
    _ = (law[|{other | (extended past profile fuel view other).run = (extended past profile fuel view world).run}])
        {other | (NativeIndexFirstReadLaw.values bits (view.column.index.request profile).transcript view.column.index.label
        view.column.index.domain view.column.index.count other).elim False (bad (collected profile fuel view world).1)} := by
          apply NativeShakeProjection.conditional_event_congr (extended_replay replay profile fuel view) world
          intro other same
          have state := congrArg (fun packet => packet.1.2) same
          simp only [run_extended] at state
          simp only [event,state]
    _ = _ := NativeIndexUnseenLaw.conditional_uniform (extended_replay replay profile fuel view) world bits
          (view.column.index.request profile).transcript view.column.index.label view.column.index.domain
          view.column.index.count column.2.1 power unseen _

/-- Exact original-posterior composition averages all collector outcomes.
It does not condition away suspension or resample the field challenges. -/
theorem conditional_uniform {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (view : View) (input : Input)
    (parsed : SingleOpeningChallengeLink.parse input = some view)
    (step : S → OracleMachine.Command S A) (world : World)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (bits : ℕ) (power : view.column.index.domain.val = 2^bits)
    (bad : State → (Fin view.column.index.count.val → Fin (2^bits)) → Prop) :
    (law[|{other | (past other).run = (past world).run}]) {other | event profile fuel view bits bad other} =
      ∫⁻ current, Pr{let draw ← $ᵗ (Fin view.column.index.count.val → Fin (2^bits))}[bad (collected profile fuel view current).1 draw]
        ∂law[|{other | (past other).run = (past world).run}] := by
  rw [OracleHistoryComposition.refinement_event replay (extended_replay replay profile fuel view)
    (fun packet => packet.1.1) (fun _ => rfl) world _ (event_measurable replay profile fuel view bits bad)]
  apply lintegral_congr_ae
  filter_upwards [ae_cond_mem (μ := law) (ObservationReplay.fiber_measurable replay world)] with current same
  have first : CausalStreamExposure.firstRead step (past current).run = some input := by rw [same]; exact selected
  exact retained_uniform replay profile fuel view input parsed step current first bits power bad
end
end FormalProof4FHE.HasteBoots.SingleOpeningFieldColumnLaw
