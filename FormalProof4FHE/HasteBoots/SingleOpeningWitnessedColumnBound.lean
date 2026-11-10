module
public import FormalProof4FHE.HasteBoots.SingleOpeningFieldColumnLaw
@[expose] public section

/-! Bound the event that both has a column-disagreement witness and passes
all shared checks. Correct or otherwise unwitnessed collector states need no
disagreement assumption. All native collector budgets retain their real mass. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningWitnessedColumnBound
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeTranscript (Execution)
open SingleOpeningChallengeLink (View)
open NativeFieldVector (State)
open SingleOpeningFieldColumnLaw (collected event)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def checked {Test Symbol : Type} [DecidableEq Symbol] (bits count : ℕ)
    (raw claimed : State → Test → Fin (2^bits) → Symbol) (distance : ℕ)
    (state : State) (draw : Fin count → Fin (2^bits)) : Prop :=
  state.remaining = 0 ∧ (∃ test, distance ≤ hammingDist (raw state test) (claimed state test)) ∧
    ∀ test, ColumnOpening.Agrees (raw state test) (claimed state test) draw

theorem conditional_bound {S A Test Symbol : Type} [DecidableEq Symbol]
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (view : View) (input : Input)
    (parsed : SingleOpeningChallengeLink.parse input = some view)
    (step : S → OracleMachine.Command S A) (world : World)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (bits : ℕ) (power : view.column.index.domain.val = 2^bits)
    (raw claimed : State → Test → Fin (2^bits) → Symbol) (distance : ℕ) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event profile fuel view bits (checked bits view.column.index.count.val raw claimed distance) other} ≤
      ColumnOpening.missBound (Fin (2^bits)) view.column.index.count.val distance := by
  have positive : law {other | (past other).run = (past world).run} ≠ 0 := by
    rw [ObservationReplay.fiber_eq_assignment replay world]
    exact OraclePosterior.assignment_ne_zero _ _
  let := cond_isProbabilityMeasure (μ := law) positive
  rw [SingleOpeningFieldColumnLaw.conditional_uniform replay profile fuel view input parsed step world selected bits power]
  calc
    _ ≤ ∫⁻ _current, ColumnOpening.missBound (Fin (2^bits)) view.column.index.count.val distance
        ∂law[|{other | (past other).run = (past world).run}] := by
      apply lintegral_mono
      intro current
      dsimp only
      by_cases witness : ∃ test, distance ≤ hammingDist (raw (collected profile fuel view current).1 test) (claimed (collected profile fuel view current).1 test)
      · exact (prEvent_mono _ _ _ (fun _ accepted => accepted.2.2)).trans
          (ColumnOpening.shared_bound (raw (collected profile fuel view current).1)
            (claimed (collected profile fuel view current).1) view.column.index.count.val distance witness)
      · have empty : checked bits view.column.index.count.val raw claimed distance (collected profile fuel view current).1 = (fun _ => False) := by
          funext draw
          exact propext ⟨fun yes => witness yes.2.1,False.elim⟩
        rw [empty,prEvent_false]
        exact bot_le
    _ = _ := by simp

theorem event_monotone {Test Symbol : Type} [DecidableEq Symbol] (profile : Digest) (view : View) (bits : ℕ)
    (raw claimed : State → Test → Fin (2^bits) → Symbol) (distance : ℕ) :
    Monotone (fun fuel => {world | event profile fuel view bits (checked bits view.column.index.count.val raw claimed distance) world}) := by
  intro first second ordered world member
  change event profile first view bits (checked bits view.column.index.count.val raw claimed distance) world at member
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  have complete : (collected profile first view world).1.remaining = 0 := by
    unfold event at member
    cases draws : NativeIndexFirstReadLaw.values bits (view.column.index.request profile).transcript view.column.index.label
        view.column.index.domain view.column.index.count world with
    | none => simp only [draws,Option.elim_none] at member
    | some draw => simp only [draws,Option.elim_some] at member; exact member.1
  have same : (collected profile (first+extra) view world).1 = (collected profile first view world).1 := by
    unfold collected
    rw [NativeFieldVector.execute_add]
    dsimp only
    unfold collected at complete
    rw [NativeFieldVector.execute_complete NativeFields.goldilocksModulus extra _ world complete]
  change event profile (first+extra) view bits (checked bits view.column.index.count.val raw claimed distance) world
  simpa only [event,same] using member

/-- The distance witness is part of the winning event. No premise asserts
that every reachable completed state has a false response. -/
theorem eventual_bound {S A Test Symbol : Type} [DecidableEq Symbol]
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (view : View) (input : Input)
    (parsed : SingleOpeningChallengeLink.parse input = some view)
    (step : S → OracleMachine.Command S A) (world : World)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (bits : ℕ) (power : view.column.index.domain.val = 2^bits)
    (raw claimed : State → Test → Fin (2^bits) → Symbol) (distance : ℕ) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, event profile fuel view bits (checked bits view.column.index.count.val raw claimed distance) other} ≤
      ColumnOpening.missBound (Fin (2^bits)) view.column.index.count.val distance := by
  have union : {other | ∃ fuel, event profile fuel view bits (checked bits view.column.index.count.val raw claimed distance) other} =
      ⋃ fuel : ℕ, {other | event profile fuel view bits (checked bits view.column.index.count.val raw claimed distance) other} := by
    ext other
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union,(event_monotone profile view bits raw claimed distance).measure_iUnion]
  exact iSup_le (fun fuel => conditional_bound replay profile fuel view input parsed step world selected bits power raw claimed distance)

theorem eventual_measurable {P Test Symbol : Type} [DecidableEq Symbol]
    {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (view : View) (bits : ℕ) (raw claimed : State → Test → Fin (2^bits) → Symbol) (distance : ℕ) :
    MeasurableSet {world | ∃ fuel, event profile fuel view bits (checked bits view.column.index.count.val raw claimed distance) world} := by
  have union : {world | ∃ fuel, event profile fuel view bits (checked bits view.column.index.count.val raw claimed distance) world} =
      ⋃ fuel : ℕ, {world | event profile fuel view bits (checked bits view.column.index.count.val raw claimed distance) world} := by
    ext world
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => SingleOpeningFieldColumnLaw.event_measurable replay profile fuel view bits _)
end
end FormalProof4FHE.HasteBoots.SingleOpeningWitnessedColumnBound
