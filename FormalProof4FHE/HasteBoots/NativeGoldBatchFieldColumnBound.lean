module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFieldColumnLaw
@[expose] public section

/-! One shared-column loss after actual native field collection. The test
family may depend on every collected field value. Only completed outcomes
can win; their union over all budgets has no retry or group/lane factor.
The application must still derive the disagreement witness from its source. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFieldColumnBound
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeTranscript (Execution)
open NativeGoldBatchChallengeLink (View)
open NativeFieldVector (State)
open NativeGoldBatchFieldColumnLaw (collected event)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def agrees {Test Symbol : Type} (bits count : ℕ)
    (raw claimed : State → Test → Fin (2^bits) → Symbol)
    (state : State) (draw : Fin count → Fin (2^bits)) : Prop :=
  state.remaining = 0 ∧ ∀ test, ColumnOpening.Agrees (raw state test) (claimed state test) draw

theorem conditional_bound {S A Test Symbol : Type} [DecidableEq Symbol]
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (fuel : ℕ) (view : View) (input : Input)
    (parsed : NativeGoldBatchChallengeLink.parse input = some view)
    (step : S → OracleMachine.Command S A) (world : World)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (bits : ℕ) (power : view.column.index.domain.val = 2^bits)
    (raw claimed : State → Test → Fin (2^bits) → Symbol) (distance : ℕ)
    (witness : ∀ current, (past current).run = (past world).run →
      (collected profile fuel view current).1.remaining = 0 →
      ∃ test, distance ≤ hammingDist (raw (collected profile fuel view current).1 test)
        (claimed (collected profile fuel view current).1 test)) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event profile fuel view bits (agrees bits view.column.index.count.val raw claimed) other} ≤
      ColumnOpening.missBound (Fin (2^bits)) view.column.index.count.val distance := by
  have positive : law {other | (past other).run = (past world).run} ≠ 0 := by
    rw [ObservationReplay.fiber_eq_assignment replay world]
    exact OraclePosterior.assignment_ne_zero _ _
  let := cond_isProbabilityMeasure (μ := law) positive
  rw [NativeGoldBatchFieldColumnLaw.conditional_uniform replay profile fuel view input parsed step world selected bits power]
  calc
    _ ≤ ∫⁻ _current, ColumnOpening.missBound (Fin (2^bits)) view.column.index.count.val distance
        ∂law[|{other | (past other).run = (past world).run}] := by
      apply lintegral_mono_ae
      filter_upwards [ae_cond_mem (μ := law) (ObservationReplay.fiber_measurable replay world)] with current same
      by_cases complete : (collected profile fuel view current).1.remaining = 0
      · have equal : agrees bits view.column.index.count.val raw claimed (collected profile fuel view current).1 =
            (fun draw => ∀ test, ColumnOpening.Agrees (raw (collected profile fuel view current).1 test)
              (claimed (collected profile fuel view current).1 test) draw) := by
          funext draw
          exact propext (and_iff_right complete)
        rw [equal]
        exact ColumnOpening.shared_bound (raw (collected profile fuel view current).1)
          (claimed (collected profile fuel view current).1) view.column.index.count.val distance (witness current same complete)
      · have empty : agrees bits view.column.index.count.val raw claimed (collected profile fuel view current).1 =
            (fun _ => False) := by
          funext draw
          exact propext ⟨fun yes => complete yes.1,False.elim⟩
        rw [empty,prEvent_false]
        exact bot_le
    _ = _ := by simp

theorem event_monotone {Test Symbol : Type} (profile : Digest) (view : View) (bits : ℕ)
    (raw claimed : State → Test → Fin (2^bits) → Symbol) :
    Monotone (fun fuel => {world | event profile fuel view bits (agrees bits view.column.index.count.val raw claimed) world}) := by
  intro first second ordered world member
  change event profile first view bits (agrees bits view.column.index.count.val raw claimed) world at member
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
  change event profile (first+extra) view bits (agrees bits view.column.index.count.val raw claimed) world
  simpa only [event,same] using member

/-- All collector budgets share the same matrix, raw responses and ordered
column vector once complete. There is no union-bound factor for budgets. -/
theorem eventual_bound {S A Test Symbol : Type} [DecidableEq Symbol]
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (profile : Digest) (view : View) (input : Input)
    (parsed : NativeGoldBatchChallengeLink.parse input = some view)
    (step : S → OracleMachine.Command S A) (world : World)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (bits : ℕ) (power : view.column.index.domain.val = 2^bits)
    (raw claimed : State → Test → Fin (2^bits) → Symbol) (distance : ℕ)
    (witness : ∀ fuel current, (past current).run = (past world).run →
      (collected profile fuel view current).1.remaining = 0 →
      ∃ test, distance ≤ hammingDist (raw (collected profile fuel view current).1 test)
        (claimed (collected profile fuel view current).1 test)) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, event profile fuel view bits (agrees bits view.column.index.count.val raw claimed) other} ≤
      ColumnOpening.missBound (Fin (2^bits)) view.column.index.count.val distance := by
  have union : {other | ∃ fuel, event profile fuel view bits (agrees bits view.column.index.count.val raw claimed) other} =
      ⋃ fuel : ℕ, {other | event profile fuel view bits (agrees bits view.column.index.count.val raw claimed) other} := by
    ext other
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union,(event_monotone profile view bits raw claimed).measure_iUnion]
  exact iSup_le (fun fuel => conditional_bound replay profile fuel view input parsed step world selected bits power raw claimed distance (witness fuel))
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFieldColumnBound
