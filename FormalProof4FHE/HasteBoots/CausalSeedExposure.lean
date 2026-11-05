module

public import FormalProof4FHE.HasteBoots.NativeChildSeedView
@[expose] public section

/-! The pending request and orphan-seed target set are selected from the
complete causal past. Eligible first reads have a full512-bit conditional
seed bound, then exact averaging over actual histories. This is a new
exposure event; inherited failures, parent/helper association, receipt
guesses and attacker-work coupling remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.CausalSeedExposure
open InputIndexedOracle (World Input law)
open NativeTranscript (Execution Observation)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def request {S A : Type} (step : S → OracleMachine.Command S A) : S ⊕ A → Option OracleProgram.Request
  | .inr _ => none
  | .inl state => match step state with
    | .done _ => none
    | .start input _ => some (.start input)
    | .read input offset count _ => some (.read input offset count)
    | .hash input _ => some (.hash input)

def firstRead {S A : Type} (step : S → OracleMachine.Command S A) (history : (S ⊕ A) × List Observation) : Option Input :=
  match request step history.1 with
  | some (.read input offset count) =>
    if 0 < count ∧ offset < 64 ∧ OracleFirstExposure.locate history.2 (OracleFirstExposure.seedCoordinates input) = none then
      some input else none
  | _ => none

theorem firstRead_fresh {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List Observation) (input : Input) (selected : firstRead step history = some input) :
    ∀ position : Fin 64, (.inl (input,position.val) : InputIndexedOracle.Coordinate) ∉
      ObservationReplay.footprint history.2 := by
  unfold firstRead at selected
  split at selected <;> simp at selected
  obtain ⟨accepted,rfl⟩ := selected
  exact (OracleFirstExposure.seed_none _ _).mp accepted.2.2

def event {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List Observation) (world : World) : Prop :=
  match firstRead step history with
  | some input => InputIndexedOracle.block world input 0 64 ∈ NativeChildSeedView.guesses history.2
  | none => False

def risk {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List Observation) : ENNReal :=
  match firstRead step history with
  | some _ => ((NativeChildSeedView.guesses history.2).card : ENNReal)/(2 : ENNReal)^512
  | none => 0

theorem conditional_event {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event step (past other).run other} =
      risk step (past world).run := by
  calc _ = (law[|{other | (past other).run = (past world).run}]) {other | event step (past world).run other} := by
        apply NativeShakeProjection.conditional_event_congr replay world
        intro other same
        rw [same]
       _ = _ := by
        cases selected : firstRead step (past world).run with
        | none => simp [event,risk,selected]
        | some input =>
          simp only [event,risk,selected]
          exact OracleSeedGuessing.fresh_seed_targets replay world input _
            (firstRead_fresh step (past world).run input selected)


theorem event_measurable {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    MeasurableSet {world | event step (past world).run world} := by
  let := OracleHistoryCharge.histories_countable replay
  have fixed (history : (S ⊕ A) × List Observation) : MeasurableSet {world | event step history world} := by
    cases selected : firstRead step history with
    | none => simp [event,selected]
    | some input =>
      simpa only [event,selected,Set.preimage,Finset.mem_coe] using
        (InputIndexedOracle.block_measurable input 0 64) (NativeChildSeedView.guesses history.2).measurableSet
  have union : {world | event step (past world).run world} =
      ⋃ history : OracleHistoryCharge.Histories past,
        OracleHistoryCharge.fiber past history ∩ {world | event step history.val world} := by
    ext world
    constructor
    · intro yes
      exact Set.mem_iUnion.mpr ⟨⟨(past world).run,⟨world,rfl⟩⟩,rfl,yes⟩
    · intro yes
      obtain ⟨history,same,yes⟩ := Set.mem_iUnion.mp yes
      change (past world).run = history.val at same
      change event step (past world).run world
      rw [same]
      exact yes
  rw [union]
  exact MeasurableSet.iUnion (fun history => (OracleHistoryCharge.fiber_measurable replay history).inter (fixed history.val))

theorem averaged_event {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    law {world | event step (past world).run world} = ∫⁻ world, risk step (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (event_measurable step replay)]
  apply lintegral_congr
  intro world
  exact conditional_event step replay world

end
end FormalProof4FHE.HasteBoots.CausalSeedExposure
