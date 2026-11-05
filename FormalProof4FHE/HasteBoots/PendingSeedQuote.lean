module

public import FormalProof4FHE.HasteBoots.CausalExposureCoverage
@[expose] public section

/-! A seed quote in the pending complete input is fixed before the first
logical seed hit, even when it was absent from prior raw observations.
Its risk is bounded separately and combined with the prior-quote ledger.
Partial seeds, receipts and attacker-work coupling remain separate. -/
namespace FormalProof4FHE.HasteBoots.PendingSeedQuote
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation Execution)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open CausalExposureLifetime (history history_replay retained retained_history retained_replay)
noncomputable section

def event {S A : Type} (step : S → OracleMachine.Command S A) (history : (S ⊕ A) × List Observation) (world : World) : Prop :=
  match CausalSeedExposure.firstRead step history with
  | none => False
  | some input => match NativeChildSeedView.quote input with
    | none => False
    | some seed => InputIndexedOracle.block world input 0 64 = seed

def risk {S A : Type} (step : S → OracleMachine.Command S A) (history : (S ⊕ A) × List Observation) : ENNReal :=
  match CausalSeedExposure.firstRead step history with
  | none => 0
  | some input => match NativeChildSeedView.quote input with
    | none => 0
    | some _ => 1/(2 : ENNReal)^512

theorem conditional_event {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event step (past other).run other} = risk step (past world).run := by
  calc
    _ = (law[|{other | (past other).run = (past world).run}]) {other | event step (past world).run other} := by
      apply NativeShakeProjection.conditional_event_congr replay world
      intro other same
      rw [same]
    _ = _ := by
      cases selected : CausalSeedExposure.firstRead step (past world).run with
      | none => simp [event,risk,selected]
      | some input =>
        cases quoted : NativeChildSeedView.quote input with
        | none => simp [event,risk,selected,quoted]
        | some seed =>
          simp only [event,risk,selected,quoted]
          simpa only [Finset.card_singleton,Finset.mem_singleton,Nat.cast_one] using
            OracleSeedGuessing.fresh_seed_targets replay world input {seed}
              (CausalSeedExposure.firstRead_fresh step (past world).run input selected)

theorem event_measurable {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    MeasurableSet {world | event step (past world).run world} := by
  let := OracleHistoryCharge.histories_countable replay
  have fixed (history : (S ⊕ A) × List Observation) : MeasurableSet {world | event step history world} := by
    cases selected : CausalSeedExposure.firstRead step history with
    | none => simp [event,selected]
    | some input =>
      cases quoted : NativeChildSeedView.quote input with
      | none => simp [event,selected,quoted]
      | some seed =>
        simpa only [event,selected,quoted,Set.preimage,Finset.mem_coe,Finset.mem_singleton] using
          (InputIndexedOracle.block_measurable input 0 64) ({seed} : Finset NativeRootMessage.Digest).measurableSet
  have union : {world | event step (past world).run world} = ⋃ history : OracleHistoryCharge.Histories past,
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
  exact lintegral_congr (fun world => conditional_event step replay world)
theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, PendingSeedQuote.event step (history past initial step fuel world).run world}) ≤
      law inherited + ∑' fuel : ℕ, ∫⁻ world, PendingSeedQuote.risk step (history past initial step fuel world).run ∂law := by
  have union : {world | ∃ fuel, PendingSeedQuote.event step (history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | PendingSeedQuote.event step (history past initial step fuel world).run world} := by
    ext world
    simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, law {world | PendingSeedQuote.event step (history past initial step fuel world).run world} := measure_iUnion_le _
       _ = _ := by
        congr 1
        funext fuel
        exact PendingSeedQuote.averaged_event step (history_replay replay initial step fuel)
def totalCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : ENNReal :=
  ∑' fuel : ℕ, PendingSeedQuote.risk step (history past initial step fuel world).run

theorem totalCharge_lintegral {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) :
    (∫⁻ world, totalCharge past initial step world ∂law) =
      ∑' fuel : ℕ, ∫⁻ world, PendingSeedQuote.risk step (history past initial step fuel world).run ∂law := by
  exact lintegral_tsum (fun fuel =>
    (OracleExecutionLaw.score_measurable (history_replay replay initial step fuel) (PendingSeedQuote.risk step)).aemeasurable)

theorem lifetime_le_totalCharge {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, PendingSeedQuote.event step (history past initial step fuel world).run world}) ≤
      law inherited + ∫⁻ world, totalCharge past initial step world ∂law := by
  rw [totalCharge_lintegral replay initial step]
  exact lifetime_le replay initial step inherited


theorem retained_event {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) :
    (law[|{other | (retained past initial step fuel other).run = (retained past initial step fuel world).run}])
      {other | event step (history past initial step fuel other).run other} =
      risk step (history past initial step fuel world).run := by
  calc
    _ = (law[|{other | (retained past initial step fuel other).run = (retained past initial step fuel world).run}]) {other | event step (history past initial step fuel world).run other} := by
      apply NativeShakeProjection.conditional_event_congr (retained_replay replay initial step fuel) world
      intro other same
      rw [← retained_history,← retained_history,same]
    _ = _ := by
      cases selected : CausalSeedExposure.firstRead step (history past initial step fuel world).run with
      | none => simp [event,risk,selected]
      | some input =>
        cases quoted : NativeChildSeedView.quote input with
        | none => simp [event,risk,selected,quoted]
        | some seed =>
          simp only [event,risk,selected,quoted]
          simpa only [Finset.card_singleton,Finset.mem_singleton,Nat.cast_one] using
            OracleSeedGuessing.fresh_seed_targets (retained_replay replay initial step fuel) world input {seed}
              (CausalSeedExposure.firstRead_fresh step (history past initial step fuel world).run input selected)
theorem conditional_step_event {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) :
    (law[|{other | (past other).run = (past world).run}])
      {other | PendingSeedQuote.event step (history past initial step fuel other).run other} =
      ∫⁻ other, PendingSeedQuote.risk step (history past initial step fuel other).run
        ∂law[|{other | (past other).run = (past world).run}] := by
  rw [OracleHistoryComposition.refinement_event replay (retained_replay replay initial step fuel)
    (fun packet => packet.1.1) (fun _ => rfl) world _
    (PendingSeedQuote.event_measurable step (history_replay replay initial step fuel))]
  apply lintegral_congr
  intro current
  exact retained_event replay initial step fuel current

theorem conditional_lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) (inherited : Set World) :
    (law[|{other | (past other).run = (past world).run}])
      (inherited ∪ {other | ∃ fuel, PendingSeedQuote.event step (history past initial step fuel other).run other}) ≤
      (law[|{other | (past other).run = (past world).run}]) inherited +
        ∫⁻ other, totalCharge past initial step other ∂law[|{other | (past other).run = (past world).run}] := by
  have union : {other | ∃ fuel, PendingSeedQuote.event step (history past initial step fuel other).run other} =
      ⋃ fuel : ℕ, {other | PendingSeedQuote.event step (history past initial step fuel other).run other} := by
    ext other
    simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, (law[|{other | (past other).run = (past world).run}])
           {other | PendingSeedQuote.event step (history past initial step fuel other).run other} := measure_iUnion_le _
       _ = _ := by
        simp_rw [conditional_step_event replay initial step _ world]
        exact (lintegral_tsum (fun fuel =>
          (OracleExecutionLaw.score_measurable (history_replay replay initial step fuel) (PendingSeedQuote.risk step)).aemeasurable)).symm
theorem totalCharge_measurable {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) : Measurable (totalCharge past initial step) :=
  Measurable.tsum (fun fuel => OracleExecutionLaw.score_measurable
    (history_replay replay initial step fuel) (PendingSeedQuote.risk step))

theorem lifetime_measurable {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) :
    MeasurableSet {world | ∃ fuel, PendingSeedQuote.event step (history past initial step fuel world).run world} := by
  have union : {world | ∃ fuel, PendingSeedQuote.event step (history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | PendingSeedQuote.event step (history past initial step fuel world).run world} := by
    ext world
    simp
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => PendingSeedQuote.event_measurable step (history_replay replay initial step fuel))

/-- Prior and pending-input quotes accumulate on the same complete execution, retaining inherited bad probability. -/
theorem combined_lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel world).run world ∨
      event step (history past initial step fuel world).run world}) ≤
      law inherited + (∫⁻ world, CausalExposureLifetime.totalCharge past initial step world ∂law) +
        ∫⁻ world, totalCharge past initial step world ∂law := by
  have union : {world | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel world).run world ∨
      event step (history past initial step fuel world).run world} =
      {world | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel world).run world} ∪
      {world | ∃ fuel, event step (history past initial step fuel world).run world} := by
    ext world
    constructor
    · rintro ⟨fuel,old | new⟩
      · exact Or.inl ⟨fuel,old⟩
      · exact Or.inr ⟨fuel,new⟩
    · rintro (⟨fuel,old⟩ | ⟨fuel,new⟩)
      · exact ⟨fuel,Or.inl old⟩
      · exact ⟨fuel,Or.inr new⟩
  rw [union,← Set.union_assoc]
  exact (lifetime_le_totalCharge replay initial step _).trans
    (add_le_add (CausalExposureLifetime.lifetime_le_totalCharge replay initial step inherited) le_rfl)

theorem conditional_combined_lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) (inherited : Set World) :
    (law[|{other | (past other).run = (past world).run}])
      (inherited ∪ {other | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel other).run other ∨
        event step (history past initial step fuel other).run other}) ≤
      (law[|{other | (past other).run = (past world).run}]) inherited +
        (∫⁻ other, CausalExposureLifetime.totalCharge past initial step other ∂law[|{other | (past other).run = (past world).run}]) +
        ∫⁻ other, totalCharge past initial step other ∂law[|{other | (past other).run = (past world).run}] := by
  have union : {other | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel other).run other ∨
      event step (history past initial step fuel other).run other} =
      {other | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel other).run other} ∪
      {other | ∃ fuel, event step (history past initial step fuel other).run other} := by
    ext other
    constructor
    · rintro ⟨fuel,old | new⟩
      · exact Or.inl ⟨fuel,old⟩
      · exact Or.inr ⟨fuel,new⟩
    · rintro (⟨fuel,old⟩ | ⟨fuel,new⟩)
      · exact ⟨fuel,Or.inl old⟩
      · exact ⟨fuel,Or.inr new⟩
  rw [union,← Set.union_assoc]
  exact (conditional_lifetime_le replay initial step world _).trans
    (add_le_add (CausalExposureLifetime.conditional_lifetime_le replay initial step world inherited) le_rfl)
end
end FormalProof4FHE.HasteBoots.PendingSeedQuote
