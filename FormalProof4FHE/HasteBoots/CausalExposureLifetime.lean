module

public import FormalProof4FHE.HasteBoots.CausalSeedExposure
@[expose] public section

/-! First-seed exposure risk over all analysis prefixes of an unbounded causal
machine. The same inherited raw history selects its local state and remains
in every target set. The charge is probabilistic risk, not attacker work;
receipt guesses, full native coverage and physical-cost coupling remain open. -/
namespace FormalProof4FHE.HasteBoots.CausalExposureLifetime
open InputIndexedOracle (World law)
open NativeTranscript (Execution Observation)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def history {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) : Execution (S ⊕ A) :=
  past world >>= fun state => OracleProgram.run (OracleMachine.take step fuel (initial state)) world

theorem history_replay {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (fuel : ℕ) :
    ObservationReplay.Replayable (history past initial step fuel) :=
  ObservationReplay.bind_replay replay (fun _ => OracleProgram.run_replay _)

/-- Inherited bad events and all new first-seed exposures accumulate over the actual unbounded causal execution. -/
theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel world).run world}) ≤
      law inherited + ∑' fuel : ℕ, ∫⁻ world, CausalSeedExposure.risk step (history past initial step fuel world).run ∂law := by
  have union : {world | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | CausalSeedExposure.event step (history past initial step fuel world).run world} := by
    ext world
    simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, law {world | CausalSeedExposure.event step (history past initial step fuel world).run world} := measure_iUnion_le _
       _ = _ := by
        congr 1
        funext fuel
        exact CausalSeedExposure.averaged_event step (history_replay replay initial step fuel)
def totalCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : ENNReal :=
  ∑' fuel : ℕ, CausalSeedExposure.risk step (history past initial step fuel world).run

theorem totalCharge_lintegral {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) :
    (∫⁻ world, totalCharge past initial step world ∂law) =
      ∑' fuel : ℕ, ∫⁻ world, CausalSeedExposure.risk step (history past initial step fuel world).run ∂law := by
  exact lintegral_tsum (fun fuel =>
    (OracleExecutionLaw.score_measurable (history_replay replay initial step fuel) (CausalSeedExposure.risk step)).aemeasurable)

theorem lifetime_le_totalCharge {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel world).run world}) ≤
      law inherited + ∫⁻ world, totalCharge past initial step world ∂law := by
  rw [totalCharge_lintegral replay initial step]
  exact lifetime_le replay initial step inherited

theorem history_run {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) :
    (history past initial step fuel world).run =
      ((OracleProgram.run (OracleMachine.take step fuel (initial (past world).run.1)) world).run.1,
       (past world).run.2++(OracleProgram.run (OracleMachine.take step fuel (initial (past world).run.1)) world).run.2) :=
  ObservationReplay.run_bind _ _

/-- Retain the prelude boundary only for posterior conditioning. It is not a native message. -/
def retained {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) : Execution ((P × List Observation) × (S ⊕ A)) :=
  let first := (past world).run
  let second := (OracleProgram.run (OracleMachine.take step fuel (initial first.1)) world).run
  WriterT.mk ((first,second.1),first.2++second.2)

def project {P S A : Type} (packet : ((P × List Observation) × (S ⊕ A)) × List Observation) :
    (S ⊕ A) × List Observation := (packet.1.2,packet.2)

theorem retained_history {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) :
    project (retained past initial step fuel world).run = (history past initial step fuel world).run := by
  rw [history_run]
  rfl

theorem retained_replay {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (fuel : ℕ) :
    ObservationReplay.Replayable (retained past initial step fuel) := by
  constructor
  · intro world
    exact (ObservationReplay.agrees_append _ _ _).mpr
      ⟨replay.truthful world,(OracleProgram.run_replay _).truthful world⟩
  · intro world other truthful
    obtain ⟨earlier,later⟩ := (ObservationReplay.agrees_append _ _ _).mp truthful
    have first := replay.replay world other earlier
    have second := (OracleProgram.run_replay (OracleMachine.take step fuel (initial (past world).run.1))).replay world other later
    change (((past other).run,(OracleProgram.run (OracleMachine.take step fuel (initial (past other).run.1)) other).run.1),
      (past other).run.2++(OracleProgram.run (OracleMachine.take step fuel (initial (past other).run.1)) other).run.2) = _
    rw [first,second]
    rfl

theorem retained_event {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) :
    (law[|{other | (retained past initial step fuel other).run = (retained past initial step fuel world).run}])
      {other | CausalSeedExposure.event step (history past initial step fuel other).run other} =
      CausalSeedExposure.risk step (history past initial step fuel world).run := by
  calc
    _ = (law[|{other | (retained past initial step fuel other).run = (retained past initial step fuel world).run}]) {other | CausalSeedExposure.event step (history past initial step fuel world).run other} := by
      apply NativeShakeProjection.conditional_event_congr (retained_replay replay initial step fuel) world
      intro other same
      rw [← retained_history,← retained_history,same]
    _ = _ := by
      cases selected : CausalSeedExposure.firstRead step (history past initial step fuel world).run with
      | none => simp [CausalSeedExposure.event,CausalSeedExposure.risk,selected]
      | some input =>
        simp only [CausalSeedExposure.event,CausalSeedExposure.risk,selected]
        exact OracleSeedGuessing.fresh_seed_targets (retained_replay replay initial step fuel) world input _
          (CausalSeedExposure.firstRead_fresh step (history past initial step fuel world).run input selected)

theorem conditional_step_event {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (fuel : ℕ) (world : World) :
    (law[|{other | (past other).run = (past world).run}])
      {other | CausalSeedExposure.event step (history past initial step fuel other).run other} =
      ∫⁻ other, CausalSeedExposure.risk step (history past initial step fuel other).run
        ∂law[|{other | (past other).run = (past world).run}] := by
  rw [OracleHistoryComposition.refinement_event replay (retained_replay replay initial step fuel)
    (fun packet => packet.1.1) (fun _ => rfl) world _
    (CausalSeedExposure.event_measurable step (history_replay replay initial step fuel))]
  apply lintegral_congr
  intro current
  exact retained_event replay initial step fuel current

theorem conditional_lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) (inherited : Set World) :
    (law[|{other | (past other).run = (past world).run}])
      (inherited ∪ {other | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel other).run other}) ≤
      (law[|{other | (past other).run = (past world).run}]) inherited +
        ∫⁻ other, totalCharge past initial step other ∂law[|{other | (past other).run = (past world).run}] := by
  have union : {other | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel other).run other} =
      ⋃ fuel : ℕ, {other | CausalSeedExposure.event step (history past initial step fuel other).run other} := by
    ext other
    simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, (law[|{other | (past other).run = (past world).run}])
           {other | CausalSeedExposure.event step (history past initial step fuel other).run other} := measure_iUnion_le _
       _ = _ := by
        simp_rw [conditional_step_event replay initial step _ world]
        exact (lintegral_tsum (fun fuel =>
          (OracleExecutionLaw.score_measurable (history_replay replay initial step fuel) (CausalSeedExposure.risk step)).aemeasurable)).symm
theorem totalCharge_measurable {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) : Measurable (totalCharge past initial step) :=
  Measurable.tsum (fun fuel => OracleExecutionLaw.score_measurable
    (history_replay replay initial step fuel) (CausalSeedExposure.risk step))

theorem lifetime_measurable {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) :
    MeasurableSet {world | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel world).run world} := by
  have union : {world | ∃ fuel, CausalSeedExposure.event step (history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | CausalSeedExposure.event step (history past initial step fuel world).run world} := by
    ext world
    simp
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => CausalSeedExposure.event_measurable step (history_replay replay initial step fuel))

end
end FormalProof4FHE.HasteBoots.CausalExposureLifetime
