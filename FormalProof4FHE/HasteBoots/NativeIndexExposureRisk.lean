module
public import FormalProof4FHE.HasteBoots.NativeIndexFirstReadLaw
public import FormalProof4FHE.HasteBoots.CausalExposureLifetime
@[expose] public section

/-! Adaptive native index requests charged at actual first stream reads.
Selection and predicates see only the complete causal history. Invalid or
nonmatching requests contribute no event and no charge. The exact native
result/log is retained. These are probability charges, not physical costs;
protocol-specific selection/coverage and false-acceptance reduction remain
necessary. -/
namespace FormalProof4FHE.HasteBoots.NativeIndexExposureRisk
open InputIndexedOracle (Input World law)
open NativeTranscript (Execution Observation)
open NativePrequeryIndexLaw (Request requestInput outcome)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open CausalExposureLifetime (history history_replay)
open scoped Classical
noncomputable section

abbrev Packet (S A : Type) := (S ⊕ A) × List Observation
abbrev Result := Option NativeIndexRequest.Result × List Observation

def eligible {S A : Type} (step : S → OracleMachine.Command S A) (packet : Packet S A) (request : Request) : Prop :=
  NativeIndexRequest.check request.domain request.count = true ∧
    CausalStreamExposure.firstRead step packet = some (requestInput request.transcript request.label request.domain request.count)

def event {S A : Type} (step : S → OracleMachine.Command S A) (select : Packet S A → Option Request)
    (bad : Packet S A → Result → Prop) (packet : Packet S A) (world : World) : Prop :=
  match select packet with
  | none => False
  | some request => eligible step packet request ∧ bad packet (OracleProgram.run request.program world).run

def risk {S A : Type} (step : S → OracleMachine.Command S A) (select : Packet S A → Option Request)
    (bad : Packet S A → Result → Prop) (packet : Packet S A) : ENNReal :=
  match select packet with
  | none => 0
  | some request => if eligible step packet request then
      Pr{let raw ← $ᵗ (Fin (request.count.val*8) → InputIndexedOracle.Byte)}[
        bad packet (outcome request.transcript request.label request.domain request.count raw)] else 0

/-- Adaptivity changes neither the raw processing nor the complete native
log. Eligibility derives freshness from the real mixed history. -/
theorem conditional_event {S A : Type} (step : S → OracleMachine.Command S A)
    (select : Packet S A → Option Request) (bad : Packet S A → Result → Prop)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event step select bad (past other).run other} =
      risk step select bad (past world).run := by
  calc
    _ = (law[|{other | (past other).run = (past world).run}]) {other | event step select bad (past world).run other} := by
      apply NativeShakeProjection.conditional_event_congr replay world
      intro other same
      rw [same]
    _ = _ := by
      cases selected : select (past world).run with
      | none => simp [event,risk,selected]
      | some request =>
        by_cases valid : eligible step (past world).run request
        · simp only [event,risk,selected,valid,true_and,ite_true]
          exact NativeIndexFirstReadLaw.request_event step replay world request.transcript request.label request.domain request.count valid.1 valid.2 (bad (past world).run)
        · simp [event,risk,selected,valid]

theorem event_measurable {S A : Type} (step : S → OracleMachine.Command S A)
    (select : Packet S A → Option Request) (bad : Packet S A → Result → Prop)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    MeasurableSet {world | event step select bad (past world).run world} := by
  let := OracleHistoryCharge.histories_countable replay
  have fixed (packet : Packet S A) : MeasurableSet {world | event step select bad packet world} := by
    cases selected : select packet with
    | none => simp [event,selected]
    | some request =>
      by_cases valid : eligible step packet request
      · simpa only [event,selected,valid,true_and] using
          OracleExecutionLaw.event_measurable (OracleProgram.run_replay request.program) (bad packet)
      · simp [event,selected,valid]
  have union : {world | event step select bad (past world).run world} = ⋃ packet : OracleHistoryCharge.Histories past,
      OracleHistoryCharge.fiber past packet ∩ {world | event step select bad packet.val world} := by
    ext world
    constructor
    · intro yes
      exact Set.mem_iUnion.mpr ⟨⟨(past world).run,⟨world,rfl⟩⟩,rfl,yes⟩
    · intro yes
      obtain ⟨packet,same,yes⟩ := Set.mem_iUnion.mp yes
      change (past world).run = packet.val at same
      change event step select bad (past world).run world
      rw [same]
      exact yes
  rw [union]
  exact MeasurableSet.iUnion (fun packet => (OracleHistoryCharge.fiber_measurable replay packet).inter (fixed packet.val))

theorem averaged_event {S A : Type} (step : S → OracleMachine.Command S A)
    (select : Packet S A → Option Request) (bad : Packet S A → Result → Prop)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    law {world | event step select bad (past world).run world} =
      ∫⁻ world, risk step select bad (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (event_measurable step select bad replay)]
  exact lintegral_congr (fun world => conditional_event step select bad replay world)

def totalCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (select : Packet S A → Option Request)
    (bad : Packet S A → Result → Prop) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk step select bad (history past initial step fuel world).run

/-- Arbitrary quotas and responses selected from each real prefix are
averaged over their full history mass, over the unbounded machine lifetime. -/
theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (select : Packet S A → Option Request)
    (bad : Packet S A → Result → Prop) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, event step select bad (history past initial step fuel world).run world}) ≤
      law inherited + ∫⁻ world, totalCharge past initial step select bad world ∂law := by
  have union : {world | ∃ fuel, event step select bad (history past initial step fuel world).run world} =
      ⋃ fuel : ℕ, {world | event step select bad (history past initial step fuel world).run world} := by ext world; simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc _ ≤ ∑' fuel : ℕ, law {world | event step select bad (history past initial step fuel world).run world} := measure_iUnion_le _
       _ = ∑' fuel : ℕ, ∫⁻ world, risk step select bad (history past initial step fuel world).run ∂law := by
         congr 1
         funext fuel
         exact averaged_event step select bad (history_replay replay initial step fuel)
       _ = _ := (lintegral_tsum (fun fuel =>
          (OracleExecutionLaw.score_measurable (history_replay replay initial step fuel) (risk step select bad)).aemeasurable)).symm

/-- The charge for all shared checks has one witness miss bound, even when
there are arbitrarily many groups. The request quota retains duplicates. -/
theorem shared_risk_bound {S A Test Symbol : Type} [DecidableEq Symbol]
    (step : S → OracleMachine.Command S A) (select : Packet S A → Option Request)
    (packet : Packet S A) (request : Request) (selected : select packet = some request)
    (valid : eligible step packet request) (bits : ℕ) (power : request.domain.val = 2^bits)
    (raw claimed : Test → Fin (2^bits) → Symbol) (distance : ℕ)
    (witness : ∃ test, distance ≤ hammingDist (raw test) (claimed test)) :
    risk step select (fun _ result => (result.1.bind (fun sample =>
      NativeGoldPcsDraws.typed bits request.count.val sample.draws)).elim False
        (fun draw => ∀ test, ColumnOpening.Agrees (raw test) (claimed test) draw)) packet ≤
      ColumnOpening.missBound (Fin (2^bits)) request.count.val distance := by
  have fits : bits ≤ 64 := by
    have bounded : 2^bits < 2^64 := power ▸ request.domain.isLt
    have small := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp bounded
    omega
  simp only [risk,selected,valid,ite_true,outcome,Option.bind_some,power,
    NativeIndexRequest.ordered_ofFn,NativeIndexFirstReadLaw.typed_ofFn,Option.elim_some]
  rw [NativeAtomicIndexLaw.uniform_draws bits request.count.val fits
    (fun draw => ∀ test, ColumnOpening.Agrees (raw test) (claimed test) draw)]
  exact ColumnOpening.shared_bound raw claimed request.count.val distance witness

theorem totalCharge_measurable {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (select : Packet S A → Option Request)
    (bad : Packet S A → Result → Prop) : Measurable (totalCharge past initial step select bad) :=
  Measurable.tsum (fun fuel => OracleExecutionLaw.score_measurable (history_replay replay initial step fuel) (risk step select bad))
end
end FormalProof4FHE.HasteBoots.NativeIndexExposureRisk
