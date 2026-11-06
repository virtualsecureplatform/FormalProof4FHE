module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnBound
@[expose] public section

/-! Causal selection and unbounded lifetime charging for the concrete native
random/structured column event. The full pending input supplies the parsed
responses; the old history supplies the first-field source. Early receipts,
application event coverage and physical work remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnExposure
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBatchChallengeLink (View)
open NativeGoldBlockCode (logSize)
open NativeRootMessage (Digest)
open NativeTranscript (Execution)
open NativeIndexExposureRisk (Packet)
open InputIndexedOracle (Input World law)
open CausalExposureLifetime (history history_replay)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def select {S A : Type} (ctx : Context) (step : S → OracleMachine.Command S A) (packet : Packet S A) : Option View := do
  let input ← CausalStreamExposure.firstRead step packet
  let decoded ← NativeGoldBatchChallengeLink.parse input
  if decoded.column.index.label = NativeGoldBatchColumns.label ∧ 0 < decoded.column.index.count.val ∧
      decoded.column.index.domain.val = 2^(logSize ctx.parameters.code) then some decoded else none

theorem selected_link {S A : Type} (ctx : Context) (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (decoded : View) (selected : select ctx step packet = some decoded) :
    ∃ input, CausalStreamExposure.firstRead step packet = some input ∧ NativeGoldBatchChallengeLink.parse input = some decoded ∧
      decoded.column.index.label = NativeGoldBatchColumns.label ∧ 0 < decoded.column.index.count.val ∧
      decoded.column.index.domain.val = 2^(logSize ctx.parameters.code) := by
  unfold select at selected
  obtain ⟨input,first,chosen⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨view,parsed,chosen⟩ := Option.bind_eq_some_iff.mp chosen
  split at chosen
  next valid =>
    have equal := Option.some.inj chosen
    subst decoded
    exact ⟨input,first,parsed,valid⟩
  next => contradiction

def event {S A : Type} (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (profile : Digest) (step : S → OracleMachine.Command S A) (packet : Packet S A) (radius : ℕ) (world : World) : Prop :=
  match select ctx step packet with
  | none => False
  | some decoded => NativeGoldBatchConcreteColumnBound.event dummy ctx primitive profile decoded packet.2 radius world

def risk {S A : Type} (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (step : S → OracleMachine.Command S A) (packet : Packet S A) (radius : ℕ) : ENNReal :=
  match select ctx step packet with
  | none => 0
  | some decoded => match NativeGoldBatchFirstFieldSource.recover dummy packet.2 decoded.field with
    | none => 0
    | some _ => ColumnOpening.missBound (NativeGoldBatchConcreteColumnFamily.Position ctx) decoded.column.index.count.val
        (NativeGoldBatchConcreteColumnBound.distance ctx primitive radius)

theorem conditional_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (profile : Digest) (step : S → OracleMachine.Command S A) (world : World) (radius : ℕ) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event dummy ctx primitive profile step (past other).run radius other} ≤ risk dummy ctx primitive step (past world).run radius := by
  calc
    _ = (law[|{other | (past other).run = (past world).run}])
        {other | event dummy ctx primitive profile step (past world).run radius other} := by
      apply NativeShakeProjection.conditional_event_congr replay world
      intro other same
      rw [same]
    _ ≤ _ := by
      cases chosen : select ctx step (past world).run with
      | none => simp only [event,risk,chosen,Set.ofPred_false,measure_empty,le_refl]
      | some decoded =>
        obtain ⟨input,first,parsed,_,_,power⟩ := selected_link ctx step (past world).run decoded chosen
        simp only [event,risk,chosen]
        cases found : NativeGoldBatchFirstFieldSource.recover dummy (past world).run.2 decoded.field with
        | none => simp only [NativeGoldBatchConcreteColumnBound.event,found,Set.ofPred_false,measure_empty,le_refl]
        | some sourceLog =>
          exact NativeGoldBatchConcreteColumnBound.conditional_bound replay dummy ctx primitive profile decoded input parsed step world first power radius

theorem event_measurable {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (profile : Digest) (step : S → OracleMachine.Command S A) (radius : ℕ) :
    MeasurableSet {world | event dummy ctx primitive profile step (past world).run radius world} := by
  apply OracleProgramHistory.event_measurable replay (fun packet world => event dummy ctx primitive profile step packet radius world)
  intro packet
  cases chosen : select ctx step packet with
  | none => simp only [event,chosen,Set.ofPred_false]; exact MeasurableSet.empty
  | some decoded =>
    simp only [event,chosen]
    exact NativeGoldBatchConcreteColumnBound.fixed_measurable replay dummy ctx primitive profile decoded packet.2 radius

theorem averaged_bound {S A : Type} {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (profile : Digest) (step : S → OracleMachine.Command S A) (radius : ℕ) :
    law {world | event dummy ctx primitive profile step (past world).run radius world} ≤
      ∫⁻ world, risk dummy ctx primitive step (past world).run radius ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (event_measurable replay dummy ctx primitive profile step radius)]
  exact lintegral_mono (fun world => conditional_bound replay dummy ctx primitive profile step world radius)

def totalCharge {P S A : Type} (past : World → Execution P) (initial : P → S) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (step : S → OracleMachine.Command S A) (radius : ℕ) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk dummy ctx primitive step (history past initial step fuel world).run radius

/-- One charge per eligible complete-input first exposure over the entire
causal lifetime. Collector budgets remain inside each event, with no cap. -/
theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (profile : Digest) (step : S → OracleMachine.Command S A) (radius : ℕ) (inherited : Set World) :
    law (inherited ∪ {world | ∃ fuel, event dummy ctx primitive profile step (history past initial step fuel world).run radius world}) ≤
      law inherited + ∫⁻ world, totalCharge past initial dummy ctx primitive step radius world ∂law := by
  have union : {world | ∃ fuel, event dummy ctx primitive profile step (history past initial step fuel world).run radius world} =
      ⋃ fuel : ℕ, {world | event dummy ctx primitive profile step (history past initial step fuel world).run radius world} := by ext world; simp
  rw [union]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑' fuel : ℕ, law {world | event dummy ctx primitive profile step (history past initial step fuel world).run radius world} := measure_iUnion_le _
    _ ≤ ∑' fuel : ℕ, ∫⁻ world, risk dummy ctx primitive step (history past initial step fuel world).run radius ∂law :=
      ENNReal.tsum_le_tsum (fun fuel => averaged_bound (history_replay replay initial step fuel) dummy ctx primitive profile step radius)
    _ = _ := (lintegral_tsum (fun fuel =>
      (OracleExecutionLaw.score_measurable (history_replay replay initial step fuel) (fun packet => risk dummy ctx primitive step packet radius)).aemeasurable)).symm
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnExposure
