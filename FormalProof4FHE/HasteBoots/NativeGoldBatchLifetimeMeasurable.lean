module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeSoundness
@[expose] public section

/-! Any-batch false-acceptance events are measurable despite arbitrary
scheduler/state types. Complete-history replay fixes the accepted work and
the canonical field view used by the analysis extractor. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeMeasurable
open NativeGoldBatchLifetimeSoundness (Witness Failure)
open NativeGoldBatchPcsProgram (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation Execution)
open InputIndexedOracle (World)
open CausalExposureLifetime (history)
open OracleProgram (run)
open MeasureTheory
noncomputable section

theorem witness_replay (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (world other : World) (log : List Observation) (agrees : ObservationReplay.Agrees other log)
    (witness : Witness Memory dummy ctx radius world log) : Nonempty (Witness Memory dummy ctx radius other log) := by
  have accepted := NativeGoldBatchAnySourceRisk.accepted_replay world other log agrees witness.candidate witness.choose
    witness.verifierFuel witness.memory witness.work witness.accepted
  have original := witness.accepted
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,_⟩ := original
  have prepared := (NativeGoldBatchPcsProgram.completed_origin witness.candidate witness.choose witness.verifierFuel witness.memory world
    witness.work completion executed).prepared
  have phase := (NativeGoldBatchPreparedChallenge.parsed_origin witness.candidate world witness.work prepared frames parent valid fits
    witness.responseFits witness.decoded witness.parsed).2.1
  have oldField : NativeGoldBatchFieldInputView.parse (NativeGoldBatchRandomLaw.phase witness.work).pending.input = some witness.decoded.field := by
    rw [← phase,NativeGoldBatchFieldInputView.phase_input]
    exact NativeGoldBatchFirstFieldSource.linked_field_parsed _ witness.decoded witness.parsed
  have acceptedCopy := accepted
  obtain ⟨_,newCompletion,_,newExecuted,_,_⟩ := acceptedCopy
  have newPrepared := (NativeGoldBatchPcsProgram.completed_origin witness.candidate witness.choose witness.verifierFuel witness.memory other
    witness.work newCompletion newExecuted).prepared
  obtain ⟨context,_,parsed,newPhase,_⟩ := NativeGoldBatchPreparedChallenge.prepared_link witness.candidate other witness.work newPrepared
    frames parent valid fits witness.responseFits
  let decoded := NativeGoldBatchPreparedChallenge.recovered witness.candidate other witness.work frames context
  have newField : NativeGoldBatchFieldInputView.parse (NativeGoldBatchRandomLaw.phase witness.work).pending.input = some decoded.field := by
    rw [← newPhase,NativeGoldBatchFieldInputView.phase_input]
    exact NativeGoldBatchFirstFieldSource.linked_field_parsed _ decoded parsed
  have fieldEq : decoded.field = witness.decoded.field := Option.some.inj (newField.symm.trans oldField)
  have falseClaim : NativeGoldBatchCausalCoverage.FalseClaim dummy witness.candidate witness.primitive witness.work decoded log witness.capacity radius := by
    have oldFalse := witness.falseClaim
    unfold NativeGoldBatchCausalCoverage.FalseClaim NativeGoldBatchConcreteColumnFamily.source at oldFalse ⊢
    rw [fieldEq]
    exact oldFalse
  exact ⟨{
    candidate := witness.candidate
    sameParameters := witness.sameParameters
    sameProfile := witness.sameProfile
    primitive := witness.primitive
    capacity := witness.capacity
    choose := witness.choose
    verifierFuel := witness.verifierFuel
    memory := witness.memory
    work := witness.work
    decoded := decoded
    parsed := parsed
    responseFits := witness.responseFits
    accepted := accepted
    falseClaim := falseClaim }⟩

def HistoryFailure (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ) (log : List Observation) : Prop :=
  ∃ world, Nonempty (Witness Memory dummy ctx radius world log)

theorem witness_iff_history (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (world : World) (log : List Observation) (truthful : ObservationReplay.Agrees world log) :
    Nonempty (Witness Memory dummy ctx radius world log) ↔ HistoryFailure Memory dummy ctx radius log := by
  constructor
  · exact fun witness => ⟨world,witness⟩
  · rintro ⟨other,⟨witness⟩⟩
    exact witness_replay Memory dummy ctx radius other world log truthful witness

theorem finite_measurable {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    {past : World → Execution P} (replay : ObservationReplay.Replayable past) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ) :
    MeasurableSet {world | Nonempty (Witness Memory dummy ctx radius world (history past initial step fuel world).run.2)} := by
  have same : {world | Nonempty (Witness Memory dummy ctx radius world (history past initial step fuel world).run.2)} =
      {world | HistoryFailure Memory dummy ctx radius (history past initial step fuel world).run.2} := by
    ext world
    exact witness_iff_history Memory dummy ctx radius world _ ((CausalExposureLifetime.history_replay replay initial step fuel).truthful world)
  rw [same]
  exact OracleExecutionLaw.event_measurable (CausalExposureLifetime.history_replay replay initial step fuel)
    (fun packet => HistoryFailure Memory dummy ctx radius packet.2)

theorem failure_measurable {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    {past : World → Execution P} (replay : ObservationReplay.Replayable past) (initial : P → S)
    (step : S → OracleMachine.Command S A) : MeasurableSet {world | Failure Memory dummy ctx radius past initial step world} := by
  have union : {world | Failure Memory dummy ctx radius past initial step world} =
      ⋃ fuel : ℕ, {world | Nonempty (Witness Memory dummy ctx radius world (history past initial step fuel world).run.2)} := by
    ext world
    simp only [Failure,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => finite_measurable Memory dummy ctx radius replay initial step fuel)
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeMeasurable
