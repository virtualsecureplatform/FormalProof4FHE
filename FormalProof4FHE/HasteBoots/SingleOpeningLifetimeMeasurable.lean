module
public import FormalProof4FHE.HasteBoots.SingleOpeningLifetimeSoundness
@[expose] public section

/-! Complete-history replay fixes accepted single-opening work and the
field binding used by the common-source extractor. Failure is measurable
even with arbitrary scheduler and machine-state types. Native sampler
receipts are reconstructed under replay, not assumed world-independent. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningLifetimeMeasurable
open SingleOpeningLifetimeSoundness (Witness Failure)
open NativeGoldPcsExecution (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation Execution)
open InputIndexedOracle (World)
open CausalExposureLifetime (history)
open OracleProgram (run)
open MeasureTheory
noncomputable section

theorem accepted_replay {Memory : Type} (world other : World) (log : List Observation)
    (agrees : ObservationReplay.Agrees other log) (ctx : Context) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (work : NativeGoldPcsWorkers.Prepared)
    (accepted : SingleOpeningAvailability.Accepted world log ctx choose fuel memory work) :
    SingleOpeningAvailability.Accepted other log ctx choose fuel memory work := by
  obtain ⟨framed,completion,parent,executed,status,observed⟩ := accepted
  have same := (OracleProgram.run_replay (NativeGoldPcsProgram.program ctx choose fuel memory)).replay world other
    (fun entry member => agrees entry (observed.subset member))
  exact ⟨framed,completion,parent,by rw [same]; exact executed,status,by rw [same]; exact observed⟩

theorem witness_replay (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (world other : World) (log : List Observation) (agrees : ObservationReplay.Agrees other log)
    (witness : Witness Memory dummy ctx radius world log) : Nonempty (Witness Memory dummy ctx radius other log) := by
  have accepted := accepted_replay world other log agrees witness.candidate witness.choose witness.verifierFuel witness.memory witness.work witness.accepted
  have original := witness.accepted
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,observed⟩ := original
  have origin := NativeGoldPcsProgram.completed_origin witness.candidate witness.choose witness.verifierFuel witness.memory world witness.work completion executed
  let columns := NativeGoldPcsColumns.protocol NativeGoldBlockCode.description witness.candidate.parameters witness.candidate.transcript
    witness.candidate.root witness.candidate.query witness.candidate.claimed witness.candidate.opening witness.candidate.fieldFuel
  have prefixLog : (run columns world).run.2 = (run witness.candidate.prefix world).run.2 := by
    change _ = (run (NativeGoldPcsWorkers.protocol witness.candidate.tables witness.candidate.parameters witness.candidate.transcript
      witness.candidate.root witness.candidate.query witness.candidate.claimed witness.candidate.opening witness.candidate.fieldFuel) world).run.2
    rw [NativeGoldPcsWorkers.run_protocol,NativeGoldPcsEncoding.run_protocol]
  have columnsObserved : (run columns world).run.2.Sublist log := by
    apply List.Sublist.trans _ observed
    rw [origin.log,← prefixLog]
    exact List.sublist_append_left _ _
  have same := (OracleProgram.run_replay columns).replay world other (fun entry member => agrees entry (columnsObserved.subset member))
  have otherColumns : (run columns other).run.1 =
      .columns witness.work.geometry witness.receipt.state witness.work.structured witness.sample := by
    rw [same]
    exact witness.receipt.columns
  obtain ⟨receipt⟩ := SingleOpeningSamplingReceipt.ofSampled witness.candidate other witness.work witness.sample
    ⟨witness.receipt.state,otherColumns,witness.receipt.random,witness.receipt.transcript⟩
  have stateEq : receipt.state = witness.receipt.state := by
    have result := receipt.columns.symm.trans otherColumns
    have projected := congrArg (fun outcome => match outcome with
      | NativeGoldPcsColumns.Outcome.columns _ state _ _ => some state
      | _ => none) result
    exact Option.some.inj projected
  have pendingEq : (SingleOpeningRandomLaw.phase receipt).pending = (SingleOpeningRandomLaw.phase witness.receipt).pending := by
    rw [← (SingleOpeningPreparedChallenge.prepared_header receipt).1,← (SingleOpeningPreparedChallenge.prepared_header witness.receipt).1,stateEq]
  have inputEq := congrArg NativeTranscript.Transcript.input pendingEq
  have phase := (SingleOpeningPreparedChallenge.parsed_origin witness.receipt origin.prepared frames parent valid fits
    witness.responseFits witness.decoded witness.parsed).2.1
  have oldField : SingleOpeningFieldInputView.parse (SingleOpeningRandomLaw.phase witness.receipt).pending.input = some witness.decoded.field := by
    rw [← phase,SingleOpeningFieldInputView.phase_input]
    exact SingleOpeningFirstFieldSource.linked_field_parsed _ witness.decoded witness.parsed
  have acceptedCopy := accepted
  obtain ⟨_,newCompletion,_,newExecuted,_,_⟩ := acceptedCopy
  have newPrepared := (NativeGoldPcsProgram.completed_origin witness.candidate witness.choose witness.verifierFuel witness.memory other witness.work newCompletion newExecuted).prepared
  obtain ⟨context,_,parsed,newPhase,_⟩ := SingleOpeningPreparedChallenge.prepared_link receipt newPrepared frames parent valid fits witness.responseFits
  let decoded := SingleOpeningPreparedChallenge.recovered receipt frames context
  have newField : SingleOpeningFieldInputView.parse (SingleOpeningRandomLaw.phase receipt).pending.input = some decoded.field := by
    rw [← newPhase,SingleOpeningFieldInputView.phase_input]
    exact SingleOpeningFirstFieldSource.linked_field_parsed _ decoded parsed
  rw [inputEq] at newField
  have fieldEq : decoded.field = witness.decoded.field := Option.some.inj (newField.symm.trans oldField)
  have falseClaim : SingleOpeningCausalCoverage.FalseClaim dummy witness.candidate witness.origin decoded log radius := by
    have oldFalse := witness.falseClaim
    unfold SingleOpeningCausalCoverage.FalseClaim SingleOpeningConcreteColumnFamily.source at oldFalse ⊢
    rw [fieldEq]
    exact oldFalse
  exact ⟨{
    candidate := witness.candidate
    sameParameters := witness.sameParameters
    sameProfile := witness.sameProfile
    origin := witness.origin
    choose := witness.choose
    verifierFuel := witness.verifierFuel
    memory := witness.memory
    work := witness.work
    sample := witness.sample
    receipt := receipt
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
  have union : {world | Failure Memory dummy ctx radius past initial step world} = ⋃ fuel : ℕ,
      {world | Nonempty (Witness Memory dummy ctx radius world (history past initial step fuel world).run.2)} := by
    ext world
    simp only [Failure,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => finite_measurable Memory dummy ctx radius replay initial step fuel)

end
end FormalProof4FHE.HasteBoots.SingleOpeningLifetimeMeasurable
