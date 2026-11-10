module
public import FormalProof4FHE.HasteBoots.SingleOpeningPreparedChallenge
public import FormalProof4FHE.HasteBoots.CausalStreamLineage
@[expose] public section

/-! Accepted single openings expose their actual field and column inputs in
the shared complete history. Exact first-read packets and inherited exposures
are derived, not supplied. This is stream coverage, not false-claim soundness. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningChallengeHistory
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (description)
open NativeTranscript (Observation Execution)
open InputIndexedOracle (Input World bytes)
open SingleOpeningSamplingReceipt (Receipt)
open OracleProgram (run)
noncomputable section
variable {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}

theorem prepared_column_log (receipt : Receipt ctx world work sample) :
    (run (NativeIndexRequest.request (SingleOpeningColumnLaw.transcript receipt world) NativeGoldPcsColumns.label
      ctx.parameters.code.blocks ctx.parameters.queries) world).run.2.Sublist (run ctx.prefix world).run.2 := by
  obtain ⟨next,prelude,columnsLog⟩ := NativeGoldPcsColumns.columns_observations description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work.geometry receipt.state work.structured sample receipt.columns
  have nextEq : next = receipt.next :=
    (NativeFieldVector.Status.finished.inj (NativeGoldPcsPrelude.Outcome.sampling.inj (prelude.symm.trans receipt.prelude)).2).2
  change List.Sublist _ (run (NativeGoldPcsWorkers.protocol ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel) world).run.2
  rw [NativeGoldPcsWorkers.run_protocol,NativeGoldPcsEncoding.run_protocol,columnsLog,nextEq,receipt.finished_parent]
  rw [NativePrequeryIndexLaw.request_run world _ _ _ _ (SingleOpeningColumnLaw.prepared_check receipt)]
  exact List.sublist_append_right _ _

theorem prepared_field_log (receipt : Receipt ctx world work sample) :
    (run (NativePrimeRequest.request NativeFields.goldilocksModulus ctx.fieldFuel receipt.bound .vector NativeGoldPcsPrelude.randomLabel work.geometry.randomCount) world).run.2.Sublist
      (run ctx.prefix world).run.2 := by
  obtain ⟨_,_,columnsLog⟩ := NativeGoldPcsColumns.columns_observations description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work.geometry receipt.state work.structured sample receipt.columns
  obtain ⟨built,shape,_,_,_⟩ := NativeGoldPcsPrelude.sampling_origin description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work.geometry (.finished receipt.state receipt.next) receipt.prelude
  have preludeLog : (run (NativeGoldPcsPrelude.protocol description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel) world).run.2 =
      (run (NativeGoldPcsBinding.protocol description.row ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed) world).run.2 ++
      (run (NativePrimeRequest.request NativeFields.goldilocksModulus ctx.fieldFuel receipt.bound .vector NativeGoldPcsPrelude.randomLabel work.geometry.randomCount) world).run.2 := by
    rw [NativeGoldPcsPrelude.run_protocol]
    simp only [built,ite_eq_left shape,receipt.binding,NativeGoldPcsPrelude.sample]
  change List.Sublist _ (run (NativeGoldPcsWorkers.protocol ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel) world).run.2
  rw [NativeGoldPcsWorkers.run_protocol,NativeGoldPcsEncoding.run_protocol,columnsLog,preludeLog]
  exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)

theorem prepared_column_read (receipt : Receipt ctx world work sample) :
    .output (SingleOpeningColumnLaw.input receipt world) 0 (bytes world (SingleOpeningColumnLaw.input receipt world) 0 (ctx.parameters.queries.val*8)) ∈
      (run ctx.prefix world).run.2 := by
  apply (prepared_column_log receipt).subset
  rw [NativePrequeryIndexLaw.request_run world _ _ _ _ (SingleOpeningColumnLaw.prepared_check receipt)]
  simp only [NativePrequeryIndexLaw.outcome,List.mem_cons,List.not_mem_nil,or_false]
  right
  rfl

theorem prepared_field_read (receipt : Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    .output (SingleOpeningRandomLaw.phase receipt).pending.input 0 (bytes world (SingleOpeningRandomLaw.phase receipt).pending.input 0 8) ∈
      (run ctx.prefix world).run.2 := by
  have dims := SingleOpeningRectangularData.dimensions ctx world work prepared
  have positive : work.geometry.randomCount.val ≠ 0 := by
    rw [SingleOpeningRandomLaw.count prepared,dims.2.2]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) dims.1) dims.1
  have read := NativePrimeReadExposure.finished_read NativeFields.goldilocksModulus ctx.fieldFuel receipt.bound .vector NativeGoldPcsPrelude.randomLabel
    work.geometry.randomCount positive world receipt.state receipt.next receipt.field
  have width : CanonicalByteSampler.byteCount NativeFields.goldilocksModulus = 8 := by decide +kernel
  rw [width] at read
  exact (prepared_field_log receipt).subset read

theorem seen_of_output (input : Input) (offset : ℕ) (values : Input) (log : List Observation)
    (member : .output input offset values ∈ log) (positive : values ≠ []) : CausalStreamExposure.seen log input = true := by
  apply List.any_eq_true.mpr
  refine ⟨_,member,?_⟩
  simp only [CausalStreamExposure.touches,decide_eq_true_eq,true_and]
  exact List.length_pos_iff.mpr positive

theorem accepted_exposures {Memory : Type} (receipt : Receipt ctx world work sample) (history : List Observation)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : SingleOpeningAvailability.Accepted world history ctx choose fuel memory work) :
    CausalStreamExposure.seen history (SingleOpeningColumnLaw.input receipt world) = true ∧
      CausalStreamExposure.seen history (SingleOpeningRandomLaw.phase receipt).pending.input = true := by
  obtain ⟨_,completion,_,executed,_,observed⟩ := accepted
  have origin := NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed
  have preparedLog : (run ctx.prefix world).run.2.Sublist history := by
    apply List.Sublist.trans _ observed
    rw [origin.log]
    exact List.sublist_append_left _ _
  have spec := NativeBrakedownParameters.build_spec description ctx.parameters work.geometry
    (SingleOpeningRectangularData.geometry ctx world work origin.prepared)
  have positive : 0 < ctx.parameters.queries.val := Nat.pos_of_ne_zero spec.basic.2.2.2
  constructor
  · apply seen_of_output _ 0 _ history (preparedLog.subset (prepared_column_read receipt))
    rw [← List.length_pos_iff,InputIndexedOracle.bytes_length]
    omega
  · apply seen_of_output _ 0 _ history (preparedLog.subset (prepared_field_read receipt origin.prepared))
    rw [← List.length_pos_iff,InputIndexedOracle.bytes_length]
    decide

/-- Every noninherited stream has a real earlier machine packet and a split
of the complete observed history at its first positive read, at any offset. -/
def Covered {P S A : Type} (past : World → Execution P) (initial : P → S) (step : S → OracleMachine.Command S A)
    (fuel : ℕ) (world : World) (input : Input) : Prop :=
  CausalStreamExposure.seen (past world).run.2 input = true ∨ ∃ index < fuel,
    CausalStreamExposure.firstRead step (CausalExposureLifetime.history past initial step index world).run = some input ∧
    CausalFirstStreamPrefix.recover input (CausalExposureLifetime.history past initial step fuel world).run.2 =
      some (CausalExposureLifetime.history past initial step index world).run.2 ∧
    ∃ offset values after, values ≠ [] ∧ (CausalExposureLifetime.history past initial step fuel world).run.2 =
      (CausalExposureLifetime.history past initial step index world).run.2 ++ .output input offset values :: after

theorem accepted_coverage {P S A Memory : Type} (past : World → Execution P) (initial : P → S) (step : S → OracleMachine.Command S A)
    (fuel : ℕ) (receipt : Receipt ctx world work sample) (choose : NativeGoldPcsProgram.Scheduler Memory) (verifierFuel : ℕ) (memory : Memory)
    (accepted : SingleOpeningAvailability.Accepted world (CausalExposureLifetime.history past initial step fuel world).run.2 ctx choose verifierFuel memory work) :
    Covered past initial step fuel world (SingleOpeningColumnLaw.input receipt world) ∧
      Covered past initial step fuel world (SingleOpeningRandomLaw.phase receipt).pending.input := by
  have touched := accepted_exposures receipt _ choose verifierFuel memory accepted
  exact ⟨CausalStreamLineage.coverage past initial step fuel world _ touched.1,
    CausalStreamLineage.coverage past initial step fuel world _ touched.2⟩

end
end FormalProof4FHE.HasteBoots.SingleOpeningChallengeHistory
