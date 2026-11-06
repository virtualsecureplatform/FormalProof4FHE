module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchColumnRequestLaw
public import FormalProof4FHE.HasteBoots.NativeGoldBatchAnySourceRisk
@[expose] public section

/-! Accepted native batches expose their actual complete field and column
inputs in the recorded mixed history. No stream-touch witness is supplied
by a caller, and the native positive column quota is derived from preparation. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchChallengeHistory
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCode (description)
open NativeTranscript (Observation)
open InputIndexedOracle (World Input bytes)
open OracleProgram (run)
noncomputable section

theorem prepared_column_log (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    (run (NativeIndexRequest.request (NativeGoldBatchColumnRequestLaw.transcript ctx work world)
      NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries) world).run.2.Sublist
        (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2 := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work prepared
  obtain ⟨next,prelude,columnsLog⟩ := NativeGoldBatchColumns.columns_log description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have finished := (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.2.2
  have receipt := (NativeFieldReceipt.finished_origin NativeFields.goldilocksModulus ctx.fieldFuel geometry.randomCount.val
    (NativePrimeRequest.prepare binding.parent .vector) NativeGoldBatchPrelude.randomLabel world state next finished).choose_spec.2.1
  rw [NativeGoldBatchPcsProgram.run_prepareProgram,columnsLog,receipt]
  exact List.sublist_append_right _ _

theorem prepared_column_read (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    .output (NativeGoldBatchColumnRequestLaw.input ctx work world) 0
      (bytes world (NativeGoldBatchColumnRequestLaw.input ctx work world) 0 (ctx.parameters.queries.val*8)) ∈
        (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2 := by
  apply (prepared_column_log ctx world work prepared).subset
  rw [NativePrequeryIndexLaw.request_run world _ _ _ _ (NativeGoldBatchColumnRequestLaw.prepared_check ctx world work prepared)]
  simp only [NativePrequeryIndexLaw.outcome,List.mem_cons,List.not_mem_nil,or_false]
  right
  rfl

theorem seen_of_output (input : Input) (offset : ℕ) (values : Input) (log : List Observation)
    (member : .output input offset values ∈ log) (positive : values ≠ []) :
    CausalStreamExposure.seen log input = true := by
  apply List.any_eq_true.mpr
  refine ⟨_,member,?_⟩
  simp only [CausalStreamExposure.touches,decide_eq_true_eq,true_and]
  exact List.length_pos_iff.mpr positive

theorem accepted_exposures {Memory : Type} (ctx : Context) (world : World) (work : Prepared)
    (history : List Observation) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work) :
    CausalStreamExposure.seen history (NativeGoldBatchColumnRequestLaw.input ctx work world) = true ∧
      CausalStreamExposure.seen history (NativeGoldBatchRandomLaw.phase work).pending.input = true := by
  obtain ⟨_,completion,_,executed,_,observed⟩ := accepted
  have origin := NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed
  have preparedLog : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2.Sublist history := by
    apply List.Sublist.trans _ observed
    rw [origin.log]
    exact List.sublist_append_left _ _
  have geometry := NativeBrakedownParameters.build_spec description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work origin.prepared)
  have positive : 0 < ctx.parameters.queries.val := Nat.pos_of_ne_zero geometry.basic.2.2.2
  constructor
  · apply seen_of_output _ 0 _ history (preparedLog.subset (prepared_column_read ctx world work origin.prepared))
    rw [← List.length_pos_iff,InputIndexedOracle.bytes_length]
    omega
  · obtain ⟨_,_,_,read⟩ := NativeGoldBatchReadExposure.prepared_read ctx world work origin.prepared
    apply seen_of_output _ 0 _ history (preparedLog.subset read)
    rw [← List.length_pos_iff,InputIndexedOracle.bytes_length]
    decide
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchChallengeHistory
