module
public import FormalProof4FHE.HasteBoots.OracleProgramMachine
public import FormalProof4FHE.HasteBoots.CausalStreamCoverage
public import FormalProof4FHE.HasteBoots.NativeGoldBatchColumnRequestLaw
public import FormalProof4FHE.HasteBoots.NativeGoldBatchReadExposure
@[expose] public section

/-! The actual native preparation exposes both complete challenge streams.
Embedding its real log into any causal machine history yields chronological
first-read witnesses, or inherited exposures, without an external freshness
certificate. This does not claim that future selected response/phase metadata
is measurable at those earlier prefixes, or that receipt knowledge is present. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchStreamCoverage
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (description)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World bytes)
open OracleProgram (run)
noncomputable section

/-- The ordered-index output is part of the original preparation log. -/
theorem prepared_column_read (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    Observation.output (NativeGoldBatchColumnRequestLaw.input ctx work world) 0
      (bytes world (NativeGoldBatchColumnRequestLaw.input ctx work world) 0 (ctx.parameters.queries.val*8)) ∈
      (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2 := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work prepared
  obtain ⟨next,prelude,columnsLog⟩ := NativeGoldBatchColumns.columns_log description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have finished := (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.2.2
  obtain ⟨_,_,receipt,_⟩ := NativeFieldReceipt.finished_origin NativeFields.goldilocksModulus ctx.fieldFuel geometry.randomCount.val
    (NativePrimeRequest.prepare binding.parent .vector) NativeGoldBatchPrelude.randomLabel world state next finished
  have valid : NativeIndexRequest.check (description.row.blocks ctx.parameters.code) ctx.parameters.queries = true :=
    NativeGoldBatchColumnRequestLaw.prepared_check ctx world _ prepared
  rw [NativeGoldBatchPcsProgram.run_prepareProgram,columnsLog,receipt,
    NativePrequeryIndexLaw.request_run world _ _ _ _ valid]
  apply List.mem_append_right
  change Observation.output _ 0 _ ∈ [Observation.start _,Observation.output _ 0 _]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem prepared_positive_quota (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    0 < ctx.parameters.queries.val := by
  have built := NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared
  exact Nat.pos_of_ne_zero (NativeBrakedownParameters.build_spec description ctx.parameters work.geometry built).basic.2.2.2

/-- A positive native read remains a touch inside any containing raw log. -/
theorem seen_of_read (log : List Observation) (world : World) (input : Input) (offset count : ℕ)
    (positive : 0 < count) (present : Observation.output input offset (bytes world input offset count) ∈ log) :
    CausalStreamExposure.seen log input = true := by
  apply List.any_eq_true.mpr
  refine ⟨Observation.output input offset (bytes world input offset count),present,?_⟩
  simp only [CausalStreamExposure.touches,InputIndexedOracle.bytes_length,decide_eq_true_eq]
  exact ⟨True.intro,positive⟩

/-- Both challenges are actually exposed, with positivity derived from native
parameter validation rather than assumed from the analysis quota. -/
theorem prepared_streams (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (log : List Observation) (contained : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2.Sublist log) :
    CausalStreamExposure.seen log (NativeGoldBatchRandomLaw.phase work).pending.input = true ∧
      CausalStreamExposure.seen log (NativeGoldBatchColumnRequestLaw.input ctx work world) = true := by
  have read := (NativeGoldBatchReadExposure.prepared_read ctx world work prepared).choose_spec.2.2
  constructor
  · exact seen_of_read log world _ 0 8 (by decide) (contained.subset read)
  · exact seen_of_read log world _ 0 _ (by have positive := prepared_positive_quota ctx world work prepared; omega)
      (contained.subset (prepared_column_read ctx world work prepared))

/-- No assumption that the verifier initiated either first read: off-path,
far-offset and earlier partial reads are selected at their real machine time.
Inherited exposures remain explicit. The two stream witnesses need not be
ordered like the native verifier's later use of those streams. -/
theorem prepared_coverage {P S A : Type} (past : World → NativeTranscript.Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (fuel : ℕ) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (contained : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2.Sublist
      (CausalExposureLifetime.history past initial step fuel world).run.2) :
    (CausalStreamExposure.seen (past world).run.2 (NativeGoldBatchRandomLaw.phase work).pending.input = true ∨
      ∃ index < fuel, CausalStreamExposure.firstRead step (CausalExposureLifetime.history past initial step index world).run =
        some (NativeGoldBatchRandomLaw.phase work).pending.input) ∧
    (CausalStreamExposure.seen (past world).run.2 (NativeGoldBatchColumnRequestLaw.input ctx work world) = true ∨
      ∃ index < fuel, CausalStreamExposure.firstRead step (CausalExposureLifetime.history past initial step index world).run =
        some (NativeGoldBatchColumnRequestLaw.input ctx work world)) := by
  have exposed := prepared_streams ctx world work prepared _ contained
  exact ⟨CausalStreamCoverage.coverage past initial step fuel world _ exposed.1,
    CausalStreamCoverage.coverage past initial step fuel world _ exposed.2⟩
/-- Actual native preparation after an arbitrary inherited prelude has a
path-dependent completion prefix. Both streams are covered there; no caller
supplies an embedding of the native log or a uniform termination bound. -/
theorem native_after_coverage {P : Type} (past : World → NativeTranscript.Execution P)
    (context : P → Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram (context (past world).run.1)) world).run.1 = .prepared work) :
    ∃ fuel,
      (CausalStreamExposure.seen (past world).run.2 (NativeGoldBatchRandomLaw.phase work).pending.input = true ∨
        ∃ index < fuel, CausalStreamExposure.firstRead OracleProgramMachine.step
          (CausalExposureLifetime.history past (fun value => NativeGoldBatchPcsProgram.prepareProgram (context value)) OracleProgramMachine.step index world).run =
            some (NativeGoldBatchRandomLaw.phase work).pending.input) ∧
      (CausalStreamExposure.seen (past world).run.2 (NativeGoldBatchColumnRequestLaw.input (context (past world).run.1) work world) = true ∨
        ∃ index < fuel, CausalStreamExposure.firstRead OracleProgramMachine.step
          (CausalExposureLifetime.history past (fun value => NativeGoldBatchPcsProgram.prepareProgram (context value)) OracleProgramMachine.step index world).run =
            some (NativeGoldBatchColumnRequestLaw.input (context (past world).run.1) work world)) := by
  obtain ⟨fuel,complete⟩ := OracleProgramMachine.complete
    (NativeGoldBatchPcsProgram.prepareProgram (context (past world).run.1)) world
  refine ⟨fuel,prepared_coverage past (fun value => NativeGoldBatchPcsProgram.prepareProgram (context value))
    OracleProgramMachine.step fuel _ world work prepared ?_⟩
  rw [CausalExposureLifetime.history_run,complete]
  exact List.sublist_append_right _ _

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchStreamCoverage
