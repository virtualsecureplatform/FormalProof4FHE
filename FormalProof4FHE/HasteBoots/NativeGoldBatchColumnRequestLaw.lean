module
public import FormalProof4FHE.HasteBoots.NativeIndexFirstReadLaw
public import FormalProof4FHE.HasteBoots.NativeGoldBatchResponseBinding
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRandomLaw
public import FormalProof4FHE.HasteBoots.NativeFieldReceipt
@[expose] public section

/-! The actual response-bound native batch column request. Its parent is the
completed field receipt, not a supplied transcript. Recorded receipt replay
pins that parent on the posterior fiber. First-read eligibility yields the
shared ordered draw law. Early/unrecorded receipt lineage and global coverage
remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchColumnRequestLaw
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (Tables logSize description)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript Observation)
open NativeUsizeMessage (Usize)
open InputIndexedOracle (Input World law)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def parent (work : Prepared) (world : World) : Transcript := (NativeTranscript.finishField world work.state.phase).run.1

def transcript (ctx : Context) (work : Prepared) (world : World) : Transcript := NativeGoldBatchOpening.bindResponses (parent work world) ctx.opening

def input (ctx : Context) (work : Prepared) (world : World) : Input :=
  NativePrequeryIndexLaw.requestInput (transcript ctx work world) NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries

def values (ctx : Context) (work : Prepared) (world : World) :=
  NativeIndexFirstReadLaw.values (logSize ctx.parameters.code) (transcript ctx work world)
    NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries world

/-- Both field completion and the exact shared index request come from the
same native preparation, with the retained response message in between. -/
theorem prepared_request (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    (run (NativeIndexRequest.request (transcript ctx work world) NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries) world).run.1 = some work.sample := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work prepared
  obtain ⟨next,prelude,_,drawn,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have finished := (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.2.2
  obtain ⟨_,_,receipt,_⟩ := NativeFieldReceipt.finished_origin NativeFields.goldilocksModulus ctx.fieldFuel geometry.randomCount.val
    (NativePrimeRequest.prepare binding.parent .vector) NativeGoldBatchPrelude.randomLabel world state next finished
  rw [receipt] at drawn
  exact drawn

theorem prepared_check (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    NativeIndexRequest.check ctx.parameters.code.blocks ctx.parameters.queries = true :=
  NativeIndexRequest.accepted_check _ _ _ _ world work.sample (prepared_request ctx world work prepared)

/-- Actual typed ordered draws coincide with those already used by native
workers, including every duplicate occurrence. -/
theorem values_original (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    values ctx work world = NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws := by
  unfold values NativeIndexFirstReadLaw.values
  rw [prepared_request ctx world work prepared]
  rfl

theorem prepared_typed (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code) :
    ∃ draw, values ctx work world = some draw ∧ (List.ofFn draw).map Fin.val = work.sample.draws ∧
      work.sample.indices = NativeIndexRequest.distinct work.sample.draws ∧
      ∀ index, ∃ job ∈ work.jobs, job.index = (draw index).val := by
  obtain ⟨draw,typed,ordered,covered⟩ := NativeGoldBatchDraws.prepared_typed ctx world work prepared tables message block blowup constructed
  exact ⟨draw,by rw [values_original ctx world work prepared,typed],ordered,
    (NativeGoldBatchDraws.prepared_sample ctx world work prepared).2.1,covered⟩

/-- The request commits to every raw response-group row; columns and paths
are selected later and do not affect this response-bound nonce. -/
theorem response_bound (ctx : Context) (work : Prepared) (world : World) (opening : NativeGoldBatchOpening.Opening) :
    NativeGoldBatchResponseBinding.input (parent work world) NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries opening = input ctx work world ↔
      opening.test = ctx.opening.test ∧ opening.evaluations = ctx.opening.evaluations :=
  NativeGoldBatchResponseBinding.input_eq_iff _ _ _ _ opening ctx.opening

/-- The actual completed receipt, if already recorded, fixes the native
parent on the whole replay fiber. No fresh-receipt assumption is made. -/
theorem parent_on_fiber {P : Type} {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (world other : World) (work : Prepared)
    (observed : (NativeTranscript.finishField world work.state.phase).run.2.Sublist (past world).run.2)
    (fiber : (past other).run = (past world).run) : parent work other = parent work world :=
  NativeFieldReceipt.transcript_on_fiber replay world other work.state.phase observed fiber

theorem parent_on_fiber_of_known {P : Type} {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (world other : World) (work : Prepared)
    (known : NativeFieldReceipt.Known (past world).run.2 work.state.phase)
    (fiber : (past other).run = (past world).run) : parent work other = parent work world :=
  NativeFieldReceipt.transcript_on_fiber_of_known replay world other work.state.phase known fiber

/-- Local column law with the native receipt parent recomputed in each
world. Its constancy is proved from the observed receipt, not assumed. -/
theorem conditional_uniform {S A : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (known : NativeFieldReceipt.Known (past world).run.2 work.state.phase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (input ctx work world))
    (event : (Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code))) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (values ctx work other).elim False event} =
        Pr{let draw ← $ᵗ (Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code)))}[event draw] := by
  have power := (NativeGoldBlockCodeMeaning.constructor_log tables message block blowup ctx.parameters.code constructed).2
  have fixed := NativeIndexFirstReadLaw.conditional_uniform step replay world (logSize ctx.parameters.code)
    (transcript ctx work world) NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries
    (prepared_check ctx world work prepared) power selected event
  refine Eq.trans ?_ fixed
  apply NativeShakeProjection.conditional_event_congr replay world
  intro other same
  have parentEq := parent_on_fiber_of_known replay world other work known same
  change (NativeIndexFirstReadLaw.values _ (transcript ctx work other) _ _ _ other).elim False event ↔ _
  simp only [transcript,parentEq]

/-- Shared native draws give a single witness miss bound. The number of
response groups and lanes does not multiply the probability. -/
theorem shared_bound {S A Test Symbol : Type} [DecidableEq Symbol] (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (known : NativeFieldReceipt.Known (past world).run.2 work.state.phase)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (input ctx work world))
    (raw claimed : Test → Fin (2^(logSize ctx.parameters.code)) → Symbol) (distance : ℕ)
    (witness : ∃ test, distance ≤ hammingDist (raw test) (claimed test)) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (values ctx work other).elim False (fun draw => ∀ test, ColumnOpening.Agrees (raw test) (claimed test) draw)} ≤
        ColumnOpening.missBound (Fin (2^(logSize ctx.parameters.code))) ctx.parameters.queries.val distance := by
  rw [conditional_uniform ctx world work prepared tables message block blowup constructed step replay known selected]
  exact ColumnOpening.shared_bound raw claimed ctx.parameters.queries.val distance witness
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchColumnRequestLaw
