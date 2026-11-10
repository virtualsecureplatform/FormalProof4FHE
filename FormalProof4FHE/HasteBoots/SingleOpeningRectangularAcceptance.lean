module
public import FormalProof4FHE.HasteBoots.SingleOpeningRectangularChecks
@[expose] public section

/-! Actual native single-opening acceptance supplies a complete rectangular
view, or the existing shared history Bad. One query-independent common decoder
extracts the analysis table. This is not efficient public application extraction
or a production Fiat--Shamir probability theorem. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningRectangularAcceptance
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (logSize)
open NativeFieldRepresentation (goldValue)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (Program run)
open SingleOpeningRectangularData
open SingleOpeningRectangularChecks (source Frozen)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- A derived analysis view of one actual native single-opening acceptance. -/
structure View (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (history : List Observation) (origin : CacheBackedSingleOpening.Origin ctx) where
  prepared : (run ctx.prefix world).run.1 = .prepared work
  context : Digest
  log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest
  sample : NativeIndexRequest.Result
  draw : Fin ctx.parameters.queries.val → Fin (2^logSize ctx.parameters.code)
  hashed : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context
  snapshots : ∀ index : NativeMerkleShapeFamily.Height,
    ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints
  sampled : SingleOpeningRectangularChecks.Sampled ctx world work sample
  jobs : work.jobs.map NativeGoldColumnWorker.Job.index = NativeIndexRequest.distinct sample.draws
  typed : NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val sample.draws = some draw
  ordered : (List.ofFn draw).map Fin.val = sample.draws
  randomChecks : RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
    (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
    (source ctx world work prepared (Frozen dummy context work log)) (Weights ctx world work prepared work.random)
    (messages ctx ctx.opening.test.val) draw
  structuredChecks : RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
    (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
    (source ctx world work prepared (Frozen dummy context work log)) (RectangularMatrixResponse.weights (left ctx world work prepared))
    (messages ctx ctx.opening.evaluation.val) draw
  finishes : claimed ctx = RectangularMatrixResponse.finishMessage (right ctx world work prepared) (messages ctx ctx.opening.evaluation.val)

/-- Neither the typed draw vector nor source/response equations are supplied as
certificates: the actual accepted call derives every field of the view. -/
theorem accepted_view_or_bad {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (origin : CacheBackedSingleOpening.Origin ctx) (history : List Observation)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : SingleOpeningAvailability.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history) :
    Nonempty (View dummy ctx world work history origin) ∨ NativeRootFamilyLifetime.Bad dummy history := by
  rcases SharedOpeningAvailability.single_view_or_bad dummy ctx world work origin history choose fuel memory accepted truthful with available | bad
  · left
    obtain ⟨_,completion,parent,executed,status,_⟩ := accepted
    have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
    obtain ⟨context,log,sample,draw,hashed,snapshots,sampled,jobs,typed,ordered,randomChecks,structuredChecks⟩ :=
      SingleOpeningRectangularChecks.source_checks dummy ctx world work prepared origin history available.source
    exact ⟨⟨prepared,context,log,sample,draw,hashed,snapshots,sampled,jobs,typed,ordered,randomChecks,structuredChecks,
      accepted_claim ctx world work prepared choose fuel memory completion executed parent status⟩⟩
  · exact Or.inr bad

/-- The ordered native helper verifier supplies the individual accepted call
and its observed subtrace, including receipts before a later helper stop. -/
theorem helper_receipt_view_or_bad {B Memory : Type} (dummy : Digest) (ctx : NativeGoldHelperVerification.Context B)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (bound : NativeSharedLookupBody.Bound) (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening)
    (status : NativeGoldHelperVerification.Result Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers bound plan status)
    (receipt : NativeGoldHelperVerification.Receipt Memory) (member : receipt ∈ status.progress.receipts)
    (origin : CacheBackedSingleOpening.Origin (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (framed : SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.2.Sublist history) :
    Nonempty (View dummy _ world receipt.work history origin) ∨ NativeRootFamilyLifetime.Bad dummy history := by
  obtain ⟨checked,trace⟩ := NativeGoldHelperVerification.helpers_receipts ctx choose memory world bound plan status executed receipt member
  exact accepted_view_or_bad dummy _ world receipt.work origin history choose ctx.workerFuel receipt.memory
    ⟨framed,receipt.completion,receipt.after,checked.1,checked.2,trace.trans observed⟩ truthful

namespace View
variable {dummy : Digest} {ctx : Context} {world : World} {work : Prepared}
  {history : List Observation} {origin : CacheBackedSingleOpening.Origin ctx}

/-- This table depends on the complete frozen word, retained code and radius,
not on the opening's left/right query or its claimed result. -/
def table (view : View dummy ctx world work history origin) (radius : ℕ) :=
  RectangularMatrixOpeningKernel.extract
    (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
    origin.capacity radius (source ctx world work view.prepared (Frozen dummy view.context work view.log))

/-- Falsity against that table is exactly the one-opening kernel error with
its actual checked random/structured equations. There is no lane union bound. -/
theorem false_iff_error (view : View dummy ctx world work history origin) (radius : ℕ) :
    (claimed ctx ≠ matrixEvaluation (left ctx world work view.prepared) (right ctx world work view.prepared) (view.table radius)) ↔
    (RectangularMatrixResponse.finishMessage (right ctx world work view.prepared) (messages ctx ctx.opening.evaluation.val) ≠
      matrixEvaluation (left ctx world work view.prepared) (right ctx world work view.prepared) (view.table radius) ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
        (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
        (source ctx world work view.prepared (Frozen dummy view.context work view.log)) (Weights ctx world work view.prepared work.random)
        (messages ctx ctx.opening.test.val) view.draw ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
        (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
        (source ctx world work view.prepared (Frozen dummy view.context work view.log)) (RectangularMatrixResponse.weights (left ctx world work view.prepared))
        (messages ctx ctx.opening.evaluation.val) view.draw) := by
  constructor
  · intro different
    rw [view.finishes] at different
    exact ⟨different,view.randomChecks,view.structuredChecks⟩
  · rintro ⟨different,_,_⟩
    rw [view.finishes]
    exact different
/-- An honestly encoded original table is recovered exactly at radius zero.
Message capacity and nonzero code width come from the retained constructor. -/
theorem table_encoded (view : View dummy ctx world work history origin)
    (original : Fin (2^ctx.parameters.leftVariables.val) → Fin ctx.parameters.code.messageLength.val → Fin ctx.parameters.width.val → NativeFields.Goldilocks)
    (encoded : source ctx world work view.prepared (Frozen dummy view.context work view.log) =
      fun position row => BlockEncoder.encode
        (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
        (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
          (fun index => original row.1 index row.2)) position) : view.table 0 = original := by
  have spec := NativeGoldBlockCode.build_spec origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  unfold table
  rw [encoded]
  exact RectangularMatrixOpeningKernel.extract_encoded _ (by simpa only [Fintype.card_fin] using Nat.le_of_lt dimensions.2.1)
    origin.capacity original

end View

/-- Any accepted native call and retained original code may witness a missing
rectangular view in this history. -/
def Failure (Memory : Type) (dummy : Digest) (history : List Observation) (world : World) : Prop :=
  ∃ (ctx : Context) (choose : NativeGoldPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory) (work : Prepared),
    SingleOpeningAvailability.Accepted world history ctx choose fuel memory work ∧
      ∃ origin : CacheBackedSingleOpening.Origin ctx, ¬Nonempty (View dummy ctx world work history origin)

theorem failure_implies_bad (Memory : Type) (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) (failed : Failure Memory dummy history world) :
    NativeRootFamilyLifetime.Bad dummy history := by
  obtain ⟨ctx,choose,fuel,memory,work,accepted,origin,missing⟩ := failed
  exact (accepted_view_or_bad dummy ctx world work origin history choose fuel memory accepted truthful).resolve_left missing

/-- The extra deterministic rectangular transport consumes no new hash risk. -/
theorem failure_le_charge {A : Type} (Memory : Type) (dummy : Digest) (program : Program A) :
    InputIndexedOracle.law {world | Failure Memory dummy (run program world).run.2 world} ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape)
        (CheckpointCollision.loss unifSpec NativeMerkleShapeFamily.shape)
        ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
        (CheckpointExecution.empty NativeMerkleShapeFamily.shape) := by
  have included : {world | Failure Memory dummy (run program world).run.2 world} ⊆
      {world | NativeRootFamilyLifetime.Bad dummy (run program world).run.2} := by
    intro world failed
    exact failure_implies_bad Memory dummy world _ ((OracleProgram.run_replay program).truthful world) failed
  exact (measure_mono included).trans (NativeRootFamilyAudit.bad_le_charge dummy program)

end
end FormalProof4FHE.HasteBoots.SingleOpeningRectangularAcceptance
