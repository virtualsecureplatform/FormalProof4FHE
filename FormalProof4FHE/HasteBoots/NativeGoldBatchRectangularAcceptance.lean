module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularChecks
@[expose] public section

/-! Native acceptance supplies the entire deterministic rectangular opening
view. The common decoder below is an analysis extractor, not the efficient
public application extractor. The production Fiat–Shamir law is still needed
before an interactive kernel bound can bound the native event. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularAcceptance
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler)
open NativeGoldBlockCode (Tables logSize)
open NativeGoldBatchResponseMeaning (Domain)
open NativeGoldBatchLinearEquations (Frozen)
open NativeGoldBatchRectangularWeights (source)
open NativeGoldBatchRectangularData (Group Query groupOf messages testMessages left right claimed)
open NativeGoldBatchRectangularChecks (random)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeFieldRepresentation (goldValue)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- Analysis data derived from one witnessed native acceptance. These fields
are theorem conclusions and are never arguments of the native verifier. -/
structure View (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (history : List Observation)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) where
  prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work
  context : Digest
  log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest
  draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code))
  hashed : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context
  snapshots : ∀ index : NativeMerkleShapeFamily.Height,
    ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints
  typed : NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws = some draw
  ordered : (List.ofFn draw).map Fin.val = work.sample.draws
  randomChecks : RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val) (Domain ctx primitive)
    (source ctx world work prepared (Frozen dummy context work log)) (random ctx world work prepared) (testMessages ctx work) draw
  groupChecks : ∀ test : Group ctx work × Fin ctx.parameters.width.val, ColumnOpening.Agrees
    (StructuredOpening.combine (RectangularBatchOpeningKernel.weights (left ctx world work prepared) test)
      (source ctx world work prepared (Frozen dummy context work log)))
    (BlockEncoder.encode (Domain ctx primitive) (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (messages ctx work test.1 test.2))) draw
  finishes : ∀ query : Query work,
    claimed ctx work query = RectangularBatchOpeningKernel.finishMessage (groupOf ctx work) (right ctx world work prepared) (messages ctx work) query

/-- Actual native execution, truthful history and absence of source
inconsistency supply every field of the rectangular opening view. -/
theorem accepted_view {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (history : List Observation) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history)
    (noDisagreement : ¬CheckpointAvailability.Disagreement NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy history)) :
    Nonempty (View dummy ctx world work history primitive) := by
  have available := NativeGoldBatchAnySourceRisk.accepted_has_source dummy world history truthful ctx choose fuel memory work accepted noDisagreement
  obtain ⟨_,completion,parent,executed,status,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨context,log,draw,hashed,snapshots,typed,ordered,randomChecks,groupChecks⟩ :=
    NativeGoldBatchRectangularChecks.source_checks dummy ctx world work prepared tables message block blowup constructed primitive history available
  exact ⟨⟨prepared,context,log,draw,hashed,snapshots,typed,ordered,randomChecks,groupChecks,
    NativeGoldBatchRectangularData.accepted_claim ctx world work prepared choose fuel memory completion executed parent status⟩⟩

/-- Falsity against the common analysis table is exactly the batch kernel's
any-false-original-query event. There is no query/group/lane union bound. -/
theorem false_iff_error (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (history : List Observation)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (view : View dummy ctx world work history primitive)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ) :
    (∃ query : Query work, claimed ctx work query ≠ matrixEvaluation
      (NativeGoldBatchRectangularWeights.left ctx world work view.prepared query) (right ctx world work view.prepared query)
      (RectangularMatrixOpeningKernel.extract (Domain ctx primitive) capacity radius
        (source ctx world work view.prepared (Frozen dummy view.context work view.log)))) ↔
    ((∃ query : Query work, RectangularBatchOpeningKernel.finishMessage (groupOf ctx work) (right ctx world work view.prepared) (messages ctx work) query ≠ matrixEvaluation
      (left ctx world work view.prepared (groupOf ctx work query)) (right ctx world work view.prepared query)
      (RectangularMatrixOpeningKernel.extract (Domain ctx primitive) capacity radius
        (source ctx world work view.prepared (Frozen dummy view.context work view.log)))) ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val) (Domain ctx primitive)
        (source ctx world work view.prepared (Frozen dummy view.context work view.log)) (random ctx world work view.prepared) (testMessages ctx work) view.draw ∧
      ∀ test : Group ctx work × Fin ctx.parameters.width.val, ColumnOpening.Agrees
        (StructuredOpening.combine (RectangularBatchOpeningKernel.weights (left ctx world work view.prepared) test)
          (source ctx world work view.prepared (Frozen dummy view.context work view.log)))
        (BlockEncoder.encode (Domain ctx primitive) (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (messages ctx work test.1 test.2))) view.draw) := by
  constructor
  · rintro ⟨query,different⟩
    rw [view.finishes query,← NativeGoldBatchRectangularData.original_left ctx world work view.prepared query] at different
    exact ⟨⟨query,different⟩,view.randomChecks,view.groupChecks⟩
  · rintro ⟨⟨query,different⟩,_,_⟩
    exact ⟨query,by rw [view.finishes query,← NativeGoldBatchRectangularData.original_left ctx world work view.prepared query]; exact different⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularAcceptance
