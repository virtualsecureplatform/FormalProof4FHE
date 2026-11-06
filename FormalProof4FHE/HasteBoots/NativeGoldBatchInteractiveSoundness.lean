module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularAcceptance
@[expose] public section

/-! Interactive native-finishing soundness with probabilistic adaptive response
state. The experiment samples a uniform test matrix and fresh ordered columns;
identifying that experiment with production Fiat–Shamir execution remains open.
No trial bound, query/group factor, response enumeration or losslessness
assumption is used. This is not a physical attacker-work theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchInteractiveSoundness
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (Tables logSize encoding)
open NativeGoldBatchResponseMeaning (Domain)
open NativeGoldBatchRectangularData (Query Group groupOf left right claimed)
open NativeGoldBatchRectangularWeights (Row)
open NativeFieldRepresentation (goldValue)
open NativeFields (Goldilocks)
open InputIndexedOracle (World)
open OracleProgram (run)
open OracleComp
noncomputable section

def messages (ctx : Context) (work : Prepared) (opening : NativeGoldBatchOpening.Opening)
    (group : Group ctx work) (lane : Fin ctx.parameters.width.val) :=
  NativeGoldResponseMessages.message (encoding ctx.parameters.code work.planRoot)
    (((opening.evaluations.val[group.val]?).map (fun row => row.val)).getD []) lane.val

def testMessages (ctx : Context) (work : Prepared) (opening : NativeGoldBatchOpening.Opening)
    (lane : Fin ctx.parameters.width.val) :=
  NativeGoldResponseMessages.message (encoding ctx.parameters.code work.planRoot) opening.test.val lane.val

/-- Actual pure native finishing checks every original claimed value against
its assigned response, for any adaptively supplied opening payload. -/
theorem finish_claim (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (opening : NativeGoldBatchOpening.Opening)
    (accepted : NativeGoldBatchPcsProgram.finish ctx.parameters work.binding opening = .ok ()) (query : Query work) :
    claimed ctx work query = RectangularBatchOpeningKernel.finishMessage (groupOf ctx work) (right ctx world work prepared) (messages ctx work opening) query := by
  obtain ⟨response,value,responseRead,valueRead,verified⟩ := NativeGoldBatchPcsProgram.claim_origin ctx.parameters work.binding opening query
    (NativeGoldBatchPcsProgram.finish_each ctx.parameters work.binding opening accepted query)
  have native := NativeGoldSuffixFinishing.claim_message ctx.parameters (work.binding.queries.val.get query) response.val value
    (NativeGoldBatchPcsProgram.prepared_query_valid ctx world work prepared query) verified
  have transport := NativeGoldSuffixFinishing.transport_message ctx.parameters (work.binding.queries.val.get query)
    (encoding ctx.parameters.code work.planRoot) response.val
    (NativeGoldBatchFinishingMeaning.prepared_query_length ctx world work prepared query)
    (NativeGoldBatchFinishingMeaning.prepared_message_length ctx world work prepared)
  rw [← transport] at native
  funext lane
  have entry := congrArg (fun words => (words[lane.val]?).getD (goldValue 0)) native
  change claimed ctx work query lane = RectangularMatrixResponse.finishMessage (right ctx world work prepared query) (messages ctx work opening (groupOf ctx work query)) lane
  unfold claimed messages
  rw [valueRead,responseRead]
  simpa only [Option.map_some,Option.getD_some,List.getElem?_map,Option.getD_map,List.getElem?_ofFn,lane.isLt,reduceDIte,right] using entry

/-- Any false original native claim that passes native finishing and the
common-source checks has one rectangular opening loss. Private response
coins/state may depend on the full test matrix; all ordered draws are shared. -/
theorem soundness_bound {Response : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ)
    (word : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks)
    (respond : (Fin ctx.parameters.width.val → Row ctx → Goldilocks) → ProbComp Response)
    (opening : Response → NativeGoldBatchOpening.Opening)
    [SampleableType (Row ctx → Goldilocks)]
    [SampleableType (Fin ctx.parameters.width.val → Row ctx → Goldilocks)]
    [SampleableType (Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code)))]
    [SampleableType (Submodule.span Goldilocks (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := Goldilocks) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val : Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks))) :
    Pr{let pair ← RectangularOpeningKernel.experiment (F := Goldilocks) (Row := Row ctx) (Position := Fin (2^(logSize ctx.parameters.code))) ctx.parameters.width.val ctx.parameters.queries.val respond}[
      (∃ query : Query work, claimed ctx work query ≠ matrixEvaluation
        (NativeGoldBatchRectangularWeights.left ctx world work prepared query) (right ctx world work prepared query)
        (RectangularMatrixOpeningKernel.extract (Domain ctx primitive)
          (NativeGoldBlockCodeMeaning.constructor_dimensions tables message block blowup ctx.parameters.code constructed).2.2.1 radius word)) ∧
      NativeGoldBatchPcsProgram.finish ctx.parameters work.binding (opening pair.1.2) = .ok () ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val) (Domain ctx primitive) word pair.1.1
        (testMessages ctx work (opening pair.1.2)) pair.2 ∧
      ∀ test : Group ctx work × Fin ctx.parameters.width.val, ColumnOpening.Agrees
        (StructuredOpening.combine (RectangularBatchOpeningKernel.weights (left ctx world work prepared) test) word)
        (BlockEncoder.encode (Domain ctx primitive) (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
          (messages ctx work (opening pair.1.2) test.1 test.2))) pair.2] ≤
      ((Code.minDist (BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val : Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) : ENNReal) / Fintype.card Goldilocks)^ctx.parameters.width.val +
      max (ColumnOpening.missBound (Fin (2^(logSize ctx.parameters.code))) ctx.parameters.queries.val
        (Code.minDist (BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val : Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) - radius))
        (ColumnOpening.missBound (Fin (2^(logSize ctx.parameters.code))) ctx.parameters.queries.val (radius+1)) := by
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions tables message block blowup ctx.parameters.code constructed
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
  let : NeZero ctx.parameters.code.messageBlocks.val := ⟨Nat.ne_of_gt dimensions.1⟩
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨geometry.code.2.2.2.2⟩
  have bound := RectangularBatchOpeningKernel.soundness_bound (Domain ctx primitive)
    (by simpa only [Fintype.card_fin] using Nat.le_of_lt dimensions.2.1) dimensions.2.2.1 radius ctx.parameters.width.val ctx.parameters.queries.val
    word (groupOf ctx work) (left ctx world work prepared) (right ctx world work prepared) respond
    (fun _ response => testMessages ctx work (opening response)) (fun _ response => messages ctx work (opening response)) large small
  refine (prEvent_mono _ _ _ ?_).trans bound
  intro pair event
  obtain ⟨query,different⟩ := event.1
  have finished := finish_claim ctx world work prepared (opening pair.1.2) event.2.1 query
  rw [finished,← NativeGoldBatchRectangularData.original_left ctx world work prepared query] at different
  exact ⟨⟨query,different⟩,event.2.2⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchInteractiveSoundness
