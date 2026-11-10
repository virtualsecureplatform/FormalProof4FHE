module
public import FormalProof4FHE.HasteBoots.SingleOpeningRectangularAcceptance
@[expose] public section

/-! Native single-opening finishing in the ideal rectangular experiment.
Responses may use arbitrary private probabilistic state after the full random
test matrix. The column vector is sampled later. This is not the production
Fiat--Shamir law or a physical attacker-work bound. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningInteractiveSoundness
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (logSize)
open NativeFieldRepresentation (goldValue)
open NativeFields (Goldilocks)
open InputIndexedOracle (World)
open OracleProgram (run)
open SingleOpeningRectangularData
open OracleComp
noncomputable section

theorem finish_claim (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (opening : NativeGoldPcsOpening.Opening)
    (accepted : NativeGoldPcsClaim.verify ctx.parameters ctx.query opening.evaluation.val ctx.claimed = .ok ()) :
    claimed ctx = RectangularMatrixResponse.finishMessage (right ctx world work prepared) (messages ctx opening.evaluation.val) := by
  obtain ⟨data⟩ := SingleOpeningFinishing.prepared_encoding ctx world work prepared
  have native := NativeGoldSuffixFinishing.claim_message ctx.parameters ctx.query opening.evaluation.val ctx.claimed data.valid accepted
  have transfer := NativeGoldSuffixFinishing.transport_message ctx.parameters ctx.query
    (NativeGoldBlockCode.encoding ctx.parameters.code data.planRoot) opening.evaluation.val data.size data.shape
  rw [← transfer] at native
  have rightEq : NativeGoldSuffixFinishing.encodedRight ctx.parameters ctx.query
      (NativeGoldBlockCode.encoding ctx.parameters.code data.planRoot) data.size data.shape = right ctx world work prepared := by rfl
  have messagesEq : (fun lane : Fin ctx.parameters.width.val => NativeGoldResponseMessages.message
      (NativeGoldBlockCode.encoding ctx.parameters.code data.planRoot) opening.evaluation.val lane.val) = messages ctx opening.evaluation.val := by rfl
  rw [rightEq,messagesEq] at native
  change ctx.claimed.val.map goldValue = List.ofFn (RectangularMatrixResponse.finishMessage
    (right ctx world work prepared) (messages ctx opening.evaluation.val)) at native
  funext lane
  have entry := congrArg (fun words => (words[lane.val]?).getD (goldValue 0)) native
  simpa only [claimed,List.getElem?_map,Option.getD_map,List.getElem?_ofFn,lane.isLt,reduceDIte,Option.getD_some] using entry

theorem distance (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx) :
    Code.minDist (BlockCode.code
      (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
      Set (Fin (2^logSize ctx.parameters.code) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) =
      ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1 := by
  have spec := NativeGoldBlockCode.build_spec origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  have logs := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed).2
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  have exactDistance := BlockCode.minDist
    (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
    ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val dimensions.1
  simpa only [Fintype.card_fin,← logs] using exactDistance

/-- The actual native finishing gate is retained in the event. No response
encoding/degree/primitive-root certificate is an experiment premise. -/
theorem soundness_bound {Response : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (origin : CacheBackedSingleOpening.Origin ctx)
    (radius : ℕ)
    (word : Fin (2^logSize ctx.parameters.code) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks)
    (respond : (Fin ctx.parameters.width.val → Row ctx → Goldilocks) → ProbComp Response)
    (opening : Response → NativeGoldPcsOpening.Opening)
    [SampleableType (Row ctx → Goldilocks)]
    [SampleableType (Fin ctx.parameters.width.val → Row ctx → Goldilocks)]
    [SampleableType (Fin ctx.parameters.queries.val → Fin (2^logSize ctx.parameters.code))]
    [SampleableType (Submodule.span Goldilocks (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := Goldilocks) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1) :
    Pr{let pair ← RectangularOpeningKernel.experiment (F := Goldilocks) (Row := Row ctx)
        (Position := Fin (2^logSize ctx.parameters.code)) ctx.parameters.width.val ctx.parameters.queries.val respond}[
      claimed ctx ≠ matrixEvaluation (left ctx world work prepared) (right ctx world work prepared)
        (RectangularMatrixOpeningKernel.extract
          (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
          origin.capacity radius word) ∧
      NativeGoldPcsClaim.verify ctx.parameters ctx.query (opening pair.1.2).evaluation.val ctx.claimed = .ok () ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
        (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
        word pair.1.1 (messages ctx (opening pair.1.2).test.val) pair.2 ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
        (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
        word (RectangularMatrixResponse.weights (left ctx world work prepared)) (messages ctx (opening pair.1.2).evaluation.val) pair.2] ≤
      (((ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1 : ℕ) : ENNReal) / Fintype.card Goldilocks)^ctx.parameters.width.val +
      max (ColumnOpening.missBound (Fin (2^logSize ctx.parameters.code)) ctx.parameters.queries.val
        ((ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1)-radius))
        (ColumnOpening.missBound (Fin (2^logSize ctx.parameters.code)) ctx.parameters.queries.val (radius+1)) := by
  have spec := NativeGoldBlockCode.build_spec origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  have dims := NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed
  have logs := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block origin.request.blowup ctx.parameters.code origin.constructed).2
  let : NeZero ctx.parameters.code.messageBlocks.val := ⟨Nat.ne_of_gt dims.1⟩
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  have enough : ctx.parameters.code.messageBlocks.val ≤ Fintype.card (Fin (2^logSize ctx.parameters.code)) := by
    simpa only [Fintype.card_fin] using Nat.le_of_lt dims.2.1
  have cardinal : ctx.parameters.code.blocks.val ≤ Fintype.card Goldilocks := by
    have embedded := Fintype.card_le_of_injective
      (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
      (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive).injective
    simpa only [Fintype.card_fin,← logs] using embedded
  have large : radius < Fintype.card Goldilocks := by have positive := dims.1; omega
  have distanceEq := distance ctx origin
  have nativeSmall : 3*radius < Code.minDist (BlockCode.code
      (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
      Set (Fin (2^logSize ctx.parameters.code) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) := by
    rw [distanceEq]
    exact small
  have bound := RectangularMatrixOpeningKernel.soundness_bound
    (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
    enough origin.capacity radius ctx.parameters.width.val ctx.parameters.queries.val word (left ctx world work prepared)
    (right ctx world work prepared) respond (fun _ response => messages ctx (opening response).test.val)
    (fun _ response => messages ctx (opening response).evaluation.val) large nativeSmall
  apply le_trans (prEvent_mono _ _ _ ?_) (by simpa only [distanceEq] using bound)
  rintro pair ⟨different,verified,randomChecks,structuredChecks⟩
  rw [finish_claim ctx world work prepared (opening pair.1.2) verified] at different
  exact ⟨different,randomChecks,structuredChecks⟩

end
end FormalProof4FHE.HasteBoots.SingleOpeningInteractiveSoundness
