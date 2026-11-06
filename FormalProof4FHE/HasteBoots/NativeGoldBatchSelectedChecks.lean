module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedWord
@[expose] public section

/-! Every accepted native random/group check uses the earlier selected
source and one shared ordered draw vector. All original finishing claims
are retained. The false-claim disagreement reduction, full Fiat–Shamir
composition and physical attacker-work bound remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedChecks
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCode (Tables logSize)
open NativeGoldBatchRectangularData (Group Query groupOf left right messages testMessages claimed)
open NativeGoldBatchLinearEquations (Frozen)
open NativeGoldBatchSelectedSource (log)
open NativeGoldBatchSelectedWord (word)
open NativeGoldBatchFieldInputView (View)
open NativeMerkleShapeFamily (height tag)
open NativeGoldColumnAuthentication (encoding)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem accepted_checks {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (before after : List Observation) (field : View)
    (parsed : NativeGoldBatchFieldInputView.parse (NativeGoldBatchRandomLaw.phase work).pending.input = some field)
    (offset : ℕ) (values : Input) (positive : values ≠ [])
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world
      (before++ .output (NativeGoldBatchRandomLaw.phase work).pending.input offset values :: after) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (before++ .output (NativeGoldBatchRandomLaw.phase work).pending.input offset values :: after))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy (before++ .output (NativeGoldBatchRandomLaw.phase work).pending.input offset values :: after))) :
    ∃ (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
      (draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code))),
      NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val) (NativeGoldBatchResponseMeaning.Domain ctx primitive)
        (word dummy field.data.context ctx.root ctx (log dummy before field)) (NativeGoldBatchRecoveredMatrix.random ctx work.state) (testMessages ctx work) draw ∧
      (∀ test : Group ctx work × Fin ctx.parameters.width.val, ColumnOpening.Agrees
        (StructuredOpening.combine (RectangularBatchOpeningKernel.weights (left ctx world work prepared) test)
          (word dummy field.data.context ctx.root ctx (log dummy before field)))
        (BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
          (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (messages ctx work test.1 test.2))) draw) ∧
      ∀ query : Query work, claimed ctx work query = RectangularBatchOpeningKernel.finishMessage
        (groupOf ctx work) (right ctx world work prepared) (messages ctx work) query := by
  obtain ⟨requests,_,computed,_,checks⟩ := NativeGoldBatchSelectedSource.accepted_selected dummy ctx world work choose fuel memory
    before after field parsed offset values positive accepted truthful noDisagreement
  obtain ⟨_,completion,next,executed,status,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have layout := NativeGoldBatchResponseMeaning.prepared_layout ctx world work prepared tables message block blowup constructed
  have sameHeight : height (tag field.data.context work) = logSize ctx.parameters.code :=
    (NativeMerkleShapeFamily.tag_height field.data.context ctx world work prepared).trans layout.2.2.2
  have spec := NativeGoldBatchRawRequests.prepare_spec height (tag field.data.context work) work requests computed
  have combinations : ∀ entry ∈ requests, ∃ bound : entry.2.position.val < 2^(logSize ctx.parameters.code),
      ∀ response ∈ work.groups, ∀ lane : Fin work.width,
        StructuredOpening.combine (NativeGoldBatchLinearEquations.Weights work work.random lane)
          (NativeGoldBatchLinearEquations.Word ctx work (Frozen dummy field.data.context work (log dummy before field))) ⟨entry.2.position.val,bound⟩ =
          NativeGoldBatchResponseMeaning.Lane ctx work work.test lane.val ⟨entry.2.position.val,bound⟩ ∧
        StructuredOpening.combine (NativeGoldBatchLinearEquations.Weights work response.1 lane)
          (NativeGoldBatchLinearEquations.Word ctx work (Frozen dummy field.data.context work (log dummy before field))) ⟨entry.2.position.val,bound⟩ =
          NativeGoldBatchResponseMeaning.Lane ctx work response.2 lane.val ⟨entry.2.position.val,bound⟩ := by
    intro entry member
    obtain ⟨inside,leaf,siblings,_,same⟩ := NativeGoldRawRequests.fromJob_spec height (tag field.data.context work) work.root entry.1 entry.2 (spec.2 entry member)
    have bounded : entry.2.position.val < 2^(logSize ctx.parameters.code) := by rw [same]; simpa only [sameHeight] using inside
    refine ⟨bounded,?_⟩
    apply NativeGoldBatchLinearEquations.column_equations ctx world work prepared tables message block blowup constructed requests
      (Frozen dummy field.data.context work (log dummy before field)) ⟨entry.2.position.val,bounded⟩
    have equations := (checks entry member).2
    have frozen : Frozen dummy field.data.context work (log dummy before field) entry.2.position.val =
        NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log dummy before field⟩ entry.2.position := by
      rw [same]
      unfold Frozen
      congr 1
      apply Fin.ext
      exact Nat.mod_eq_of_lt inside
    rw [frozen]
    exact equations
  obtain ⟨draw,typed,ordered,_⟩ := NativeGoldBatchDraws.prepared_typed ctx world work prepared tables message block blowup constructed
  obtain ⟨random,groups⟩ := NativeGoldBatchOrderedChecks.requests_agree ctx world work prepared field.data.context requests computed draw ordered _ combinations
  have rectangular := NativeGoldBatchRectangularChecks.checks ctx world work prepared tables message block blowup constructed primitive
    (Frozen dummy field.data.context work (log dummy before field)) draw random groups
  rw [NativeGoldBatchSelectedWord.prepared_word dummy field.data.context ctx world work prepared tables message block blowup constructed,
    NativeGoldBatchRecoveredMatrix.prepared_random ctx world work prepared] at rectangular
  exact ⟨prepared,draw,typed,ordered,rectangular.1,rectangular.2,
    NativeGoldBatchRectangularData.accepted_claim ctx world work prepared choose fuel memory completion executed next status⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedChecks
