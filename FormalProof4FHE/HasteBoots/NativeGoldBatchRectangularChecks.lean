module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularData
@[expose] public section

/-! All native response groups use one frozen source and the same ordered
column draw vector. The random matrix and structured weights below are actual
native words projected through the common geometry bijection. No independence
or fresh-challenge law is asserted by this deterministic transport. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularChecks
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (Tables logSize)
open NativeGoldBatchResponseMeaning (Lane Domain)
open NativeGoldBatchLinearEquations (Weights Word Frozen)
open NativeGoldBatchRectangularWeights (source)
open NativeGoldBatchRectangularData (Group evaluationIndex weightIndex encoded messages testMessages left)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def lane (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (index : Fin ctx.parameters.width.val) : Fin work.width :=
  Fin.cast (NativeGoldBatchPcsProgram.prepared_binding ctx world work prepared).2.1.symm index

def random (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (index : Fin ctx.parameters.width.val)
    (row : NativeGoldBatchRectangularWeights.Row ctx) :=
  Weights work work.random (lane ctx world work prepared index) (NativeGoldBatchRectangularWeights.rowEquiv ctx world work prepared row)

theorem group_combine (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (group : Group ctx work) (index : Fin ctx.parameters.width.val)
    (values : ℕ → ℕ → NativeFields.Goldilocks) (symbol : Fin (2^(logSize ctx.parameters.code))) :
    StructuredOpening.combine (Weights work (work.weights.get (weightIndex ctx world work prepared group)) (lane ctx world work prepared index))
      (Word ctx work values) symbol =
    StructuredOpening.combine (RectangularMatrixResponse.weights (left ctx world work prepared group) index) (source ctx world work prepared values) symbol := by
  obtain ⟨words,read,meaning⟩ := NativeGoldBatchRectangularWeights.original_combine ctx world work prepared (NativeGoldBatchRectangularData.owner ctx work group)
  change work.weights[(NativeGoldBatchRectangularData.groupOf ctx work (NativeGoldBatchRectangularData.owner ctx work group)).val]? = some words at read
  rw [NativeGoldBatchRectangularData.owner_group] at read
  have actual : work.weights[group.val]? = some (work.weights.get (weightIndex ctx world work prepared group)) :=
    List.getElem?_eq_getElem (weightIndex ctx world work prepared group).isLt
  have same : words = work.weights.get (weightIndex ctx world work prepared group) := Option.some.inj (read.symm.trans actual)
  subst words
  exact meaning index values symbol

/-- All native random/group column agreements become the rectangular checks
on the same reindexed source and ordered draws. -/
theorem checks (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (values : ℕ → ℕ → NativeFields.Goldilocks)
    (draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code)))
    (randomChecks : ∀ index : Fin work.width, ColumnOpening.Agrees
      (StructuredOpening.combine (Weights work work.random index) (Word ctx work values)) (Lane ctx work work.test index.val) draw)
    (groupChecks : ∀ response ∈ work.groups, ∀ index : Fin work.width, ColumnOpening.Agrees
      (StructuredOpening.combine (Weights work response.1 index) (Word ctx work values)) (Lane ctx work response.2 index.val) draw) :
    RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val) (Domain ctx primitive)
      (source ctx world work prepared values) (random ctx world work prepared) (testMessages ctx work) draw ∧
    ∀ test : Group ctx work × Fin ctx.parameters.width.val, ColumnOpening.Agrees
      (StructuredOpening.combine (RectangularBatchOpeningKernel.weights (left ctx world work prepared) test)
        (source ctx world work prepared values))
      (BlockEncoder.encode (Domain ctx primitive) (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (messages ctx work test.1 test.2))) draw := by
  constructor
  · intro index query
    have checked := randomChecks (lane ctx world work prepared index) query
    rw [NativeGoldBatchRectangularWeights.combine_reindex ctx world work prepared] at checked
    have coding := congrFun (NativeGoldBatchRectangularData.test_encoded_messages ctx world work prepared tables message block blowup constructed primitive) index
    change _ = Lane ctx work work.test index.val (draw query) at checked
    rw [coding] at checked
    exact checked
  · intro test query
    have checked := groupChecks _ (NativeGoldBatchRectangularData.group_pair ctx world work prepared test.1) (lane ctx world work prepared test.2) query
    change StructuredOpening.combine (Weights work (work.weights.get (weightIndex ctx world work prepared test.1)) (lane ctx world work prepared test.2))
      (Word ctx work (values)) (draw query) = encoded ctx world work prepared test.1 test.2 (draw query) at checked
    rw [group_combine ctx world work prepared] at checked
    rw [NativeGoldBatchRectangularData.encoded_messages ctx world work prepared tables message block blowup constructed primitive] at checked
    exact checked

/-- The source, actual typed draws (including repetitions), and every test
and group check are obtained from one actual native source witness. -/
theorem source_checks (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (history : List Observation) (available : NativeGoldBatchAnySourceRisk.HasSource dummy ctx work history world) :
    ∃ (context : Digest) (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest)
      (draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code))),
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
      (∀ index : NativeMerkleShapeFamily.Height,
        ⟨(context,index),⟨work.root,log⟩⟩ ∈ (NativeGoldBatchFamilyAvailability.reconstructed dummy history).checkpoints.checkpoints) ∧
      NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val) (Domain ctx primitive)
        (source ctx world work prepared (Frozen dummy context work log)) (random ctx world work prepared) (testMessages ctx work) draw ∧
      ∀ test : Group ctx work × Fin ctx.parameters.width.val, ColumnOpening.Agrees
        (StructuredOpening.combine (RectangularBatchOpeningKernel.weights (left ctx world work prepared) test)
          (source ctx world work prepared (Frozen dummy context work log)))
        (BlockEncoder.encode (Domain ctx primitive) (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (messages ctx work test.1 test.2))) draw := by
  obtain ⟨context,log,draw,hashed,snapshots,typed,ordered,randomChecks,groupChecks⟩ :=
    NativeGoldBatchOrderedChecks.source_agrees dummy ctx world work prepared tables message block blowup constructed history available
  have transported := checks ctx world work prepared tables message block blowup constructed primitive
    (Frozen dummy context work log) draw randomChecks groupChecks
  exact ⟨context,log,draw,hashed,snapshots,typed,ordered,transported.1,transported.2⟩

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularChecks
