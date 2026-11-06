module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchWeightMeaning
public import FormalProof4FHE.HasteBoots.NativeGoldBatchLinearEquations
@[expose] public section

/-! A single query-independent reindexing of the frozen native source rows
exposes the left-cell/source-lane product used by rectangular batch soundness. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularWeights
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldPackedMeaning (pairValue)
open NativeGoldBatchLinearEquations (Weights Word)
open InputIndexedOracle (World)
open OracleProgram (run)
open scoped BigOperators
noncomputable section

abbrev Row (ctx : Context) := Fin (2^ctx.parameters.leftVariables.val) × Fin ctx.parameters.width.val

def rowEquiv (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) : Row ctx ≃ Fin work.geometry.rows :=
  finProdFinEquiv.trans (finCongr (NativeGoldBatchWeightMeaning.prepared_dimensions ctx world work executed).2.2.symm)

theorem rowEquiv_val (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (row : Row ctx) :
    (rowEquiv ctx world work executed row).val = row.1.val*ctx.parameters.width.val+row.2.val := by
  change row.2.val+ctx.parameters.width.val*row.1.val = _
  ring

theorem prefix_length (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.binding.queries.val.length) :
    (((work.binding.queries.val.get index).models.take ctx.parameters.leftVariables.val).map (pairValue ctx.parameters.width.val)).length = ctx.parameters.leftVariables.val := by
  have size := NativeGoldBatchFinishingMeaning.prepared_query_length ctx world work executed index
  have spec := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work executed)
  rw [List.length_map,List.length_take,size,Nat.min_eq_left spec.basic.2.1]

/-- Original ordered left weights, on the common checked left-cell type. -/
def left (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.binding.queries.val.length) (cell : Fin (2^ctx.parameters.leftVariables.val)) :=
  FlatMatrixFold.weights (((work.binding.queries.val.get index).models.take ctx.parameters.leftVariables.val).map (pairValue ctx.parameters.width.val))
    (Fin.cast (congrArg (fun n => 2^n) (prefix_length ctx world work executed index).symm) cell)

theorem original_weights (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.binding.queries.val.length) :
    ∃ words, work.weights[(NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val]? = some words ∧
      ∀ (lane : Fin ctx.parameters.width.val) (row : Row ctx),
        Weights work words (Fin.cast (NativeGoldBatchPcsProgram.prepared_binding ctx world work executed).2.1.symm lane)
          (rowEquiv ctx world work executed row) =
          RectangularMatrixResponse.weights (left ctx world work executed index) lane row := by
  obtain ⟨words,read,meaning⟩ := NativeGoldBatchWeightMeaning.prepared_original ctx world work executed index
  refine ⟨words,read,?_⟩
  intro lane row
  have result := meaning lane (Fin.cast (congrArg (fun n => 2^n) (prefix_length ctx world work executed index).symm) row.1) row.2
  simpa only [Weights,rowEquiv_val,Fin.val_cast,RectangularMatrixResponse.weights,left,Nat.add_assoc] using result

/-- Reindex one immutable source by left cell and source lane. The map uses
only the checked geometry, independently of original queries and groups. -/
def source (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (values : ℕ → ℕ → NativeFields.Goldilocks) :=
  fun symbol row => Word ctx work values symbol (rowEquiv ctx world work executed row)

/-- The same source and the same column position are retained by reindexing;
no extra matrix, draw, decoder or authentication is introduced. -/
theorem combine_reindex (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (weights : Fin work.geometry.rows → NativeFields.Goldilocks)
    (values : ℕ → ℕ → NativeFields.Goldilocks) (symbol : Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code))) :
    StructuredOpening.combine weights (Word ctx work values) symbol =
      StructuredOpening.combine (fun row => weights (rowEquiv ctx world work executed row)) (source ctx world work executed values) symbol := by
  exact ((rowEquiv ctx world work executed).sum_comp (fun row => weights row • Word ctx work values symbol row)).symm
/-- Actual original-query structured combinations use the rectangular left
weights on one query-independent source, at the original column position. -/
theorem original_combine (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.binding.queries.val.length) :
    ∃ words, work.weights[(NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val]? = some words ∧
      ∀ (lane : Fin ctx.parameters.width.val) (values : ℕ → ℕ → NativeFields.Goldilocks)
        (symbol : Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code))),
        StructuredOpening.combine
          (Weights work words (Fin.cast (NativeGoldBatchPcsProgram.prepared_binding ctx world work executed).2.1.symm lane))
          (Word ctx work values) symbol =
        StructuredOpening.combine (RectangularMatrixResponse.weights (left ctx world work executed index) lane)
          (source ctx world work executed values) symbol := by
  obtain ⟨words,read,meaning⟩ := original_weights ctx world work executed index
  refine ⟨words,read,?_⟩
  intro lane values symbol
  rw [combine_reindex ctx world work executed]
  have same := funext (meaning lane)
  rw [same]

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularWeights
