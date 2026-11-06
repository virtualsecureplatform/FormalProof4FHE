module
public import FormalProof4FHE.HasteBoots.NativeGoldQueryWeightMeaning
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFinishingMeaning
@[expose] public section

/-! Actual native batch preparation computes the left weights for every group.
The first original group owner supplies the raw computation; all original
queries in that group retain the same ordered semantic left prefix. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchWeightMeaning
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (description)
open NativeGoldPackedMeaning (pairValue)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem prepared_dimensions (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    ctx.parameters.width.val ≠ 0 ∧ ctx.parameters.width.val*ctx.parameters.width.val < 2^64 ∧
      work.geometry.rows = 2^ctx.parameters.leftVariables.val*ctx.parameters.width.val := by
  have spec := NativeBrakedownParameters.build_spec description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work executed)
  refine ⟨spec.basic.1,?_,?_⟩
  · have bound := spec.allocations.2.2.2.2.1
    have positive : 0 < 2^ctx.parameters.leftVariables.val := pow_pos (by decide) _
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ positive)) bound
  · rw [spec.computed]
    rfl

theorem prepared_group (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (group : Fin (NativeGoldQueryGroups.groupCount ctx.parameters.leftVariables.val work.binding.queries)) :
    ∃ words, work.weights[group.val]? = some words ∧
      NativeGoldPcsArithmetic.structured ctx.parameters.width.val ctx.parameters.leftVariables.val
        (work.binding.queries.val.get (NativeGoldQueryGroups.representative ctx.parameters.leftVariables.val work.binding.queries group)).models = some words := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,computed,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  obtain ⟨bounded,read⟩ := NativeGoldBatchColumns.structured_group ctx.parameters binding.queries weights computed group
  exact ⟨weights[group.val],List.getElem?_eq_getElem bounded,read⟩

/-- Every original query reads its group's actual computed weights. The row
stride is the checked native geometry; the right query remains original. -/
theorem prepared_original (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.binding.queries.val.length) :
    ∃ words, work.weights[(NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val]? = some words ∧
      ∀ (lane : Fin ctx.parameters.width.val)
        (cell : Fin (2^(((work.binding.queries.val.get index).models.take ctx.parameters.leftVariables.val).map (pairValue ctx.parameters.width.val)).length))
        (channel : Fin ctx.parameters.width.val),
        NativeGoldColumnChecks.view words (lane.val*work.geometry.rows+cell.val*ctx.parameters.width.val+channel.val) =
          RectangularMatrixResponse.weights
            (FlatMatrixFold.weights (((work.binding.queries.val.get index).models.take ctx.parameters.leftVariables.val).map (pairValue ctx.parameters.width.val))) lane (cell,channel) := by
  let group := NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index
  let owner := NativeGoldQueryGroups.representative ctx.parameters.leftVariables.val work.binding.queries group
  obtain ⟨words,read,computed⟩ := prepared_group ctx world work executed group
  refine ⟨words,read,?_⟩
  have prefixes := NativeGoldQueryWeightMeaning.representative_prefix ctx.parameters.width.val ctx.parameters.leftVariables.val work.binding.queries index
  change ((work.binding.queries.val.get owner).models.take ctx.parameters.leftVariables.val).map (pairValue ctx.parameters.width.val) = _ at prefixes
  rw [← prefixes]
  have valid := NativeGoldBatchPcsProgram.prepared_query_valid ctx world work executed owner
  have dims := prepared_dimensions ctx world work executed
  have size := NativeGoldBatchFinishingMeaning.prepared_query_length ctx world work executed owner
  have spec := NativeBrakedownParameters.build_spec description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work executed)
  have prefixLength : ((work.binding.queries.val.get owner).models.take ctx.parameters.leftVariables.val).length = ctx.parameters.leftVariables.val := by
    rw [List.length_take,size,Nat.min_eq_left spec.basic.2.1]
  intro lane cell channel
  have result := NativeGoldWeightLayout.structured_get ctx.parameters.width.val ctx.parameters.leftVariables.val
    (work.binding.queries.val.get owner).models words dims.1 dims.2.1
    (fun pair member => valid pair (List.mem_of_mem_take member)) computed lane cell channel
  simpa only [NativeGoldColumnChecks.view,dims.2.2,prefixLength] using result
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchWeightMeaning
