module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchPcsProgram
@[expose] public section

/-! Every original prepared batch row passed its native pair binding check.
The exact raw row length yields a field encoding without changing bytes. -/
namespace FormalProof4FHE.HasteBoots.BatchClaimShape
open NativeGoldBatchPcsProgram (Context Prepared)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem prepared_pair (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.binding.queries.val.length) (row : NativeLookupRequestWire.Row)
    (found : work.binding.values.val[index.val]? = some row) :
    NativeGoldPcsBinding.check ctx.parameters (work.binding.queries.val.get index) row = true := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work prepared
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin NativeGoldBlockCode.description ctx.parameters ctx.parent ctx.root
    ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have bound := (NativeGoldBatchPrelude.sampling_origin NativeGoldBlockCode.description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.1
  obtain ⟨valid,_,_,same,_⟩ := NativeGoldBatchBinding.bound_origin NativeGoldBlockCode.description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound
  cases same
  have checks := (NativeGoldBatchBinding.check_iff _ _ _).mp valid
  have valueBound : index.val < ctx.values.val.length := by rw [← checks.2.1]; exact index.isLt
  have rowEq : ctx.values.val[index.val] = row := Option.some.inj ((List.getElem?_eq_getElem valueBound).symm.trans found)
  rw [← rowEq]
  exact checks.2.2.get index.isLt valueBound

theorem prepared_width (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.binding.queries.val.length) (row : NativeLookupRequestWire.Row)
    (found : work.binding.values.val[index.val]? = some row) : row.val.length = ctx.parameters.width.val :=
  ((NativeGoldPcsBinding.check_iff _ _ _).mp (prepared_pair ctx world work prepared index row found)).2.1

theorem row_encoding (width : ℕ) (row : NativeLookupRequestWire.Row) (length : row.val.length = width) :
    row.val.map NativeFieldRepresentation.goldValue = List.ofFn (fun lane : Fin width =>
      NativeFieldRepresentation.goldValue (row.val[lane.val]?.getD 0)) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,length]
  · intro index inside other
    have bound : index < row.val.length := by simpa only [List.length_map] using inside
    simp only [List.getElem_map,List.getElem_ofFn,List.getElem?_eq_getElem bound,Option.getD_some]

end
end FormalProof4FHE.HasteBoots.BatchClaimShape
