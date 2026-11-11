module
public import FormalProof4FHE.HasteBoots.QueryRectangularNativeMeaning
@[expose] public section

/-! Validated original PCS matrices supply their own typed query interpreter.
No decoded query, semantic matrix or successful-reader certificate is input. -/
namespace FormalProof4FHE.HasteBoots.QueryNativeInterpretationComplete
open NativeFields (Goldilocks)
open NativeGoldCoefficientsQuery (readMatrix readPairs interpret)
noncomputable section

theorem matrix (width : ℕ) (raw : NativeGoldMatrix.Matrix)
    (valid : NativeGoldMatrix.validate raw width = true) : ∃ value, readMatrix width raw = some value := by
  exact ⟨NativeGoldMatrixMeaning.semantic width raw valid,by simp only [readMatrix,valid,dite_true]⟩

theorem pairs (width : ℕ) (raw : List NativeGoldCoefficientsQuery.Pair)
    (valid : NativeGoldMatrixWeights.QueryValid width raw) :
    ∃ query, readPairs width raw.length raw = some query := by
  induction raw with
  | nil => exact ⟨.nil,rfl⟩
  | cons head tail ih =>
    have checked := valid head List.mem_cons_self
    obtain ⟨zero,zeroRead⟩ := matrix width head.zero checked.1
    obtain ⟨one,oneRead⟩ := matrix width head.one checked.2
    obtain ⟨rest,restRead⟩ := ih (fun pair member => valid pair (List.mem_cons_of_mem head member))
    exact ⟨.cons (fun bit => if bit then one else zero) rest,
      by simp only [List.length_cons,readPairs,zeroRead,oneRead,restRead,Option.bind_some,Option.map_some]⟩

theorem query (width n : ℕ) (raw : NativeGoldPcsWire.Query)
    (valid : NativeGoldMatrixWeights.QueryValid width raw.models) (length : raw.models.length = n) :
    ∃ value : ExtensionQuery.Broadcast Goldilocks width n, interpret width n ⟨raw.models,none⟩ = some value := by
  subst n
  obtain ⟨value,read⟩ := pairs width raw.models valid
  exact ⟨⟨value,none⟩,by simp only [interpret,read,Option.bind_some,NativeGoldCoefficientsQuery.readPost,Option.map_some]⟩

theorem prepared (ctx : NativeGoldPcsExecution.Context) (world : InputIndexedOracle.World) (work : NativeGoldPcsWorkers.Prepared)
    (executed : (OracleProgram.run ctx.prefix world).run.1 = .prepared work) :
    ∃ value : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val ctx.parameters.numVariables.val,
      interpret ctx.parameters.width.val ctx.parameters.numVariables.val ⟨ctx.query.models,none⟩ = some value := by
  obtain ⟨data⟩ := SingleOpeningFinishing.prepared_encoding ctx world work executed
  exact query _ _ _ data.valid data.size

end
end FormalProof4FHE.HasteBoots.QueryNativeInterpretationComplete
