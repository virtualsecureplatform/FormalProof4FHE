module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularWeights
import all FormalProof4FHETest.HasteBootsBatchMeaningSmoke
open FormalProof4FHE.HasteBoots
open NativeFieldRepresentation (goldValue)
namespace HasteBootsNativeWeightsSmoke
noncomputable section
open HasteBootsBatchMeaningSmoke (usize)

def matrix (values : List NativeFieldRepresentation.GoldWord) (size : values.length < 2^64) : NativeGoldPcsWire.Matrix :=
  ⟨usize 3,⟨values,size⟩⟩
def a := matrix [1,1,0,0,1,0,0,0,1] (by decide)
def b := matrix [1,0,0,1,1,0,0,0,1] (by decide)
def one := matrix [1,0,0,0,1,0,0,0,1] (by decide)
def zero := matrix [0,0,0,0,0,0,0,0,0] (by decide)
def lazyA := matrix [18446744069414584322,18446744069414584322,18446744069414584321,18446744069414584321,18446744069414584322,18446744069414584321,18446744069414584321,18446744069414584321,18446744069414584322] (by decide)
def first : NativeGoldPcsWire.Query := ⟨[(a,one),(b,zero),(zero,zero)],by decide⟩
def aliasedQuery : NativeGoldPcsWire.Query := ⟨[(lazyA,one),(b,zero),(one,one)],by decide⟩
def reversed : NativeGoldPcsWire.Query := ⟨[(b,zero),(a,one),(zero,zero)],by decide⟩
def queries : NativePrefixCodec.Vector NativeGoldPcsWire.Query := ⟨[first,aliasedQuery,reversed],by decide⟩
def query := first.models.take 2

theorem valid : NativeGoldMatrixWeights.QueryValid 3 query := by
  intro pair member
  change pair ∈ [NativeGoldPcsWire.pairModel (a,one),NativeGoldPcsWire.pairModel (b,zero)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> constructor <;> decide +kernel
def computed := NativeGoldMatrixWeights.weights 3 query
theorem present : computed.isSome = true := by decide +kernel
def weights := computed.get present
theorem weights_spec : NativeGoldMatrixWeights.weights 3 query = some weights := (Option.some_get present).symm
example : NativeGoldMatrixWeights.weights 0 [] = none := by decide +kernel
example : (NativeGoldMatrixWeights.weights 3 []).map List.length = some 1 := by decide +kernel
example : NativeGoldPcsArithmetic.structured 3 1 [] = none := by decide +kernel
example : weights.length = 4 := by decide +kernel
-- The zero/zero branch is B*A, and address one is B*I.
example : goldValue ((NativeGoldPcsArithmetic.layout 3 weights)[0]?.getD 0) = 1 := by decide +kernel
example : goldValue ((NativeGoldPcsArithmetic.layout 3 weights)[3]?.getD 0) = 1 := by decide +kernel
example : goldValue ((NativeGoldPcsArithmetic.layout 3 weights)[12+0*3+1]?.getD 0) = 2 := by decide +kernel
example : goldValue ((NativeGoldPcsArithmetic.layout 3 weights)[6]?.getD 0) = 0 := by decide +kernel
-- Swapping the original pair order produces A*B and changes entry (0,0).
def reverseWeights := (NativeGoldMatrixWeights.weights 3 (reversed.models.take 2)).get (by decide +kernel)
example : goldValue ((NativeGoldPcsArithmetic.layout 3 reverseWeights)[0]?.getD 0) = 2 := by decide +kernel
example : ∀ (lane : Fin 3) (cell : Fin (2^(query.map (NativeGoldPackedMeaning.pairValue 3)).length)) (channel : Fin 3),
    goldValue ((NativeGoldPcsArithmetic.layout 3 weights)[lane.val*((2^query.length)*3)+cell.val*3+channel.val]?.getD 0) =
      RectangularMatrixResponse.weights (FlatMatrixFold.weights (query.map (NativeGoldPackedMeaning.pairValue 3))) lane (cell,channel) :=
  NativeGoldWeightLayout.computed_get 3 query weights (by decide) (by decide) valid weights_spec

example : NativeGoldQueryGroups.groupCount 2 queries = 2 := by decide +kernel
example : (NativeGoldQueryGroups.group 2 queries ⟨0,by decide⟩).val = 0 := by decide +kernel
example : (NativeGoldQueryGroups.group 2 queries ⟨1,by decide⟩).val = 0 := by decide +kernel
example : (NativeGoldQueryGroups.group 2 queries ⟨2,by decide⟩).val = 1 := by decide +kernel
example : (NativeGoldQueryGroups.representative 2 queries ⟨0,by decide +kernel⟩).val = 0 := by decide +kernel
example : (first.models.take 2).map (NativeGoldPackedMeaning.pairValue 3) =
    (aliasedQuery.models.take 2).map (NativeGoldPackedMeaning.pairValue 3) :=
  NativeGoldQueryWeightMeaning.prefix_value 3 2 first aliasedQuery (by decide +kernel)

-- The actual three-packing/four-code-coordinate prepared batch, with two
-- original queries sharing one group, supplies each original left weight.
open HasteBootsBatchMeaningSmoke (ctx world work prepared)
example : ctx.parameters.width.val = 3 ∧ ctx.parameters.code.blockWidth.val = 4 := by decide +kernel
example (index : Fin work.binding.queries.val.length) :
    ∃ words, work.weights[(NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val]? = some words ∧
      ∀ (lane : Fin ctx.parameters.width.val)
        (cell : Fin (2^(((work.binding.queries.val.get index).models.take ctx.parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue ctx.parameters.width.val)).length))
        (channel : Fin ctx.parameters.width.val),
        NativeGoldColumnChecks.view words (lane.val*work.geometry.rows+cell.val*ctx.parameters.width.val+channel.val) =
          RectangularMatrixResponse.weights
            (FlatMatrixFold.weights (((work.binding.queries.val.get index).models.take ctx.parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue ctx.parameters.width.val))) lane (cell,channel) :=
  NativeGoldBatchWeightMeaning.prepared_original ctx world work prepared index
example : (NativeGoldBatchRectangularWeights.rowEquiv ctx world work prepared (⟨1,by decide +kernel⟩,⟨2,by decide +kernel⟩)).val = 5 := by decide +kernel
example (values : ℕ → ℕ → NativeFields.Goldilocks)
    (symbol : Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code)))
    (row : NativeGoldBatchRectangularWeights.Row ctx) (component : Fin ctx.parameters.code.blockWidth.val) :
    NativeGoldBatchRectangularWeights.source ctx world work prepared values symbol row component =
      values symbol.val ((row.1.val*ctx.parameters.width.val+row.2.val)*ctx.parameters.code.blockWidth.val+component.val) := by
  simp only [NativeGoldBatchRectangularWeights.source,NativeGoldBatchLinearEquations.Word,NativeGoldBatchRectangularWeights.rowEquiv_val]
example (index : Fin work.binding.queries.val.length) :
    ∃ words, work.weights[(NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val]? = some words ∧
      ∀ (lane : Fin ctx.parameters.width.val) (values : ℕ → ℕ → NativeFields.Goldilocks)
        (symbol : Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code))),
        StructuredOpening.combine
          (NativeGoldBatchLinearEquations.Weights work words (Fin.cast (NativeGoldBatchPcsProgram.prepared_binding ctx world work prepared).2.1.symm lane))
          (NativeGoldBatchLinearEquations.Word ctx work values) symbol =
        StructuredOpening.combine (RectangularMatrixResponse.weights (NativeGoldBatchRectangularWeights.left ctx world work prepared index) lane)
          (NativeGoldBatchRectangularWeights.source ctx world work prepared values) symbol :=
  NativeGoldBatchRectangularWeights.original_combine ctx world work prepared index

end
end HasteBootsNativeWeightsSmoke
