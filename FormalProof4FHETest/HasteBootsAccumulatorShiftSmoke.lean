module
import FormalProof4FHE.HasteBoots.AccumulatorShiftQueries
import FormalProof4FHETest.HasteBootsPublicMonomialEvaluationSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsPublicMonomialEvaluationSmoke
open PackedSumcheckSubclaim (Query)
open scoped Matrix
namespace HasteBootsAccumulatorShiftSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

def query : Query (ZMod 17) 2 2 := .cons rowFirst (.cons rowSecond .nil)
def flatTable : Fin 4 → Fin 2 → ZMod 17 := ![![1,2],![3,4],![5,6],![7,8]]
def table (cell : MatrixFold.Cube 2) : Fin 2 → ZMod 17 := flatTable (FlatMatrixFold.index 2 cell)

-- Original low-bit-first ordering, all carry branches and the wrap branch.
example : query.fold table = ![16,14] := by decide +kernel
example : ((AccumulatorShiftQueries.shifted query).map (fun branch => branch.fold table)).sum = ![1,8] := by decide +kernel
example : (AccumulatorShiftQueries.shifted query).length = 3 := by decide +kernel
example : (AccumulatorShiftQueries.shifted query).map Query.toList =
    [[AccumulatorShiftQueries.selector true (rowFirst false),rowSecond],
     [AccumulatorShiftQueries.selector false 1,
       AccumulatorShiftQueries.selector true (rowSecond false * rowFirst true)],
     [AccumulatorShiftQueries.selector false (rowSecond true * rowFirst true),
       AccumulatorShiftQueries.selector false 1]] := by decide +kernel

-- Independently evaluated branch values expose both noncommuting products.
example : ((AccumulatorShiftQueries.carries query 1).map (fun branch => branch.fold table)) = [![5,10],![10,11]] := by decide +kernel
example : (AccumulatorShiftQueries.wrap query 1).fold table = ![3,4] := by decide +kernel
example : ((AccumulatorShiftQueries.carries query 1).map (fun branch => branch.fold table)).sum ≠ ![1,8] := by decide +kernel

example : ((AccumulatorShiftQueries.shifted query).map (fun branch => branch.fold table)).sum =
    query.fold (fun row => table (AccumulatorShiftQueries.successor row)) :=
  AccumulatorShiftQueries.shifted_fold query table

example : ((AccumulatorShiftQueries.shifted query).map (fun branch => branch.fold table)).sum =
    query.fold (fun row => flatTable ⟨((FlatMatrixFold.index 2 row).val+1)%4,by omega⟩) :=
  AccumulatorShiftQueries.shifted_fold_flat query flatTable

-- The first and last active rows are selected without a matrix challenge.
example : (AccumulatorShiftQueries.selected ((FlatMatrixFold.index 2).symm (0 : Fin 4)) : Query (ZMod 17) 2 2).fold table = ![1,2] := by decide +kernel
example : (AccumulatorShiftQueries.selected ((FlatMatrixFold.index 2).symm (2 : Fin 4)) : Query (ZMod 17) 2 2).fold table = ![5,6] := by decide +kernel
example : (AccumulatorShiftQueries.selected ((FlatMatrixFold.index 2).symm (3 : Fin 4)) : Query (ZMod 17) 2 2).fold table = ![7,8] := by decide +kernel

-- Binary carry and wrap agree with the scalar flat row addresses.
example : (FlatMatrixFold.index 2 (AccumulatorShiftQueries.successor ((FlatMatrixFold.index 2).symm (1 : Fin 4)))).val = 2 := by decide +kernel
example : (FlatMatrixFold.index 2 (AccumulatorShiftQueries.successor ((FlatMatrixFold.index 2).symm (3 : Fin 4)))).val = 0 := by decide +kernel

-- No row variables: native shift_queries returns the single original query.
example : AccumulatorShiftQueries.shifted (.nil : Query (ZMod 17) 2 0) = [.nil] := rfl
example : ((AccumulatorShiftQueries.shifted (.nil : Query (ZMod 17) 2 0)).map
    (fun branch => branch.fold (fun _ => (![9,10] : Fin 2 → ZMod 17)))).sum = ![9,10] := by decide +kernel
end
end HasteBootsAccumulatorShiftSmoke
