module
import FormalProof4FHE.HasteBoots.AccumulatorPackedQueries
import FormalProof4FHETest.HasteBootsPublicMonomialEvaluationSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsPublicMonomialEvaluationSmoke
open PackedSumcheckSubclaim (Query)
open scoped Matrix
open Matrix
namespace HasteBootsAccumulatorPackedSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

def coefficientQuery : Query (ZMod 17) 2 2 := .cons first (.cons second .nil)
def rows : Query (ZMod 17) 2 2 := .cons rowFirst (.cons rowSecond .nil)
def query := AccumulatorPackedQueries.whole coefficientQuery rows halfPair

def vector (index : ℕ) : Fin 2 → ZMod 17 := ![(index+1 : ℕ),(3*index+2 : ℕ)]
def table (cell : MatrixFold.Cube 5) : Fin 2 → ZMod 17 := vector (FlatMatrixFold.index 5 cell).val

def start : MatrixFold.Cube 2 := (true,(true,()))
def finish : MatrixFold.Cube 2 := (false,(true,()))
def endpoint (choice : Bool) (cell : MatrixFold.Cube 2) : Fin 2 → ZMod 17 :=
  let index := (FlatMatrixFold.index 2 cell).val
  ![(index+(if choice then 7 else 1) : ℕ),(2*index+(if choice then 3 else 2) : ℕ)]
def endPoint (choice : Bool) (cell : MatrixFold.Cube 2) : Fin 2 → ZMod 17 := endpoint choice cell+![3,5]
def parsedEndpoint (choice : Bool) (index : ℕ) : Fin 2 → ZMod 17 :=
  ![(index+(if choice then 7 else 1) : ℕ),(2*index+(if choice then 3 else 2) : ℕ)]
def nextIndex (index : ℕ) : ℕ := index%4+4*((index/4+1)%4)+16*(index/16)
def impulseTable (cell : MatrixFold.Cube 5) : Fin 2 → ZMod 17 :=
  let index := (FlatMatrixFold.index 5 cell).val
  if (index/4)%4 = 3 then parsedEndpoint (decide (16 ≤ index)) (index%4) else 0
def output (cell : MatrixFold.Cube 5) : Fin 2 → ZMod 17 :=
  let index := (FlatMatrixFold.index 5 cell).val
  vector (nextIndex index)-
    (if (index/4)%4 = 3 then parsedEndpoint (decide (16 ≤ index)) (index%4) else 0)+
    (if (index/4)%4 = 2 then parsedEndpoint (decide (16 ≤ index)) (index%4)+![3,5] else 0)
def duplicate (cell : MatrixFold.Cube 5) : Fin 2 → ZMod 17 := vector ((FlatMatrixFold.index 5 cell).val%16)

-- Complete source addresses and the original matrix order remain inspectable.
example : (FlatMatrixFold.index 5 (AccumulatorPackedQueries.coordinate (c := 2) (r := 2) (true,(false,())) finish true)).val = 25 := by decide +kernel
example : query.toList = [first,second,rowFirst,rowSecond,halfPair] := rfl
example : query.fold table = ![9,1] := by decide +kernel
example : ((AccumulatorPackedQueries.shiftWhole coefficientQuery rows halfPair).map (fun branch => branch.fold table)).sum = ![6,0] := by decide +kernel
example : (AccumulatorPackedQueries.shiftWhole coefficientQuery rows halfPair).map (fun branch => branch.toList.take 2) =
    [coefficientQuery.toList,coefficientQuery.toList,coefficientQuery.toList] := by decide +kernel
example : (AccumulatorPackedQueries.shiftWhole coefficientQuery rows halfPair).map (fun branch => branch.toList.getLast?) =
    [some halfPair,some halfPair,some halfPair] := by decide +kernel
example : (AccumulatorPackedQueries.whole coefficientQuery (AccumulatorShiftQueries.selected finish) halfPair).fold table = ![6,7] := by decide +kernel

-- A half selected with the summed matrices equals the duplicated source.
theorem copies : ∀ (cell row : MatrixFold.Cube 2) (choice : Bool),
    duplicate (AccumulatorPackedQueries.coordinate cell row choice) = table (AccumulatorPackedQueries.coordinate cell row false) := by decide +kernel
example : (AccumulatorPackedQueries.whole coefficientQuery rows (AccumulatorPackedQueries.selectHalf halfPair false)).fold table = query.fold duplicate :=
  AccumulatorPackedQueries.duplicate_fold coefficientQuery rows false halfPair table duplicate copies

-- The endpoint correction has its row matrix on the inside of both half matrices.
theorem pointmass : ∀ (cell row : MatrixFold.Cube 2) (choice : Bool), impulseTable (AccumulatorPackedQueries.coordinate cell row choice) =
    AccumulatorPackedQueries.impulse start (endpoint choice cell) row := by decide +kernel
example : query.fold impulseTable =
    halfPair false *ᵥ (AccumulatorShiftQueries.weight rows start *ᵥ coefficientQuery.fold (endpoint false)) +
    halfPair true *ᵥ (AccumulatorShiftQueries.weight rows start *ᵥ coefficientQuery.fold (endpoint true)) :=
  AccumulatorPackedQueries.whole_impulse coefficientQuery rows halfPair start endpoint impulseTable pointmass
example : query.fold impulseTable = ![14,12] := by decide +kernel
example : AccumulatorShiftQueries.weight rows start *ᵥ
    (halfPair false *ᵥ coefficientQuery.fold (endpoint false)+halfPair true *ᵥ coefficientQuery.fold (endpoint true)) ≠ ![14,12] := by decide +kernel

-- A pointwise corrected cyclic constraint yields the literal full check.
theorem cyclic : ∀ (cell row : MatrixFold.Cube 2) (choice : Bool),
    table (AccumulatorPackedQueries.coordinate cell (AccumulatorShiftQueries.successor row) choice)-output (AccumulatorPackedQueries.coordinate cell row choice) =
      AccumulatorPackedQueries.impulse start (endpoint choice cell) row-
      AccumulatorPackedQueries.impulse finish (endPoint choice cell) row := by decide +kernel
example : ((AccumulatorPackedQueries.shiftWhole coefficientQuery rows halfPair).map (fun branch => branch.fold table)).sum-query.fold output =
    AccumulatorPackedQueries.correction coefficientQuery halfPair (AccumulatorShiftQueries.weight rows start) endpoint-
    AccumulatorPackedQueries.correction coefficientQuery halfPair (AccumulatorShiftQueries.weight rows finish) endPoint :=
  AccumulatorPackedQueries.continuity_check coefficientQuery rows halfPair start finish endpoint endPoint table output cyclic
example : ((AccumulatorPackedQueries.shiftWhole coefficientQuery rows halfPair).map (fun branch => branch.fold table)).sum-query.fold output = ![15,4] := by decide +kernel

-- With no coefficient/round bits, the original half query is still retained.
example : AccumulatorPackedQueries.shiftWhole (.nil : Query (ZMod 17) 2 0) .nil halfPair = [.cons halfPair .nil] := rfl
-- Original source opening counts, without merging slots or shift branches.
example : List.ofFn (fun role : Fin 7 => (AccumulatorPackedQueries.queries coefficientQuery rows halfPair finish role).length) =
    [5,1,3,2,1,1,1] := by decide +kernel
example : AccumulatorPackedQueries.queries coefficientQuery rows halfPair finish 0 =
    query :: AccumulatorPackedQueries.whole coefficientQuery (AccumulatorShiftQueries.selected (AccumulatorShiftQueries.zero 2)) halfPair ::
      AccumulatorPackedQueries.shiftWhole coefficientQuery rows halfPair := rfl
example : (AccumulatorPackedQueries.queries (.nil : Query (ZMod 17) 2 0) .nil halfPair () 0).length = 3 := rfl

end
end HasteBootsAccumulatorPackedSmoke
