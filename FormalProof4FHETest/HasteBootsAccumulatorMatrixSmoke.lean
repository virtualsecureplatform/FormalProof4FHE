module
public import FormalProof4FHE.HasteBoots.AccumulatorMatrixSoundness
public import FormalProof4FHETest.HasteBootsPublicMonomialEvaluationSmoke
@[expose] public section
open FormalProof4FHE.HasteBoots
open HasteBootsPublicMonomialEvaluationSmoke
open PackedSumcheckSubclaim (Query)
open OracleSpec OracleComp
open scoped Matrix
namespace HasteBootsAccumulatorMatrixSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

-- The complete source is fixed independently of all matrix queries.
def input (cell : MatrixFold.Cube 3) : Fin 2 → ZMod 17 :=
  let p := AccumulatorQuerySplit.coordinates 1 1 cell
  let index := (FlatMatrixFold.index 1 p.1).val
  if p.2.2 then ![(index+3 : ℕ),(index+4 : ℕ)] else ![(index+1 : ℕ),(index+2 : ℕ)]

def good : AccumulatorMatrixSoundness.Sources (ZMod 17) 2 1 1 where
  input := input
  product := input
  difference := 0
  external := 0
  output := input
  duplicateA := AccumulatorMatrixSoundness.copyHalf input false
  duplicateB := AccumulatorMatrixSoundness.copyHalf input true
  initial := 0
  final := 0
  start := (true,())
  finish := (true,())

def bad : AccumulatorMatrixSoundness.Sources (ZMod 17) 2 1 1 :=
  { good with difference := fun cell => if (FlatMatrixFold.index 3 cell).val = 0 then ![1,0] else 0 }

def query : Query (ZMod 17) 2 3 :=
  AccumulatorPackedQueries.whole (.cons first .nil) (.cons rowFirst .nil) halfPair

def zeroQuery : Query (ZMod 17) 2 3 := .cons (fun _ => 0) (.cons (fun _ => 0) (.cons (fun _ => 0) .nil))

theorem good_holds : AccumulatorMatrixSoundness.Holds good := by
  unfold AccumulatorMatrixSoundness.Holds
  decide +kernel

theorem bad_false : ¬AccumulatorMatrixSoundness.Holds bad := by
  intro holds
  have zero := congrFun (congrFun (holds (0 : Fin 5)) (false,(false,(false,())))) (0 : Fin 2)
  have nonzero : AccumulatorMatrixSoundness.residual bad (0 : Fin 5) (false,(false,(false,()))) (0 : Fin 2) ≠ 0 := by decide +kernel
  exact nonzero zero

-- Every arbitrary complete query has the exact coefficient/row/half split.
example : AccumulatorPackedQueries.whole (AccumulatorQuerySplit.parts (c := 1) (r := 1) query).1
    (AccumulatorQuerySplit.parts (c := 1) (r := 1) query).2.1 (AccumulatorQuerySplit.parts (c := 1) (r := 1) query).2.2 = query :=
  AccumulatorQuerySplit.rebuild (c := 1) (r := 1) query
example : (AccumulatorQuerySplit.parts (c := 1) (r := 1) query).1.toList = [first] := rfl
example : (AccumulatorQuerySplit.parts (c := 1) (r := 1) query).2.1.toList = [rowFirst] := rfl
example : (AccumulatorQuerySplit.parts (c := 1) (r := 1) query).2.2 = halfPair := rfl
example : AccumulatorQuerySplit.coordinates 1 1 (AccumulatorPackedQueries.coordinate (c := 1) (r := 1) (true,()) (false,()) true) =
    ((true,()),((false,()),true)) :=
  AccumulatorQuerySplit.coordinates_apply (c := 1) (r := 1) (true,()) (false,()) true

example : AccumulatorMatrixSoundness.CoreCheck good query :=
  AccumulatorMatrixSoundness.honest_coreCheck good good_holds query
example : ¬AccumulatorMatrixSoundness.CoreCheck bad query := by
  unfold AccumulatorMatrixSoundness.CoreCheck
  decide +kernel
example : query.fold (AccumulatorMatrixSoundness.residual bad 0) = ![1,0] := by decide +kernel
example : query.fold (AccumulatorMatrixSoundness.residual bad 0) = AccumulatorMatrixSoundness.error bad query 0 :=
  AccumulatorMatrixSoundness.fold_residual bad query 0

-- A chosen zero query passes a false source. Freshness cannot be dropped.
example : AccumulatorMatrixSoundness.CoreCheck bad zeroQuery := by
  unfold AccumulatorMatrixSoundness.CoreCheck
  decide +kernel

-- Core validity deliberately does not assert the two public endpoint checks.
example : good.input (AccumulatorPackedQueries.coordinate (c := 1) (r := 1) (false,()) (false,()) false) ≠ good.initial false (false,()) := by decide +kernel

def nodes : PackedSumcheckRound.Node 2 ↪ ZMod 17 where
  toFun := fun entry => (2*entry.2.val+(if entry.1 then 1 else 0) : ℕ)
  inj' := by decide +kernel

local instance : SampleableType (Fin 2 → ZMod 17) := SampleableType.ofFintype _

-- Concrete fresh-query instantiation, with no factor for the five constraints.
example : Pr{let sampled ← MatrixCompression.sample nodes 3}[AccumulatorMatrixSoundness.CoreCheck bad sampled] ≤
    (27 : ENNReal)/289 := by
  have bound := AccumulatorMatrixSoundness.fresh_core_bound nodes bad bad_false
  norm_num [ZMod.card] at bound
  calc
    _ ≤ (3 : ENNReal)*((3 : ENNReal)/17)^2 := bound
    _ = _ := by norm_num [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← mul_assoc]
end
end HasteBootsAccumulatorMatrixSmoke
