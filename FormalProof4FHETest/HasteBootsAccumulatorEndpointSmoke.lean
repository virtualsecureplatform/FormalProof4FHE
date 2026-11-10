module
import FormalProof4FHE.HasteBoots.AccumulatorEndpointSoundness
import FormalProof4FHETest.HasteBootsAccumulatorMatrixSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsAccumulatorMatrixSmoke
open HasteBootsPublicMonomialEvaluationSmoke
open PackedSumcheckSubclaim (Query)
open OracleSpec OracleComp
open scoped Matrix
namespace HasteBootsAccumulatorEndpointSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
local instance : SampleableType (Fin 2 → ZMod 17) := SampleableType.ofFintype _

def actualEndpoint (choice : Bool) (cell : MatrixFold.Cube 1) : Fin 2 → ZMod 17 :=
  good.input (AccumulatorPackedQueries.coordinate cell (show MatrixFold.Cube 1 from (false,())) choice)
def honest : AccumulatorMatrixSoundness.Sources (ZMod 17) 2 1 1 :=
  { good with initial := actualEndpoint, final := actualEndpoint }

theorem honest_holds : AccumulatorEndpointSoundness.FullHolds honest := by
  constructor
  · unfold AccumulatorMatrixSoundness.Holds
    decide +kernel
  · unfold AccumulatorEndpointSoundness.Holds
    decide +kernel

theorem bad_endpoint : ¬AccumulatorEndpointSoundness.Holds good := by
  intro holds
  have zero := congrFun (congrFun (holds false) (false,(false,()))) (0 : Fin 2)
  have nonzero : AccumulatorEndpointSoundness.residual good false (false,(false,())) (0 : Fin 2) ≠ 0 := by decide +kernel
  exact nonzero zero

theorem bad_full : ¬AccumulatorEndpointSoundness.FullHolds good := fun holds => bad_endpoint holds.2

-- Row pairs are absent from the endpoint projection; coefficient and half
-- matrices keep their original values and order.
example : (MatrixQueryProjection.endpoint (c := 1) (r := 1) query).toList = [first,halfPair] := rfl
example : MatrixQueryProjection.endpoint (c := 1) (r := 1) query =
    AccumulatorPackedQueries.append (AccumulatorQuerySplit.parts (c := 1) (r := 1) query).1
      (.cons (AccumulatorQuerySplit.parts (c := 1) (r := 1) query).2.2 .nil) :=
  MatrixQueryProjection.endpoint_parts (c := 1) (r := 1) query
example : (MatrixQueryProjection.erase 1 0 1 (.cons first (.cons halfPair .nil))).toList = [first,halfPair] := rfl
example : (MatrixQueryProjection.erase 0 1 1 (.cons rowFirst (.cons halfPair .nil))).toList = [halfPair] := rfl

-- The preceding endpoint-only counterexample is now detected, even though
-- its five full-dimension residuals all vanish.
example : AccumulatorMatrixSoundness.CoreCheck good query :=
  AccumulatorMatrixSoundness.honest_coreCheck good good_holds query
example : ¬AccumulatorEndpointSoundness.Check good query := by
  unfold AccumulatorEndpointSoundness.Check
  decide +kernel
example : (MatrixQueryProjection.endpoint (c := 1) (r := 1) query).fold
    (AccumulatorEndpointSoundness.residual good false) = ![7,3] := by decide +kernel
example : (AccumulatorEndpointSoundness.rowQuery (c := 1) (r := 1) query (show MatrixFold.Cube 1 from (false,()))).fold good.input = ![7,3] := by decide +kernel
example : AccumulatorEndpointSoundness.expected (c := 1) (r := 1) query honest.initial = ![7,3] := by decide +kernel
example : AccumulatorEndpointSoundness.Check honest query :=
  AccumulatorEndpointSoundness.honest_check honest honest_holds.2 query
example : AccumulatorEndpointSoundness.FullCheck honest query :=
  ⟨AccumulatorMatrixSoundness.honest_coreCheck honest honest_holds.1 query,
    AccumulatorEndpointSoundness.honest_check honest honest_holds.2 query⟩
example : AccumulatorEndpointSoundness.FullCheck good zeroQuery := by
  unfold AccumulatorEndpointSoundness.FullCheck AccumulatorEndpointSoundness.Check AccumulatorMatrixSoundness.CoreCheck
  decide +kernel

-- The marginal law is derived from the full sampler; row draws are not
-- removed from the original experiment or its eventual work accounting.
example : MatrixQueryProjection.endpoint (c := 1) (r := 1) <$> MatrixCompression.sample nodes 3 =ᵈ
    MatrixCompression.sample nodes 2 := MatrixQueryProjection.sample_endpoint nodes 1 1

example : Pr{let sampled ← MatrixCompression.sample nodes 3}[AccumulatorEndpointSoundness.Check good sampled] ≤
    (18 : ENNReal)/289 := by
  have bound := AccumulatorEndpointSoundness.fresh_endpoint_bound nodes good bad_endpoint
  norm_num [ZMod.card] at bound
  calc
    _ ≤ (2 : ENNReal)*((3 : ENNReal)/17)^2 := bound
    _ = _ := by norm_num [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← mul_assoc]

-- All seven constraints use the same query and the original full-dimension
-- bound, without an endpoint-count or seven-constraint multiplier.
example : Pr{let sampled ← MatrixCompression.sample nodes 3}[AccumulatorEndpointSoundness.FullCheck good sampled] ≤
    (27 : ENNReal)/289 := by
  have bound := AccumulatorEndpointSoundness.fresh_full_bound nodes good bad_full
  norm_num [ZMod.card] at bound
  calc
    _ ≤ (3 : ENNReal)*((3 : ENNReal)/17)^2 := bound
    _ = _ := by norm_num [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← mul_assoc]
end
end HasteBootsAccumulatorEndpointSmoke
