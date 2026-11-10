module
import FormalProof4FHE.HasteBoots.PackedBlindRotationTrace
import FormalProof4FHETest.HasteBootsPackedAccumulatorTraceSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsAccumulatorTraceSmoke HasteBootsHadamardBlindRotationSmoke
open HasteBootsPackedAccumulatorTraceSmoke (rounds embed decompositionA decompositionB holds)
open NativeBlindRotation (Cipher digit)
open OracleSpec OracleComp
namespace HasteBootsPackedBlindRotationTraceSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
local instance : SampleableType (Fin (2^1) → ZMod 17) := SampleableType.ofFintype _

-- Independent packed widths; every lane of every relation is constrained.
def address (width : ℕ) (positive : 0 < width) (half : Bool) (index : Fin 4) : MatrixFold.Cube 3 × Fin width :=
  ((half,(FlatMatrixFold.index 2).symm index),⟨index.val%width,Nat.mod_lt _ positive⟩)

def monomial (round : Fin 3) : PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 1) 3 3 :=
  fun factor cell _ =>
    let index := FlatMatrixFold.index 2 cell.2
    let row := AccumulatorTrace.active rounds.shape round
    match factor with
    | .inl (_,isPublic) => if isPublic then BlindRotationMonomial.powers 2 2 (controls round).2 index
      else BlindRotationNTT.transform 2 2 (tables.input row cell.1) index
    | .inr _ => BlindRotationNTT.transform 2 2 (tables.product row cell.1) index

def external (round : Fin 3) : PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 2) 3 6 :=
  fun factor cell _ =>
    let index := FlatMatrixFold.index 2 cell.2
    let row := AccumulatorTrace.active rounds.shape round
    match factor with
    | .inl (position,isKey) =>
      if isKey then BlindRotationNTT.transform 2 2 ((controls round).1 (position.val == 1) 0 cell.1) index
      else BlindRotationNTT.transform 2 2 (digit 2 (0 : Fin 1) (tables.difference row (position.val == 1))) index
    | .inr _ => BlindRotationNTT.transform 2 2 (tables.external row cell.1) index

def stages (round : Fin 3) : PackedBlindRotationTrace.Stages 17 2 1 3 3 3 6 where
  monomial := monomial round
  monomialAddress := address 3 (by decide +kernel)
  external := external round
  externalAddress := address 6 (by decide +kernel)

theorem multiplication : PackedBlindRotationTrace.AllHolds (c := 1) (lanes := 1) 2 2 rounds tables controls stages := by
  intro round
  fin_cases round <;> constructor <;> (try unfold PBSHadamard.Relation) <;> decide +kernel

-- No coefficient-domain rotation or external-product identity is supplied.
example : NativeBlindRotation.ValidTrace 2 (List.ofFn controls) accumulator
    (List.ofFn (AccumulatorTrace.traceAt rounds.shape tables)) final :=
  PackedBlindRotationTrace.validTrace (c := 1) (lanes := 1) (r := 2)
    2 primitive embed rounds tables accumulator final decompositionA decompositionB holds 2 controls stages multiplication
example : final = NativeBlindRotation.run 2 (List.ofFn controls) accumulator :=
  PackedBlindRotationTrace.output_eq_run (c := 1) (lanes := 1) (r := 2)
    2 primitive embed rounds tables accumulator final decompositionA decompositionB holds 2 controls stages multiplication
example : (address 3 (by decide +kernel) true (2 : Fin 4)).2.val = 2 := by decide +kernel
example : (address 6 (by decide +kernel) false (3 : Fin 4)).2.val = 3 := by decide +kernel
example : (controls (1 : Fin 3)).2 = 0 := by decide +kernel

-- A zero public factor can satisfy the monomial relation with a zero result,
-- but cannot establish the original public powers or the reference rotation.
def wrongPublic : PackedBlindRotationTrace.Stages 17 2 1 3 3 3 6 :=
  { stages 0 with monomial := fun factor cell lane => match factor with
    | .inl (_,false) => monomial 0 factor cell lane
    | _ => 0 }
example : PBSHadamard.Relation wrongPublic.monomial := by
  unfold PBSHadamard.Relation
  decide +kernel
example : ¬PackedBlindRotationTrace.Holds 2 2 (controls 0).2 (controls 0).1
    (tables.input 0) (tables.product 0) (tables.difference 0) (tables.external 0) wrongPublic := by
  intro hypothesis
  have power := hypothesis.publicPowers false
  have wrong : PBSMonomialBlindRotation.project wrongPublic.monomial (wrongPublic.monomialAddress false) (.inl (0,true)) ≠
      BlindRotationMonomial.powers 2 2 (controls 0).2 := by decide +kernel
  exact wrong power

-- Wrong public outputs are covered without an assumed per-round conclusion.
example : Pr{let query ← MatrixCompression.sample (b := 2^1) HasteBootsAccumulatorMatrixSmoke.nodes 4}[
    AccumulatorEndpointSoundness.FullCheck
      (PackedAccumulatorTrace.sources (c := 1) (lanes := 1) embed rounds tables accumulator 0 decompositionA decompositionB) query] ≤
    (36 : ENNReal)/289 := by
  have wrong : (0 : Cipher 17 4) ≠ NativeBlindRotation.run 2 (List.ofFn controls) accumulator := by decide +kernel
  have bound := PackedBlindRotationTrace.wrong_output_bound (c := 1) (lanes := 1) (r := 2)
    HasteBootsAccumulatorMatrixSmoke.nodes 2 primitive embed rounds tables accumulator 0 decompositionA decompositionB
    2 controls stages multiplication wrong
  norm_num [ZMod.card] at bound
  calc
    _ ≤ (4 : ENNReal)*((3 : ENNReal)/17)^2 := bound
    _ = _ := by norm_num [div_eq_mul_inv,mul_pow,← ENNReal.inv_pow,← mul_assoc]
end
end HasteBootsPackedBlindRotationTraceSmoke
