module
import FormalProof4FHE.HasteBoots.PBSMonomialBlindRotation
import FormalProof4FHETest.HasteBootsHadamardBlindRotationSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsHadamardBlindRotationSmoke
open NativeBlindRotation (Poly Cipher rotate)
namespace HasteBootsMonomialBlindRotationSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

-- Explicit coefficients cover both signs and a second complete turn.
example : rotate 0 left = left := by decide +kernel
example : rotate 4 left = -left := by decide +kernel
example : rotate 8 left = left := by decide +kernel
example : rotate 9 left = polynomial 13 1 2 3 := by decide +kernel
-- Unbounded exponents belong to the mathematical action. The native plan
-- accepts only rotations below 2N; this is not a native acceptance example.
example : rotate 10001 left = polynomial 13 1 2 3 := by decide +kernel
example : BlindRotationNTT.transform 2 (2 : ZMod 17) (rotate 5 left) =
    BlindRotationNTT.transform 2 (2 : ZMod 17) left * BlindRotationMonomial.powers 2 2 5 :=
  BlindRotationMonomial.transform_rotate 2 2 primitive left 5

def product : Cipher 17 4 := fun half =>
  if half then polynomial 5 1 15 13 else polynomial 5 4 2 16

def monomialTables (result : Cipher 17 4) :
    PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 1) 3 1 :=
  fun factor cell _ =>
    let index := FlatMatrixFold.index 2 cell.2
    match factor with
    | .inl (_,isPublic) => if isPublic then BlindRotationMonomial.powers 2 2 1 index
      else transform (accumulator cell.1) index
    | .inr _ => transform (result cell.1) index

theorem monomialRelation : PBSHadamard.Relation (monomialTables product) := by
  unfold PBSHadamard.Relation
  decide +kernel

theorem source : ∀ half, BlindRotationNTT.transform 2 (2 : ZMod 17) (accumulator half) =
    PBSMonomialBlindRotation.project (monomialTables product) (address half) (.inl (0,false)) := by
  intro half
  funext index
  cases half <;> fin_cases index <;> decide +kernel

theorem publicPowers : ∀ half,
    PBSMonomialBlindRotation.project (monomialTables product) (address half) (.inl (0,true)) =
      BlindRotationMonomial.powers 2 2 1 := by
  intro half
  funext index
  cases half <;> fin_cases index <;> decide +kernel

theorem monomialResult : ∀ half, BlindRotationNTT.transform 2 (2 : ZMod 17) (trace.product half) =
    PBSMonomialBlindRotation.project (monomialTables product) (address half) (.inr ()) := by
  intro half
  funext index
  cases half <;> fin_cases index <;> decide +kernel

-- No coefficient rotation equality is supplied to this composed step theorem.
example : NativeBlindRotation.ValidStep 2 control 1 accumulator trace :=
  PBSMonomialBlindRotation.validStep_of_relations (log := 2) (levels := 1) (cells := 3) (width := 1)
    2 primitive 2 1 control accumulator trace (monomialTables product) address
    monomialRelation source publicPowers monomialResult (tables output) address
    (by decide +kernel) rfl hadamard digits keys result

-- Both halves are constrained. Corrupting the true half breaks the relation.
def corruptedProduct : Cipher 17 4 := fun half =>
  if half then polynomial 6 1 15 13 else product false
example : ¬PBSHadamard.Relation (monomialTables corruptedProduct) := by
  unfold PBSHadamard.Relation
  decide +kernel

-- A truthful Hadamard relation with a wrong public factor cannot establish
-- the required rotation: the public-power premise is independently necessary.
def wrongPublicTables :
    PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 1) 3 1 :=
  fun factor cell _ => match factor with
    | .inl (_,false) => transform (accumulator cell.1) (FlatMatrixFold.index 2 cell.2)
    | .inl (_,true) => 0
    | .inr _ => 0
example : PBSHadamard.Relation wrongPublicTables := by
  unfold PBSHadamard.Relation
  decide +kernel
example : PBSMonomialBlindRotation.project (log := 2) wrongPublicTables (address true) (.inl (0,true)) ≠
    BlindRotationMonomial.powers 2 2 1 := by decide +kernel
end
end HasteBootsMonomialBlindRotationSmoke
