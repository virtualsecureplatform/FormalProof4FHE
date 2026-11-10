module
import FormalProof4FHE.HasteBoots.PublicMonomialTable
import FormalProof4FHETest.HasteBootsHadamardBlindRotationSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsHadamardBlindRotationSmoke
open scoped Matrix
open NativeBlindRotation (Poly Cipher)
namespace HasteBootsPublicMonomialTableSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

-- The original order and duplicate rotations are retained. Round 3 is padding.
def rotations : Fin 3 → Fin 8 := ![1,5,1]
example : PublicMonomialTable.coefficients (q := 17) (n := 4) (1 : Fin 8) = polynomial 0 1 0 0 := by decide +kernel
example : PublicMonomialTable.coefficients (q := 17) (n := 4) (5 : Fin 8) = polynomial 0 16 0 0 := by decide +kernel
example : PublicMonomialTable.coefficients (q := 17) (n := 4) (7 : Fin 8) = polynomial 0 0 0 16 := by decide +kernel
example : PublicMonomialTable.table (log := 2) 2 rotations false (1 : Fin 4) = polynomial 15 2 9 8 := by decide +kernel
example : PublicMonomialTable.table (log := 2) (2 : ZMod 17) rotations true (3 : Fin 4) = 0 := by decide +kernel
example : PublicMonomialTable.table (log := 2) (2 : ZMod 17) rotations false (0 : Fin 4) =
    PublicMonomialTable.table (log := 2) 2 rotations true (2 : Fin 4) := by decide +kernel
example (half : Bool) : PublicMonomialTable.table (log := 2) (2 : ZMod 17) rotations half (1 : Fin 4) =
    BlindRotationMonomial.powers 2 2 5 :=
  PublicMonomialTable.table_round (q := 17) (log := 2) (rounds := 3) (padded := 4) 2 primitive rotations (by decide +kernel : 3 ≤ 4) half (1 : Fin 3)
-- Empty rounds and the smallest supported transform do not need exclusions.
example (empty : Fin 0 → Fin 8) : PublicMonomialTable.table (log := 2) (2 : ZMod 17) empty true (0 : Fin 1) = 0 :=
  PublicMonomialTable.table_inactive (q := 17) (log := 2) (rounds := 0) (padded := 1) 2 primitive empty true 0 (by decide +kernel)
example : PublicMonomialTable.coefficients (q := 17) (n := 1) (1 : Fin 2) = fun _ => -1 := by decide +kernel

def product : Cipher 17 4 := fun half =>
  if half then polynomial 5 1 15 13 else polynomial 5 4 2 16

def tables : PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 1) 3 1 :=
  fun factor cell _ =>
    let index := FlatMatrixFold.index 2 cell.2
    match factor with
    | .inl (_,isPublic) => if isPublic then PublicMonomialTable.table (log := 2) 2 rotations cell.1 (0 : Fin 4) index
      else transform (accumulator cell.1) index
    | .inr _ => transform (product cell.1) index

theorem relation : PBSHadamard.Relation tables := by
  unfold PBSHadamard.Relation
  decide +kernel

theorem source : ∀ half, BlindRotationNTT.transform 2 (2 : ZMod 17) (accumulator half) =
    PBSMonomialBlindRotation.project tables (address half) (.inl (0,false)) := by
  intro half
  funext index
  cases half <;> fin_cases index <;> decide +kernel

theorem publicRow : ∀ half, PBSMonomialBlindRotation.project tables (address half) (.inl (0,true)) =
    PublicMonomialTable.table (log := 2) 2 rotations half (0 : Fin 4) := by
  intro half
  funext index
  cases half <;> fin_cases index <;> decide +kernel

theorem result : ∀ half, BlindRotationNTT.transform 2 (2 : ZMod 17) (product half) =
    PBSMonomialBlindRotation.project tables (address half) (.inr ()) := by
  intro half
  funext index
  cases half <;> fin_cases index <;> decide +kernel

-- Uses the signed-coefficient materialization, not a supplied node-power table.
example : product = fun half => NativeBlindRotation.rotate 1 (accumulator half) := by
  have certified := PublicMonomialTable.rotate_of_table (q := 17) (log := 2) (rounds := 3)
    (padded := 4) (cells := 3) (width := 1) 2 primitive rotations (0 : Fin 4)
    (by decide +kernel : (0 : Fin 4).val < 3) accumulator product tables address relation source publicRow result
  exact certified

-- An inactive row is zero rather than the multiplicative identity.
example : PublicMonomialTable.table (log := 2) (2 : ZMod 17) rotations false (3 : Fin 4) ≠
    BlindRotationMonomial.powers 2 2 0 := by decide +kernel
end
end HasteBootsPublicMonomialTableSmoke
