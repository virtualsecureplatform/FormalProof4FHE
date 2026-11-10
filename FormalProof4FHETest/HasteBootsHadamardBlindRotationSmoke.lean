module
public import FormalProof4FHE.HasteBoots.PBSHadamardBlindRotation
@[expose] public section
open FormalProof4FHE.HasteBoots
open scoped BigOperators Matrix
open NativeBlindRotation (Poly Cipher Control digit externalProduct)
namespace HasteBootsHadamardBlindRotationSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

def polynomial (a b c d : ZMod 17) : Poly 17 4 := ![a,b,c,d]
def left : Poly 17 4 := polynomial 1 2 3 4
def right : Poly 17 4 := polynomial 5 6 7 8

theorem primitive : IsPrimitiveRoot (2 : ZMod 17) 8 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by decide +kernel) (by decide +kernel)
  intro exponent positive small
  interval_cases exponent <;> decide +kernel

-- Golden negacyclic coefficients, including wraparound subtraction.
example : NativeBlindRotation.mul left right = polynomial 12 15 2 9 := by decide +kernel
example : NativeBlindRotation.mul (polynomial 0 0 0 1) (polynomial 0 1 0 0) = polynomial 16 0 0 0 := by decide +kernel

-- Native-order butterflies, rather than only a supplied transform map.
example : NTTButterfly.flatTransform 2 (2 : ZMod 17) 4 (NativeBlindRotation.mul left right) = polynomial 3 3 6 2 := by decide +kernel

def input : Cipher 17 4 := fun half => if half then polynomial 4 3 2 1 else left

def control : Control 17 4 1 := fun source _ half =>
  if source then (if half then polynomial 0 0 0 1 else polynomial 0 0 1 0)
  else (if half then polynomial 0 1 0 0 else polynomial 1 0 0 0)

def output : Cipher 17 4 := fun half =>
  if half then polynomial 14 16 1 3 else polynomial 16 1 3 3

def transform (poly : Poly 17 4) : Poly 17 4 :=
  NTTButterfly.flatTransform 2 (2 : ZMod 17) 4 poly

def address (half : Bool) (index : Fin 4) : MatrixFold.Cube 3 × Fin 1 :=
  ((half,(FlatMatrixFold.index 2).symm index),0)

def tables (result : Cipher 17 4) :
    PackedSumcheckExecution.Tables (ZMod 17) (PBSHadamard.Factor 2) 3 1 :=
  fun factor cell _ =>
    let index := FlatMatrixFold.index 2 cell.2
    match factor with
    | .inl (position,isKey) =>
      if isKey then transform (control (position.val == 1) 0 cell.1) index
      else transform (digit 2 (0 : Fin 1) (input (position.val == 1))) index
    | .inr _ => transform (result cell.1) index

-- A full packed-table Hadamard relation with both source families, both
-- output halves and a lane address for every NTT point.
theorem hadamard : PBSHadamard.Relation (tables output) := by
  unfold PBSHadamard.Relation
  decide +kernel

theorem digits : ∀ half source (level : Fin 1),
    BlindRotationNTT.transform 2 (2 : ZMod 17) (digit 2 level (input source)) =
      PBSHadamardBlindRotation.project (levels := 1) (tables output) (address half)
        (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false)) := by
  intro half source level
  apply funext
  intro index
  fin_cases level
  cases half <;> cases source <;> fin_cases index <;> decide +kernel

theorem keys : ∀ half source (level : Fin 1),
    BlindRotationNTT.transform 2 (2 : ZMod 17) (control source level half) =
      PBSHadamardBlindRotation.project (levels := 1) (tables output) (address half)
        (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true)) := by
  intro half source level
  apply funext
  intro index
  fin_cases level
  cases half <;> cases source <;> fin_cases index <;> decide +kernel

theorem result : ∀ half, BlindRotationNTT.transform 2 (2 : ZMod 17) (output half) =
    PBSHadamardBlindRotation.project (levels := 1) (tables output) (address half) (.inr ()) := by
  intro half
  apply funext
  intro index
  cases half <;> fin_cases index <;> decide +kernel

-- The application bridge recovers the reference coefficient external product.
example : output = externalProduct 2 control input :=
  PBSHadamardBlindRotation.externalProduct_of_relations (log := 2) (levels := 1) (cells := 3) (width := 1) 2 primitive 2 control input output (tables output) address
    hadamard digits keys result


def accumulator : Cipher 17 4 := fun half =>
  if half then polynomial 1 15 13 12 else polynomial 4 2 16 12

def trace : NativeBlindRotation.StepTrace 17 4 where
  product := fun half => NativeBlindRotation.rotate 1 (accumulator half)
  difference := input
  external := output
  output := accumulator+output

-- A complete nonzero-rotation reference step uses the proved external-product
-- bridge, with its other stage identities checked on the same trace.
example : NativeBlindRotation.ValidStep 2 control 1 accumulator trace :=
  PBSHadamardBlindRotation.validStep_of_relations (log := 2) (levels := 1) (cells := 3) (width := 1)
    2 primitive 2 1 control accumulator trace (tables output) address rfl (by decide +kernel) rfl
    hadamard digits keys result

def corrupted : Cipher 17 4 := fun half =>
  if half then output true else polynomial 0 1 3 3

-- Changing an output coefficient breaks the relation while the original
-- digit and key factors remain fixed.
example : ¬PBSHadamard.Relation (tables corrupted) := by
  unfold PBSHadamard.Relation
  decide +kernel

-- Empty gadget families are not hidden behind a positive-level assumption.
example (empty : Control 17 4 0) (value : Cipher 17 4) : externalProduct 2 empty value = 0 := by
  funext half index
  simp only [externalProduct, Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, Pi.zero_apply]
end
end HasteBootsHadamardBlindRotationSmoke
