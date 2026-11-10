module
public import FormalProof4FHE.HasteBoots.PublicMonomialEvaluation
@[expose] public section
open FormalProof4FHE.HasteBoots
open scoped Matrix
open Matrix
namespace HasteBootsPublicMonomialEvaluationSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev Pair := MatrixFold.Pair (F := ZMod 17) (Lane := Fin 2)

theorem primitive : IsPrimitiveRoot (3 : ZMod 17) 16 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by decide +kernel) (by decide +kernel)
  intro exponent positive small
  interval_cases exponent <;> decide +kernel

def first : Pair := fun bit => if bit then !![0,1;1,0] else !![1,2;0,1]
def second : Pair := fun bit => if bit then !![2,1;0,1] else !![1,0;3,1]
def coefficient : List Pair := [first,second]
def rowFirst : Pair := fun bit => if bit then !![1,0;1,1] else !![1,1;0,1]
def rowSecond : Pair := fun bit => if bit then !![0,1;1,1] else !![2,0;0,1]
def rowQuery : List Pair := [rowFirst,rowSecond]
def halfPair : Pair := first
def rotations : Fin 3 → Fin 16 := ![1,9,1]

-- Native N=8, width=2 lane initialization reverses the lane over all 3 bits.
example : PublicMonomialEvaluation.base (3 : ZMod 17) 1 2 = ![3,14] := by decide +kernel
example : PublicMonomialEvaluation.address 1 2 (false,(true,())) (1 : Fin 2) = (5 : Fin 8) := by decide +kernel
example : PublicMonomialEvaluation.materialized (3 : ZMod 17) 1 2 (1 : Fin 16) (true,(false,())) = ![5,12] := by decide +kernel
example : PublicMonomialEvaluation.loop (3 : ZMod 17) coefficient ![3,14] = ![2,13] := by decide +kernel
example : PublicMonomialEvaluation.loop (3 : ZMod 17) coefficient.reverse ![3,14] = ![2,5] := by decide +kernel
-- Noncommuting query matrices make reversed coefficient order observable.
example : PublicMonomialEvaluation.loop (3 : ZMod 17) coefficient ![3,14] ≠
    PublicMonomialEvaluation.loop (3 : ZMod 17) coefficient.reverse ![3,14] := by decide +kernel

example : PublicMonomialEvaluation.loop (3 : ZMod 17) coefficient (PublicMonomialEvaluation.base 3 1 2) =
    MatrixFold.foldAll coefficient (PublicMonomialEvaluation.materialized 3 1 2 (1 : Fin 16)) := by
  have correct := PublicMonomialEvaluation.loop_materialized (q := 17) 3 1 coefficient primitive (1 : Fin 16)
  exact correct

-- The coefficient bridge also uses the native contiguous flat row layout.
example : PublicMonomialEvaluation.loop (3 : ZMod 17) coefficient (PublicMonomialEvaluation.base 3 1 2) =
    FlatMatrixFold.foldAll coefficient (fun cell lane =>
      NTTButterfly.flatTransform 3 (3 : ZMod 17) 9
        (PublicMonomialTable.coefficients (n := 8) (1 : Fin 16))
        (PublicMonomialEvaluation.flatAddress 1 2 cell lane)) := by
  have correct := PublicMonomialEvaluation.loop_flat_materialized (q := 17) 3 1 coefficient primitive (1 : Fin 16)
  exact correct

-- Both active signs and the inactive row are checked independently.
example : PublicMonomialEvaluation.optimizedRows (3 : ZMod 17) 1 coefficient rotations (0 : Fin 4) = ![2,13] := by decide +kernel
example : PublicMonomialEvaluation.optimizedRows (3 : ZMod 17) 1 coefficient rotations (1 : Fin 4) = ![15,4] := by decide +kernel
example : PublicMonomialEvaluation.optimizedRows (3 : ZMod 17) 1 coefficient rotations (3 : Fin 4) = 0 := by decide +kernel
example : PublicMonomialEvaluation.evaluate (3 : ZMod 17) 1 coefficient rowQuery halfPair rotations = ![15,14] := by decide +kernel

-- The complete staged evaluator agrees with the original signed-coefficient
-- transforms, preserving row/half matrix order and zero padding.
example : PublicMonomialEvaluation.evaluate (3 : ZMod 17) 1 coefficient rowQuery halfPair rotations =
    halfPair false *ᵥ FlatMatrixFold.foldAll rowQuery (PublicMonomialEvaluation.materializedRows 3 1 coefficient rotations false) +
    halfPair true *ᵥ FlatMatrixFold.foldAll rowQuery (PublicMonomialEvaluation.materializedRows 3 1 coefficient rotations true) := by
  have correct := PublicMonomialEvaluation.evaluate_materialized (q := 17) 3 1 coefficient rowQuery halfPair primitive rotations
  exact correct

-- Zero coefficient bits retain the supplied lane vector.
example : PublicMonomialEvaluation.loop (3 : ZMod 17) ([] : List Pair) ![1,2] = ![1,2] := rfl
-- The explicitly proved address identities also include zero-bit dimensions.
example : MonomialBitOrder.reverseCube (n := 0) () = () := rfl
end
end HasteBootsPublicMonomialEvaluationSmoke
