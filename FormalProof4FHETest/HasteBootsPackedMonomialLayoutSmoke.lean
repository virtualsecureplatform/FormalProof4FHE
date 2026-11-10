module
import FormalProof4FHE.HasteBoots.PackedMonomialLayout
import FormalProof4FHETest.HasteBootsPublicMonomialEvaluationSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsPublicMonomialEvaluationSmoke
open scoped Matrix
namespace HasteBootsPackedMonomialLayoutSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

def publicSource : Fin 32 → Fin 2 → ZMod 17 :=
  PackedMonomialLayout.source (lanes := 1) (coefficient := 2) (rows := 2) 3 rotations

-- The last cell/last lane is the final scalar in the allocation.
example : PackedMonomialLayout.layout 2 2 ((3 : Fin 4),((3 : Fin 4),true)) = (31 : Fin 32) := by decide +kernel
example : 2*(PackedMonomialLayout.layout 2 2 ((3 : Fin 4),((3 : Fin 4),true))).val+1 = 63 := by decide +kernel
-- Original rows, signs, duplicated halves and padding remain visible.
example : publicSource 0 = ![3,14] := by decide +kernel
example : publicSource 16 = publicSource 0 := by decide +kernel
example : publicSource 5 1 = 5 := by decide +kernel
example : publicSource 27 1 = 6 := by decide +kernel
example : publicSource 28 = 0 := by decide +kernel
example : PackedMonomialLayout.word (lanes := 1) (coefficient := 2) (rows := 2) (3 : ZMod 17) rotations 32 = 0 := by decide +kernel

-- One full query evaluates the same fixed source; no staged-layout equality
-- is supplied by the fixture or assumed as a hypothesis.
example : PublicMonomialEvaluation.evaluate (3 : ZMod 17) 1 coefficient rowQuery halfPair rotations =
    FlatMatrixFold.foldAll (coefficient++(rowQuery++[halfPair]))
      (fun position => publicSource (PackedMonomialLayout.queryIndex coefficient rowQuery halfPair position)) := by
  have correct := PackedMonomialLayout.evaluate_packed (q := 17) 3 1 coefficient rowQuery halfPair primitive rotations
  exact correct

example : FlatMatrixFold.foldAll (coefficient++(rowQuery++[halfPair]))
    (fun position => publicSource (PackedMonomialLayout.queryIndex coefficient rowQuery halfPair position)) = ![15,14] := by
  have correct := PackedMonomialLayout.evaluate_packed (q := 17) 3 1 coefficient rowQuery halfPair primitive rotations
  have golden : PublicMonomialEvaluation.evaluate (3 : ZMod 17) 1 coefficient rowQuery halfPair rotations = ![15,14] := by decide +kernel
  exact correct.symm.trans golden

-- The source is unchanged while the two query blocks exchange places.
-- Noncommuting matrices make this incorrect variable order observable.
example : FlatMatrixFold.foldAll (rowQuery++(coefficient++[halfPair]))
    (fun position => publicSource (PackedMonomialLayout.queryIndex rowQuery coefficient halfPair position)) ≠ ![15,14] := by
  have swapped := PackedMonomialLayout.evaluate_packed (q := 17) 3 1 rowQuery coefficient halfPair primitive rotations
  intro equal
  have wrong : PublicMonomialEvaluation.evaluate (3 : ZMod 17) 1 rowQuery coefficient halfPair rotations ≠ ![15,14] := by decide +kernel
  exact wrong (swapped.trans equal)

-- Slicing the complete query recovers exactly the three input blocks.
example : (coefficient++(rowQuery++[halfPair])).take coefficient.length = coefficient :=
  PackedMonomialLayout.coefficient_query_slice _ _ _
example : ((coefficient++(rowQuery++[halfPair])).drop coefficient.length).take rowQuery.length = rowQuery :=
  PackedMonomialLayout.row_query_slice _ _ _
example : (coefficient++(rowQuery++[halfPair])).getLast? = some halfPair :=
  PackedMonomialLayout.half_query_slice _ _ _

-- Empty coefficient and row blocks still leave the single half variable.
example : PackedMonomialLayout.layout 0 0 ((0 : Fin 1),((0 : Fin 1),true)) = (1 : Fin 2) := by decide +kernel
end
end HasteBootsPackedMonomialLayoutSmoke
