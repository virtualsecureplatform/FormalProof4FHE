module
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.ExecutableRectangularMatrixExtraction
import all FormalProof4FHE.HasteBoots.CommonSourceReindex
import all FormalProof4FHE.HasteBoots.ExecutableSourceCoefficients
import all FormalProof4FHE.HasteBoots.ExecutableCommonSource
import all FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
import all FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
import all FormalProof4FHE.HasteBoots.ExecutablePolynomial
import all FormalProof4FHE.HasteBoots.FiniteMatrixSolver
import all FormalProof4FHE.HasteBoots.FiniteLinearSolver
import all FormalProof4FHE.HasteBoots.RowLayout
import all FormalProof4FHE.HasteBoots.NativeFields
import all ArkLib.Data.CodingTheory.BerlekampWelch.Condition
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def points {F : Type} [Field F] (pos : Fin 5) : F := pos.val
-- Packing width three is independent of code-symbol width two. Original size
-- three leaves one unused coefficient coordinate in each padded source row.
private def honest {F : Type} [Field F] (pos : Fin 5) (row : Fin 2 × Fin 3) (lane : Fin 2) : F :=
  (1 + row.1.val * 3 + row.2.val + lane.val : F) + 3 * points pos
private def close {F : Type} [Field F] (pos : Fin 5) (row : Fin 2 × Fin 3) (lane : Fin 2) : F :=
  honest pos row lane + if pos = 2 then 1 else 0
private def spread {F : Type} [Field F] (pos : Fin 5) (row : Fin 2 × Fin 3) (lane : Fin 2) : F :=
  honest pos row lane + if (lane = 0 ∧ pos = 2) ∨ (lane = 1 ∧ pos = 3) then 1 else 0

private def recoverCheck (F : Type) [Field F] [DecidableEq F] : Bool :=
  let table := ExecutableRectangularMatrixExtraction.table (m := 2) (size := 3) 1 points (by decide) (close (F := F))
  decide (table 0 0 0 = 1 ∧ table 0 0 2 = 3 ∧ table 1 0 0 = 4 ∧ table 1 1 2 = 7 ∧ table 1 2 2 = 3)

/-- info: true -/
#guard_msgs in
#eval recoverCheck (ZMod 7)
/-- info: true -/
#guard_msgs in
#eval recoverCheck NativeFields.Goldilocks
/-- info: true -/
#guard_msgs in
#eval recoverCheck NativeFields.BabyBear

/-- info: true -/
#guard_msgs in
#eval let table := ExecutableRectangularMatrixExtraction.table (m := 2) (size := 3) 1 points (by decide) (spread (F := ZMod 7))
      decide (table 0 0 0 = 0 ∧ table 1 1 2 = 0 ∧ table 1 2 2 = 0)
