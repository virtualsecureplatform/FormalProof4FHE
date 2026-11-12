module
import all FormalProof4FHE.HasteBoots.CallerCompressionRecovery

namespace HasteBootsLookupSourceFixationSmoke
open FormalProof4FHE.HasteBoots
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3)
noncomputable section

abbrev request : NativeSharedLookupStatement.Request :=
  ⟨2,[[0,0],[0,1]],1,⟨[0,1],⟨5,by decide +kernel⟩⟩⟩
def sources (column : Fin 2) (high : MatrixFold.Cube 1) (lane : Fin 4) : Goldilocks :=
  if column.val = 0 then 0 else (lane.val+4*(if high.1 then 1 else 0) : ℕ)
theorem shape : 3+1 = 2^NativeScalarQueryShape.laneBits (3+1) := by decide +kernel
theorem enough : request.terminal.logicalLength.val ≤ 2^(NativeScalarQueryShape.laneBits (3+1)+1) := by decide +kernel
abbrev tuples := LookupTupleTest.tuples request shape enough sources

theorem native_lane_order : tuples 2 1 = 2 ∧ tuples 4 1 = 4 := by decide +kernel

/-- The five logical positions are the exact original flat prefix; padded
positions five through seven do not become extra lookup source rows. -/
theorem active_prefix : List.ofFn (fun position => (tuples position 1).val) = [0,1,2,3,4] := by decide +kernel

theorem public_order : LookupTupleTest.publicRows request 0 1 = 0 ∧ LookupTupleTest.publicRows request 1 1 = 1 := by decide +kernel

theorem genuine_nonmember : ∃ position, ∀ row, tuples position ≠ LookupTupleTest.publicRows request row := by
  refine ⟨2,?_⟩
  intro row same
  have different : tuples 2 1 ≠ LookupTupleTest.publicRows request row 1 := by
    fin_cases row <;> decide +kernel
  exact different (congrFun same 1)

/-- This actual nonmember family nevertheless passes compression at y=0.
Fixing only the compressed scalar would lose the false lookup witness. -/
theorem compression_misses_nonmember : LookupTupleTest.compression request shape enough sources (0 : Goldilocks3) := by
  refine ⟨genuine_nonmember,?_⟩
  intro position
  refine ⟨0,?_⟩
  have sourceZero : tuples position 0 = 0 := rfl
  have tableZero : LookupTupleTest.publicRows request 0 0 = 0 := by decide +kernel
  change TupleHash.hash 0 (tuples position) = TupleHash.hash 0 (LookupTupleTest.publicRows request 0)
  simp [TupleHash.hash_eq_sum,Fin.sum_univ_two,sourceZero,tableZero]

/-- The width interpretation is explicit even for an unvalidated short row;
this does not assert that the original configuration validator accepts it. -/
theorem short_public_row_zero_fill : LookupTupleTest.publicRows {request with table := [[1]]} 0 1 = 0 := by decide +kernel

end
end HasteBootsLookupSourceFixationSmoke
