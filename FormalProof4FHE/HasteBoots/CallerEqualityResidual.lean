module
public import FormalProof4FHE.HasteBoots.CallerEqualityFamily
public import FormalProof4FHE.HasteBoots.LookupInitialArithmetic
public import FormalProof4FHE.HasteBoots.EqualityCandidateKernel
@[expose] public section

/-! The original caller's nonzero masked residual and its actual native EQ
point give the candidate kernel test. Native/scalar dimension casts retain
both the point coordinate order and the complete Boolean residual table. -/
namespace FormalProof4FHE.HasteBoots.CallerEqualityResidual
open scoped BigOperators
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open OracleProgram (Program)
open NativeExtensionFields (Goldilocks3)
open MatrixFold (Cube)
noncomputable section

theorem test_cast {n m : ℕ} (dimension : n = m) (residual : Cube m → Goldilocks3)
    (native : Fin n → Goldilocks3) (scalar : Fin m → Goldilocks3) (point : HEq native scalar) :
    ((∃ cell, residual (cast (congrArg Cube dimension) cell) ≠ 0) ∧
      (∑ cell, PackedEqualityCube.weight native cell * residual (cast (congrArg Cube dimension) cell)) = 0) ↔
      ((∃ cell, residual cell ≠ 0) ∧ (∑ cell, PackedEqualityCube.weight scalar cell * residual cell) = 0) := by
  cases dimension
  cases point
  rfl

theorem point_heq {n m : ℕ} (dimension : n = m) (native : Fin n → Goldilocks3)
    (raw : Fin m → NativeGoldExtensionArithmetic.Word)
    (values : (List.ofFn raw).map NativeFieldWire.goldExtensionValue = List.ofFn native) :
    HEq native (fun index => NativeFieldWire.goldExtensionValue (raw index)) := by
  cases dimension
  rw [List.map_ofFn] at values
  exact heq_of_eq (List.ofFn_injective values).symm

theorem positive {n : ℕ} (residual : Cube n → Goldilocks3) (point : Fin n → Goldilocks3)
    (missed : (∃ cell, residual cell ≠ 0) ∧ (∑ cell, PackedEqualityCube.weight point cell * residual cell) = 0) : 0 < n := by
  cases n with
  | zero =>
    obtain ⟨⟨cell,nonzero⟩,vanished⟩ := missed
    have zero : residual cell = 0 := by
      simp only [PackedEqualityCube.weight_zero,one_mul] at vanished
      have singleton : (Finset.univ : Finset (Cube 0)) = {cell} := by
        ext item
        simp only [Finset.mem_univ,Finset.mem_singleton]
        exact iff_of_true trivial (by cases item; cases cell; rfl)
      simpa only [singleton,Finset.sum_singleton] using vanished
    exact (nonzero zero).elim
  | succ n => omega

variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

theorem test (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupEquality.Draw data.origin.geometry.geometry.1.val Goldilocks3)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (drawAt : data.origin.ready.machine.draws[data.index.val]? = some draw)
    (recovered : CallerEqualityFamily.Recovery data draw first)
    (candidate : EqualityFactorCandidate.Candidate program first.position world)
    (named : candidate.family = CallerEqualityFamily.candidate data draw first drawAt recovered)
    (evidence : NativeGoldLookupEquality.DrawEvidence draw (List.ofFn data.job.view.eqPoint))
    (dummy : NativeRootMessage.Digest) (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (missed : LookupInitialArithmetic.EqualityMiss data dummy) :
    EqualityCandidateResidual.test candidate dummy candidate.family.draw.point := by
  obtain ⟨family,compression,offset,y,r⟩ := candidate
  dsimp only at named
  cases named
  have full : EqualityCandidateResidual.scalar
      ⟨CallerEqualityFamily.candidate data draw first drawAt recovered,compression,offset,y,r⟩ dummy =
      LookupInitialArithmetic.residual data dummy := by
    rw [EqualityCandidateResidual.scalar_full _ dummy safe]
    rfl
  have scalarMiss : (∃ cell, EqualityCandidateResidual.scalar
      ⟨CallerEqualityFamily.candidate data draw first drawAt recovered,compression,offset,y,r⟩ dummy cell ≠ 0) ∧
      (∑ cell, PackedEqualityCube.weight (fun index => NativeFieldWire.goldExtensionValue (data.job.view.eqPoint index)) cell *
        EqualityCandidateResidual.scalar ⟨CallerEqualityFamily.candidate data draw first drawAt recovered,compression,offset,y,r⟩ dummy cell) = 0 := by
    rw [full]
    exact missed
  exact (test_cast data.job.view.dimension _ draw.point _
    (point_heq data.job.view.dimension draw.point data.job.view.eqPoint evidence.value)).mpr scalarMiss

end
end FormalProof4FHE.HasteBoots.CallerEqualityResidual
