module
public import FormalProof4FHE.HasteBoots.LookupEqualityExposure
@[expose] public section

/-! The actual equality miss is expressed at its native vector dimension,
using the exact original collector point and canonical decoded residual. -/
namespace FormalProof4FHE.HasteBoots.LookupEqualityResidual
open scoped BigOperators
open MatrixFold (Cube)
open NativeExtensionFields (Goldilocks3)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeFieldWire (goldExtensionValue)
open AllocatedFamilyFunctions (Allocation)
open OracleProgram (Program)
open MeasureTheory ProbabilityTheory
noncomputable section

theorem weighted_transport {n m : ℕ} (same : n = m) (point : Fin m → Goldilocks3) (table : Cube m → Goldilocks3) :
    (∑ cell : Cube n, PackedEqualityCube.weight (fun i => point (Fin.cast same i)) cell *
      table (cast (congrArg Cube same) cell)) = ∑ cell, PackedEqualityCube.weight point cell * table cell := by
  cases same
  rfl

theorem nonzero_transport {n m : ℕ} (same : n = m) (table : Cube m → Goldilocks3)
    (bad : ∃ cell, table cell ≠ 0) : ∃ cell : Cube n, table (cast (congrArg Cube same) cell) ≠ 0 := by
  cases same
  exact bad

variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
  {program : Program A} {world : World}

def residual (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :
    Cube data.origin.geometry.geometry.1.val → Goldilocks3 := fun cell =>
  LookupInitialArithmetic.residual data dummy (cast (congrArg Cube data.job.view.dimension) cell)

/-- Both the original point and the false residual remain attached to the
same original job. The collector event uses no fresh replacement point. -/
theorem miss (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (missed : LookupInitialArithmetic.EqualityMiss data dummy) :
    ∃ draw : NativeLookupEquality.Draw data.origin.geometry.geometry.1.val Goldilocks3,
      data.origin.ready.machine.draws[data.index.val]? = some draw ∧
      (∃ budget, GoldEqualityPointLaw.values data.origin.geometry.geometry.1.val budget
        (EqualityCollectorTrace.start draw.coefficients) world = some draw.point) ∧
      (∃ cell, residual data dummy cell ≠ 0) ∧
      (∑ cell, PackedEqualityCube.weight draw.point cell * residual data dummy cell) = 0 := by
  obtain ⟨draw,found,collected,points⟩ := LookupEqualityExposure.original data.origin data.job
  have pointEq : draw.point = fun i => goldExtensionValue (data.job.view.eqPoint (Fin.cast data.job.view.dimension i)) := by
    funext i
    have inside : i.val < LookupInitialArithmetic.dimension data := (Fin.cast data.job.view.dimension i).isLt
    have atPoint := congrArg (fun values : List Goldilocks3 => values[i.val]?) points
    simp only [List.map_ofFn,List.getElem?_ofFn,dite_eq_left i.isLt,dite_eq_left inside] at atPoint
    exact Option.some.inj atPoint
  refine ⟨draw,found,collected,nonzero_transport data.job.view.dimension _ missed.1,?_⟩
  rw [pointEq]
  unfold residual
  exact (weighted_transport data.job.view.dimension
    (fun i => goldExtensionValue (data.job.view.eqPoint i)) (LookupInitialArithmetic.residual data dummy)).trans missed.2

/-- Fixed residual, original native collector, all candidate budgets. In the
adaptive composition, data must first be fixed on the conditioning fiber. -/
def Event (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (phase : NativeTranscript.FieldPhase) (other : World) : Prop :=
  (∃ cell, residual data dummy cell ≠ 0) ∧
    ∃ budget, (GoldEqualityPointLaw.values data.origin.geometry.geometry.1.val budget phase other).elim False
      (fun point => (∑ cell, PackedEqualityCube.weight point cell * residual data dummy cell) = 0)

theorem of_miss (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (missed : LookupInitialArithmetic.EqualityMiss data dummy) :
    ∃ draw : NativeLookupEquality.Draw data.origin.geometry.geometry.1.val Goldilocks3,
      data.origin.ready.machine.draws[data.index.val]? = some draw ∧
      Event data dummy (EqualityCollectorTrace.start draw.coefficients) world := by
  obtain ⟨draw,found,⟨budget,collected⟩,bad,zero⟩ := miss data dummy missed
  refine ⟨draw,found,bad,budget,?_⟩
  rw [collected]
  exact zero

theorem conditional_bound {S B : Type} (step : S → OracleMachine.Command S B)
    {past : World → NativeTranscript.Execution (S ⊕ B)} (replay : ObservationReplay.Replayable past)
    (reference : World) (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (dummy : Digest) (phase : NativeTranscript.FieldPhase)
    (selected : CausalStreamExposure.firstRead step (past reference).run = some phase.pending.input) :
    (InputIndexedOracle.law[|{other | (past other).run = (past reference).run}])
      {other | Event data dummy phase other} ≤
      (data.origin.geometry.geometry.1.val : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  by_cases bad : ∃ cell, residual data dummy cell ≠ 0
  · have included : {other | Event data dummy phase other} ⊆
        {other | ∃ budget, (GoldEqualityPointLaw.values data.origin.geometry.geometry.1.val budget phase other).elim False
          (fun point => (∑ cell, PackedEqualityCube.weight point cell * residual data dummy cell) = 0)} := by
      intro other failed
      exact failed.2
    exact (measure_mono included).trans
      (GoldEqualityPointLaw.eventual_residual_bound step replay reference dummy _ phase selected (residual data dummy) bad)
  · have included : {other | Event data dummy phase other} ⊆ ∅ := by
      intro other failed
      exact (bad failed.1).elim
    exact (measure_mono included).trans (by simp)

end
end FormalProof4FHE.HasteBoots.LookupEqualityResidual
