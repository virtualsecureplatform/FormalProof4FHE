module
public import FormalProof4FHE.HasteBoots.CallerPairedPreparation
public import FormalProof4FHE.HasteBoots.LookupReciprocalEnforcement
@[expose] public section

/-! Interpret the original native sum/zero claims as the decoded helper sum
and EQ-weighted masked residual. Nonzero Boolean residuals can cancel at the
actual EQ point; that exception is retained rather than assumed impossible. -/
namespace FormalProof4FHE.HasteBoots.LookupInitialArithmetic
open scoped BigOperators
open OracleSpec OracleComp
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFieldWire (goldExtensionValue)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open OracleProgram (Program run)
open AllocatedFamilyFunctions (Allocation)
open MatrixFold (Cube)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
  {program : Program A} {world : World}

abbrev dimension (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :=
  NativeScalarQueryShape.laneBits (3+data.origin.padding)+data.lookup.body.sourceVariables

def helper (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :
    Cube (dimension data) → Goldilocks3 := fun cell => PaddedExtension.decode goldilocksBasis
      (CanonicalAllocatedTables.helpers allocation data.origin data.index data.job data.geometry dummy (run program world).run.2 cell)

def source (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :
    Cube (dimension data) → Goldilocks3 :=
  ExtensionLookupIdentity.hashTable (goldExtensionValue (data.origin.ready.jobs.get data.index).output.y)
    (fun column => LookupSourceFlattening.flatten
      (NativeScalarQueryShape.checked_power _ _ _ data.job.view.shape)
      (CanonicalAllocatedTables.sources allocation data.origin data.index data.job data.geometry dummy (run program world).run.2 column))

def residual (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :
    Cube (dimension data) → Goldilocks3 := fun cell =>
  ReciprocalMask.residual (goldExtensionValue (data.origin.ready.jobs.get data.index).output.r)
    (source data dummy cell) (helper data dummy cell)
    (decide ((FlatMatrixFold.index (dimension data) cell).val <
      (data.origin.ready.jobs.get data.index).tag.request.terminal.logicalLength.val))

def weighted (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) : Goldilocks3 :=
  ∑ cell, PackedEqualityCube.weight (fun i => goldExtensionValue (data.job.view.eqPoint i)) cell * residual data dummy cell

def EqualityMiss (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) : Prop :=
  (∃ cell, residual data dummy cell ≠ 0) ∧ weighted data dummy = 0

theorem sum_truth (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :
    CallerPairedPreparation.sumTruth data dummy = ∑ cell, helper data dummy cell := by
  exact ScalarLookupExpression.sum_initial (helper data dummy)

theorem identity_truth (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :
    CallerFramedAllocatedJob.truth data dummy = weighted data dummy := by
  unfold CallerFramedAllocatedJob.truth AllocatedIdentityAlternatives.truth
  split_ifs with full
  · have dimensionEq := data.job.view.dimension
    have fullDimension : (data.origin.ready.jobs.get data.index).tag.request.terminal.logicalLength.val = 2^(dimension data) := by
      rw [full,dimensionEq]
    change ScalarSourcePolynomial.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
      ExtensionLookupIdentity.fullIndices (dimension data) []
      (LookupIdentityCausalReduction.fullTables data.job.view
        (CanonicalAllocatedTables.sources allocation data.origin data.index data.job data.geometry dummy (run program world).run.2)
        (CanonicalAllocatedTables.helpers allocation data.origin data.index data.job data.geometry dummy (run program world).run.2)) = _
    unfold LookupIdentityCausalReduction.fullTables
    rw [ScalarLookupExpression.full_initial]
    unfold weighted residual source helper
    rw [fullDimension]

  · exact ScalarLookupExpression.partial_initial _ _ _ _ _ _

/-- Recover both literal initial claims and their request-indexed counts from
successful native preparation. Repetitions retain their original job index. -/
theorem claims (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    ∃ counts, ctx.proof.values.multiplicities[(data.origin.ready.jobs.get data.index).tag.ordinal.val]? = some counts ∧
      ScalarChainHealing.value (2*data.index.val) data.origin.ready.statement.claims.val =
        some (goldExtensionValue (NativeGoldExtensionArithmetic.tableSum (data.origin.ready.jobs.get data.index).output.inverses counts)) ∧
      ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val = some 0 := by
  obtain ⟨_,_,counts,atCounts,even,odd⟩ := LookupScalarGrammar.protocol_pair ctx.requests.property.le
    (NativeSharedLookupParent.models ctx.requests) data.origin.geometry.geometry.1 ctx.proof.values.multiplicities
    ctx.proof.values.roots ctx.proof.roots.property 7 ctx.lookupFuel ctx.equalityFuel _ world data.origin.ready
    data.origin.prepared data.index.val data.index.isLt
  refine ⟨counts,atCounts,?_,?_⟩
  · simp only [ScalarChainHealing.value,even,Option.map_some]
    rfl
  · simp only [ScalarChainHealing.value,odd,Option.map_some,NativeGoldLookup.zero_value]

def FalsePair (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest) : Prop :=
  (ScalarChainHealing.value (2*data.index.val) data.origin.ready.statement.claims.val ≠ some (CallerPairedPreparation.sumTruth data dummy)) ∨
    (ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠ some (CallerFramedAllocatedJob.truth data dummy))

/-- Exact characterization uses the original public sum and actual EQ point.
It does not replace pointwise validity with a vanishing weighted sum. -/
theorem false_pair_iff (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (counts : List NativeFieldRepresentation.GoldWord)
    (atCounts : ctx.proof.values.multiplicities[(data.origin.ready.jobs.get data.index).tag.ordinal.val]? = some counts) :
    FalsePair data dummy ↔
      (∑ cell, helper data dummy cell) ≠ goldExtensionValue (NativeGoldExtensionArithmetic.tableSum
        (data.origin.ready.jobs.get data.index).output.inverses counts) ∨ weighted data dummy ≠ 0 := by
  obtain ⟨actual,atActual,even,odd⟩ := claims data
  have same : actual = counts := Option.some.inj (atActual.symm.trans atCounts)
  subst actual
  rw [FalsePair,even,odd,sum_truth,identity_truth]
  simp only [ne_eq,Option.some.injEq]
  constructor <;> intro h <;> rcases h with h | h
  · exact Or.inl (Ne.symm h)
  · exact Or.inr (Ne.symm h)
  · exact Or.inl (Ne.symm h)
  · exact Or.inr (Ne.symm h)

/-- A concrete bad reciprocal relation is covered by an originally false
scalar equation or a nonzero residual missed by the original equality draw. -/
theorem obstruction (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (counts : List NativeFieldRepresentation.GoldWord)
    (atCounts : ctx.proof.values.multiplicities[(data.origin.ready.jobs.get data.index).tag.ordinal.val]? = some counts)
    (broken : (∑ cell, helper data dummy cell) ≠ goldExtensionValue (NativeGoldExtensionArithmetic.tableSum
      (data.origin.ready.jobs.get data.index).output.inverses counts) ∨ ∃ cell, residual data dummy cell ≠ 0) :
    FalsePair data dummy ∨ EqualityMiss data dummy := by
  by_cases nonzero : weighted data dummy ≠ 0
  · exact Or.inl ((false_pair_iff data dummy counts atCounts).mpr (Or.inr nonzero))
  · rcases broken with badSum | badCell
    · exact Or.inl ((false_pair_iff data dummy counts atCounts).mpr (Or.inl badSum))
    · exact Or.inr ⟨badCell,not_not.mp nonzero⟩

/-- Reciprocal nonpassing implies the concrete native obstruction once the
original producer's public total is identified. The total and nonzero-r links
remain explicit obligations; neither is inferred from scalar acceptance. -/
theorem nonpassing_covered {size : ℕ}
    (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (counts : List NativeFieldRepresentation.GoldWord)
    (atCounts : ctx.proof.values.multiplicities[(data.origin.ready.jobs.get data.index).tag.ordinal.val]? = some counts)
    (table multiplicities : Fin size → Goldilocks3)
    (rNonzero : goldExtensionValue (data.origin.ready.jobs.get data.index).output.r ≠ 0)
    (publicTotal : goldExtensionValue (NativeGoldExtensionArithmetic.tableSum
      (data.origin.ready.jobs.get data.index).output.inverses counts) =
        ∑ i, multiplicities i * (goldExtensionValue (data.origin.ready.jobs.get data.index).output.r + table i)⁻¹)
    (notPasses : ¬ReciprocalDetection.Passes
      (LookupReciprocalEnforcement.activeSource
        (Nat.add_sub_of_le data.job.view.enough) (source data dummy)) table multiplicities
      (goldExtensionValue (data.origin.ready.jobs.get data.index).output.r)) :
    FalsePair data dummy ∨ EqualityMiss data dummy := by
  apply obstruction data dummy counts atCounts
  have bad := LookupReciprocalEnforcement.not_passes_obstruction
    (Nat.add_sub_of_le data.job.view.enough)
    (goldExtensionValue (data.origin.ready.jobs.get data.index).output.r)
    (source data dummy) (helper data dummy) table multiplicities rNonzero notPasses
  rw [← publicTotal] at bad
  exact bad

local instance : SampleableType Goldilocks3 := SampleableType.ofFintype _

/-- Fixed-table equality bound. This independent uniform point is not the
actual adaptive native draw; fixation and transcript-law composition remain. -/
theorem fixed_residual_bound
    (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    [SampleableType (Fin (dimension data) → Goldilocks3)]
    (bad : ∃ cell, residual data dummy cell ≠ 0) :
    Pr{let point ← $ᵗ (Fin (dimension data) → Goldilocks3)}[
      (∑ cell, PackedEqualityCube.weight point cell * residual data dummy cell) = 0] ≤
      (dimension data : ENNReal) / Fintype.card Goldilocks3 := by
  have nonzero : ∃ cell, residual data dummy ((PackedEqualityCube.bits (dimension data)).symm cell) ≠ 0 := by
    obtain ⟨cell,bad⟩ := bad
    exact ⟨PackedEqualityCube.bits (dimension data) cell,by simpa only [Equiv.symm_apply_apply] using bad⟩
  simpa only [PackedEqualityCube.weighted_sum] using
    (PackedZeroEquality.point_bound
      (fun cell => residual data dummy ((PackedEqualityCube.bits (dimension data)).symm cell)) nonzero)

end
end FormalProof4FHE.HasteBoots.LookupInitialArithmetic
