module
public import FormalProof4FHE.HasteBoots.EqualityResidualCongruence
@[expose] public section

/-! Original job metadata and fixed complete families/r/y determine the whole
native-dimension residual. Its nonzero/EQ-vanishing test is fixed on the same
prefix fiber; the equality point remains the fresh test argument. -/
namespace FormalProof4FHE.HasteBoots.EqualityCandidateResidual
open scoped BigOperators
open InputIndexedOracle (World)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open NativeExtensionFields (Goldilocks3)
open NativeScalarQueryShape (laneBits)
open EqualityFactorCandidate (Candidate)
open MatrixFold (Cube)
noncomputable section

structure Alignment {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) : Prop where
  padding : left.family.selection.origin.padding = right.family.selection.origin.padding
  rows : left.family.selection.body.sourceVariables = right.family.selection.body.sourceVariables
  helperPadding : AllocatedLookupTables.helperPadding (ctx := left.family.selection.ctx) = AllocatedLookupTables.helperPadding (ctx := right.family.selection.ctx)
  request : (left.family.selection.origin.ready.jobs.get left.family.selection.index).tag.request =
    (right.family.selection.origin.ready.jobs.get right.family.selection.index).tag.request
  nativeDimension : left.family.selection.origin.geometry.geometry.1.val = right.family.selection.origin.geometry.geometry.1.val

theorem alignment {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.family.selection.family.input = right.family.selection.family.input)
    (ordinal : left.family.selection.index.val = right.family.selection.index.val)
    (same : (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    Alignment left right := by
  have families := (OriginalScalarFamily.compare program position world other left.family.selection.family right.family.selection.family dummy input same).resolve_right
    (JobReferenceFixation.family_bad_false program position world other dummy good safe)
  have agree := families.1
  have registry := left.family.selection.registry.symm.trans (agree.1.trans right.family.selection.registry)
  have helper := left.family.selection.helper.symm.trans (agree.2.1.trans right.family.selection.helper)
  have requests := left.family.selection.requests.symm.trans (agree.2.2.1.trans right.family.selection.requests)
  have dimensions := OriginalJobOrdinal.dimensions left.family.selection.origin right.family.selection.origin registry
  refine ⟨dimensions.2,dimensions.1,congrArg (fun parameters => parameters.width.val-3) helper,
    OriginalJobOrdinal.request left.family.selection.origin right.family.selection.origin requests left.family.selection.index right.family.selection.index ordinal,?_⟩
  rw [left.family.selection.job.view.dimension,right.family.selection.job.view.dimension,dimensions.1,dimensions.2]

def scalar {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) :=
  EqualityResidualCongruence.packed (NativeScalarQueryShape.checked_power _ _ _ candidate.family.selection.job.view.shape)
    (candidate.family.selection.origin.ready.jobs.get candidate.family.selection.index).output.r
    (candidate.family.selection.origin.ready.jobs.get candidate.family.selection.index).output.y
    (candidate.family.selection.origin.ready.jobs.get candidate.family.selection.index).tag.request.terminal.logicalLength.val
    (EqualityFamilyCandidate.sources candidate.family dummy) (EqualityFamilyCandidate.helpers candidate.family dummy)

/-- Prefix residual construction uses exactly the complete-run canonical
families, outside the same seed-order exception already used by stability. -/
theorem scalar_full {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    scalar candidate dummy = EqualityResidualCongruence.packed
      (NativeScalarQueryShape.checked_power _ _ _ candidate.family.selection.job.view.shape)
      (candidate.family.selection.origin.ready.jobs.get candidate.family.selection.index).output.r
      (candidate.family.selection.origin.ready.jobs.get candidate.family.selection.index).output.y
      (candidate.family.selection.origin.ready.jobs.get candidate.family.selection.index).tag.request.terminal.logicalLength.val
      (CanonicalAllocatedTables.sources candidate.family.selection.allocation candidate.family.selection.origin candidate.family.selection.index
        candidate.family.selection.job candidate.family.selection.geometry dummy (OracleProgram.run program world).run.2)
      (CanonicalAllocatedTables.helpers candidate.family.selection.allocation candidate.family.selection.origin candidate.family.selection.index
        candidate.family.selection.job candidate.family.selection.geometry dummy (OracleProgram.run program world).run.2) := by
  have stable := EqualityFamilyCandidate.tables_at_first candidate.family dummy safe
  unfold scalar
  rw [stable.1,stable.2]

def residual {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) : Cube candidate.family.selection.origin.geometry.geometry.1.val → Goldilocks3 :=
  fun cell => scalar candidate dummy (cast (congrArg Cube candidate.family.selection.job.view.dimension) cell)

theorem residual_fixed {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.family.selection.family.input = right.family.selection.family.input)
    (ordinal : left.family.selection.index.val = right.family.selection.index.val)
    (same : (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    HEq (residual left dummy) (residual right dummy) := by
  have aligned := alignment left right dummy input ordinal same good safe
  obtain ⟨families,y,r⟩ := EqualityFactorCandidate.fixed _ _ _ _ left right dummy input ordinal same good safe
  have tables := EqualityResidualCongruence.packed_congr
    (NativeScalarQueryShape.checked_power _ _ _ left.family.selection.job.view.shape)
    (NativeScalarQueryShape.checked_power _ _ _ right.family.selection.job.view.shape)
    _ _ _ _ _ _ (EqualityFamilyCandidate.sources left.family dummy) (EqualityFamilyCandidate.sources right.family dummy)
    (EqualityFamilyCandidate.helpers left.family dummy) (EqualityFamilyCandidate.helpers right.family dummy)
    aligned.padding aligned.rows aligned.helperPadding (congrArg NativeSharedLookupStatement.Request.columns aligned.request)
    r.symm y.symm (congrArg (fun request => request.terminal.logicalLength.val) aligned.request) families.1 families.2
  exact EqualityResidualCongruence.native_transport left.family.selection.job.view.dimension right.family.selection.job.view.dimension
    aligned.nativeDimension (by rw [aligned.padding,aligned.rows]) (scalar left dummy) (scalar right dummy) tables

def test {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest)
    (point : Fin candidate.family.selection.origin.geometry.geometry.1.val → Goldilocks3) : Prop :=
  (∃ cell, residual candidate dummy cell ≠ 0) ∧
    (∑ cell, PackedEqualityCube.weight point cell * residual candidate dummy cell) = 0

theorem test_congr {ln rn : ℕ} (dimension : ln = rn) (left : Cube ln → Goldilocks3) (right : Cube rn → Goldilocks3)
    (tables : HEq left right) :
    HEq (fun point : Fin ln → Goldilocks3 => (∃ cell, left cell ≠ 0) ∧ (∑ cell, PackedEqualityCube.weight point cell * left cell) = 0)
      (fun point : Fin rn → Goldilocks3 => (∃ cell, right cell ≠ 0) ∧ (∑ cell, PackedEqualityCube.weight point cell * right cell) = 0) := by
  cases dimension
  cases tables
  rfl

theorem test_fixed {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.family.selection.family.input = right.family.selection.family.input)
    (ordinal : left.family.selection.index.val = right.family.selection.index.val)
    (same : (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    HEq (test left dummy) (test right dummy) :=
  test_congr (alignment left right dummy input ordinal same good safe).nativeDimension _ _
    (residual_fixed left right dummy input ordinal same good safe)

end
end FormalProof4FHE.HasteBoots.EqualityCandidateResidual
