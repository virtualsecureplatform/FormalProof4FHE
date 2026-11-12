module
public import FormalProof4FHE.HasteBoots.LookupMultiplicityFixation
public import FormalProof4FHE.HasteBoots.LookupReciprocalKernel
public import FormalProof4FHE.HasteBoots.LookupTupleTest
@[expose] public section

/-! Reciprocal statements retain the original source prefix, request rows
and grouped count row. Their remaining scalar parameter is the original y;
fixing y from the earlier compression receipt is a separate obligation. -/
namespace FormalProof4FHE.HasteBoots.LookupReciprocalStatement
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3)
open NativeFieldRepresentation (GoldWord)
open NativeScalarQueryShape (laneBits)
open NativeSharedLookupStatement (Request)
open MatrixFold (Cube)
open InputIndexedOracle (World)
open OracleProgram (Program runPrefix)
noncomputable section

def statement {padding rows : ℕ} (request : Request) (shape : 3+padding = 2^laneBits (3+padding))
    (enough : request.terminal.logicalLength.val ≤ 2^(laneBits (3+padding)+rows))
    (sources : Fin request.columns → Cube rows → Fin (3+padding) → Goldilocks)
    (counts : List GoldWord) (y : Goldilocks3) : Goldilocks3 → Prop :=
  LookupReciprocalKernel.test
    (fun position => TupleHash.hash y (LookupTupleTest.tuples request shape enough sources position))
    (fun row => TupleHash.hash y (LookupTupleTest.publicRows request row))
    (fun row => algebraMap Goldilocks Goldilocks3 (NativeFieldRepresentation.goldValue (counts[row.val]?.getD 0)))

theorem statement_congr {lp rp lr rr : ℕ} (left right : Request)
    (leftShape : 3+lp = 2^laneBits (3+lp)) (rightShape : 3+rp = 2^laneBits (3+rp))
    (leftEnough : left.terminal.logicalLength.val ≤ 2^(laneBits (3+lp)+lr))
    (rightEnough : right.terminal.logicalLength.val ≤ 2^(laneBits (3+rp)+rr))
    (leftSources : Fin left.columns → Cube lr → Fin (3+lp) → Goldilocks)
    (rightSources : Fin right.columns → Cube rr → Fin (3+rp) → Goldilocks)
    (leftCounts rightCounts : List GoldWord) (leftY rightY : Goldilocks3)
    (padding : lp = rp) (rows : lr = rr) (request : left = right) (sources : HEq leftSources rightSources)
    (counts : leftCounts = rightCounts) (y : leftY = rightY) :
    statement left leftShape leftEnough leftSources leftCounts leftY =
      statement right rightShape rightEnough rightSources rightCounts rightY := by
  cases padding
  cases rows
  cases request
  cases sources
  cases counts
  cases y
  rfl

def test {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupMultiplicityFixation.Candidate program position world) (dummy : NativeRootMessage.Digest)
    (y : Goldilocks3) : Goldilocks3 → Prop :=
  statement (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request
    (NativeScalarQueryShape.checked_power _ _ _ candidate.source.job.view.shape) candidate.source.job.view.enough
    (LookupSourceCandidate.sources candidate.source dummy) (LookupMultiplicityFixation.row candidate) y

/-- The decoded source prefix equals the complete original caller source
outside the existing seed-order event; counts remain the original raw row. -/
theorem test_full {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupMultiplicityFixation.Candidate program position world) (dummy : NativeRootMessage.Digest)
    (y : Goldilocks3) (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    test candidate dummy y =
      statement (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request
        (NativeScalarQueryShape.checked_power _ _ _ candidate.source.job.view.shape) candidate.source.job.view.enough
        (CanonicalAllocatedTables.sources candidate.source.allocation candidate.source.origin candidate.source.index candidate.source.job
          candidate.source.geometry dummy (OracleProgram.run program world).run.2)
        (LookupMultiplicityFixation.row candidate) y := by
  unfold test
  rw [LookupSourceCandidate.sources_full candidate.source dummy safe]

/-- Once the original compression value agrees, the complete reciprocal
test agrees on the existing good fiber, with all source positions retained. -/
theorem test_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : LookupMultiplicityFixation.Candidate program position world)
    (right : LookupMultiplicityFixation.Candidate program position other) (dummy : NativeRootMessage.Digest)
    (leftY rightY : Goldilocks3) (y : leftY = rightY)
    (input : left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input)
    (ordinal : left.source.index.val = right.source.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    test left dummy leftY = test right dummy rightY := by
  obtain ⟨registry,requests,sources,counts⟩ := LookupMultiplicityFixation.fixed program position world other left right dummy input ordinal same good safe
  have dimensions := OriginalJobOrdinal.dimensions left.source.origin right.source.origin registry
  exact statement_congr _ _ (NativeScalarQueryShape.checked_power _ _ _ left.source.job.view.shape)
    (NativeScalarQueryShape.checked_power _ _ _ right.source.job.view.shape) left.source.job.view.enough right.source.job.view.enough
    _ _ _ _ _ _ dimensions.2 dimensions.1
    (OriginalJobOrdinal.request left.source.origin right.source.origin requests left.source.index right.source.index ordinal) sources counts y

end
end FormalProof4FHE.HasteBoots.LookupReciprocalStatement
