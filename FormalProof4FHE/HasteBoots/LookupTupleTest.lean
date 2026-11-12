module
public import FormalProof4FHE.HasteBoots.LookupSourceCandidate
public import FormalProof4FHE.HasteBoots.LookupPairChallengeBounds
@[expose] public section

/-! Whole tuple-compression tests use the exact original active prefix and
all decoded source lanes. Public rows retain request order, interpreting the
native width's missing entries as zero; validated rectangular request recovery
is a separate obligation. No helper or equality point enters this test. -/
namespace FormalProof4FHE.HasteBoots.LookupTupleTest
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3)
open NativeScalarQueryShape (laneBits)
open NativeSharedLookupStatement (Request)
open MatrixFold (Cube)
open LookupSourceCandidate (Candidate)
noncomputable section

def publicRows (request : Request) : Fin request.table.length → Fin request.columns → Goldilocks :=
  fun row column => ((request.table.get row).map NativeFieldRepresentation.goldValue)[column.val]?.getD 0

def tuples {padding rows : ℕ} (request : Request) (shape : 3+padding = 2^laneBits (3+padding))
    (enough : request.terminal.logicalLength.val ≤ 2^(laneBits (3+padding)+rows))
    (sources : Fin request.columns → Cube rows → Fin (3+padding) → Goldilocks) :=
  LookupPairArithmetic.activeTuples (Nat.add_sub_of_le enough)
    (fun column => LookupSourceFlattening.flatten shape (sources column))

def compression {padding rows : ℕ} (request : Request) (shape : 3+padding = 2^laneBits (3+padding))
    (enough : request.terminal.logicalLength.val ≤ 2^(laneBits (3+padding)+rows))
    (sources : Fin request.columns → Cube rows → Fin (3+padding) → Goldilocks) (y : Goldilocks3) : Prop :=
  (∃ position, ∀ row, tuples request shape enough sources position ≠ publicRows request row) ∧
    ∀ position, ∃ row, TupleHash.hash y (tuples request shape enough sources position) = TupleHash.hash y (publicRows request row)

theorem compression_congr {lp rp lr rr : ℕ} (left right : Request)
    (leftShape : 3+lp = 2^laneBits (3+lp)) (rightShape : 3+rp = 2^laneBits (3+rp))
    (leftEnough : left.terminal.logicalLength.val ≤ 2^(laneBits (3+lp)+lr))
    (rightEnough : right.terminal.logicalLength.val ≤ 2^(laneBits (3+rp)+rr))
    (leftSources : Fin left.columns → Cube lr → Fin (3+lp) → Goldilocks)
    (rightSources : Fin right.columns → Cube rr → Fin (3+rp) → Goldilocks)
    (padding : lp = rp) (rows : lr = rr) (request : left = right) (sources : HEq leftSources rightSources) :
    compression left leftShape leftEnough leftSources = compression right rightShape rightEnough rightSources := by
  cases padding
  cases rows
  cases request
  cases sources
  rfl

def test {A : Type} {program : OracleProgram.Program A} {position : ℕ} {world : InputIndexedOracle.World}
    (candidate : Candidate program position world) (dummy : NativeRootMessage.Digest) : Goldilocks3 → Prop :=
  compression (candidate.origin.ready.jobs.get candidate.index).tag.request
    (NativeScalarQueryShape.checked_power _ _ _ candidate.job.view.shape) candidate.job.view.enough
    (LookupSourceCandidate.sources candidate dummy)

theorem test_full {A : Type} {program : OracleProgram.Program A} {position : ℕ} {world : InputIndexedOracle.World}
    (candidate : Candidate program position world) (dummy : NativeRootMessage.Digest)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    test candidate dummy = compression (candidate.origin.ready.jobs.get candidate.index).tag.request
      (NativeScalarQueryShape.checked_power _ _ _ candidate.job.view.shape) candidate.job.view.enough
      (CanonicalAllocatedTables.sources candidate.allocation candidate.origin candidate.index candidate.job candidate.geometry dummy
        (OracleProgram.run program world).run.2) := by
  unfold test
  rw [LookupSourceCandidate.sources_full candidate dummy safe]

theorem test_fixed {A : Type} (program : OracleProgram.Program A) (position : ℕ) (world other : InputIndexedOracle.World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : NativeRootMessage.Digest)
    (input : left.draw.coefficients.phase.pending.input = right.draw.coefficients.phase.pending.input)
    (ordinal : left.index.val = right.index.val)
    (same : (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    test left dummy = test right dummy := by
  obtain ⟨registry,_,requests,sources⟩ := (LookupSourceCandidate.compare program position world other left right dummy input ordinal same).resolve_right
    (JobReferenceFixation.family_bad_false program position world other dummy good safe)
  have dimensions := OriginalJobOrdinal.dimensions left.origin right.origin registry
  exact compression_congr _ _ (NativeScalarQueryShape.checked_power _ _ _ left.job.view.shape)
    (NativeScalarQueryShape.checked_power _ _ _ right.job.view.shape) left.job.view.enough right.job.view.enough
    (LookupSourceCandidate.sources left dummy) (LookupSourceCandidate.sources right dummy) dimensions.2 dimensions.1
    (OriginalJobOrdinal.request left.origin right.origin requests left.index right.index ordinal) sources

end
end FormalProof4FHE.HasteBoots.LookupTupleTest
