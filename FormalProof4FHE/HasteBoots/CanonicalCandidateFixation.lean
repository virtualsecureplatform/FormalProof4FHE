module
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedJobWork
@[expose] public section

/-! Attained native job candidates retain canonical per-object decoders.
The existing metadata/factor fixation and canonical family fixation share
one original replay fiber and the same reference bad alternatives. -/
namespace FormalProof4FHE.HasteBoots.CanonicalCandidateFixation
open InputIndexedOracle (Input World)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open JobReferenceCandidate (Candidate)
noncomputable section

def sources {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) :=
  CanonicalAllocatedTables.sources candidate.selection.allocation candidate.selection.origin candidate.selection.index
    candidate.selection.job candidate.selection.geometry dummy (runPrefix position program world).run.2

def helpers {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) :=
  CanonicalAllocatedTables.helpers candidate.selection.allocation candidate.selection.origin candidate.selection.index
    candidate.selection.job candidate.selection.geometry dummy (runPrefix position program world).run.2

structure Fixed {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest) : Prop where
  base : JobReferenceFixation.Fixed left right dummy 0
  families : HEq (sources left dummy) (sources right dummy) ∧ HEq (helpers left dummy) (helpers right dummy)

theorem fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.selection.family.input = right.selection.family.input) (ordinal : left.selection.index.val = right.selection.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    Fixed left right dummy := by
  have base := JobReferenceFixation.fixed program position world other left right dummy 0 input ordinal same good safe
  have family := (CanonicalAllocatedFamilyFixation.families_on_fiber left.selection.allocation right.selection.allocation left.selection.origin
    right.selection.origin program position left.selection.family right.selection.family left.selection.registry right.selection.registry
    left.selection.helper right.selection.helper left.selection.requests right.selection.requests left.selection.roots right.selection.roots
    input same left.selection.index right.selection.index ordinal left.selection.job right.selection.job left.selection.geometry right.selection.geometry dummy).resolve_right
      (JobReferenceFixation.family_bad_false program position world other dummy good safe)
  exact ⟨base,family⟩

theorem class_fixed {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (world reference other : World)
    (left : JobReferenceSelection.Class program position input ordinal reference) (right : JobReferenceSelection.Class program position input ordinal other)
    (leftFiber : (ParentFactorFiber.extend (runPrefix position program) reference).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (rightFiber : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (dummy : Digest) (good : JobReferenceFixation.Good program position reference dummy) (safe : ¬JobReferenceSelection.Bad program position dummy other) :
    Fixed left.val right.val dummy := by
  have otherGood : JobReferenceFixation.Good program position other dummy := Classical.not_not.mp safe
  apply fixed program position reference other left.val right.val dummy
    (left.property.1.trans right.property.1.symm) (left.property.2.trans right.property.2.symm) (rightFiber.trans leftFiber.symm) good
  intro bad
  rcases bad with receipt | context
  · exact otherGood.receipt receipt
  · exact otherGood.context context


end
end FormalProof4FHE.HasteBoots.CanonicalCandidateFixation
