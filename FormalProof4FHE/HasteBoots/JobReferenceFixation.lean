module
public import FormalProof4FHE.HasteBoots.JobReferenceCandidate
@[expose] public section

/-! One good attained reference fixes the complete native family and all
three original-position factors on the joint fiber. Counterfactual receipt
and late-context bad mass is retained as one union, without per-factor fees. -/
namespace FormalProof4FHE.HasteBoots.JobReferenceFixation
open InputIndexedOracle (World law)
open OracleProgram (Program runPrefix)
open JobReferenceCandidate (Candidate)
open NativeRootMessage (Digest)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

structure Good {A : Type} (program : Program A) (position : ℕ) (world : World) (dummy : Digest) : Prop where
  parent : ¬ProgramParentSeedCollision.Bad program world
  root : ¬NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2
  context : ¬ProgramContextTarget.Bad program world
  receipt : ¬ProgramReceiptCoverage.Bad program world
  collision : ¬ProgramReceiptCollision.Bad program world

def CounterBad {A : Type} (program : Program A) (world : World) : Prop :=
  ProgramReceiptCoverage.Bad program world ∨ ProgramContextTarget.Bad program world

def Fixed {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest) (radius : ℕ) : Prop :=
  (FamilyPosteriorMismatch.Agrees left.selection.family.parent right.selection.family.parent ∧ left.selection.family.roots = right.selection.family.roots) ∧
  (HEq (left.selection.sources dummy radius) (right.selection.sources dummy radius) ∧
    HEq (left.selection.helpers dummy radius) (right.selection.helpers dummy radius)) ∧
  right.compression.value.word = left.compression.value.word ∧ right.offset.value.word = left.offset.value.word ∧
    right.point.value.point = left.point.value.point

theorem family_bad_false {A : Type} (program : Program A) (position : ℕ) (world other : World) (dummy : Digest)
    (good : Good program position world dummy) (safe : ¬CounterBad program other)
    (bad : ProgramParentSeedCollision.Bad program world ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
      ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other) : False := by
  rcases bad with bad | bad | bad | bad
  · exact good.parent bad
  · exact good.root bad
  · exact good.context bad
  · exact safe (Or.inr bad)

theorem receipt_bad_false {A : Type} (program : Program A) (position : ℕ) (world other : World) (dummy : Digest)
    (good : Good program position world dummy) (safe : ¬CounterBad program other)
    (bad : ProgramReceiptCoverage.Bad program world ∨ ProgramReceiptCoverage.Bad program other ∨ ProgramReceiptCollision.Bad program world) : False := by
  rcases bad with bad | bad | bad
  · exact good.receipt bad
  · exact safe (Or.inl bad)
  · exact good.collision bad

theorem fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest) (radius : ℕ)
    (input : left.selection.family.input = right.selection.family.input) (ordinal : left.selection.index.val = right.selection.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : Good program position world dummy) (safe : ¬CounterBad program other) : Fixed left right dummy radius := by
  have data := (OriginalScalarFamily.compare program position world other left.selection.family right.selection.family dummy input same).resolve_right
    (family_bad_false program position world other dummy good safe)
  have family := (AllocatedJobFamily.compare program position world other left.selection right.selection input ordinal same dummy radius).resolve_right
    (family_bad_false program position world other dummy good safe)
  let rightCompression := right.compression.reindex input.symm (congrArg ScalarReceiptMatching.Position.compression ordinal.symm)
  let rightOffset := right.offset.reindex input.symm (congrArg ScalarReceiptMatching.Position.offset ordinal.symm)
  let rightPoint := right.point.reindex input.symm (congrArg ScalarReceiptMatching.Position.equalityPoint ordinal.symm)
  have compression := (PositionedFactorSamples.scalar program position world other _ _ left.compression rightCompression left.first left.first_position same).resolve_right
    (receipt_bad_false program position world other dummy good safe)
  have offset := (PositionedFactorSamples.scalar program position world other _ _ left.offset rightOffset left.first left.first_position same).resolve_right
    (receipt_bad_false program position world other dummy good safe)
  have point := (PositionedFactorSamples.point program position world other _ _ left.point rightPoint left.first left.first_position same).resolve_right
    (receipt_bad_false program position world other dummy good safe)
  exact ⟨data,family,compression,offset,point⟩

def Mismatch {A : Type} (program : Program A) (position : ℕ) (world : World)
    (reference : Candidate program position world) (dummy : Digest) (radius : ℕ) (other : World) : Prop :=
  ∃ candidate : Candidate program position other,
    reference.selection.family.input = candidate.selection.family.input ∧ reference.selection.index.val = candidate.selection.index.val ∧
    (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧ ¬Fixed reference candidate dummy radius

theorem mismatch_implies_bad {A : Type} (program : Program A) (position : ℕ) (world : World)
    (reference : Candidate program position world) (dummy : Digest) (radius : ℕ) (good : Good program position world dummy)
    (other : World) (mismatch : Mismatch program position world reference dummy radius other) : CounterBad program other := by
  by_contra safe
  obtain ⟨candidate,input,ordinal,same,different⟩ := mismatch
  exact different (fixed program position world other reference candidate dummy radius input ordinal same good safe)

theorem conditional_le {A : Type} (program : Program A) (position : ℕ) (world : World)
    (reference : Candidate program position world) (dummy : Digest) (radius : ℕ) (good : Good program position world dummy) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Mismatch program position world reference dummy radius other} ≤
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | CounterBad program other} :=
  measure_mono (fun other mismatch => mismatch_implies_bad program position world reference dummy radius good other mismatch)

end
end FormalProof4FHE.HasteBoots.JobReferenceFixation
