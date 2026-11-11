module
public import FormalProof4FHE.HasteBoots.AttainableReferenceBound
@[expose] public section

/-! Attainable native job references on a fixed completed prefix fiber. A
reference has the actual scalar input and job ordinal of the event class.
Empty good classes are covered by bad mass, not normalized away. -/
namespace FormalProof4FHE.HasteBoots.JobReferenceSelection
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open JobReferenceCandidate (Candidate)
open JobReferenceFixation (Good Fixed)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

abbrev Class {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (world : World) :=
  {candidate : Candidate program position world // candidate.selection.family.input = input ∧ candidate.selection.index.val = ordinal}

def Bad {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World) : Prop := ¬Good program position world dummy

theorem choose_or_cover {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (world : World)
    (dummy : Digest) (event : Set World)
    (witness : ∀ other, (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run → other ∈ event →
      ¬Bad program position dummy other → Nonempty (Class program position input ordinal other)) :
    (∃ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧
      ∃ _ : Class program position input ordinal reference, Good program position reference dummy) ∨
    {other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run} ∩ event ⊆ {other | Bad program position dummy other} :=
  AttainableReferenceBound.choose_or_cover _ event _ (Class program position input ordinal) (fun reference _ => Good program position reference dummy)
    witness (fun _ _ safe _ => Classical.not_not.mp safe)

/-- Fixed-reference kernels can now be bounded separately and composed with
one posterior bad remainder. Every reference in the bound is attained on the
same original input/job class; no successful-world mass floor is used. -/
theorem conditional_le {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (world : World)
    (dummy : Digest) (event : Set World)
    (test : (reference : World) → Class program position input ordinal reference → Set World) (risk : ENNReal)
    (witness : ∀ other, (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run → other ∈ event →
      ¬Bad program position dummy other → Nonempty (Class program position input ordinal other))
    (covered : ∀ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run →
      ∀ candidate : Class program position input ordinal reference, Good program position reference dummy →
      ∀ other, (ParentFactorFiber.extend (runPrefix position program) other).run =
          (ParentFactorFiber.extend (runPrefix position program) world).run → other ∈ event →
        ¬Bad program position dummy other → other ∈ test reference candidate)
    (bounded : ∀ reference, (ParentFactorFiber.extend (runPrefix position program) reference).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run →
      ∀ candidate : Class program position input ordinal reference, Good program position reference dummy →
      (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run}]) (test reference candidate) ≤ risk) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) event ≤
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Bad program position dummy other} + risk := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  rcases choose_or_cover program position input ordinal world dummy event witness with ⟨reference,same,candidate,good⟩ | allBad
  · have included := FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event)
      (fun other => Bad program position dummy other ∨ other ∈ test reference candidate) (by
        intro other fiber occurred
        by_cases bad : Bad program position dummy other
        · exact Or.inl bad
        · exact Or.inr (covered reference same candidate good other fiber occurred bad))
    exact included.trans ((measure_union_le _ _).trans (add_le_add le_rfl (bounded reference same candidate good)))
  · have included := FactorPosteriorMismatch.conditional_mono replay world (fun other => other ∈ event) (Bad program position dummy)
      (fun other fiber occurred => allBad ⟨fiber,occurred⟩)
    exact included.trans (le_add_of_nonneg_right (by exact zero_le))

/-- Outside the same bad remainder, any attained reference and attained event
candidate in the class have the same whole family and all original factors. -/
theorem class_fixed {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (world reference other : World)
    (left : Class program position input ordinal reference) (right : Class program position input ordinal other)
    (leftFiber : (ParentFactorFiber.extend (runPrefix position program) reference).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (rightFiber : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (dummy : Digest) (radius : ℕ) (good : Good program position reference dummy) (safe : ¬Bad program position dummy other) :
    Fixed left.val right.val dummy radius := by
  have otherGood : Good program position other dummy := Classical.not_not.mp safe
  apply JobReferenceFixation.fixed program position reference other left.val right.val dummy radius
    (left.property.1.trans right.property.1.symm) (left.property.2.trans right.property.2.symm) (rightFiber.trans leftFiber.symm) good
  intro bad
  rcases bad with receipt | context
  · exact otherGood.receipt receipt
  · exact otherGood.context context

end
end FormalProof4FHE.HasteBoots.JobReferenceSelection
