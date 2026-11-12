module
public import FormalProof4FHE.HasteBoots.RefinedEqualityKernel
@[expose] public section

/-! Adaptive original equality classes choose attained good references on
the same refined fiber. Empty good classes are covered by existing bad mass,
without a successful-world probability floor or measurable chooser. -/
namespace FormalProof4FHE.HasteBoots.EqualityClassKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open EqualityFactorCandidate (Candidate)
open JobReferenceFixation (Good)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

abbrev Class {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (world : World) :=
  {candidate : Candidate program position world // candidate.family.selection.family.input = input ∧ candidate.family.selection.index.val = ordinal}

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


def Event {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (dummy : Digest) (world : World) : Prop :=
  ∃ candidate : Class program position input ordinal world, EqualityCandidateKernel.Event candidate.val dummy world

/-- One original job/input class has at most 63/q^3 native equality loss,
plus the existing shared bad remainder on the same refined prefix fiber. -/
theorem bound {A : Type} (program : Program A) (position : ℕ) (input : Input) (ordinal : ℕ) (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | Event program position input ordinal dummy other} ≤
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | Bad program position dummy other} + (63 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  apply conditional_le program position input ordinal world dummy
    {other | Event program position input ordinal dummy other}
    (fun _ candidate => {other | EqualityCandidateKernel.Event candidate.val dummy other}) _
  · intro other _ occurred _
    obtain ⟨candidate,_⟩ := occurred
    exact ⟨candidate⟩
  · intro reference leftFiber left good other rightFiber occurred safe
    obtain ⟨right,failed⟩ := occurred
    have otherGood : Good program position other dummy := Classical.not_not.mp safe
    have counterSafe : ¬JobReferenceFixation.CounterBad program other := by
      rintro (receipt | context)
      · exact otherGood.receipt receipt
      · exact otherGood.context context
    have events := EqualityCandidateKernel.event_fixed left.val right.val dummy
      (left.property.1.trans right.property.1.symm) (left.property.2.trans right.property.2.symm)
      (rightFiber.trans leftFiber.symm) good counterSafe
    rw [events]
    exact failed
  · intro reference same candidate _
    have native := RefinedEqualityKernel.bound program position reference candidate.val dummy
    rw [same] at native
    have dimension : candidate.val.family.selection.origin.geometry.geometry.1.val ≤ 63 := by
      rw [candidate.val.family.selection.job.view.dimension]
      have shift := candidate.val.family.selection.job.view.shift
      omega
    have numerator : (candidate.val.family.selection.origin.geometry.geometry.1.val : ENNReal) ≤ 63 := by exact_mod_cast dimension
    exact native.trans (ENNReal.div_le_div_right numerator _)

end
end FormalProof4FHE.HasteBoots.EqualityClassKernel
