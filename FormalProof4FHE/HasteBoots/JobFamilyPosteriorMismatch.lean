module
public import FormalProof4FHE.HasteBoots.AllocatedJobFamily
@[expose] public section

/-! Disagreement of complete selected native source/helper functions on a
fixed joint prefix fiber is covered by counterfactual late-context bad mass.
The original job ordinal and literal scalar input are retained explicitly. -/
namespace FormalProof4FHE.HasteBoots.JobFamilyPosteriorMismatch
open InputIndexedOracle (World law)
open OracleProgram (Program runPrefix)
open AllocatedJobFamily (Selection)
open NativeRootMessage (Digest)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def Mismatch {A : Type} (program : Program A) (position : ℕ) (world : World)
    (reference : Selection program position world) (dummy : Digest) (radius : ℕ) (other : World) : Prop :=
  ∃ candidate : Selection program position other,
    reference.family.input = candidate.family.input ∧ reference.index.val = candidate.index.val ∧
    (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧
    ¬(HEq (reference.sources dummy radius) (candidate.sources dummy radius) ∧
      HEq (reference.helpers dummy radius) (candidate.helpers dummy radius))

theorem mismatch_implies_bad {A : Type} (program : Program A) (position : ℕ) (world : World)
    (reference : Selection program position world) (dummy : Digest) (radius : ℕ)
    (parentSafe : ¬ProgramParentSeedCollision.Bad program world)
    (rootSafe : ¬NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2)
    (contextSafe : ¬ProgramContextTarget.Bad program world) (other : World)
    (mismatch : Mismatch program position world reference dummy radius other) : ProgramContextTarget.Bad program other := by
  obtain ⟨candidate,input,ordinal,same,different⟩ := mismatch
  rcases AllocatedJobFamily.compare program position world other reference candidate input ordinal same dummy radius with equal | bad | bad | bad | bad
  · exact False.elim (different equal)
  · exact False.elim (parentSafe bad)
  · exact False.elim (rootSafe bad)
  · exact False.elim (contextSafe bad)
  · exact bad

theorem conditional_le {A : Type} (program : Program A) (position : ℕ) (world : World)
    (reference : Selection program position world) (dummy : Digest) (radius : ℕ)
    (parentSafe : ¬ProgramParentSeedCollision.Bad program world)
    (rootSafe : ¬NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2)
    (contextSafe : ¬ProgramContextTarget.Bad program world) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Mismatch program position world reference dummy radius other} ≤
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | ProgramContextTarget.Bad program other} :=
  measure_mono (fun other mismatch => mismatch_implies_bad program position world reference dummy radius parentSafe rootSafe contextSafe other mismatch)

/-- The counterfactual remainder at each fixed analysis prefix averages to
the existing lifetime target charge, rather than a new per-job ledger. -/
theorem averaged_counterfactual_charge {A : Type} (program : Program A) (position : ℕ) :
    (∫⁻ world, (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | ProgramContextTarget.Bad program other} ∂law) ≤
      ∫⁻ world, ProgramContextTarget.totalCharge program world ∂law :=
  ProgramContextTarget.posterior_average_le program (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))

end
end FormalProof4FHE.HasteBoots.JobFamilyPosteriorMismatch
