module
public import FormalProof4FHE.HasteBoots.OriginalPackedFamily
@[expose] public section

/-! A good reference family's posterior competitors can disagree on original
family data only in the counterfactual world's late-context event. Its mass
is retained and averages to the same whole-program target charge. -/
namespace FormalProof4FHE.HasteBoots.FamilyPosteriorMismatch
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open OriginalParentFamily (Family)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

def Agrees {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Family program position world) (right : Family program position other) : Prop :=
  left.registry = right.registry ∧ left.helper = right.helper ∧ left.requests = right.requests ∧
    left.parent = right.parent ∧ left.bindings = right.bindings

def Mismatch {A : Type} (program : Program A) (position : ℕ) (world : World)
    (reference : Family program position world) (input : Input) (other : World) : Prop :=
  ∃ candidate : Family program position other,
    NativeChildSeedView.quote input = some (InputIndexedOracle.block other candidate.input 0 64) ∧
    (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run ∧ ¬Agrees reference candidate

theorem mismatch_implies_bad {A : Type} (program : Program A) (position : ℕ) (world : World)
    (reference : Family program position world) (input : Input) (dummy : NativeRootMessage.Digest)
    (quote : NativeChildSeedView.quote input = some (InputIndexedOracle.block world reference.input 0 64))
    (parentSafe : ¬ProgramParentSeedCollision.Bad program world)
    (rootSafe : ¬NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2)
    (contextSafe : ¬ProgramContextTarget.Bad program world) (other : World)
    (mismatch : Mismatch program position world reference input other) : ProgramContextTarget.Bad program other := by
  obtain ⟨candidate,otherQuote,same,different⟩ := mismatch
  rcases OriginalParentFamily.compare program position world other reference candidate input dummy quote otherQuote same with equal | bad | bad | bad | bad
  · exact False.elim (different equal)
  · exact False.elim (parentSafe bad)
  · exact False.elim (rootSafe bad)
  · exact False.elim (contextSafe bad)
  · exact bad

theorem conditional_le {A : Type} (program : Program A) (position : ℕ) (world : World)
    (reference : Family program position world) (input : Input) (dummy : NativeRootMessage.Digest)
    (quote : NativeChildSeedView.quote input = some (InputIndexedOracle.block world reference.input 0 64))
    (parentSafe : ¬ProgramParentSeedCollision.Bad program world)
    (rootSafe : ¬NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2)
    (contextSafe : ¬ProgramContextTarget.Bad program world) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Mismatch program position world reference input other} ≤
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | ProgramContextTarget.Bad program other} :=
  measure_mono (fun other mismatch => mismatch_implies_bad program position world reference input dummy quote parentSafe rootSafe contextSafe other mismatch)

/-- This bound can be used after selecting any good attainable reference
family. It does not assume the whole posterior fiber consists of good runs. -/
theorem averaged_counterfactual_charge {A : Type} (program : Program A) (position : ℕ) :
    (∫⁻ world, (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | ProgramContextTarget.Bad program other} ∂law) ≤
      ∫⁻ world, ProgramContextTarget.totalCharge program world ∂law :=
  ProgramContextTarget.posterior_average_le program (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))

end
end FormalProof4FHE.HasteBoots.FamilyPosteriorMismatch
