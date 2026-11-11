module
public import FormalProof4FHE.HasteBoots.ProgramParentSeedCollision
public import FormalProof4FHE.HasteBoots.ParentFactorFiber
@[expose] public section

/-! Two actual parent candidates matching the same quoted seed on the joint
fiber are the same raw input, or witness the separately bounded parent-seed
collision ledger. No uniqueness assumption about a partial cache is used. -/
namespace FormalProof4FHE.HasteBoots.ParentMatchFixation
open InputIndexedOracle (Input World)
open OracleProgram (Program runPrefix)
noncomputable section

theorem on_fiber {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (input left right : Input)
    (leftNamed : left ∈ ParentSeedCandidates.inputs (runPrefix position program world).run.2)
    (rightNamed : right ∈ ParentSeedCandidates.inputs (runPrefix position program other).run.2)
    (leftQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block world left 0 64))
    (rightQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block other right 0 64))
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    right = left ∨ ProgramParentSeedCollision.Bad program world := by
  have old := ParentFactorFiber.old_packet (runPrefix position program) world other same
  have rightOld := rightNamed
  rw [old] at rightOld
  have fixed := ParentSeedCompletion.seed_on_fiber (OracleProgram.prefix_replay position program) world other right rightOld
    (ParentFactorFiber.parent_packet (runPrefix position program) world other same)
  have equal : InputIndexedOracle.block world right 0 64 = InputIndexedOracle.block world left 0 64 :=
    fixed.symm.trans (Option.some.inj (rightQuote.symm.trans leftQuote))
  by_cases sameInput : right = left
  · exact Or.inl sameInput
  · exact Or.inr (ProgramParentSeedCollision.prefix_covers program world position ⟨right,rightOld,left,leftNamed,sameInput,equal⟩)

/-- Native semantic ancestry supplies candidate membership for both parents;
no independent naming certificate is needed at this comparison boundary. -/
theorem known_on_fiber {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (input left right : Input) (leftContext rightContext : NativeRootMessage.Digest)
    (leftKnown : NativeParentLineage.Known world (runPrefix position program world).run.2 left leftContext)
    (rightKnown : NativeParentLineage.Known other (runPrefix position program other).run.2 right rightContext)
    (leftQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block world left 0 64))
    (rightQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block other right 0 64))
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    right = left ∨ ProgramParentSeedCollision.Bad program world :=
  on_fiber program position world other input left right (ParentSeedCandidates.helper_known leftKnown)
    (ParentSeedCandidates.helper_known rightKnown) leftQuote rightQuote same

end
end FormalProof4FHE.HasteBoots.ParentMatchFixation
