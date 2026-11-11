module
public import FormalProof4FHE.HasteBoots.GoldContextCoverage
@[expose] public section

/-! Whole ordered registry identity follows from the common strict parent
view and actual context computations. One shared exception covers all slots;
duplicate and unused entries are retained, without a per-slot union charge. -/
namespace FormalProof4FHE.HasteBoots.OriginalRegistryFiber
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeGoldBlockCode (Stored description)
open NativeSharedLookupParent (Oracle)
open NativePrefixCodec (Vector)
open OracleProgram (Program run runPrefix)
noncomputable section

theorem oracle_eq (left right : Oracle Stored) (parameters : left.parameters = right.parameters) (root : left.root = right.root) : left = right := by
  cases left
  cases right
  cases parameters
  cases root
  rfl

theorem registry {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left right : Vector (Oracle Stored)) (input : Input) (helper dummy : Digest) (view : SharedParentInputView.View)
    (known : NativeParentLineage.Known world (runPrefix position program world).run.2 input helper)
    (parsed : SharedParentInputView.parse input = some view)
    (leftComputed : (run (NativeSharedLookupParent.contexts description.row left.val) world).run.1 = some view.sources.val)
    (rightComputed : (run (NativeSharedLookupParent.contexts description.row right.val) other).run.1 = some view.sources.val)
    (leftFull : ∀ index : Fin left.val.length,
      (run (NativeBrakedownContext.context description.row (left.val.get index).parameters) world).run.2.Sublist (run program world).run.2)
    (rightFull : ∀ index : Fin right.val.length,
      (run (NativeBrakedownContext.context description.row (right.val.get index).parameters) other).run.2.Sublist (run program other).run.2)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    left = right ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
      ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other := by
  by_cases rootBad : NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2
  · exact Or.inr (Or.inl rootBad)
  by_cases lateLeft : ProgramContextTarget.Bad program world
  · exact Or.inr (Or.inr (Or.inl lateLeft))
  by_cases lateRight : ProgramContextTarget.Bad program other
  · exact Or.inr (Or.inr (Or.inr lateRight))
  apply Or.inl
  apply Subtype.ext
  have count : left.val.length = right.val.length :=
    (OriginalSharedParent.length description.row left world view leftComputed).symm.trans
      (OriginalSharedParent.length description.row right other view rightComputed)
  apply List.ext_getElem count
  intro index leftBound rightBound
  have compared := GoldContextCoverage.registry_slot_on_fiber program position world other left right input helper dummy view known parsed
    leftComputed rightComputed ⟨index,leftBound⟩ ⟨index,rightBound⟩ rfl (leftFull ⟨index,leftBound⟩) (rightFull ⟨index,rightBound⟩) same
  rcases compared with equal | bad
  · exact oracle_eq _ _ equal.1 equal.2
  · rcases bad with bad | bad | bad
    · exact False.elim (rootBad bad)
    · exact False.elim (lateLeft bad)
    · exact False.elim (lateRight bad)

end
end FormalProof4FHE.HasteBoots.OriginalRegistryFiber
