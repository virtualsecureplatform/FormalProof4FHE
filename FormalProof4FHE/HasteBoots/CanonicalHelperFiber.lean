module
public import FormalProof4FHE.HasteBoots.OriginalRegistryFiber
public import FormalProof4FHE.HasteBoots.SharedParentBindingsData
@[expose] public section

/-! The actual canonical binding sequence fixes the helper context digest.
Observed full preimages identify its original parameter record outside the
same shared hash bad event. Empty synthetic sequences cannot supply a helper. -/
namespace FormalProof4FHE.HasteBoots.CanonicalHelperFiber
open InputIndexedOracle (World)
open NativeGoldBlockCode (Stored description)
open NativeBrakedownContext (Parameters)
open NativeSharedLookupParent (Oracle)
open NativeCanonicalLookupWire (Binding)
open NativeLookupRequestWire (Request)
open OracleProgram (Program run runPrefix)
noncomputable section

theorem helper_contexts (leftRegistry rightRegistry : List (Oracle Stored)) (leftHelper rightHelper : Parameters Stored)
    (world other : World) (leftRequests rightRequests : List Request) (bindings : List Binding) (nonempty : bindings ≠ [])
    (leftRelated : List.Forall₂ (ParentBindingTrace.ForRequest description.row leftRegistry leftHelper world) leftRequests bindings)
    (rightRelated : List.Forall₂ (ParentBindingTrace.ForRequest description.row rightRegistry rightHelper other) rightRequests bindings) :
    (run (NativeBrakedownContext.context description.row leftHelper) world).run.1 =
      (run (NativeBrakedownContext.context description.row rightHelper) other).run.1 := by
  cases leftRelated with
  | nil => exact False.elim (nonempty rfl)
  | cons leftHead leftTail =>
    cases rightRelated with
    | cons rightHead rightTail =>
      obtain ⟨_,_,_,leftComputed,_⟩ := leftHead
      obtain ⟨_,_,_,rightComputed,_⟩ := rightHead
      exact leftComputed.trans rightComputed.symm

theorem parameters {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (leftRegistry rightRegistry : List (Oracle Stored)) (leftHelper rightHelper : Parameters Stored)
    (leftRequests rightRequests : List Request) (bindings : List Binding) (nonempty : bindings ≠ [])
    (leftRelated : List.Forall₂ (ParentBindingTrace.ForRequest description.row leftRegistry leftHelper world) leftRequests bindings)
    (rightRelated : List.Forall₂ (ParentBindingTrace.ForRequest description.row rightRegistry rightHelper other) rightRequests bindings)
    (leftObserved : (run (NativeBrakedownContext.context description.row leftHelper) world).run.2.Sublist (runPrefix position program world).run.2)
    (rightObserved : (run (NativeBrakedownContext.context description.row rightHelper) other).run.2.Sublist (runPrefix position program other).run.2)
    (dummy : NativeRootMessage.Digest)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    leftHelper = rightHelper ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 := by
  have contexts := helper_contexts leftRegistry rightRegistry leftHelper rightHelper world other leftRequests rightRequests bindings nonempty leftRelated rightRelated
  have computed : (run (NativeBrakedownContext.context description.row leftHelper) world).run.1 =
      some (InputIndexedOracle.sha512 world (GoldContextInput.bytes leftHelper)) := by rw [GoldContextCollision.context_run]
  exact GoldContextFiber.on_parent_fiber (OracleProgram.prefix_replay position program) world other leftHelper rightHelper _ dummy
    computed (contexts.symm.trans computed) leftObserved rightObserved same


/-- Actual complete computations and chronological helper naming discharge
old-prefix observations with the bounded late-context alternative. -/
theorem parameters_covered {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (leftRegistry rightRegistry : List (Oracle Stored)) (leftHelper rightHelper : Parameters Stored)
    (leftRequests rightRequests : List Request) (bindings : List Binding) (nonempty : bindings ≠ [])
    (leftRelated : List.Forall₂ (ParentBindingTrace.ForRequest description.row leftRegistry leftHelper world) leftRequests bindings)
    (rightRelated : List.Forall₂ (ParentBindingTrace.ForRequest description.row rightRegistry rightHelper other) rightRequests bindings)
    (leftInput rightInput : InputIndexedOracle.Input)
    (leftKnown : NativeParentLineage.Known world (runPrefix position program world).run.2 leftInput
      (InputIndexedOracle.sha512 world (GoldContextInput.bytes leftHelper)))
    (rightKnown : NativeParentLineage.Known other (runPrefix position program other).run.2 rightInput
      (InputIndexedOracle.sha512 other (GoldContextInput.bytes rightHelper)))
    (leftFull : (run (NativeBrakedownContext.context description.row leftHelper) world).run.2.Sublist (run program world).run.2)
    (rightFull : (run (NativeBrakedownContext.context description.row rightHelper) other).run.2.Sublist (run program other).run.2)
    (dummy : NativeRootMessage.Digest)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    leftHelper = rightHelper ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
      ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other := by
  have leftComputed : (run (NativeBrakedownContext.context description.row leftHelper) world).run.1 =
      some (InputIndexedOracle.sha512 world (GoldContextInput.bytes leftHelper)) := by rw [GoldContextCollision.context_run]
  have rightComputed : (run (NativeBrakedownContext.context description.row rightHelper) other).run.1 =
      some (InputIndexedOracle.sha512 other (GoldContextInput.bytes rightHelper)) := by rw [GoldContextCollision.context_run]
  rcases GoldContextCoverage.helper program world position leftInput leftHelper _ leftKnown leftComputed leftFull with leftObserved | bad
  · rcases GoldContextCoverage.helper program other position rightInput rightHelper _ rightKnown rightComputed rightFull with rightObserved | bad
    · rcases parameters program position world other leftRegistry rightRegistry leftHelper rightHelper leftRequests rightRequests bindings nonempty
        leftRelated rightRelated leftObserved rightObserved dummy same with equal | bad
      · exact Or.inl equal
      · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inr bad))
  · exact Or.inr (Or.inr (Or.inl bad))

end
end FormalProof4FHE.HasteBoots.CanonicalHelperFiber
