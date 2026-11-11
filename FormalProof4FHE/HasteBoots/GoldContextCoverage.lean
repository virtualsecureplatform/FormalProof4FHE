module
public import FormalProof4FHE.HasteBoots.ProgramContextTarget
public import FormalProof4FHE.HasteBoots.GoldContextFiber
public import FormalProof4FHE.HasteBoots.RegistryContextObservation
@[expose] public section

/-! Prior parameter-preimage coverage follows from causal naming and actual
complete computations outside a bounded late-target exception. Comparing two
worlds retains that exception in each world and the shared reference hash bad
event; counterfactual bad mass is not silently discarded. -/
namespace FormalProof4FHE.HasteBoots.GoldContextCoverage
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeGoldBlockCode (Stored description)
open NativeBrakedownContext (Parameters)
open OracleProgram (Program run runPrefix)
noncomputable section

theorem helper {A : Type} (program : Program A) (world : World) (position : ℕ) (input : Input)
    (parameters : Parameters Stored) (digest : Digest)
    (known : NativeParentLineage.Known world (runPrefix position program world).run.2 input digest)
    (computed : (run (NativeBrakedownContext.context description.row parameters) world).run.1 = some digest)
    (full : (run (NativeBrakedownContext.context description.row parameters) world).run.2.Sublist (run program world).run.2) :
    (run (NativeBrakedownContext.context description.row parameters) world).run.2.Sublist (runPrefix position program world).run.2 ∨
      ProgramContextTarget.Bad program world :=
  ProgramContextTarget.context_observed_or_bad program world position parameters digest computed full
    (ContextDigestTargets.helper_known world _ input digest known)

theorem source {A : Type} (program : Program A) (world : World) (position : ℕ) (input : Input)
    (parameters : Parameters Stored) (key : NativeCanonicalLookupWire.Source)
    (known : NativeSourceLineage.Known world (runPrefix position program world).run.2 input key)
    (computed : (run (NativeBrakedownContext.context description.row parameters) world).run.1 = some key.1)
    (full : (run (NativeBrakedownContext.context description.row parameters) world).run.2.Sublist (run program world).run.2) :
    (run (NativeBrakedownContext.context description.row parameters) world).run.2.Sublist (runPrefix position program world).run.2 ∨
      ProgramContextTarget.Bad program world :=
  ProgramContextTarget.context_observed_or_bad program world position parameters key.1 computed full
    (ContextDigestTargets.source_known world _ input key known)

/-- The strict parent parser names every original registry context in the
old history, including duplicate and unused slots. -/
theorem registry_named {A : Type} (program : Program A) (world : World) (position : ℕ) (input : Input)
    (helper : Digest) (known : NativeParentLineage.Known world (runPrefix position program world).run.2 input helper)
    (view : SharedParentInputView.View) (parsed : SharedParentInputView.parse input = some view)
    (key : NativeCanonicalLookupWire.Source) (member : key ∈ view.sources.val) :
    key.1 ∈ ContextDigestTargets.targets (runPrefix position program world).run.2 := by
  apply ContextDigestTargets.known_input world _ input helper key.1 known
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨key,?_,rfl⟩
  obtain ⟨bytes,valid⟩ := SharedParentInputView.parse_sound input view parsed
  change key ∈ (NativeRootInputView.raw input).getD []
  rw [bytes,NativeRootInputView.raw_complete _ valid,Option.getD_some]
  exact (NativeRootInputView.recognized_sources view.frames (SharedParentInputView.registryFrame view.sources)
    (by simp [SharedParentInputView.View.frames]) view.sources.val (NativeRootInputView.registry_complete view.sources)).subset member

/-- Same named digest and actual full computations identify parameters,
except for the shared hash bad event or late-target risk in either world. -/
theorem parameters_on_fiber {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left right : Parameters Stored) (digest dummy : Digest)
    (leftComputed : (run (NativeBrakedownContext.context description.row left) world).run.1 = some digest)
    (rightComputed : (run (NativeBrakedownContext.context description.row right) other).run.1 = some digest)
    (leftFull : (run (NativeBrakedownContext.context description.row left) world).run.2.Sublist (run program world).run.2)
    (rightFull : (run (NativeBrakedownContext.context description.row right) other).run.2.Sublist (run program other).run.2)
    (named : digest ∈ ContextDigestTargets.targets (runPrefix position program world).run.2)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    left = right ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
      ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other := by
  have packet := ParentFactorFiber.old_packet (runPrefix position program) world other same
  have otherNamed : digest ∈ ContextDigestTargets.targets (runPrefix position program other).run.2 := by rw [packet]; exact named
  rcases ProgramContextTarget.context_observed_or_bad program world position left digest leftComputed leftFull named with leftObserved | bad
  · rcases ProgramContextTarget.context_observed_or_bad program other position right digest rightComputed rightFull otherNamed with rightObserved | bad
    · rcases GoldContextFiber.on_parent_fiber (OracleProgram.prefix_replay position program) world other left right digest dummy
        leftComputed rightComputed leftObserved rightObserved same with equal | bad
      · exact Or.inl equal
      · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inr bad))
  · exact Or.inr (Or.inr (Or.inl bad))


/-- Original corresponding registry slots need complete-execution evidence,
not independently supplied old-prefix context observations. -/
theorem registry_slot_on_fiber {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left right : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle Stored))
    (input : Input) (helper dummy : Digest) (view : SharedParentInputView.View)
    (known : NativeParentLineage.Known world (runPrefix position program world).run.2 input helper)
    (parsed : SharedParentInputView.parse input = some view)
    (leftComputed : (run (NativeSharedLookupParent.contexts description.row left.val) world).run.1 = some view.sources.val)
    (rightComputed : (run (NativeSharedLookupParent.contexts description.row right.val) other).run.1 = some view.sources.val)
    (leftIndex : Fin left.val.length) (rightIndex : Fin right.val.length) (ordinal : leftIndex.val = rightIndex.val)
    (leftFull : (run (NativeBrakedownContext.context description.row left.val[leftIndex.val].parameters) world).run.2.Sublist (run program world).run.2)
    (rightFull : (run (NativeBrakedownContext.context description.row right.val[rightIndex.val].parameters) other).run.2.Sublist (run program other).run.2)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    (left.val[leftIndex.val].parameters = right.val[rightIndex.val].parameters ∧ left.val[leftIndex.val].root = right.val[rightIndex.val].root) ∨
      NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
        ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other := by
  obtain ⟨source,found,context,_⟩ := OriginalSharedParent.slot description.row left world view leftComputed leftIndex
  have compared := OriginalSharedParent.slot_compare description.row left world description.row right other view leftComputed rightComputed leftIndex rightIndex ordinal
  have named := registry_named program world position input helper known view parsed source (List.mem_of_getElem? found)
  rcases parameters_on_fiber program position world other _ _ source.1 dummy context (compared.1.symm.trans context)
      leftFull rightFull named same with equal | bad
  · exact Or.inl ⟨equal,compared.2⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.GoldContextCoverage
