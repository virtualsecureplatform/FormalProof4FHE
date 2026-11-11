module
public import FormalProof4FHE.HasteBoots.PackedContextCongruence
public import FormalProof4FHE.HasteBoots.AllocatedContextCoverage
@[expose] public section

/-! Original family data recovered from an actual native caller. The parser
fields retain exact request/binding order; provenance and complete native
context observations are separate proof fields, never inferred from syntax. -/
namespace FormalProof4FHE.HasteBoots.OriginalParentFamily
open InputIndexedOracle (Input World)
open NativeGoldBlockCode (Stored description)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (Parameters)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeRootMessage (Digest)
open OracleProgram (Program run runPrefix)
noncomputable section

structure Family {A : Type} (program : Program A) (position : ℕ) (world : World) where
  registry : Vector (Oracle Stored)
  helper : Parameters Stored
  requests : Vector Request
  input : Input
  parent : SharedParentInputView.View
  bindings : ParentBindingsView.View
  known : NativeParentLineage.Known world (runPrefix position program world).run.2 input
    (InputIndexedOracle.sha512 world (GoldContextInput.bytes helper))
  parsed : SharedParentInputView.parse input = some parent
  bindingParsed : ParentBindingsView.parse (TranscriptFrame.encodeMany parent.before) = some bindings
  computed : (run (NativeSharedLookupParent.contexts description.row registry.val) world).run.1 = some parent.sources.val
  requests_eq : bindings.requests = requests
  related : List.Forall₂ (ParentBindingTrace.ForRequest description.row registry.val helper world) requests.val bindings.bindings
  nonempty : bindings.bindings ≠ []
  helperFull : (run (NativeBrakedownContext.context description.row helper) world).run.2.Sublist (run program world).run.2
  registryFull : ∀ slot : Fin registry.val.length,
    (run (NativeBrakedownContext.context description.row (registry.val.get slot).parameters) world).run.2.Sublist (run program world).run.2

/-- Every component of the original family is compared at once. The two
late-context alternatives are retained in their own worlds, alongside the
one reference parent-seed and shared root/hash exceptions. -/
theorem compare {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Family program position world) (right : Family program position other) (input : Input) (dummy : Digest)
    (leftQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block world left.input 0 64))
    (rightQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block other right.input 0 64))
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    (left.registry = right.registry ∧ left.helper = right.helper ∧ left.requests = right.requests ∧
      left.parent = right.parent ∧ left.bindings = right.bindings) ∨
      ProgramParentSeedCollision.Bad program world ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
        ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other := by
  rcases SharedParentBindingsData.compare_on_fiber program position world other input left.input right.input left.parent right.parent _ _
      left.known right.known left.parsed right.parsed leftQuote rightQuote left.bindings right.bindings left.bindingParsed right.bindingParsed same with matched | bad
  · obtain ⟨parents,bindings⟩ := matched
    have rightComputed : (run (NativeSharedLookupParent.contexts description.row right.registry.val) other).run.1 = some left.parent.sources.val := by
      rw [parents]
      exact right.computed
    rcases OriginalRegistryFiber.registry program position world other left.registry right.registry left.input _ dummy left.parent left.known left.parsed
        left.computed rightComputed left.registryFull right.registryFull same with registry | bad
    · have related : List.Forall₂ (ParentBindingTrace.ForRequest description.row right.registry.val right.helper other) right.requests.val left.bindings.bindings := by
        rw [bindings]
        exact right.related
      rcases CanonicalHelperFiber.parameters_covered program position world other left.registry.val right.registry.val left.helper right.helper
          left.requests.val right.requests.val left.bindings.bindings left.nonempty left.related related left.input right.input left.known right.known
          left.helperFull right.helperFull dummy same with helper | bad
      · exact Or.inl ⟨registry,helper,left.requests_eq.symm.trans ((congrArg ParentBindingsView.View.requests bindings).trans right.requests_eq),parents,bindings⟩
      · exact Or.inr (Or.inr bad)
    · exact Or.inr (Or.inr bad)
  · exact Or.inr (Or.inl bad)

end
end FormalProof4FHE.HasteBoots.OriginalParentFamily
