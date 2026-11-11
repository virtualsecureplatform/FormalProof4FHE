module
public import FormalProof4FHE.HasteBoots.SharedParentInputView
public import FormalProof4FHE.HasteBoots.AllocatedParentPrefix
@[expose] public section

/-! Native caller success recovers the original final registry at the matched
parent-seed boundary. Every original ordinal, duplicate and unused source
entry remains represented by its literal context/root pair. -/
namespace FormalProof4FHE.HasteBoots.OriginalSharedParent
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open OracleProgram (run)
noncomputable section

def input {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B) (world : World) : Input :=
  NativeForkAncestry.seedInput (NativeSharedLookupChild.prepare
    (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities)
      NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext

theorem recover {C S B : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (success : (run (NativeSharedLookupExecution.protocol row registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound result))
    (before : List TranscriptFrame.Frame)
    (bytes : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some sources.val →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit)
    (groupedFits : (NativeLookupMultiplicityWire.grouped proof.multiplicities).length < TranscriptFrame.lengthLimit)
    (flatFits : (NativeLookupMultiplicityWire.flattened proof.multiplicities).length < TranscriptFrame.lengthLimit) :
    ∃ view : SharedParentInputView.View,
      SharedParentInputView.parse (input row registry helper parent requests proof world) = some view ∧
      view.before = before ∧
      (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some view.sources.val ∧
      view.grouped = NativeLookupMultiplicityWire.grouped proof.multiplicities ∧
      view.flat = NativeLookupMultiplicityWire.flattened proof.multiplicities := by
  obtain ⟨sources,computed,registered⟩ := NativeRegistryAncestry.bound_registration row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result success
  let view : SharedParentInputView.View := ⟨before,sources,NativeLookupMultiplicityWire.grouped proof.multiplicities,NativeLookupMultiplicityWire.flattened proof.multiplicities⟩
  refine ⟨view,?_,rfl,computed,rfl,rfl⟩
  unfold input
  rw [registered,SharedParentInputView.native_frames _ before bytes sources proof.multiplicities]
  exact SharedParentInputView.parse_native view (SharedParentInputView.valid view valid (registryFits sources computed) groupedFits flatFits)

/-- Parsing one matched raw parent identifies the full original framed
preflight prefix and final registry, not a set of mentioned sources. -/
theorem compare (left right : SharedParentInputView.View) (leftInput rightInput : Input)
    (leftParsed : SharedParentInputView.parse leftInput = some left)
    (rightParsed : SharedParentInputView.parse rightInput = some right) (same : leftInput = rightInput) : left = right := by
  rw [same] at leftParsed
  exact Option.some.inj (leftParsed.symm.trans rightParsed)

/-- Parent matching identifies the entire recovered view, or retains the
already bounded parent-seed collision event. -/
theorem compare_on_fiber {A : Type} (program : OracleProgram.Program A) (position : ℕ) (world other : World)
    (input leftInput rightInput : Input) (left right : SharedParentInputView.View)
    (leftContext rightContext : NativeRootMessage.Digest)
    (leftKnown : NativeParentLineage.Known world (OracleProgram.runPrefix position program world).run.2 leftInput leftContext)
    (rightKnown : NativeParentLineage.Known other (OracleProgram.runPrefix position program other).run.2 rightInput rightContext)
    (leftParsed : SharedParentInputView.parse leftInput = some left)
    (rightParsed : SharedParentInputView.parse rightInput = some right)
    (leftQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block world leftInput 0 64))
    (rightQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block other rightInput 0 64))
    (same : (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run) :
    left = right ∨ ProgramParentSeedCollision.Bad program world := by
  rcases ParentMatchFixation.known_on_fiber program position world other input leftInput rightInput leftContext rightContext
      leftKnown rightKnown leftQuote rightQuote same with equal | bad
  · exact Or.inl (compare left right leftInput rightInput leftParsed rightParsed equal.symm)
  · exact Or.inr bad

/-- Each original slot is linked to its own native context computation and
root, even when repeated entries also occur at other ordinals. -/
theorem slot {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (world : World)
    (view : SharedParentInputView.View)
    (computed : (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some view.sources.val)
    (index : Fin registry.val.length) :
    ∃ source, view.sources.val[index.val]? = some source ∧
      (run (NativeBrakedownContext.context row registry.val[index.val].parameters) world).run.1 = some source.1 ∧
      source.2 = registry.val[index.val].root :=
  NativeRegistryAncestry.contexts_slot row registry.val world view.sources.val computed index

theorem length {C : Type} (row : RowDescription C) (registry : Vector (Oracle C)) (world : World)
    (view : SharedParentInputView.View)
    (computed : (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some view.sources.val) :
    view.sources.val.length = registry.val.length :=
  (NativeRegistryAncestry.contexts_order row registry.val world view.sources.val computed).length_eq.symm

/-- A common recovered registry binds corresponding original ordinals to
identical context digests and roots across worlds. It does not identify full
parameter preimages merely from equality of the digests. -/
theorem slot_compare {C D : Type} (leftRow : RowDescription C) (leftRegistry : Vector (Oracle C)) (leftWorld : World)
    (rightRow : RowDescription D) (rightRegistry : Vector (Oracle D)) (rightWorld : World)
    (view : SharedParentInputView.View)
    (leftComputed : (run (NativeSharedLookupParent.contexts leftRow leftRegistry.val) leftWorld).run.1 = some view.sources.val)
    (rightComputed : (run (NativeSharedLookupParent.contexts rightRow rightRegistry.val) rightWorld).run.1 = some view.sources.val)
    (leftIndex : Fin leftRegistry.val.length) (rightIndex : Fin rightRegistry.val.length) (ordinal : leftIndex.val = rightIndex.val) :
    (run (NativeBrakedownContext.context leftRow leftRegistry.val[leftIndex.val].parameters) leftWorld).run.1 =
        (run (NativeBrakedownContext.context rightRow rightRegistry.val[rightIndex.val].parameters) rightWorld).run.1 ∧
      leftRegistry.val[leftIndex.val].root = rightRegistry.val[rightIndex.val].root := by
  obtain ⟨left,foundLeft,contextLeft,rootLeft⟩ := slot leftRow leftRegistry leftWorld view leftComputed leftIndex
  obtain ⟨right,foundRight,contextRight,rootRight⟩ := slot rightRow rightRegistry rightWorld view rightComputed rightIndex
  rw [← ordinal] at foundRight
  have same := Option.some.inj (foundLeft.symm.trans foundRight)
  cases same
  exact ⟨contextLeft.trans contextRight.symm,rootLeft.symm.trans rootRight⟩

end
end FormalProof4FHE.HasteBoots.OriginalSharedParent
