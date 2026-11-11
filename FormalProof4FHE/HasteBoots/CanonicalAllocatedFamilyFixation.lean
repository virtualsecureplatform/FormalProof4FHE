module
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedTables
@[expose] public section

/-! Parameter-derived per-object radii preserve the existing complete-family
fixation argument. No common source/helper decoding radius is assumed. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedFamilyFixation
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
open AllocatedFamilyFunctions (Allocation)
open CanonicalAllocatedTables (sourceAt sources helpers sourceRadius helperRadius)
noncomputable section

variable {leftCtx rightCtx : Context (Vector Opening)} {world other : World}
    {leftBody rightBody : NativeSharedLookupBody.Bound}
    (leftAllocation : Allocation leftCtx) (rightAllocation : Allocation rightCtx)
    (left : AllocatedLookupIdentity.NativeOrigin leftCtx world leftBody)
    (right : AllocatedLookupIdentity.NativeOrigin rightCtx other rightBody)

theorem sourceAt_on_fiber {A : Type} (program : Program A) (position : ℕ)
    (registry : leftCtx.registry = rightCtx.registry) (view : SharedParentInputView.View)
    (leftComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row leftCtx.registry.val) world).run.1 = some view.sources.val)
    (rightComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row rightCtx.registry.val) other).run.1 = some view.sources.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (leftIndex : Fin leftCtx.registry.val.length) (rightIndex : Fin rightCtx.registry.val.length) (ordinal : leftIndex.val = rightIndex.val)
    (leftSizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context leftCtx leftIndex).parameters)
    (rightSizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context rightCtx rightIndex).parameters) (dummy : Digest) :
    HEq (sourceAt leftAllocation left dummy (runPrefix position program world).run.2 leftIndex leftSizes)
      (sourceAt rightAllocation right dummy (runPrefix position program other).run.2 rightIndex rightSizes) := by
  have entry := OriginalPackedFamily.entry_eq leftCtx.registry rightCtx.registry registry leftIndex rightIndex ordinal
  have radii : sourceRadius leftCtx leftIndex = sourceRadius rightCtx rightIndex :=
    congrArg (fun entry : NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored => ParameterDecodingRadius.ofParameters entry.parameters) entry
  unfold sourceAt
  rw [← radii]
  exact AllocatedFamilyFunctions.sourceAt_on_fiber leftAllocation rightAllocation left right program position registry view
    leftComputed rightComputed same leftIndex rightIndex ordinal leftSizes rightSizes dummy (sourceRadius leftCtx leftIndex)

theorem sources_on_fiber {A : Type} (program : Program A) (position : ℕ)
    (registry : leftCtx.registry = rightCtx.registry) (requests : leftCtx.requests = rightCtx.requests) (view : SharedParentInputView.View)
    (leftComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row leftCtx.registry.val) world).run.1 = some view.sources.val)
    (rightComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row rightCtx.registry.val) other).run.1 = some view.sources.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (leftIndex : Fin left.ready.jobs.length) (rightIndex : Fin right.ready.jobs.length) (ordinal : leftIndex.val = rightIndex.val)
    (leftJob : LookupExecutionJob.Job left leftIndex) (rightJob : LookupExecutionJob.Job right rightIndex)
    (leftGeometry : AllocatedLookupTables.Geometry left leftIndex leftJob) (rightGeometry : AllocatedLookupTables.Geometry right rightIndex rightJob)
    (dummy : Digest) :
    HEq (sources leftAllocation left leftIndex leftJob leftGeometry dummy (runPrefix position program world).run.2)
      (sources rightAllocation right rightIndex rightJob rightGeometry dummy (runPrefix position program other).run.2) := by
  have request := OriginalJobOrdinal.request left right requests leftIndex rightIndex ordinal
  have dimensions := OriginalJobOrdinal.dimensions left right registry
  apply PackedFamilyReindex.family _ _ (congrArg NativeSharedLookupStatement.Request.columns request) dimensions.1 dimensions.2
  intro leftColumn rightColumn column
  have address := OriginalJobOrdinal.slot_ordinal (congrArg (fun registry => registry.val.length) registry) request leftJob.slots rightJob.slots
    leftColumn rightColumn column
  exact sourceAt_on_fiber leftAllocation rightAllocation left right program position registry view leftComputed rightComputed same
    (leftJob.slots.slot leftColumn) (rightJob.slots.slot rightColumn) address (leftGeometry.source leftColumn) (rightGeometry.source rightColumn) dummy

theorem helpers_on_fiber {A : Type} (program : Program A) (position : ℕ)
    (registry : leftCtx.registry = rightCtx.registry) (parameters : leftCtx.helper = rightCtx.helper)
    (leftFamily : OriginalScalarFamily.Family program position world) (rightFamily : OriginalScalarFamily.Family program position other)
    (leftHelper : leftFamily.parent.helper = leftCtx.helper) (rightHelper : rightFamily.parent.helper = rightCtx.helper)
    (bindings : leftFamily.parent.bindings = rightFamily.parent.bindings)
    (leftRoots : leftFamily.roots = leftCtx.proof.roots) (rightRoots : rightFamily.roots = rightCtx.proof.roots)
    (input : leftFamily.input = rightFamily.input)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (leftIndex : Fin left.ready.jobs.length) (rightIndex : Fin right.ready.jobs.length) (ordinal : leftIndex.val = rightIndex.val)
    (leftJob : LookupExecutionJob.Job left leftIndex) (rightJob : LookupExecutionJob.Job right rightIndex)
    (leftGeometry : AllocatedLookupTables.Geometry left leftIndex leftJob) (rightGeometry : AllocatedLookupTables.Geometry right rightIndex rightJob)
    (dummy : Digest) :
    HEq (helpers leftAllocation left leftIndex leftJob leftGeometry dummy (runPrefix position program world).run.2)
      (helpers rightAllocation right rightIndex rightJob rightGeometry dummy (runPrefix position program other).run.2) := by
  have radii : helperRadius leftCtx = helperRadius rightCtx := congrArg ParameterDecodingRadius.ofParameters parameters
  unfold helpers
  rw [← radii]
  exact AllocatedFamilyFunctions.helpers_on_fiber leftAllocation rightAllocation left right program position registry parameters leftFamily rightFamily
    leftHelper rightHelper bindings leftRoots rightRoots input same leftIndex rightIndex ordinal leftJob rightJob leftGeometry rightGeometry dummy (helperRadius leftCtx)

theorem families_on_fiber {A : Type} (program : Program A) (position : ℕ)
    (leftFamily : OriginalScalarFamily.Family program position world) (rightFamily : OriginalScalarFamily.Family program position other)
    (leftRegistry : leftFamily.parent.registry = leftCtx.registry) (rightRegistry : rightFamily.parent.registry = rightCtx.registry)
    (leftHelper : leftFamily.parent.helper = leftCtx.helper) (rightHelper : rightFamily.parent.helper = rightCtx.helper)
    (leftRequests : leftFamily.parent.requests = leftCtx.requests) (rightRequests : rightFamily.parent.requests = rightCtx.requests)
    (leftRoots : leftFamily.roots = leftCtx.proof.roots) (rightRoots : rightFamily.roots = rightCtx.proof.roots)
    (input : leftFamily.input = rightFamily.input)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (leftIndex : Fin left.ready.jobs.length) (rightIndex : Fin right.ready.jobs.length) (ordinal : leftIndex.val = rightIndex.val)
    (leftJob : LookupExecutionJob.Job left leftIndex) (rightJob : LookupExecutionJob.Job right rightIndex)
    (leftGeometry : AllocatedLookupTables.Geometry left leftIndex leftJob) (rightGeometry : AllocatedLookupTables.Geometry right rightIndex rightJob)
    (dummy : Digest) :
    (HEq (sources leftAllocation left leftIndex leftJob leftGeometry dummy (runPrefix position program world).run.2)
        (sources rightAllocation right rightIndex rightJob rightGeometry dummy (runPrefix position program other).run.2) ∧
      HEq (helpers leftAllocation left leftIndex leftJob leftGeometry dummy (runPrefix position program world).run.2)
        (helpers rightAllocation right rightIndex rightJob rightGeometry dummy (runPrefix position program other).run.2)) ∨
      ProgramParentSeedCollision.Bad program world ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
        ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other := by
  rcases OriginalScalarFamily.compare program position world other leftFamily rightFamily dummy input same with ⟨agree,_⟩ | bad
  · have registry := leftRegistry.symm.trans (agree.1.trans rightRegistry)
    have parameters := leftHelper.symm.trans (agree.2.1.trans rightHelper)
    have requests := leftRequests.symm.trans (agree.2.2.1.trans rightRequests)
    have leftComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row leftCtx.registry.val) world).run.1 =
        some leftFamily.parent.parent.sources.val := by
      rw [← leftRegistry]
      exact leftFamily.parent.computed
    have rightComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row rightCtx.registry.val) other).run.1 =
        some leftFamily.parent.parent.sources.val := by
      rw [← rightRegistry,agree.2.2.2.1]
      exact rightFamily.parent.computed
    exact Or.inl ⟨sources_on_fiber leftAllocation rightAllocation left right program position registry requests _ leftComputed rightComputed same
      leftIndex rightIndex ordinal leftJob rightJob leftGeometry rightGeometry dummy,
      helpers_on_fiber leftAllocation rightAllocation left right program position registry parameters leftFamily rightFamily leftHelper rightHelper
        agree.2.2.2.2 leftRoots rightRoots input same leftIndex rightIndex ordinal leftJob rightJob leftGeometry rightGeometry dummy⟩
  · exact Or.inr bad


end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedFamilyFixation
