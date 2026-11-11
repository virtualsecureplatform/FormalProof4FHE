module
public import FormalProof4FHE.HasteBoots.PackedFamilyReindex
@[expose] public section

/-! Congruence of the actual original allocated source/helper functions.
Allocation records carry original constructor provenance and merely abbreviate
arguments of AllocatedLookupTables; they do not define replacement tables. -/
namespace FormalProof4FHE.HasteBoots.AllocatedFamilyFunctions
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
noncomputable section

structure Allocation (ctx : Context (Vector Opening)) where
  entries : List Entry
  reachable : NativeGoldParameterStore.Reachable entries
  helperHandle : ℕ
  references : Vector Reference
  template : Context (Vector Opening)
  assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}

def sourceAt (allocation : Allocation ctx) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (dummy : Digest) (history : List Observation) (radius : ℕ) (slot : Fin ctx.registry.val.length)
    (sizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters) :=
  AllocatedLookupTables.sourceAt origin allocation.entries allocation.reachable allocation.helperHandle allocation.references allocation.template
    allocation.assembled dummy history radius slot sizes

def sources (allocation : Allocation ctx) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation) (radius : ℕ) :=
  AllocatedLookupTables.sources origin index job allocation.entries allocation.reachable allocation.helperHandle allocation.references allocation.template
    allocation.assembled geometry dummy history radius

def helpers (allocation : Allocation ctx) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation) (radius : ℕ) :=
  AllocatedLookupTables.helpers origin index job allocation.entries allocation.reachable allocation.helperHandle allocation.references allocation.template
    allocation.assembled geometry dummy history radius

variable {leftCtx rightCtx : Context (Vector Opening)} {other : World}
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
    (rightSizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context rightCtx rightIndex).parameters) (dummy : Digest) (radius : ℕ) :
    HEq (sourceAt leftAllocation left dummy (runPrefix position program world).run.2 radius leftIndex leftSizes)
      (sourceAt rightAllocation right dummy (runPrefix position program other).run.2 radius rightIndex rightSizes) := by
  have dimensions := OriginalJobOrdinal.dimensions left right registry
  have entries := OriginalPackedFamily.entry_eq leftCtx.registry rightCtx.registry registry leftIndex rightIndex ordinal
  have compared := OriginalSharedParent.slot_compare NativeGoldBlockCode.description.row leftCtx.registry world NativeGoldBlockCode.description.row rightCtx.registry other
    view leftComputed rightComputed leftIndex rightIndex ordinal
  rw [GoldContextCollision.context_run,GoldContextCollision.context_run] at compared
  have parameters : (RegistryPublicSource.context leftCtx leftIndex).parameters = (RegistryPublicSource.context rightCtx rightIndex).parameters :=
    congrArg NativeSharedLookupParent.Oracle.parameters entries
  let leftCapacity := (AllocatedScalarSource.origin leftAllocation.entries leftAllocation.reachable leftAllocation.helperHandle leftAllocation.references
    leftAllocation.template leftCtx leftAllocation.assembled leftIndex).capacityAt _ rfl
  let rightCapacity := (AllocatedScalarSource.origin rightAllocation.entries rightAllocation.reachable rightAllocation.helperHandle rightAllocation.references
    rightAllocation.template rightCtx rightAllocation.assembled rightIndex).capacityAt _ rfl
  have packed := PackedContextCongruence.packed (RegistryPublicSource.context leftCtx leftIndex) (RegistryPublicSource.context rightCtx rightIndex)
    parameters dummy _ _ _ _ (Option.some.inj compared.1) compared.2 _ _
    (congrArg Prod.snd (ParentFactorFiber.old_packet (runPrefix position program) world other same)).symm radius
    leftCapacity rightCapacity leftSizes rightSizes (left.registry_dimensions leftIndex).2 (right.registry_dimensions rightIndex).2
  exact PackedFamilyReindex.table _ _ (left.registry_dimensions leftIndex).1 (right.registry_dimensions rightIndex).1 dimensions.1 dimensions.2 packed

theorem sources_on_fiber {A : Type} (program : Program A) (position : ℕ)
    (registry : leftCtx.registry = rightCtx.registry) (requests : leftCtx.requests = rightCtx.requests) (view : SharedParentInputView.View)
    (leftComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row leftCtx.registry.val) world).run.1 = some view.sources.val)
    (rightComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row rightCtx.registry.val) other).run.1 = some view.sources.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (leftIndex : Fin left.ready.jobs.length) (rightIndex : Fin right.ready.jobs.length) (ordinal : leftIndex.val = rightIndex.val)
    (leftJob : LookupExecutionJob.Job left leftIndex) (rightJob : LookupExecutionJob.Job right rightIndex)
    (leftGeometry : AllocatedLookupTables.Geometry left leftIndex leftJob) (rightGeometry : AllocatedLookupTables.Geometry right rightIndex rightJob)
    (dummy : Digest) (radius : ℕ) :
    HEq (sources leftAllocation left leftIndex leftJob leftGeometry dummy (runPrefix position program world).run.2 radius)
      (sources rightAllocation right rightIndex rightJob rightGeometry dummy (runPrefix position program other).run.2 radius) := by
  have request := OriginalJobOrdinal.request left right requests leftIndex rightIndex ordinal
  have dimensions := OriginalJobOrdinal.dimensions left right registry
  apply PackedFamilyReindex.family _ _ (congrArg NativeSharedLookupStatement.Request.columns request) dimensions.1 dimensions.2
  intro leftColumn rightColumn column
  have address := OriginalJobOrdinal.slot_ordinal (congrArg (fun registry => registry.val.length) registry) request leftJob.slots rightJob.slots
    leftColumn rightColumn column
  exact sourceAt_on_fiber leftAllocation rightAllocation left right program position registry view leftComputed rightComputed same
    (leftJob.slots.slot leftColumn) (rightJob.slots.slot rightColumn) address (leftGeometry.source leftColumn) (rightGeometry.source rightColumn) dummy radius


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
    (dummy : Digest) (radius : ℕ) :
    HEq (helpers leftAllocation left leftIndex leftJob leftGeometry dummy (runPrefix position program world).run.2 radius)
      (helpers rightAllocation right rightIndex rightJob rightGeometry dummy (runPrefix position program other).run.2 radius) := by
  have dimensions := OriginalJobOrdinal.dimensions left right registry
  have helperPadding : AllocatedLookupTables.helperPadding (ctx := leftCtx) = AllocatedLookupTables.helperPadding (ctx := rightCtx) :=
    congrArg (fun parameters => parameters.width.val-3) parameters
  have rootVector : leftCtx.proof.roots = rightCtx.proof.roots :=
    leftRoots.symm.trans ((OriginalHelperRoots.compare leftFamily.input rightFamily.input leftFamily.roots rightFamily.roots
      leftFamily.parsed rightFamily.parsed input).trans rightRoots)
  have root := OriginalPackedFamily.entry_eq leftCtx.proof.roots rightCtx.proof.roots rootVector
    (AllocatedLookupTables.helperIndex left leftIndex) (AllocatedLookupTables.helperIndex right rightIndex) ordinal
  have related : List.Forall₂ (ParentBindingTrace.ForRequest NativeGoldBlockCode.description.row rightFamily.parent.registry.val rightFamily.parent.helper other)
      rightFamily.parent.requests.val leftFamily.parent.bindings.bindings := by
    rw [bindings]
    exact rightFamily.parent.related
  have contexts := CanonicalHelperFiber.helper_contexts leftFamily.parent.registry.val rightFamily.parent.registry.val leftFamily.parent.helper rightFamily.parent.helper
    world other leftFamily.parent.requests.val rightFamily.parent.requests.val leftFamily.parent.bindings.bindings leftFamily.parent.nonempty leftFamily.parent.related related
  rw [GoldContextCollision.context_run,GoldContextCollision.context_run] at contexts
  have digest : InputIndexedOracle.sha512 world (GoldContextInput.bytes leftCtx.helper) = InputIndexedOracle.sha512 other (GoldContextInput.bytes rightCtx.helper) := by
    simpa only [leftHelper,rightHelper] using Option.some.inj contexts
  let leftReference := AllocatedScalarHelper.reference leftAllocation.entries leftAllocation.reachable leftAllocation.helperHandle leftAllocation.references
    leftAllocation.template leftCtx leftAllocation.assembled (AllocatedLookupTables.helperIndex left leftIndex)
  let rightReference := AllocatedScalarHelper.reference rightAllocation.entries rightAllocation.reachable rightAllocation.helperHandle rightAllocation.references
    rightAllocation.template rightCtx rightAllocation.assembled (AllocatedLookupTables.helperIndex right rightIndex)
  have leftParameters : leftReference.parameters = leftCtx.helper :=
    (AllocatedScalarHelper.entry_spec leftAllocation.entries leftAllocation.reachable leftAllocation.helperHandle leftAllocation.references
      leftAllocation.template leftCtx leftAllocation.assembled).2.2.symm
  have rightParameters : rightReference.parameters = rightCtx.helper :=
    (AllocatedScalarHelper.entry_spec rightAllocation.entries rightAllocation.reachable rightAllocation.helperHandle rightAllocation.references
      rightAllocation.template rightCtx rightAllocation.assembled).2.2.symm
  let leftCapacity := (AllocatedScalarHelper.origin leftAllocation.entries leftAllocation.reachable leftAllocation.helperHandle leftAllocation.references
    leftAllocation.template leftCtx leftAllocation.assembled (AllocatedLookupTables.helperIndex left leftIndex)).capacityAt _ rfl
  let rightCapacity := (AllocatedScalarHelper.origin rightAllocation.entries rightAllocation.reachable rightAllocation.helperHandle rightAllocation.references
    rightAllocation.template rightCtx rightAllocation.assembled (AllocatedLookupTables.helperIndex right rightIndex)).capacityAt _ rfl
  have leftSizes : GoldHistorySourceTable.Geometry leftReference.parameters := by rw [leftParameters]; exact leftGeometry.helper
  have rightSizes : GoldHistorySourceTable.Geometry rightReference.parameters := by rw [rightParameters]; exact rightGeometry.helper
  have leftWidth : leftReference.parameters.width.val = 3+AllocatedLookupTables.helperPadding (ctx := leftCtx) :=
    (congrArg (fun parameters => parameters.width.val) leftParameters).trans (AllocatedLookupTables.helperWidth left)
  have rightWidth : rightReference.parameters.width.val = 3+AllocatedLookupTables.helperPadding (ctx := rightCtx) :=
    (congrArg (fun parameters => parameters.width.val) rightParameters).trans (AllocatedLookupTables.helperWidth right)
  have leftDimension : leftReference.parameters.numVariables.val = NativeScalarQueryShape.laneBits (3+left.padding)+leftBody.sourceVariables :=
    (congrArg (fun parameters => parameters.numVariables.val) leftParameters).trans ((congrArg Fin.val left.helper_dimensions.1).trans leftJob.view.dimension)
  have rightDimension : rightReference.parameters.numVariables.val = NativeScalarQueryShape.laneBits (3+right.padding)+rightBody.sourceVariables :=
    (congrArg (fun parameters => parameters.numVariables.val) rightParameters).trans ((congrArg Fin.val right.helper_dimensions.1).trans rightJob.view.dimension)
  have packed := PackedContextCongruence.packed leftReference rightReference (leftParameters.trans (parameters.trans rightParameters.symm)) dummy _ _ _ _ digest root _ _
    (congrArg Prod.snd (ParentFactorFiber.old_packet (runPrefix position program) world other same)).symm radius
    leftCapacity rightCapacity leftSizes rightSizes leftWidth rightWidth
  exact PackedFamilyReindex.table _ _ leftDimension rightDimension (by rw [dimensions.1,dimensions.2]) helperPadding packed


/-- The whole selected native job family is coupled in one branch. Source
addresses, row casts and the helper root are derived from original ordinal
data, with one shared exception alternative for both functions. -/
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
    (dummy : Digest) (radius : ℕ) :
    (HEq (sources leftAllocation left leftIndex leftJob leftGeometry dummy (runPrefix position program world).run.2 radius)
        (sources rightAllocation right rightIndex rightJob rightGeometry dummy (runPrefix position program other).run.2 radius) ∧
      HEq (helpers leftAllocation left leftIndex leftJob leftGeometry dummy (runPrefix position program world).run.2 radius)
        (helpers rightAllocation right rightIndex rightJob rightGeometry dummy (runPrefix position program other).run.2 radius)) ∨
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
      leftIndex rightIndex ordinal leftJob rightJob leftGeometry rightGeometry dummy radius,
      helpers_on_fiber leftAllocation rightAllocation left right program position registry parameters leftFamily rightFamily leftHelper rightHelper
        agree.2.2.2.2 leftRoots rightRoots input same leftIndex rightIndex ordinal leftJob rightJob leftGeometry rightGeometry dummy radius⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.AllocatedFamilyFunctions
