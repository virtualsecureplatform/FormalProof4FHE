module
import all FormalProof4FHE.HasteBoots.AllocatedScalarSource
import all FormalProof4FHE.HasteBoots.AllocatedScalarHelper
import all FormalProof4FHETest.HasteBootsSourceLogIdentitySmoke
import all FormalProof4FHETest.HasteBootsAllocatedLookupSmoke
import all FormalProof4FHETest.HasteBootsRealizedAncestrySmoke

namespace FormalProof4FHE.HasteBoots.SourceFrontierSmoke
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input World)
open HasteBootsBatchMeaningSmoke (root usize)
open SourceLogIdentitySmoke (batch firstInput batchParsed before original)
noncomputable section

/-- This fixture's key is genuinely new at the pending field read. -/
example : (batch.data.context,batch.data.root) ∉
    (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding root before).1.1.frozen := by decide +kernel

theorem resolved : (batch.data.context,batch.data.root) ∈ NativeParentLedger.resolve
    (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding root before).1.1
    (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding root before).1.2 firstInput :=
  NativeGoldBatchFieldExposure.parsed_resolved firstInput batch batchParsed _ _

/-- Executable lookup agrees with causal selection even for a new key. -/
example : SourceHistoryOwnerLog.selected before batch.data.context batch.data.root =
    NativeRootFamilySourceSelection.select (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding root before)
      (batch.data.context,batch.data.root) :=
  SourceFrontierStability.selected_eq_native root before batch.data.context batch.data.root

/-- Arbitrary response bytes, offsets, and future hashes preserve the pre-read
owner; no prior snapshot or future-log witness is supplied. -/
example (offset : ℕ) (values : Input) (positive : values ≠ []) (later : List Observation) :
    SourceHistoryOwnerLog.selected (before ++ .output firstInput offset values :: later) batch.data.context batch.data.root =
      SourceHistoryOwnerLog.selected before batch.data.context batch.data.root :=
  SourceFrontierStability.selected_read root before later batch.data.context batch.data.root firstInput offset values positive resolved

example (later : List Observation) :
    SourceHistoryOwnerLog.selected (before ++ .output firstInput 99 [255,128,1] :: later) batch.data.context batch.data.root =
      SourceHistoryOwnerLog.selected (before ++ .output firstInput 7 [0] :: []) batch.data.context batch.data.root := by
  rw [SourceFrontierStability.selected_read root before later batch.data.context batch.data.root firstInput 99 [255,128,1] (by decide) resolved,
    SourceFrontierStability.selected_read root before [] batch.data.context batch.data.root firstInput 7 [0] (by decide) resolved]

/-- All 64 supported heights share the exact same pre-read owner. -/
example (height : NativeMerkleShapeFamily.Height) (later : List Observation) :
    ⟨(batch.data.context,height),⟨batch.data.root,SourceHistoryOwnerLog.selected before batch.data.context batch.data.root⟩⟩ ∈
      (NativeGoldBatchFamilyAvailability.reconstructed root (before ++ .output firstInput 99 [0] :: later)).checkpoints.checkpoints :=
  SourceFrontierStability.read_snapshot root before later batch.data.context batch.data.root firstInput 99 [0] (by decide) resolved height

/-- Zero-byte outputs cannot freeze a new source key. -/
example : (batch.data.context,batch.data.root) ∉
    (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding root
      (before ++ [.output firstInput 0 []])).1.1.frozen := by
  change (batch.data.context,batch.data.root) ∉
    (NativeParentLedger.discover (NativeParentLedger.discover NativeParentLedger.empty NativeShakeCache.empty [10]) NativeShakeCache.empty firstInput).frozen
  rw [NativeParentLedger.discover_frozen,NativeParentLedger.discover_frozen]
  exact Finset.notMem_empty _

/-- Without a positive read, the unrecorded fallback can still change. -/
example : (SourceHistoryOwnerLog.selected before batch.data.context batch.data.root).length = 1 ∧
    (SourceHistoryOwnerLog.selected (before ++ [.output firstInput 0 [],.hash [11] (List.ofFn root)]) batch.data.context batch.data.root).length = 2 := by decide +kernel

/-- Packing width four is independent of the original code block width. -/
def reference : NativeGoldBatchPcsProgram.Context :=
  {HasteBootsBatchMeaningSmoke.ctx with parameters.width := usize 4}
theorem capacity : GoldCommonSourceTable.Capacity reference.parameters := by decide +kernel
theorem geometry : GoldHistorySourceTable.Geometry reference.parameters := by decide +kernel

example (later : List Observation) :
    ScalarPublicSourceModel.publicScalar reference root batch.data.context batch.data.root
        (before ++ .output firstInput 0 [0] :: later) 0 capacity geometry (padding := 1) (c := 2) rfl rfl =
      ScalarPublicSourceModel.publicScalar reference root batch.data.context batch.data.root before 0 capacity geometry (padding := 1) (c := 2) rfl rfl :=
  SourceFrontierStability.scalar_read reference root batch.data.context batch.data.root before later 0 capacity geometry (padding := 1) (c := 2) rfl rfl
    firstInput 0 [0] (by decide) resolved

/-- Position-indexed transfer retains the original mixed-history prefix. -/
example (later : List Observation) :
    ScalarPublicSourceModel.publicScalar reference root batch.data.context batch.data.root
        (before ++ .output firstInput 0 [0] :: later) 0 capacity geometry (padding := 1) (c := 2) rfl rfl =
      ScalarPublicSourceModel.publicScalar reference root batch.data.context batch.data.root
        ((before ++ .output firstInput 0 [0] :: later).take 1) 0 capacity geometry (padding := 1) (c := 2) rfl rfl := by
  apply SourceFrontierStability.scalar_read_at reference root batch.data.context batch.data.root _ 0 capacity geometry (padding := 1) (c := 2) rfl rfl
    1 firstInput 0 [0] (by decide) (by rfl)
  exact resolved

/-- The source reaches a real descendant read through native ancestry. The
existing seed-order risk is discharged by the fixture's proved chronology. -/
example : ScalarPublicSourceModel.publicScalar reference root HasteBootsParentStateSmoke.context
      HasteBootsParentStateSmoke.root HasteBootsRealizedAncestrySmoke.log 0 capacity geometry (padding := 1) (c := 2) rfl rfl =
    ScalarPublicSourceModel.publicScalar reference root HasteBootsParentStateSmoke.context
      HasteBootsParentStateSmoke.root (HasteBootsRealizedAncestrySmoke.log.take 3) 0 capacity geometry (padding := 1) (c := 2) rfl rfl := by
  obtain ⟨index,ancestry⟩ := HasteBootsRealizedAncestrySmoke.realized (.source (HasteBootsParentStateSmoke.context,HasteBootsParentStateSmoke.root))
    (HasteBootsSourceExposureCoverageSmoke.direct_source _ (by simp [HasteBootsSourceExposureCoverageSmoke.sources]))
  have stable := SourceFrontierStability.ancestry_scalar_read HasteBootsRealizedAncestrySmoke.step 4 0
    HasteBootsRealizedAncestrySmoke.modelWorld reference root HasteBootsParentStateSmoke.context HasteBootsParentStateSmoke.root
    0 capacity geometry (padding := 1) (c := 2) rfl rfl HasteBootsLifetimeLineageSmoke.descendantInput index (.source (HasteBootsParentStateSmoke.context,HasteBootsParentStateSmoke.root)) ancestry
    3 HasteBootsRealizedAncestrySmoke.leafInput 64 HasteBootsRealizedAncestrySmoke.leafValues HasteBootsRealizedAncestrySmoke.leaf_nonempty
    HasteBootsRealizedAncestrySmoke.positioned HasteBootsRealizedAncestrySmoke.leaf_quote_actual (List.mem_singleton_self _)
  exact stable.resolve_right HasteBootsRealizedAncestrySmoke.safe

/-- The same pre-read guarantee applies to original helper roots committed in
a descendant input, with actual helper ancestry rather than source ancestry. -/
example : ScalarPublicSourceModel.publicScalar reference root HasteBootsParentStateSmoke.context
      HasteBootsRealizedAncestrySmoke.helperRoot HasteBootsRealizedAncestrySmoke.log 0 capacity geometry (padding := 1) (c := 2) rfl rfl =
    ScalarPublicSourceModel.publicScalar reference root HasteBootsParentStateSmoke.context
      HasteBootsRealizedAncestrySmoke.helperRoot (HasteBootsRealizedAncestrySmoke.log.take 3) 0 capacity geometry (padding := 1) (c := 2) rfl rfl := by
  obtain ⟨index,ancestry⟩ := HasteBootsRealizedAncestrySmoke.realized (.helper HasteBootsParentStateSmoke.context)
    HasteBootsRealizedAncestrySmoke.direct_helper
  have stable := SourceFrontierStability.ancestry_scalar_read HasteBootsRealizedAncestrySmoke.step 4 0
    HasteBootsRealizedAncestrySmoke.modelWorld reference root HasteBootsParentStateSmoke.context HasteBootsRealizedAncestrySmoke.helperRoot
    0 capacity geometry (padding := 1) (c := 2) rfl rfl HasteBootsLifetimeLineageSmoke.descendantInput index (.helper HasteBootsParentStateSmoke.context) ancestry
    3 HasteBootsRealizedAncestrySmoke.leafInput 64 HasteBootsRealizedAncestrySmoke.leafValues HasteBootsRealizedAncestrySmoke.leaf_nonempty
    HasteBootsRealizedAncestrySmoke.positioned HasteBootsRealizedAncestrySmoke.leaf_quote_actual HasteBootsRealizedAncestrySmoke.helper_member
  exact stable.resolve_right HasteBootsRealizedAncestrySmoke.safe

section Allocated
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldHelperVerification (Context)
open NativeGoldBatchOpening (Opening)
variable (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (handle : ℕ) (references : Vector Reference) (template ctx : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries handle references template = some ctx)
    (slot : Fin ctx.registry.val.length)

/-- The original store handle, full parameters and reference root are derived
from assembly; a caller does not provide separate association certificates. -/
example : ∃ (reference : Reference) (entry : Entry), references.val[slot.val]? = some reference ∧
    entries[reference.handle]? = some entry ∧ NativeGoldParameterStore.GoodEntry entry ∧
    ctx.registry.val.get slot = ⟨entry.initialized.parameters,reference.root⟩ := by
  obtain ⟨reference,referenceAt,entryAt,good,oracle⟩ :=
    AllocatedScalarSource.original_entry entries reachable handle references template ctx assembled slot
  exact ⟨reference,_,referenceAt,entryAt,good,oracle⟩

/-- The new scalar source retains the actual original constructor request and
config even when distinct requests happen to return identical raw code. -/
example : (AllocatedScalarSource.origin entries reachable handle references template ctx assembled slot).request =
    (AllocatedCodeOrigin.registryEntry entries reachable references ctx.registry
      (AllocatedLookupContext.assemble_spec entries handle references template ctx assembled).1 slot).request :=
  (AllocatedScalarSource.origin_data entries reachable handle references template ctx assembled slot).1

/-- The observed original registry initializer determines the public full key,
including slots unused by the later opening batch. -/
example (parent : NativeTranscript.Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (registered : (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row ctx.registry parent) world).run.1 = some initialized) :
    initialized.sources.val[slot.val]? =
      some (InputIndexedOracle.sha512 world (GoldContextInput.bytes (ctx.registry.val.get slot).parameters),(ctx.registry.val.get slot).root) :=
  (AllocatedScalarSource.registered_key ctx slot parent world initialized registered).1

example (parent : NativeTranscript.Transcript) (world : World) (initialized : NativeSourceRegistry.Initialized)
    (registered : (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row ctx.registry parent) world).run.1 = some initialized) :
    ∃ (reference : Reference) (entry : Entry), references.val[slot.val]? = some reference ∧
      entries[reference.handle]? = some entry ∧ NativeGoldParameterStore.GoodEntry entry ∧
      initialized.sources.val[slot.val]? = some (InputIndexedOracle.sha512 world (GoldContextInput.bytes entry.initialized.parameters),reference.root) := by
  obtain ⟨reference,referenceAt,entryAt,good,key,_⟩ :=
    AllocatedScalarSource.allocated_registered_key entries reachable handle references template ctx assembled slot parent world initialized registered
  exact ⟨reference,_,referenceAt,entryAt,good,key⟩

/-- The same original factor is fixed before the current positive answer. -/
example (dummy context : Digest) (earlier later : List Observation) (radius : ℕ)
    (sizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters)
    {padding c : ℕ} (width : (RegistryPublicSource.context ctx slot).parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (found : (context,(ctx.registry.val.get slot).root) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy earlier).1.1
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy earlier).1.2 input) :
    AllocatedScalarSource.factor entries reachable handle references template ctx assembled slot dummy context
        (earlier ++ .output input offset values :: later) radius sizes width shape =
      AllocatedScalarSource.factor entries reachable handle references template ctx assembled slot dummy context earlier radius sizes width shape :=
  AllocatedScalarSource.read entries reachable handle references template ctx assembled slot dummy context earlier later radius sizes width shape input offset values positive found

/-- Helper extraction uses the same store's actually borrowed object. -/
example : ∃ entry : Entry, entries[handle]? = some entry ∧ NativeGoldParameterStore.GoodEntry entry ∧ ctx.helper = entry.initialized.parameters :=
  ⟨_,AllocatedScalarHelper.entry_spec entries reachable handle references template ctx assembled⟩

/-- Original helper root ordinals survive independently of later call payloads. -/
example (index : Fin ctx.proof.roots.val.length) :
    (AllocatedScalarHelper.reference entries reachable handle references template ctx assembled index).root = ctx.proof.roots.val.get index ∧
    (AllocatedScalarHelper.reference entries reachable handle references template ctx assembled index).parameters = ctx.helper := by
  exact ⟨rfl,(AllocatedScalarHelper.entry_spec entries reachable handle references template ctx assembled).2.2.symm⟩

example (index : Fin ctx.proof.roots.val.length) (dummy context : Digest) (earlier later : List Observation) (radius : ℕ)
    (sizes : GoldHistorySourceTable.Geometry (AllocatedScalarHelper.reference entries reachable handle references template ctx assembled index).parameters)
    {padding : ℕ} (width : (AllocatedScalarHelper.reference entries reachable handle references template ctx assembled index).parameters.width.val = 3+padding)
    (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (found : (context,ctx.proof.roots.val.get index) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy earlier).1.1
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy earlier).1.2 input) :
    AllocatedScalarHelper.factor entries reachable handle references template ctx assembled index dummy context
        (earlier ++ .output input offset values :: later) radius sizes width =
      AllocatedScalarHelper.factor entries reachable handle references template ctx assembled index dummy context earlier radius sizes width :=
  AllocatedScalarHelper.read entries reachable handle references template ctx assembled index dummy context earlier later radius sizes width input offset values positive found

end Allocated
end
end FormalProof4FHE.HasteBoots.SourceFrontierSmoke
