module
public import FormalProof4FHE.HasteBoots.AllocatedLookupContext
public import FormalProof4FHE.HasteBoots.RegistryPublicSource
public import FormalProof4FHE.HasteBoots.SourceFrontierStability
public import FormalProof4FHE.HasteBoots.NativeRegistryContextTrace
public import FormalProof4FHE.HasteBoots.GoldContextCollision
@[expose] public section

/-! Scalar factors from the original registry object assembled from the same
immutable store as the helper. Constructor provenance and root association
are derived from that assembly; neither is selected by a later PCS response.
This is a logical allocation adapter, not physical pointer refinement. -/
namespace FormalProof4FHE.HasteBoots.AllocatedScalarSource
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input)
noncomputable section

variable (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template ctx : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (slot : Fin ctx.registry.val.length)

/-- The full original registry slot, not a synthesized PCS call record. -/
def origin : CacheBackedCodeOrigin.Origin (RegistryPublicSource.context ctx slot) :=
  RegistryPublicSource.origin ctx entries reachable references
    (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 slot

/-- The exact allocated source object and root survive to the scalar factor. -/
theorem original_entry : ∃ reference,
    references.val[slot.val]? = some reference ∧
    entries[reference.handle]? = some (AllocatedCodeOrigin.registryEntry entries reachable references ctx.registry
      (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 slot) ∧
    NativeGoldParameterStore.GoodEntry (AllocatedCodeOrigin.registryEntry entries reachable references ctx.registry
      (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 slot) ∧
    ctx.registry.val.get slot =
      ⟨(AllocatedCodeOrigin.registryEntry entries reachable references ctx.registry
        (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 slot).initialized.parameters,reference.root⟩ :=
  AllocatedCodeOrigin.registry_entry_spec entries reachable references ctx.registry
    (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 slot

theorem origin_data :
    (origin entries reachable helperHandle references template ctx assembled slot).request =
      (AllocatedCodeOrigin.registryEntry entries reachable references ctx.registry
        (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 slot).request ∧
    (origin entries reachable helperHandle references template ctx assembled slot).config =
      (AllocatedCodeOrigin.registryEntry entries reachable references ctx.registry
        (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 slot).config := ⟨rfl,rfl⟩

/-- Only the earlier public history and context digest are variable inputs.
The root, complete parameters, constructor and packing geometry are original. -/
def factor (dummy context : Digest) (history : List Observation) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters)
    {padding c : ℕ} (width : (RegistryPublicSource.context ctx slot).parameters.width.val = 3+padding) (shape : 3+padding = 2^c) :=
  ScalarPublicSourceModel.publicScalar (RegistryPublicSource.context ctx slot) dummy context (ctx.registry.val.get slot).root
    history radius ((origin entries reachable helperHandle references template ctx assembled slot).capacityAt _ rfl) geometry width shape

/-- The literal scalar query is for this same original packed source. Unused
padding lanes are retained, and packing width is independent of code width. -/
theorem query (dummy context : Digest) (history : List Observation) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters)
    {padding c : ℕ} (width : (RegistryPublicSource.context ctx slot).parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (point : Fin (c+(RegistryPublicSource.context ctx slot).parameters.numVariables.val) → NativeExtensionFields.Goldilocks3) :
    (ExtensionLookupTerminal.sourceQuery NativeExtensionFields.goldilocksBasis shape point).evaluate
      (ScalarPublicSourceModel.publicPacked (RegistryPublicSource.context ctx slot) dummy context (ctx.registry.val.get slot).root
        history radius ((origin entries reachable helperHandle references template ctx assembled slot).capacityAt _ rfl) geometry width) =
      PaddedExtension.encode (padding := padding) NativeExtensionFields.goldilocksBasis
        (ExtensionQuery.evaluate _ point (factor entries reachable helperHandle references template ctx assembled slot dummy context history radius geometry width shape)) :=
  ScalarPublicSourceModel.publicScalar_query _ _ _ _ _ _ _ _ width shape point

/-- First-read stability is derived for the original allocated factor even
when that original key has not been frozen by an earlier read. -/
theorem read (dummy context : Digest) (before after : List Observation) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters)
    {padding c : ℕ} (width : (RegistryPublicSource.context ctx slot).parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (resolved : (context,(ctx.registry.val.get slot).root) ∈ NativeParentLedger.resolve
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy before).1.1
      (NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy before).1.2 input) :
    factor entries reachable helperHandle references template ctx assembled slot dummy context
        (before ++ .output input offset values :: after) radius geometry width shape =
      factor entries reachable helperHandle references template ctx assembled slot dummy context before radius geometry width shape :=
  SourceFrontierStability.scalar_read _ _ _ _ _ _ _ _ _ width shape input offset values positive resolved

/-- Original registry initialization computes this full context/root key and
actually observes its context hash, including unused and aliased slots. -/
theorem registered_key (parent : NativeTranscript.Transcript) (world : InputIndexedOracle.World)
    (initialized : NativeSourceRegistry.Initialized)
    (registered : (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row ctx.registry parent) world).run.1 = some initialized) :
    initialized.sources.val[slot.val]? =
        some (InputIndexedOracle.sha512 world (GoldContextInput.bytes (ctx.registry.val.get slot).parameters),
          (ctx.registry.val.get slot).root) ∧
      Observation.hash (GoldContextInput.bytes (ctx.registry.val.get slot).parameters)
          (List.ofFn (InputIndexedOracle.sha512 world (GoldContextInput.bytes (ctx.registry.val.get slot).parameters))) ∈
        (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row ctx.registry parent) world).run.2 := by
  have original := NativeSourceRegistry.initialized_origin NativeGoldBlockCode.description.row ctx.registry parent world initialized registered
  obtain ⟨key,getter,computed,root⟩ := NativeRegistryAncestry.contexts_slot NativeGoldBlockCode.description.row ctx.registry.val world
    initialized.sources.val original.2.1 slot
  have digest : InputIndexedOracle.sha512 world (GoldContextInput.bytes (ctx.registry.val.get slot).parameters) = key.1 := by
    rw [GoldContextCollision.context_run] at computed
    exact Option.some.inj computed
  have same : key = (InputIndexedOracle.sha512 world (GoldContextInput.bytes (ctx.registry.val.get slot).parameters),
      (ctx.registry.val.get slot).root) := Prod.ext digest.symm root
  refine ⟨getter.trans (congrArg some same),?_⟩
  have included := NativeRegistryContextTrace.initialized_slot NativeGoldBlockCode.description.row ctx.registry parent world initialized registered slot
  rw [GoldContextCollision.context_run] at included
  exact included.subset List.mem_cons_self

/-- The initializer key is tied to the chosen original allocation itself,
including its original reference root and full parameter serialization. -/
theorem allocated_registered_key (parent : NativeTranscript.Transcript) (world : InputIndexedOracle.World)
    (initialized : NativeSourceRegistry.Initialized)
    (registered : (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row ctx.registry parent) world).run.1 = some initialized) :
    let entry := AllocatedCodeOrigin.registryEntry entries reachable references ctx.registry
      (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 slot
    ∃ reference, references.val[slot.val]? = some reference ∧ entries[reference.handle]? = some entry ∧
      NativeGoldParameterStore.GoodEntry entry ∧
      initialized.sources.val[slot.val]? =
        some (InputIndexedOracle.sha512 world (GoldContextInput.bytes entry.initialized.parameters),reference.root) ∧
      Observation.hash (GoldContextInput.bytes entry.initialized.parameters)
          (List.ofFn (InputIndexedOracle.sha512 world (GoldContextInput.bytes entry.initialized.parameters))) ∈
        (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row ctx.registry parent) world).run.2 := by
  obtain ⟨reference,referenceAt,entryAt,good,oracle⟩ := original_entry entries reachable helperHandle references template ctx assembled slot
  have registeredKey := registered_key ctx slot parent world initialized registered
  rw [oracle] at registeredKey
  exact ⟨reference,referenceAt,entryAt,good,registeredKey⟩

/-- Realized native ancestry fixes this original allocated factor at the
actual pre-read history, or exposes the existing seed-order exception. -/
theorem ancestry_read {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : InputIndexedOracle.World)
    (dummy context : Digest) (radius : ℕ)
    (geometry : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters)
    {padding c : ℕ} (width : (RegistryPublicSource.context ctx slot).parameters.width.val = 3+padding) (shape : 3+padding = 2^c)
    (parent : Input) (parentIndex : ℕ)
    (realized : NativeSeedAncestry.Realized world (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      parent parentIndex (.source (context,(ctx.registry.val.get slot).root)))
    (position : ℕ) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[position]? = some (.output input offset values))
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64)) :
    factor entries reachable helperHandle references template ctx assembled slot dummy context
        (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 radius geometry width shape =
      factor entries reachable helperHandle references template ctx assembled slot dummy context
        ((OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position) radius geometry width shape ∨
      SeedQuoteOrder.Bad step initial world :=
  SourceFrontierStability.ancestry_scalar_read step fuel initial world _ dummy context _ radius _ geometry width shape
    parent parentIndex (.source (context,(ctx.registry.val.get slot).root)) realized position input offset values positive positioned quoted (List.mem_singleton_self _)

end
end FormalProof4FHE.HasteBoots.AllocatedScalarSource
