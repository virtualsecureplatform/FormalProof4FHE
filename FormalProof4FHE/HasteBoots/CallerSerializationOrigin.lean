module
public import FormalProof4FHE.HasteBoots.ResidentMessageBounds
@[expose] public section

/-! Original completed native execution determines the serialized parent
operands. Buffer evidence concerns those exact bindings and registry, never
an independently chosen request order, helper context or source association. -/
namespace FormalProof4FHE.HasteBoots.CallerSerializationOrigin
open NativeGoldHelperVerification (Context)
open NativeGoldBatchOpening (Opening)
open NativePrefixCodec (Vector)
open NativeCanonicalLookupWire (Binding Source)
open OracleProgram (run)
open InputIndexedOracle (World)
noncomputable section

variable {Memory A : Type} {ctx : Context (Vector Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A} {world : World}

abbrev Job := CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world

theorem completed (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) :
    (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1 = some (.bound data.lookup.body) := by
  have helpers := OpeningReceiptProofSource.helper_execution ctx data.chooseHelper data.chooseBatch data.memory world data.lookup data.progress data.after data.executed
  have origin := NativeGoldHelperVerification.helpers_origin ctx data.chooseHelper data.memory world data.lookup.body data.lookup.plan (.done data.lookup.helpers) helpers
  have native := origin.native
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] at native
  exact congrArg Prod.fst native

theorem prepared (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) :
    ∃ geometry, (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.2 = some geometry := by
  obtain ⟨geometry,launched,began,_,_,_⟩ := NativeSharedLookupExecution.bound_origin _ _ _ _ _ _ _ _ _ world data.lookup.body (completed data)
  obtain ⟨output,_,_,prepared,_,_⟩ := NativeSharedLookupParent.begin_spec _ _ _ _ _ _ _ _ world ⟨geometry,launched⟩ began
  exact ⟨output,prepared⟩

theorem binding_trace (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) :
    ∃ bindings : List Binding, List.Forall₂ (ParentBindingTrace.ForRequest NativeGoldBlockCode.description.row ctx.registry.val ctx.helper world)
      ctx.requests.val bindings := by
  obtain ⟨geometry,success⟩ := prepared data
  obtain ⟨numeric,preflight⟩ := LookupFramingRecovery.preflight_of_prepared _ _ _ _ _ world geometry success
  obtain ⟨bindings,related,_⟩ := ParentBindingTrace.preflight _ _ _ _ _ world numeric preflight
  exact ⟨bindings,related⟩

def bindings (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) : List Binding :=
  (binding_trace data).choose

theorem bindings_related (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) :
    List.Forall₂ (ParentBindingTrace.ForRequest NativeGoldBlockCode.description.row ctx.registry.val ctx.helper world) ctx.requests.val (bindings data) :=
  (binding_trace data).choose_spec

theorem registry_origin (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) :
    ∃ sources : Vector Source,
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val := by
  obtain ⟨sources,computed,_⟩ := NativeRegistryAncestry.bound_registration _ _ _ _ _ _ _ _ _ world data.lookup.body (completed data)
  exact ⟨sources,computed⟩

def sources (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) : Vector Source :=
  (registry_origin data).choose

theorem sources_computed (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) :
    (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some (sources data).val :=
  (registry_origin data).choose_spec

structure Buffers (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) where
  requests : ResidentMessageBounds.Buffer (NativeLookupRequestWire.requestsCodec.encode ctx.requests)
  bindings : ∀ binding ∈ CallerSerializationOrigin.bindings data, Nonempty (ResidentMessageBounds.Buffer (NativeCanonicalLookupWire.payload binding))
  registry : ResidentMessageBounds.Buffer (NativeCanonicalLookupWire.sourcesCodec.encode (sources data))

theorem parent_domain (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) (buffers : Buffers data) :
    NativeLookupParentFraming.Domain ctx.registry.val ctx.requests :=
  ⟨ResidentMessageBounds.fits buffers.requests,
    ResidentMessageBounds.calls_fit _ _ _ world _ _ (bindings_related data) buffers.bindings⟩

theorem registry_fits (data : Job (Memory := Memory) (ctx := ctx) (allocation := allocation) (program := program) (world := world)) (buffers : Buffers data)
    (actual : Vector Source)
    (computed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some actual.val) :
    (NativeCanonicalLookupWire.sourcesCodec.encode actual).length < TranscriptFrame.lengthLimit := by
  have same : actual = sources data := Subtype.ext (Option.some.inj (computed.symm.trans (sources_computed data)))
  rw [same]
  exact ResidentMessageBounds.fits buffers.registry

end
end FormalProof4FHE.HasteBoots.CallerSerializationOrigin
