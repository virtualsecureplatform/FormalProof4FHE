module
public import FormalProof4FHE.HasteBoots.OriginalParentBindings
public import FormalProof4FHE.HasteBoots.FramedIdentityWork
import all Init.Data.String.Defs
@[expose] public section

/-! Successful parent execution supplies its actual binding and both framed
prefixes. The only input evidence is original parent framing and native byte
allocation domains; no helper association or parsed parent is supplied. -/
namespace FormalProof4FHE.HasteBoots.LookupFramingRecovery
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription Parameters)
open NativeLookupRequestWire (Request)
open NativeCanonicalLookupWire (Binding Source)
open NativePrefixCodec (Vector)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

/-- Registration cannot turn failed preflight into successful preparation. -/
theorem preflight_of_prepared {C : Type} (row : RowDescription C) (registry : Vector (Oracle C))
    (helper : Parameters C) (parent : Transcript) (requests : Vector Request) (world : World)
    (output : NativeSharedLookupPreflight.Output)
    (success : (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.2 = some output) :
    ∃ numeric, (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 = some numeric := by
  cases numeric : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 with
  | none =>
    simp only [NativeSharedLookupParent.prepare,OracleProgram.run_bind,ObservationReplay.run_bind,
      numeric,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
    contradiction
  | some geometry => exact ⟨geometry,rfl⟩

/-- Every emitted binding uses the helper context actually computed by this execution. -/
theorem binding_helpers {C : Type} (row : RowDescription C) (registry : List (Oracle C))
    (helper : Parameters C) (world : World) (requests : List Request) (bindings : List Binding)
    (related : List.Forall₂ (ParentBindingTrace.ForRequest row registry helper world) requests bindings) :
    ∀ binding ∈ bindings, (run (NativeBrakedownContext.context row helper) world).run.1 = some binding.helper := by
  induction related with
  | nil => simp
  | @cons request binding requests bindings first rest ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨_,_,_,computed,_⟩ := first
      exact computed
    · exact ih actual later

/-- A retained native job recovers the successful parent branch that produced it. -/
theorem job_prepared {Memory A : Type} {ctx : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A} {world : World}
    (data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    ∃ geometry, (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper
      ctx.parent ctx.requests) world).run.1.2 = some geometry := by
  have executed := congrArg Prod.fst (CanonicalNativeHealingCoverage.allocated_packet data)
  have helpers := AllocatedLookupPublicOwnership.helpers_done allocation.entries allocation.helperHandle allocation.references allocation.template
    data.chooseHelper data.chooseBatch data.memory world ctx _ executed data.lookup data.progress data.after data.executed
  have origin := NativeGoldHelperVerification.helpers_origin ctx data.chooseHelper data.memory world data.lookup.body data.lookup.plan
    (.done data.lookup.helpers) helpers
  have native := origin.native
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] at native
  have completed := congrArg Prod.fst native
  change (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1 = some (.bound data.lookup.body) at completed
  obtain ⟨nativeGeometry,launched,began,_,_,_⟩ := NativeSharedLookupExecution.bound_origin _ _ _ _ _ _ _ _ _ world data.lookup.body completed
  obtain ⟨geometry,_,_,prepared,_,_⟩ := NativeSharedLookupParent.begin_spec _ _ _ _ _ _ _ _ world ⟨nativeGeometry,launched⟩ began
  exact ⟨geometry,prepared⟩

/-- Jobs retain membership in the original request list, even with repeated slots. -/
theorem job_requests_nonempty {Memory A : Type} {ctx : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A} {world : World}
    (data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world) : ctx.requests.val ≠ [] := by
  intro empty
  have member := data.job.original
  rw [NativeSharedLookupParent.models_list,empty,List.map_nil] at member
  cases member

/-- Literal frame lists recovered from the original successful preparation. -/
structure Parents {C : Type} (row : RowDescription C) (registry : Vector (Oracle C))
    (helper : Parameters C) (parent : Transcript) (requests : Vector Request) (world : World) where
  preflightFrames : List TranscriptFrame.Frame
  preflightBytes : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1.input =
    TranscriptFrame.encodeMany preflightFrames
  preflightValid : ∀ frame ∈ preflightFrames, TranscriptFrame.Valid frame
  parentFrames : List TranscriptFrame.Frame
  parentBytes : (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1.input =
    TranscriptFrame.encodeMany parentFrames
  parentValid : ∀ frame ∈ parentFrames, TranscriptFrame.Valid frame
  binding : Binding
  bound : ParentBindingTrace.frame binding ∈ parentFrames
  helperComputed : (run (NativeBrakedownContext.context row helper) world).run.1 = some binding.helper
  sources : Vector Source
  sourcesComputed : (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some sources.val
  registryBound : (⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩ : TranscriptFrame.Frame) ∈ parentFrames

/-- Actual nonempty parent preparation derives both frame lists and helper association. -/
theorem parents {C : Type} (row : RowDescription C) (registry : Vector (Oracle C))
    (helper : Parameters C) (parent : Transcript) (requests : Vector Request) (world : World)
    (output : NativeSharedLookupPreflight.Output)
    (success : (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.2 = some output)
    (nonempty : requests.val ≠ []) (before : List TranscriptFrame.Frame)
    (bytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (domain : NativeLookupParentFraming.Domain registry.val requests)
    (registryFits : ∀ sources : Vector Source,
      (run (NativeSharedLookupParent.contexts row registry.val) world).run.1 = some sources.val →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit) :
    Nonempty (Parents row registry helper parent requests world) := by
  obtain ⟨numeric,checked⟩ := preflight_of_prepared row registry helper parent requests world output success
  obtain ⟨bindings,related,emitted⟩ := ParentBindingTrace.preflight row registry.val helper parent requests world numeric checked
  let earlier := before ++ [ParentBindingsView.requestFrame requests] ++ bindings.map ParentBindingTrace.frame
  have earlierBytes : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1.input =
      TranscriptFrame.encodeMany earlier := by
    rw [emitted,NativeLookupRequestWire.bindRequests_input,bytes]
    simp only [earlier,SingleOpeningExposure.encodeMany_append,TranscriptFrame.encodeMany,
      ParentBindingsView.requestFrame,List.append_nil,List.append_assoc]
  have earlierValid : ∀ frame ∈ earlier, TranscriptFrame.Valid frame := by
    have bindingValid := OriginalParentBindings.bindings_valid row registry.val helper world requests.val bindings related domain.2
    intro frame member
    simp only [earlier,List.mem_append,List.mem_singleton,List.mem_map] at member
    rcases member with (old | rfl) | ⟨binding,named,rfl⟩
    · exact valid frame old
    · exact ⟨by change NativeLookupRequestWire.requestsLabel.length < _; decide +kernel,domain.1⟩
    · exact bindingValid binding named
  have notnil : bindings ≠ [] := by
    intro empty
    have count := related.length_eq
    rw [empty,List.length_nil] at count
    exact nonempty (List.length_eq_zero_iff.mp count)
  obtain ⟨binding,member⟩ := List.exists_mem_of_ne_nil bindings notnil
  have helperComputed := binding_helpers row registry.val helper world requests.val bindings related binding member
  obtain ⟨sources,computed,registered⟩ := NativeRegistryAncestry.prepare_registered row registry helper parent requests world output success
  let registryFrame : TranscriptFrame.Frame := ⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩
  refine ⟨⟨earlier,earlierBytes,earlierValid,earlier ++ [registryFrame],?_,?_,binding,?_,helperComputed,sources,computed,?_⟩⟩
  · rw [registered,NativeCanonicalLookupWire.registry_input,earlierBytes]
    simp only [SingleOpeningExposure.encodeMany_append,TranscriptFrame.encodeMany,List.append_nil,registryFrame]
  · intro frame named
    rcases List.mem_append.mp named with old | added
    · exact earlierValid frame old
    · obtain rfl := List.mem_singleton.mp added
      exact ⟨by change NativeCanonicalLookupWire.registryLabel.length < _; decide +kernel,registryFits sources computed⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨binding,member,rfl⟩
  · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Goldilocks native completion discharges all parent framing certificates.
Serialization allocation domains remain explicit. -/
theorem job_framing {Memory A : Type} {ctx : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A} {world : World}
    (data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (domain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (registryFits : ∀ sources : Vector Source,
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit)
    (groupedFits : (NativeLookupMultiplicityWire.grouped ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit)
    (flatFits : (NativeLookupMultiplicityWire.flattened ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit) :
    Nonempty (AllocatedLookupReadStability.Framing ctx world) := by
  obtain ⟨output,success⟩ := job_prepared data
  obtain ⟨recovered⟩ := parents NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests world output success
    (job_requests_nonempty data) before bytes valid domain registryFits
  have computed := recovered.helperComputed
  rw [GoldContextCollision.context_run] at computed
  have helper := (Option.some.inj computed).symm
  exact ⟨⟨recovered.preflightFrames,recovered.preflightBytes,recovered.preflightValid,registryFits,groupedFits,flatFits,
    recovered.parentFrames,recovered.parentBytes,recovered.parentValid,recovered.binding,recovered.bound,helper⟩⟩

end
end FormalProof4FHE.HasteBoots.LookupFramingRecovery
