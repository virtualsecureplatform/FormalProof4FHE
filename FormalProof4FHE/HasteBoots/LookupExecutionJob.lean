module
public import FormalProof4FHE.HasteBoots.LookupOriginalSlots
@[expose] public section

/-! One actual original prepared job retains its producer, equality draw,
source-slot addresses and original proof rows at the executed caller boundary. -/
namespace FormalProof4FHE.HasteBoots.LookupExecutionJob
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeSharedLookupBody (Bound)
open LookupExecutionOrigin (Origin childStart)
noncomputable section

variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : Bound}

structure Job (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (index : Fin origin.ready.jobs.length) where
  view : LookupIdentityView.View origin.padding result.sourceVariables origin.geometry.geometry.1 (origin.ready.jobs.get index) result.claims result.terminal index.val
  slots : LookupOriginalSlots.Slots registry.val.length (origin.ready.jobs.get index).tag.request
  original : (origin.ready.jobs.get index).tag.request ∈ List.ofFn (models requests)
  producerMember : view.producer ∈ (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
    (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
      (childStart row registry helper parent requests proof world)) world).1.completed
  producerJob : view.producer.job = (origin.ready.jobs.get index).tag.job
  related : List.Forall₂ (fun slot value => proof.values.sources[slot]? = some value)
    (origin.ready.jobs.get index).tag.request.terminal.sourceSlots view.checked.values
  equality : ∃ draw, origin.ready.machine.draws[index.val]? = some draw ∧ NativeGoldLookupEquality.DrawEvidence draw (List.ofFn view.eqPoint)

theorem recover (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (index : Fin origin.ready.jobs.length) : Nonempty (Job origin index) := by
  obtain ⟨view,producerMember,producerJob,related,equality⟩ := LookupIdentityView.recover requests.property.le (models requests)
    (registry.val.map Oracle.geometry) helper.geometry origin.geometry origin.preflight proof.helperOpenings.val.length proof.values origin.shape
    origin.width proof.roots.property 7 lookupFuel equalityFuel (childStart row registry helper parent requests proof world) world origin.ready
    origin.prepared proof.algebra scalarFuel result.claims origin.scalar result.sourceVariables result.terminal origin.guarded index
  have contract := NativeSharedLookupPrelude.protocol_contract requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared
  have tags := (NativeSharedLookupPrepared.prepare_spec _ _ _ contract.prepared).1
  have tagMember : (origin.ready.jobs.get index).tag ∈ NativeSharedLookupStatement.tags requests.property.le (models requests) := by
    rw [← tags]
    exact List.mem_map.mpr ⟨origin.ready.jobs.get index,List.get_mem _ _,rfl⟩
  have requestAt := (NativeSharedLookupProofShape.tag_request requests.property.le (models requests) _ tagMember).2
  have original := List.mem_of_getElem? requestAt
  obtain ⟨slots⟩ := LookupOriginalSlots.recover (registry.val.map Oracle.geometry) helper.geometry (List.ofFn (models requests)) origin.geometry
    origin.preflight (origin.ready.jobs.get index).tag.request original
  have count : (registry.val.map Oracle.geometry).length = registry.val.length := List.length_map _
  rw [count] at slots
  exact ⟨⟨view,slots,original,producerMember,producerJob,related,equality⟩⟩

/-- Each selected original address participates in the actual deferred source
verification, rather than merely being within the registry bounds. -/
theorem Job.used {origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result}
    {index : Fin origin.ready.jobs.length} (job : Job origin index) (column : Fin (origin.ready.jobs.get index).tag.request.columns) :
    NativeSharedSourceClaims.used requests (job.slots.slot column) = true := job.slots.used requests job.original column

/-- This is the original raw proof row, including every lane. It is not a
row chosen later by a PCS receipt or an equality search over aliases. -/
theorem Job.opening {origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result}
    {index : Fin origin.ready.jobs.length} (job : Job origin index) (column : Fin (origin.ready.jobs.get index).tag.request.columns) :
    ∃ original : NativeLookupRequestWire.Row, proof.sources.val[(job.slots.slot column).val]? = some original ∧
      original.val = List.ofFn (job.view.inputs column) := by
  have copied := job.slots.opening proof.values.sources job.view.checked.values job.view.inputs job.view.inputsEq job.related column
  change (proof.sources.val.map (fun value => value.val))[(job.slots.slot column).val]? = some (List.ofFn (job.view.inputs column)) at copied
  rw [List.getElem?_map] at copied
  obtain ⟨original,present,same⟩ := Option.map_eq_some_iff.mp copied
  exact ⟨original,present,same⟩

open LookupIdentityCausalReduction (partialTables fullTables Wrong)
open NativeScalarQueryShape (laneBits)
open NativeFieldWire (goldExtensionValue)

theorem Job.partial_event_or_wrong {origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result}
    {index : Fin origin.ready.jobs.length} (job : Job origin index) {helperPadding : ℕ}
    (sources : Fin (origin.ready.jobs.get index).tag.request.columns → MatrixFold.Cube result.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : MatrixFold.Cube (laneBits (3+origin.padding)+result.sourceVariables) → Fin (3+helperPadding) → NativeFields.Goldilocks)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (branch : (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val ≠ 2^origin.geometry.geometry.1.val)
    (initial : ScalarChainHealing.value (2*index.val+1) origin.ready.statement.claims.val ≠
      some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (origin.ready.jobs.get index).output.r)) ExtensionLookupIdentity.partialIndices
        (laneBits (3+origin.padding)+result.sourceVariables) (partialTables job.view sources helpers) [])) :
    ScalarFinishedSourceEvent.Event origin.ready.equality.transcript origin.ready.statement proof.algebra scalarFuel world ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (origin.ready.jobs.get index).output.r)) ExtensionLookupIdentity.partialIndices
      (laneBits (3+origin.padding)+result.sourceVariables) (partialTables job.view sources helpers) (2*index.val+1)
      (LookupScalarGrammar.identityInfo origin.geometry.geometry.1 (origin.ready.jobs.get index).tag.request) ∨ Wrong job.view sources helpers := by
  have infoAt := (LookupScalarGrammar.protocol_pair requests.property.le (models requests) origin.geometry.geometry.1 proof.values.multiplicities
    proof.values.roots proof.roots.property 7 lookupFuel equalityFuel (childStart row registry helper parent requests proof world)
    world origin.ready origin.prepared index.val index.isLt).2.1
  exact LookupIdentityCausalReduction.partial_event_or_wrong job.view origin.ready.equality.transcript frames origin.ready.statement proof.algebra
    decoded statementFits domain scalarFuel world origin.scalar infoAt branch sources helpers initial

theorem Job.full_event_or_wrong {origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result}
    {index : Fin origin.ready.jobs.length} (job : Job origin index) {helperPadding : ℕ}
    (sources : Fin (origin.ready.jobs.get index).tag.request.columns → MatrixFold.Cube result.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : MatrixFold.Cube (laneBits (3+origin.padding)+result.sourceVariables) → Fin (3+helperPadding) → NativeFields.Goldilocks)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (branch : (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val = 2^origin.geometry.geometry.1.val)
    (initial : ScalarChainHealing.value (2*index.val+1) origin.ready.statement.claims.val ≠
      some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
        (laneBits (3+origin.padding)+result.sourceVariables) (fullTables job.view sources helpers) [])) :
    ScalarFinishedSourceEvent.Event origin.ready.equality.transcript origin.ready.statement proof.algebra scalarFuel world ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
      (laneBits (3+origin.padding)+result.sourceVariables) (fullTables job.view sources helpers) (2*index.val+1)
      (LookupScalarGrammar.identityInfo origin.geometry.geometry.1 (origin.ready.jobs.get index).tag.request) ∨ Wrong job.view sources helpers := by
  have infoAt := (LookupScalarGrammar.protocol_pair requests.property.le (models requests) origin.geometry.geometry.1 proof.values.multiplicities
    proof.values.roots proof.roots.property 7 lookupFuel equalityFuel (childStart row registry helper parent requests proof world)
    world origin.ready origin.prepared index.val index.isLt).2.1
  exact LookupIdentityCausalReduction.full_event_or_wrong job.view origin.ready.equality.transcript frames origin.ready.statement proof.algebra
    decoded statementFits domain scalarFuel world origin.scalar infoAt branch sources helpers initial

end
end FormalProof4FHE.HasteBoots.LookupExecutionJob
