module
public import FormalProof4FHE.HasteBoots.AllocatedLookupIdentity
@[expose] public section

/-! Original public table families for the actual executed identity job.
PCS ownership derives their source/helper geometries. Tables use original
allocation provenance, full parameters, roots and an explicit history; no
future response record selects the family. Causal history fixing is separate. -/
namespace FormalProof4FHE.HasteBoots.AllocatedLookupTables
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open MatrixFold (Cube)
open NativeFields (Goldilocks)
open NativeScalarQueryShape (laneBits)
noncomputable section

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)

structure Geometry : Prop where
  source : ∀ column : Fin (origin.ready.jobs.get index).tag.request.columns,
    GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx (job.slots.slot column)).parameters
  helper : GoldHistorySourceTable.Geometry ctx.helper

/-- Geometry is recovered from accepted original PCS ownership, without
requiring any opening to be truthful. -/
theorem source_geometry {Memory : Type} (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory)
    (executed : (OracleProgram.run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (references : Vector Reference)
    (collected : NativeGoldParameterStore.registry entries references = some ctx.registry) (dummy : Digest) (history : List Observation)
    (slot : Fin ctx.registry.val.length)
    (owned : LookupSourcePublicOwnership.Owned ctx chooseHelper chooseBatch memory world lookup progress after executed entries reachable references collected dummy history slot) :
    GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters := by
  obtain ⟨receipt,member,associated,sizes,_⟩ := owned
  exact sizes

theorem helper_geometry {Memory : Type} (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (after : NativeGoldHelperVerification.Progress Memory)
    (executed : (OracleProgram.run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers body plan (.done after))
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (handle : ℕ) (dummy : Digest) (history : List Observation)
    (checked : NativeSharedLookupGuard.Checked)
    (owned : HelperPublicOwnership.Owned ctx choose memory world body plan after executed entries reachable handle dummy history checked) :
    GoldHistorySourceTable.Geometry ctx.helper := by
  obtain ⟨entry,found,good,parameters,receipt,member,atReceipt,query,root,opening,encoded,sizes,_⟩ := owned
  change GoldHistorySourceTable.Geometry entry.initialized.parameters at sizes
  exact parameters ▸ sizes

/-- Actual allocated acceptance derives all geometries for the selected family,
with the same single lifetime hash bad event as source ownership. -/
theorem geometry_or_bad {Memory : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (OracleProgram.run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 =
      .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory)
    (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) (dummy : Digest) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history)
    (observed : (OracleProgram.run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist history) :
    Geometry origin index job ∨ NativeRootFamilyLifetime.Bad dummy history := by
  rcases AllocatedLookupIdentity.owned_or_bad entries reachable helperHandle references template chooseHelper chooseBatch memory world ctx result executed
      lookup progress after phase origin index job dummy history truthful observed with ⟨sources,helper⟩ | bad
  · exact Or.inl ⟨fun column => source_geometry chooseHelper chooseBatch memory lookup progress after _ entries reachable references _ dummy history
        (job.slots.slot column) (sources column),
      helper_geometry chooseHelper memory lookup.plan lookup.helpers _ entries reachable helperHandle dummy history job.view.checked helper⟩
  · exact Or.inr bad

variable (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ)
    (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (geometry : Geometry origin index job) (dummy : Digest) (history : List Observation) (radius : ℕ)

/-- Each column uses its original allocated registry object. Native uniformity
transports only the row dimension and packing width; code parameters, original
constructor provenance, root and all padding lanes remain column-specific. -/
def sourceAt (slot : Fin ctx.registry.val.length)
    (sizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx slot).parameters) :
    Cube body.sourceVariables → Fin (3+origin.padding) → Goldilocks :=
  fun cell => ScalarPublicSourceModel.publicPacked (RegistryPublicSource.context ctx slot) dummy
    (InputIndexedOracle.sha512 world (GoldContextInput.bytes (ctx.registry.val.get slot).parameters))
    (ctx.registry.val.get slot).root history radius
    ((AllocatedScalarSource.origin entries reachable helperHandle references template ctx assembled slot).capacityAt _ rfl)
    sizes (origin.registry_dimensions slot).2 (cast (congrArg Cube (origin.registry_dimensions slot).1.symm) cell)

theorem sourceAt_congr (left right : Fin ctx.registry.val.length)
    (leftSizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx left).parameters)
    (rightSizes : GoldHistorySourceTable.Geometry (RegistryPublicSource.context ctx right).parameters) (same : left = right) :
    sourceAt origin entries reachable helperHandle references template assembled dummy history radius left leftSizes =
      sourceAt origin entries reachable helperHandle references template assembled dummy history radius right rightSizes := by
  subst right
  rfl

def sources : Fin (origin.ready.jobs.get index).tag.request.columns → Cube body.sourceVariables → Fin (3+origin.padding) → Goldilocks :=
  fun column => sourceAt origin entries reachable helperHandle references template assembled dummy history radius
    (job.slots.slot column) (geometry.source column)

/-- Repeated original slot addresses share the same whole-history table,
including allocation provenance and nonzero packing padding. -/
theorem sources_alias (left right : Fin (origin.ready.jobs.get index).tag.request.columns)
    (same : job.slots.slot left = job.slots.slot right) :
    sources origin index job entries reachable helperHandle references template assembled geometry dummy history radius left =
      sources origin index job entries reachable helperHandle references template assembled geometry dummy history radius right :=
  sourceAt_congr origin entries reachable helperHandle references template assembled dummy history radius
    (job.slots.slot left) (job.slots.slot right) (geometry.source left) (geometry.source right) same

/-- The helper's original proof-root ordinal is the job ordinal, independent
of which registry slots the job uses. -/
def helperIndex : Fin ctx.proof.roots.val.length :=
  ⟨index.val,by
    have counts := NativeSharedLookupPreflightLink.protocol_counts ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
      (ctx.registry.val.map NativeSharedLookupParent.Oracle.geometry) ctx.helper.geometry origin.geometry origin.preflight
      ctx.proof.helperOpenings.val.length ctx.proof.values origin.shape ctx.proof.roots.property 7 ctx.lookupFuel ctx.equalityFuel
      (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world)
      world origin.ready origin.prepared
    have roots := (NativeSharedLookupProofShape.check_spec _ _ _ _ _ origin.shape).roots
    change ctx.proof.roots.val.length = origin.geometry.repetitions.val at roots
    rw [roots,← counts.1]
    exact index.isLt⟩

def helperPadding : ℕ := ctx.helper.width.val-3

include origin in
theorem helperWidth : ctx.helper.width.val = 3+helperPadding (ctx := ctx) := by
  have widths := origin.helper_dimensions.2
  have enough : 3 ≤ ctx.helper.width.val := by rcases widths with same | degree <;> omega
  unfold helperPadding
  omega

/-- The helper retains one decoded value per original full-dimension row.
Its packing width is not flattened into more scalar coordinates. -/
def helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+helperPadding (ctx := ctx)) → Goldilocks :=
  let ref := AllocatedScalarHelper.reference entries reachable helperHandle references template ctx assembled (helperIndex origin index)
  let parameters := (AllocatedScalarHelper.entry_spec entries reachable helperHandle references template ctx assembled).2.2
  let variablesEq : ref.parameters.numVariables.val = laneBits (3+origin.padding)+body.sourceVariables :=
    (congrArg (fun parameters => parameters.numVariables.val) parameters).symm.trans
      ((congrArg Fin.val origin.helper_dimensions.1).trans job.view.dimension)
  fun cell => ScalarPublicSourceModel.publicPacked ref dummy
    (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper)) (ctx.proof.roots.val.get (helperIndex origin index)) history radius
    ((AllocatedScalarHelper.origin entries reachable helperHandle references template ctx assembled (helperIndex origin index)).capacityAt _ rfl)
    (by
      change GoldHistorySourceTable.Geometry (AllocatedScalarHelper.entry entries reachable helperHandle references template ctx assembled).initialized.parameters
      exact parameters ▸ geometry.helper) ((congrArg (fun parameters => parameters.width.val) parameters).symm.trans (helperWidth origin))
    (cast (congrArg Cube variablesEq.symm) cell)

local notation "sourceFamily" => sources origin index job entries reachable helperHandle references template assembled geometry dummy history radius
local notation "helperFamily" => helpers origin index job entries reachable helperHandle references template assembled geometry dummy history radius
open LookupIdentityCausalReduction (partialTables fullTables Wrong)
open NativeFieldWire (goldExtensionValue)

/-- The actual allocated public families feed the partial identity reduction.
The selected history is explicit; causal pre-read stability is not assumed here. -/
theorem partial_event_or_wrong (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (branch : (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val ≠ 2^origin.geometry.geometry.1.val)
    (initial : ScalarChainHealing.value (2*index.val+1) origin.ready.statement.claims.val ≠
      some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (origin.ready.jobs.get index).output.r)) ExtensionLookupIdentity.partialIndices
        (laneBits (3+origin.padding)+body.sourceVariables) (partialTables job.view sourceFamily helperFamily) [])) :
    ScalarFinishedSourceEvent.Event origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra ctx.scalarFuel world ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (origin.ready.jobs.get index).output.r)) ExtensionLookupIdentity.partialIndices
      (laneBits (3+origin.padding)+body.sourceVariables) (partialTables job.view sourceFamily helperFamily) (2*index.val+1)
      (LookupScalarGrammar.identityInfo origin.geometry.geometry.1 (origin.ready.jobs.get index).tag.request) ∨ Wrong job.view sourceFamily helperFamily :=
  job.partial_event_or_wrong (helperPadding := helperPadding (ctx := ctx)) sourceFamily helperFamily frames decoded statementFits domain branch initial

/-- The actual allocated public families feed the full identity reduction.
The selected history is explicit; causal pre-read stability is not assumed here. -/
theorem full_event_or_wrong (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll origin.ready.equality.transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (branch : (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val = 2^origin.geometry.geometry.1.val)
    (initial : ScalarChainHealing.value (2*index.val+1) origin.ready.statement.claims.val ≠
      some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
        (laneBits (3+origin.padding)+body.sourceVariables) (fullTables job.view sourceFamily helperFamily) [])) :
    ScalarFinishedSourceEvent.Event origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra ctx.scalarFuel world ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
      (laneBits (3+origin.padding)+body.sourceVariables) (fullTables job.view sourceFamily helperFamily) (2*index.val+1)
      (LookupScalarGrammar.identityInfo origin.geometry.geometry.1 (origin.ready.jobs.get index).tag.request) ∨ Wrong job.view sourceFamily helperFamily :=
  job.full_event_or_wrong (helperPadding := helperPadding (ctx := ctx)) sourceFamily helperFamily frames decoded statementFits domain branch initial

end
end FormalProof4FHE.HasteBoots.AllocatedLookupTables
