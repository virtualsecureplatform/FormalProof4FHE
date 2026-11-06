module

public import FormalProof4FHE.HasteBoots.NativeGoldLookupVerification
public import FormalProof4FHE.HasteBoots.NativeSourceClaimDomain
public import FormalProof4FHE.HasteBoots.NativeGoldScalarPcsQuery
public import FormalProof4FHE.HasteBoots.NativeDeferredBatchDomain
@[expose] public section

/-! The actual registered lookup/helper pipeline supplies original key
provenance, proof value count and source query representability. These facts
discharge source collection and batch-dispatch auxiliary domains and attach
first-used claim invariants to the combined typed execution.
This does not establish application extraction/soundness, raw availability,
Fiat–Shamir risk, physical work, numerical profiles, decoding or Rust refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupSourceInvariant
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeGoldLookupVerification (Prepared sourceProgram)
open NativeSharedLookupParent (models Oracle)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem prepared_registry {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (success : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared) :
    List.Forall₂ (fun oracle source =>
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row oracle.parameters) world).run.1 = some source.1 ∧
        source.2 = oracle.root) ctx.registry.val prepared.metadata.sources.val := by
  obtain ⟨geometry,original⟩ := NativeGoldLookupVerification.prepared_metadata ctx choose memory world prepared success
  have registered := (NativeRegisteredLookup.prepare_origin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests
    world geometry prepared.metadata original).1
  exact NativeSourceRegistry.initialized_sources NativeGoldBlockCode.description.row ctx.registry _ world prepared.metadata registered

theorem prepared_native {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (success : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared) :
    (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1 = some (.bound prepared.body) := by
  have selected := congrArg Prod.fst (NativeGoldLookupVerification.prepare_spec _ prepared success).1
  have erased := congrArg Prod.fst (NativeRegisteredLookup.helpers_erasure ctx choose memory world)
  have old := erased.symm.trans selected
  have origin := (NativeGoldHelperVerification.helpers_origin ctx choose memory world prepared.body prepared.plan (.done prepared.helpers) old).native
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] at origin
  exact congrArg Prod.fst origin

theorem prepared_values {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (success : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared) :
    ctx.proof.sources.val.length = ctx.registry.val.length := by
  have upstream := prepared_native ctx choose memory world prepared success
  obtain ⟨geometry,launched,_,_,launchedRun,_⟩ := NativeSharedLookupExecution.bound_origin NativeGoldBlockCode.description.row ctx.registry ctx.helper
    ctx.parent ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world prepared.body upstream
  have checked := NativeSharedLookupChild.launch_spec ctx.requests.property.le (models ctx.requests) .retain (ctx.registry.val.map Oracle.geometry)
    geometry ctx.proof ctx.lookupFuel ctx.equalityFuel _ world launched.1 launched.2 launchedRun
  simpa only [NativeSharedLookupProofData.Proof.values,NativeLookupRequestWire.Table.values,List.length_map] using checked.2.1.sources

/-- The actual earlier initializer and typed proof-shape gate discharge these
source indexing/allocation domains; no successful-domain certificate is supplied. -/
theorem source_available {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (success : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared) :
    NativeSourceClaimDomain.Available (run (sourceProgram ctx prepared) world).run.1 := by
  have registry := prepared_registry ctx choose memory world prepared success
  have values := prepared_values ctx choose memory world prepared success
  exact NativeSourceClaimDomain.program_available NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query ctx.proof.sources
    (NativeGoldLookupVerification.initial prepared) world registry.length_eq.symm rfl values.ge

theorem source_invariants {Memory : Type} (ctx : Context (Vector Opening)) (prepared : Prepared Memory) (world : World) :
    let after := (run (sourceProgram ctx prepared) world).run.1.progress
    NativeSourceClaimInvariant.Unique after ∧ NativeSourceClaimInvariant.Recorded prepared.query after ∧
      (after.seen.map NativeSharedSourceClaims.Seen.slot).Sublist ((List.finRange ctx.registry.val.length).map Fin.val) ∧
      ∀ previous ∈ after.seen, NativeSourceClaimInvariant.Origin NativeGoldBlockCode.description.row ctx.registry ctx.requests ctx.proof.sources world previous :=
  NativeSourceClaimInvariant.program_invariants NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query ctx.proof.sources
    (NativeGoldLookupVerification.initial prepared) world rfl

theorem source_key {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (success : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared)
    (previous : NativeSharedSourceClaims.Seen) (member : previous ∈ (run (sourceProgram ctx prepared) world).run.1.progress.seen) :
    ∃ slot : Fin prepared.metadata.sources.val.length, slot.val = previous.slot ∧ prepared.metadata.sources.val.get slot = previous.key := by
  have corresponding := prepared_registry ctx choose memory world prepared success
  obtain ⟨original,same,_,computed,root,_⟩ := (source_invariants ctx prepared world).2.2.2 previous member
  let slot : Fin prepared.metadata.sources.val.length := ⟨original.val,by rw [← corresponding.length_eq]; exact original.isLt⟩
  have relation := corresponding.get original.isLt slot.isLt
  refine ⟨slot,same.symm,?_⟩
  exact Prod.ext (Option.some.inj (relation.1.symm.trans computed)) (relation.2.trans root.symm)

theorem source_first_used {Memory : Type} (ctx : Context (Vector Opening)) (prepared : Prepared Memory) (world : World)
    (after : NativeSharedSourceClaims.Progress) (accepted : (run (sourceProgram ctx prepared) world).run.1 = .done after)
    (previous : NativeSharedSourceClaims.Seen) (member : previous ∈ after.seen) (slot : Fin ctx.registry.val.length)
    (used : NativeSharedSourceClaims.used ctx.requests slot = true)
    (context : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (ctx.registry.val.get slot).parameters) world).run.1 = some previous.key.1)
    (root : (ctx.registry.val.get slot).root = previous.key.2) : previous.slot ≤ slot.val :=
  NativeSourceClaimInvariant.program_first_used NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query ctx.proof.sources
    (NativeGoldLookupVerification.initial prepared) world rfl after accepted previous member slot used context root

theorem batches_source_available {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (prepared : Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress result) :
    NativeSourceClaimDomain.Available (run (sourceProgram ctx prepared) world).run.1 ∧
      NativeSourceClaimInvariant.Unique progress ∧ NativeSourceClaimInvariant.Recorded prepared.query progress ∧
      progress.state.claims.val.length = progress.seen.length ∧ progress.seen.length ≤ ctx.registry.val.length := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress result executed
  have invariant := source_invariants ctx prepared world
  have counts := NativeSourceClaimInvariant.program_counts NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query ctx.proof.sources
    (NativeGoldLookupVerification.initial prepared) world rfl
  simp only [origin.2.1,NativeSharedSourceClaims.Result.progress] at invariant
  let property (result : NativeSharedSourceClaims.Result) : Prop :=
    result.progress.state.claims.val.length = result.progress.seen.length ∧ result.progress.seen.length ≤ ctx.registry.val.length
  have checked : property (run (sourceProgram ctx prepared) world).run.1 := counts
  have afterCounts : property (.done progress) := origin.2.1 ▸ checked
  exact ⟨source_available ctx chooseHelper memory world prepared origin.1,invariant.1,invariant.2.1,afterCounts.1,afterCounts.2⟩

theorem bound_query {C S B : Type} (description : NativeBrakedownContext.RowDescription C)
    (registry : Vector (Oracle C)) (helper : NativeBrakedownContext.Parameters C) (parent : NativeTranscript.Transcript)
    (requests : Vector NativeLookupRequestWire.Request) (proof : NativeSharedLookupProofData.Proof S B)
    (lookupFuel equalityFuel scalarFuel : ℕ) (world : World) (body : NativeSharedLookupBody.Bound)
    (accepted : (run (NativeSharedLookupExecution.protocol description registry helper parent requests proof lookupFuel equalityFuel scalarFuel) world).run.1 = some (.bound body)) :
    ∃ query, NativeGoldPcsWire.fromPairs body.terminal.pulled.pairs = some query ∧ query.models = body.terminal.pulled.pairs := by
  obtain ⟨geometry,launched,_,_,_,executed⟩ := NativeSharedLookupExecution.bound_origin description registry helper parent requests proof
    lookupFuel equalityFuel scalarFuel world body accepted
  have bound := (NativeSharedLookupBody.body_bound (models requests) (registry.val.map Oracle.geometry) geometry.geometry.2.val
    launched.1 launched.2 proof scalarFuel world body executed).2
  have guarded := NativeSharedLookupGuard.guard_spec _ _ _ _ _ bound.guarded
  exact NativeGoldScalarPcsQuery.scalar_complete body.sourceVariables geometry.geometry.2.val body.terminal.point body.terminal.pulled guarded.query

/-- Completed helpers always lead to a representable source query and retained
metadata. The continuation's `prior` branch cannot hide either domain failure. -/
theorem helpers_prepare_complete {Memory : Type} (ctx : Context (Vector Opening)) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (body : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (after : NativeGoldHelperVerification.Progress Memory)
    (executed : (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1.1 = .helpers body plan (.done after)) :
    ∃ prepared, NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared := by
  obtain ⟨metadata,_,retained,_⟩ := NativeRegisteredLookup.helpers_metadata ctx choose memory world body plan (.done after) executed
  have erased := congrArg Prod.fst (NativeRegisteredLookup.helpers_erasure ctx choose memory world)
  have old := erased.symm.trans executed
  have native := (NativeGoldHelperVerification.helpers_origin ctx choose memory world body plan (.done after) old).native
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] at native
  have bodyRun := congrArg Prod.fst native
  obtain ⟨query,packed,_⟩ := bound_query NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world body bodyRun
  have paired : (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = (.helpers body plan (.done after),some metadata) :=
    Prod.ext executed retained
  unfold NativeGoldLookupVerification.prepare
  rw [paired]
  dsimp only
  rw [packed]
  exact ⟨⟨body,plan,after,metadata,query⟩,rfl⟩

theorem batches_dispatch_available {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (prepared : Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress result) :
    NativeDeferredBatchDomain.OutcomeAvailable result := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress result executed
  have corresponding := prepared_registry ctx chooseHelper memory world prepared origin.1
  have keys := NativeGoldLookupVerification.source_registry ctx prepared world
  rw [origin.2.1] at keys
  have sources : progress.state.sources.val.length = ctx.registry.val.length := by
    change progress.state.sources = prepared.metadata.sources at keys
    rw [keys]
    exact corresponding.length_eq.symm
  rw [← origin.2.2.1]
  exact NativeDeferredBatchDomain.program_available (NativeGoldLookupVerification.batchContext ctx progress) chooseBatch prepared.helpers.memory world sources

/-- Every used original source has an actual inserted raw claim, with the
same guarded query and complete original-registry key. Alias values are
compared in the field; their transcript spelling is not normalized. -/
theorem batches_source_claims {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (prepared : Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress result)
    (slot : Fin ctx.registry.val.length) (used : NativeSharedSourceClaims.used ctx.requests slot = true) :
    ∃ (claim : NativeDeferredOpeningBatch.Claim progress.state.sources) (row : NativeLookupRequestWire.Row)
      (digest : NativeRootMessage.Digest) (keySlot : Fin prepared.metadata.sources.val.length),
      claim ∈ progress.state.claims.val ∧ claim.query = prepared.query ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (ctx.registry.val.get slot).parameters) world).run.1 = some digest ∧
      ctx.proof.sources.val[slot.val]? = some row ∧ NativeGoldPcsClaim.equal claim.values.val row.val = true ∧
      keySlot.val = claim.slot.val ∧ prepared.metadata.sources.val.get keySlot = (digest,(ctx.registry.val.get slot).root) ∧
      claim.slot.val ≤ slot.val := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress result executed
  have recorded := (batches_source_available ctx chooseHelper chooseBatch memory world prepared progress result executed).2.2.1
  obtain ⟨digest,row,previous,computed,found,seen,key,equal,bounded⟩ := NativeSourceClaimInvariant.program_covers
    NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query ctx.proof.sources (NativeGoldLookupVerification.initial prepared)
    world progress origin.2.1 slot used
  have memberView : NativeSourceClaimInvariant.seenView prepared.query previous ∈ progress.seen.map (NativeSourceClaimInvariant.seenView prepared.query) :=
    List.mem_map.mpr ⟨previous,seen,rfl⟩
  unfold NativeSourceClaimInvariant.Recorded at recorded
  rw [← recorded] at memberView
  obtain ⟨claim,claimMember,view⟩ := List.mem_map.mp memberView
  have index := congrArg Prod.fst view
  have entries := congrArg Prod.snd view
  have queryEq := congrArg Prod.fst entries
  have valuesEq := congrArg Prod.snd entries
  dsimp only [NativeSourceClaimInvariant.claimView,NativeSourceClaimInvariant.seenView] at index queryEq valuesEq
  have previousMember : previous ∈ (run (sourceProgram ctx prepared) world).run.1.progress.seen := by
    rw [origin.2.1]
    exact seen
  obtain ⟨keySlot,keyIndex,keyComputed⟩ := source_key ctx chooseHelper memory world prepared origin.1 previous previousMember
  refine ⟨claim,row,digest,keySlot,claimMember,queryEq,computed,found,?_,keyIndex.trans index.symm,keyComputed.trans key,?_⟩
  · rw [valuesEq]
    exact equal
  · rw [index]
    exact bounded
end
end FormalProof4FHE.HasteBoots.NativeGoldLookupSourceInvariant
