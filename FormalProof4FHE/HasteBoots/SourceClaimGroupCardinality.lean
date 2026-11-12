module
public import FormalProof4FHE.HasteBoots.ParentDerivedIdentityWork
public import FormalProof4FHE.HasteBoots.NativeSourceClaimInvariant
@[expose] public section

/-! Collector uniqueness applies to full context/root keys, not roots alone.
The original recorded slots therefore place at most one inserted claim in
each canonical group. This is an execution invariant, not a count cutoff. -/
namespace FormalProof4FHE.HasteBoots.SourceClaimGroupCardinality
open NativeCanonicalLookupWire (Source)
open NativePrefixCodec (Vector)
open NativeDeferredOpeningBatch (Claim State groupClaims)
open NativeSharedSourceClaims (Progress Seen)
open NativeGoldPcsWire (Query)

def claimKey {sources : Vector Source} (claim : Claim sources) : Source := sources.val.get claim.slot

theorem keys_nodup (query : Query) (progress : Progress)
    (recorded : NativeSourceClaimInvariant.Recorded query progress)
    (unique : NativeSourceClaimInvariant.Unique progress)
    (represented : ∀ previous ∈ progress.seen, progress.state.sources.val[previous.slot]? = some previous.key) :
    (progress.state.claims.val.map claimKey).Nodup := by
  have slots := congrArg (List.map (fun view : ℕ × Query × NativeLookupRequestWire.Row =>
    progress.state.sources.val[view.1]?)) recorded
  have same : (progress.state.claims.val.map claimKey).map some = (progress.seen.map Seen.key).map some := by
    calc
      _ = progress.state.claims.val.map (fun claim => progress.state.sources.val[claim.slot.val]?) := by
        simp only [List.map_map,Function.comp_def]
        apply List.map_congr_left
        intro claim _
        simp only [claimKey,List.get_eq_getElem,List.getElem?_eq_getElem claim.slot.isLt]
      _ = progress.seen.map (fun previous => progress.state.sources.val[previous.slot]?) := by
        simpa only [List.map_map,Function.comp_def,NativeSourceClaimInvariant.claimView,NativeSourceClaimInvariant.seenView] using slots
      _ = _ := by
        simp only [List.map_map,Function.comp_def]
        exact List.map_congr_left represented
  have mapped : ((progress.state.claims.val.map claimKey).map some).Nodup := by
    rw [same]
    exact unique.map (Option.some_injective Source)
  exact mapped.of_map some

theorem group_le_one (state : State) (unique : (state.claims.val.map claimKey).Nodup)
    (group : Fin (NativeSourceRegistry.groupCount state.sources)) : (groupClaims state group).length ≤ 1 := by
  have sub : (groupClaims state group).Sublist state.claims.val := List.filter_sublist
  have nodup : ((groupClaims state group).map claimKey).Nodup := unique.sublist (sub.map claimKey)
  have belongs : ∀ claim ∈ groupClaims state group, NativeSourceRegistry.group state.sources claim.slot = group := by
    intro claim member
    exact beq_iff_eq.mp (List.mem_filter.mp member).2
  cases entries : groupClaims state group with
  | nil => simp
  | cons first tail =>
    cases tail with
    | nil => simp
    | cons second rest =>
      have firstGroup := belongs first (by rw [entries]; simp)
      have secondGroup := belongs second (by rw [entries]; simp)
      have equal := (NativeSourceRegistry.group_eq_iff state.sources first.slot second.slot).mp (firstGroup.trans secondGroup.symm)
      have same : claimKey first = claimKey second := Prod.ext equal.1 equal.2
      rw [entries,List.map_cons,List.map_cons] at nodup
      have distinct := (List.nodup_cons.mp nodup).1
      exact False.elim (distinct (by rw [same]; exact List.mem_cons_self))

theorem represented_of_origins {C : Type} (description : NativeBrakedownContext.RowDescription C)
    (registry : Vector (NativeSharedLookupParent.Oracle C)) (requests : Vector NativeLookupRequestWire.Request)
    (values : Vector NativeLookupRequestWire.Row) (world : InputIndexedOracle.World) (progress : Progress)
    (computed : List.Forall₂ (fun entry source =>
      (OracleProgram.run (NativeBrakedownContext.context description entry.parameters) world).run.1 = some source.1 ∧ source.2 = entry.root)
      registry.val progress.state.sources.val)
    (origins : ∀ previous ∈ progress.seen, NativeSourceClaimInvariant.Origin description registry requests values world previous) :
    ∀ previous ∈ progress.seen, progress.state.sources.val[previous.slot]? = some previous.key := by
  intro previous member
  obtain ⟨slot,position,_,known,root,_⟩ := origins previous member
  have inside : slot.val < progress.state.sources.val.length := by rw [← computed.length_eq]; exact slot.isLt
  have paired := computed.get slot.isLt inside
  have context : (OracleProgram.run (NativeBrakedownContext.context description registry.val[slot.val].parameters) world).run.1 = some previous.key.1 := by
    simpa only [List.get_eq_getElem] using known
  have rootEq : previous.key.2 = registry.val[slot.val].root := by simpa only [List.get_eq_getElem] using root
  have same : progress.state.sources.val[slot.val] = previous.key :=
    Prod.ext (Option.some.inj (paired.1.symm.trans context)) (paired.2.trans rootEq.symm)
  rw [position,List.getElem?_eq_getElem inside,same]

open NativeGoldHelperVerification (Context)
open NativeGoldBatchOpening (Opening)
open OracleProgram (run)

variable {Memory : Type} (ctx : Context (Vector Opening))
  (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
  (memory : Memory) (world : InputIndexedOracle.World) (lookup : NativeGoldLookupVerification.Prepared Memory)
  (progress : Progress) (after : NativeDeferredBatchVerification.Progress Memory)
  (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
    .batches lookup progress (.verification (.done after)))

include executed

theorem collected_keys_nodup : (progress.state.claims.val.map claimKey).Nodup := by
  have pipeline := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) executed
  have prepared := (NativeGoldLookupVerification.prepare_spec _ lookup pipeline.1).1
  obtain ⟨metadata,geometry,retained,registered⟩ := NativeRegisteredLookup.helpers_metadata ctx chooseHelper memory world lookup.body lookup.plan
    (.done lookup.helpers) (congrArg Prod.fst prepared)
  have same : metadata = lookup.metadata := Option.some.inj (retained.symm.trans (congrArg Prod.snd prepared))
  subst metadata
  have started := (NativeRegisteredLookup.prepare_origin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests world geometry lookup.metadata registered).1
  have metadataComputed := NativeSourceRegistry.initialized_sources NativeGoldBlockCode.description.row ctx.registry _ world lookup.metadata started
  have sources := NativeSharedSourceClaims.loop_sources NativeGoldBlockCode.description.row ctx.registry ctx.requests lookup.query ctx.proof.sources
    (List.finRange ctx.registry.val.length) ⟨NativeGoldLookupVerification.initial lookup,[]⟩ world
  change (run (NativeGoldLookupVerification.sourceProgram ctx lookup) world).run.1.progress.state.sources = lookup.metadata.sources at sources
  rw [pipeline.2.1] at sources
  change progress.state.sources = lookup.metadata.sources at sources
  rw [← sources] at metadataComputed
  have invariant := NativeSourceClaimInvariant.program_invariants NativeGoldBlockCode.description.row ctx.registry ctx.requests lookup.query ctx.proof.sources
    (NativeGoldLookupVerification.initial lookup) world rfl
  have sourceDone := pipeline.2.1
  change (run (NativeSharedSourceClaims.program NativeGoldBlockCode.description.row ctx.registry ctx.requests lookup.query ctx.proof.sources
    (NativeGoldLookupVerification.initial lookup)) world).run.1 = .done progress at sourceDone
  rw [sourceDone] at invariant
  exact keys_nodup lookup.query progress invariant.2.1 invariant.1
    (represented_of_origins NativeGoldBlockCode.description.row ctx.registry ctx.requests ctx.proof.sources world progress metadataComputed invariant.2.2.2)

theorem collected_group_le_one (group : Fin (NativeSourceRegistry.groupCount progress.state.sources)) :
    (groupClaims progress.state group).length ≤ 1 :=
  group_le_one progress.state (collected_keys_nodup ctx chooseHelper chooseBatch memory world lookup progress after executed) group

end FormalProof4FHE.HasteBoots.SourceClaimGroupCardinality
