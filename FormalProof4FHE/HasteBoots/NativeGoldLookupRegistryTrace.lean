module
public import FormalProof4FHE.HasteBoots.NativeGoldLookupVerification
public import FormalProof4FHE.HasteBoots.NativeRegistryContextTrace
@[expose] public section

/-! The actual registered preparation and original initializer occur in the
same enclosing native lookup trace, including receipts retained when later
batches stop. No independently supplied initializer log is needed. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupRegistryTrace
open InputIndexedOracle (World)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldLookupVerification (Prepared program)
open OracleProgram (Program bind run)
noncomputable section

theorem bind_log {A B : Type} (first : Program A) (next : A → Program B) (world : World) :
    (run first world).run.2.Sublist (run (bind first next) world).run.2 := by
  simp only [OracleProgram.run_bind,ObservationReplay.run_bind]
  exact List.sublist_append_left _ _

theorem prepare_initializer {C : Type} (row : NativeBrakedownContext.RowDescription C)
    (registry : Vector (NativeSharedLookupParent.Oracle C)) (helper : NativeBrakedownContext.Parameters C)
    (parent : NativeTranscript.Transcript) (requests : Vector NativeLookupRequestWire.Request) (world : World)
    (geometry : NativeSharedLookupPreflight.Output) (metadata : NativeSourceRegistry.Initialized)
    (executed : (run (NativeRegisteredLookup.prepare row registry helper parent requests) world).run.1.2 = some (geometry,metadata)) :
    (run (NativeSourceRegistry.startRegistry row registry
      (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.2.Sublist
      (run (NativeRegisteredLookup.prepare row registry helper parent requests) world).run.2 := by
  have origin := NativeRegisteredLookup.prepare_origin row registry helper parent requests world geometry metadata executed
  simp only [NativeRegisteredLookup.prepare,OracleProgram.run_bind,ObservationReplay.run_bind,origin.2.2,
    origin.1,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
  exact List.sublist_append_right _ _

theorem helpers_preparation {B Memory : Type} (ctx : NativeGoldHelperVerification.Context B)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World) :
    (run (NativeRegisteredLookup.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.2.Sublist
      (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.2 := by
  have prepared : (run (NativeRegisteredLookup.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.2.Sublist
      (run (NativeRegisteredLookup.begin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel) world).run.2 :=
    bind_log _ _ world
  have began : (run (NativeRegisteredLookup.begin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel) world).run.2.Sublist
      (run (NativeRegisteredLookup.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.2 :=
    bind_log _ _ world
  exact prepared.trans (began.trans (bind_log _ _ world))

theorem lookup_preparation {Memory : Type} (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) :
    (run (NativeRegisteredLookup.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.2.Sublist
      (run (program ctx chooseHelper chooseBatch memory) world).run.2 :=
  (helpers_preparation ctx chooseHelper memory world).trans (bind_log _ _ world)

theorem lookup_initializer {Memory : Type} (ctx : NativeGoldHelperVerification.Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress result) :
    (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row ctx.registry
      (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1) world).run.1 = some prepared.metadata ∧
    (run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row ctx.registry
      (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1) world).run.2.Sublist
      (run (program ctx chooseHelper chooseBatch memory) world).run.2 := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress result executed
  obtain ⟨geometry,registered⟩ := NativeGoldLookupVerification.prepared_metadata ctx chooseHelper memory world prepared origin.1
  exact ⟨(NativeRegisteredLookup.prepare_origin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests
      world geometry prepared.metadata registered).1,
    (prepare_initializer NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests world geometry prepared.metadata registered).trans
      (lookup_preparation ctx chooseHelper chooseBatch memory world)⟩

end
end FormalProof4FHE.HasteBoots.NativeGoldLookupRegistryTrace
