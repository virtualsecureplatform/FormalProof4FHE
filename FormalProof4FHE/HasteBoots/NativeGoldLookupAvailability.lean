module

public import FormalProof4FHE.HasteBoots.NativeGoldLookupSourceInvariant
public import FormalProof4FHE.HasteBoots.NativeDeferredBatchAvailability
@[expose] public section

/-! The whole registered Goldilocks lookup supplies deferred receipts, exact first-original metadata keys and frozen raw source equations. Stopped later dispatches retain earlier accepted receipts. Framing and allocation domains remain explicit; application soundness, lineage and physical work remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupAvailability
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeGoldLookupVerification (Prepared program batchContext)
open NativeDeferredBatchVerification (Receipt Result)
open NativeGoldBatchPcsProgram (Scheduler)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory
open NativeGoldBatchSourceRisk (Framed)
open NativeGoldBatchAnySourceRisk (HasSource)
open NativeGoldBatchFamilyAvailability (reconstructed)
open NativeMerkleShapeFamily (shape)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem batch_log_sublist {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress result) :
    (run (NativeDeferredBatchVerification.program (batchContext ctx progress) chooseBatch prepared.helpers.memory) world).run.2.Sublist
      (run (program ctx chooseHelper chooseBatch memory) world).run.2 := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress result executed
  rw [origin.2.2.2]
  exact (List.sublist_append_right _ _).trans (List.sublist_append_right _ _)

theorem batch_sources {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress result) :
    progress.state.sources = prepared.metadata.sources := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress result executed
  have sources := NativeGoldLookupVerification.source_registry ctx prepared world
  rw [origin.2.1] at sources
  exact sources

/-- Each dispatched receipt uses the earliest original complete context/root
key, even when that earlier registry slot was unused by source collection. -/
theorem receipt_owner_key {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts) :
    ∃ slot : Fin prepared.metadata.sources.val.length,
      slot.val = receipt.call.slot ∧ ctx.registry.val[slot.val]? = some receipt.call.oracle ∧
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row receipt.call.oracle.parameters) world).run.1 =
        some (prepared.metadata.sources.val.get slot).1 ∧
      receipt.call.oracle.root = (prepared.metadata.sources.val.get slot).2 ∧
      ∀ earlier : Fin prepared.metadata.sources.val.length, earlier.val < slot.val →
        prepared.metadata.sources.val.get earlier ≠ prepared.metadata.sources.val.get slot := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  have corresponding := NativeGoldLookupSourceInvariant.prepared_registry ctx chooseHelper memory world prepared origin.1
  have sources := batch_sources ctx chooseHelper chooseBatch memory world prepared progress _ executed
  have owned := NativeDeferredBatchOwnership.program_owners (batchContext ctx progress) chooseBatch prepared.helpers.memory world result origin.2.2.1 receipt member
  obtain ⟨group,_,slotEq,found,_,_,first⟩ := NativeDeferredBatchOwnership.original_spec ctx.registry progress.state receipt.call owned
  let owner := NativeSourceRegistry.representative progress.state.sources group
  let slot : Fin prepared.metadata.sources.val.length := ⟨owner.val,by rw [← sources]; exact owner.isLt⟩
  let original : Fin ctx.registry.val.length := ⟨slot.val,by rw [corresponding.length_eq]; exact slot.isLt⟩
  have originalFound : ctx.registry.val[original.val]? = some receipt.call.oracle := by
    change ctx.registry.val[owner.val]? = some receipt.call.oracle
    rw [← slotEq]
    exact found
  have oracleEq : ctx.registry.val.get original = receipt.call.oracle := by
    apply Option.some.inj
    simpa only [List.get_eq_getElem] using (List.getElem?_eq_getElem original.isLt).symm.trans originalFound
  have relation := corresponding.get original.isLt slot.isLt
  refine ⟨slot,slotEq.symm,originalFound,?_,?_,?_⟩
  · rw [← oracleEq]
    exact relation.1
  · rw [← oracleEq]
    exact relation.2.symm
  · intro earlier before
    let prior : Fin progress.state.sources.val.length := ⟨earlier.val,by rw [sources]; exact earlier.isLt⟩
    have different := first prior (by rw [slotEq]; exact before)
    intro same
    have indexEq : owner.val = receipt.call.slot := slotEq.symm
    have equalOptions : progress.state.sources.val[prior.val]? = progress.state.sources.val[owner.val]? := by
      change progress.state.sources.val[earlier.val]? = progress.state.sources.val[owner.val]?
      rw [indexEq,sources,← indexEq]
      simpa only [List.getElem?_eq_getElem earlier.isLt,List.getElem?_eq_getElem (show owner.val < prepared.metadata.sources.val.length from slot.isLt),List.get_eq_getElem] using congrArg some same
    apply different
    apply Option.some.inj
    simpa only [List.getElem?_eq_getElem prior.isLt,List.getElem?_eq_getElem owner.isLt,List.get_eq_getElem] using equalOptions

/-- The full typed registered lookup program supplies every batch receipt's
original owner, raw claims and actual source witness in its enclosing history. -/
theorem receipt_source {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (noBad : ¬CheckpointCollision.Bad shape (reconstructed dummy history)) :
    NativeDeferredBatchOwnership.OriginalCall ctx.registry progress.state receipt.call ∧
      receipt.work.root = receipt.call.oracle.root ∧ receipt.work.width = receipt.call.oracle.parameters.width.val ∧
      receipt.work.binding.queries = receipt.call.queries ∧ receipt.work.binding.values = receipt.call.values ∧
      HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  exact NativeDeferredBatchAvailability.receipt_source dummy (batchContext ctx progress) chooseBatch prepared.helpers.memory world result
    origin.2.2.1 history truthful ((batch_log_sublist ctx chooseHelper chooseBatch memory world prepared progress _ executed).trans observed)
    receipt member framed noBad

/-- The actual frozen raw source is tagged by the complete key of the
first original owner, not by a newly selected equal-root parameter object. -/
theorem receipt_owned_source {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (noBad : ¬CheckpointCollision.Bad shape (reconstructed dummy history)) :
    ∃ (slot : Fin prepared.metadata.sources.val.length)
      (requests : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request NativeMerkleShapeFamily.height))
      (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest),
      slot.val = receipt.call.slot ∧ receipt.work.root = (prepared.metadata.sources.val.get slot).2 ∧
      NativeGoldBatchFamilyRequests.prepare (prepared.metadata.sources.val.get slot).1 receipt.work = some requests ∧
      (∀ index : NativeMerkleShapeFamily.Height,
        ⟨((prepared.metadata.sources.val.get slot).1,index),⟨(prepared.metadata.sources.val.get slot).2,log⟩⟩ ∈
          (reconstructed dummy history).checkpoints.checkpoints) ∧
      ∀ entry ∈ requests,
        entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy NativeMerkleShapeFamily.height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position ∧
        NativeGoldBatchRawAvailability.Equations (NativeGoldBatchRawAvailability.view receipt.work requests)
          (NativeGoldRawAvailability.frozenValue dummy NativeMerkleShapeFamily.height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position) entry.2.position.val := by
  obtain ⟨slot,slotEq,_,keyHash,keyRoot,_⟩ := receipt_owner_key ctx chooseHelper chooseBatch memory world prepared progress result executed receipt member
  obtain ⟨_,root,_,_,_,context,requests,log,hashed,computed,snapshots,checks⟩ :=
    receipt_source dummy ctx chooseHelper chooseBatch memory world prepared progress result executed history truthful observed receipt member framed noBad
  have same : context = (prepared.metadata.sources.val.get slot).1 := Option.some.inj (hashed.symm.trans keyHash)
  have rootEq := root.trans keyRoot
  rw [same] at computed
  rw [same,rootEq] at snapshots
  exact ⟨slot,requests,log,slotEq,rootEq,computed,snapshots,checks⟩

def Failure {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (history : List Observation) (world : World) : Prop :=
  ∃ (prepared : Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : Result Memory) (receipt : Receipt Memory),
    (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result) ∧
    receipt ∈ result.progress.receipts ∧ Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) ∧
    ¬HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world

theorem failure_implies_any {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (history : List Observation) (world : World)
    (observed : (run (program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (failed : Failure dummy ctx chooseHelper chooseBatch memory history world) : NativeGoldBatchAnySourceRisk.Failure Memory dummy history world := by
  obtain ⟨prepared,progress,result,receipt,executed,member,framed,missing⟩ := failed
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  exact NativeDeferredBatchAvailability.failure_implies_any dummy (batchContext ctx progress) chooseBatch prepared.helpers.memory history world
    ((batch_log_sublist ctx chooseHelper chooseBatch memory world prepared progress _ executed).trans observed)
    ⟨result,receipt,origin.2.2.1,member,framed,missing⟩

theorem failure_replay {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (history : List Observation) (world other : World)
    (observed : (run (program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (agrees : ObservationReplay.Agrees other history)
    (failed : Failure dummy ctx chooseHelper chooseBatch memory history world) :
    Failure dummy ctx chooseHelper chooseBatch memory history other := by
  obtain ⟨prepared,progress,result,receipt,executed,member,framed,missing⟩ := failed
  have same := (OracleProgram.run_replay (program ctx chooseHelper chooseBatch memory)).replay world other
    (fun entry present => agrees entry (observed.subset present))
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  have accepted := NativeDeferredBatchAvailability.receipt_accepted (batchContext ctx progress) chooseBatch prepared.helpers.memory world result
    origin.2.2.1 history ((batch_log_sublist ctx chooseHelper chooseBatch memory world prepared progress _ executed).trans observed) receipt member framed
  have sameContext := NativeGoldBatchAnySourceRisk.accepted_context_replay world other history agrees
    (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) chooseBatch ctx.workerFuel receipt.memory receipt.work accepted
  refine ⟨prepared,progress,result,receipt,?_,member,framed,?_⟩
  · rw [same]; exact executed
  · rintro ⟨context,requests,log,hashed,computed,snapshots,checks⟩
    exact missing ⟨context,requests,log,by rw [← sameContext]; exact hashed,computed,snapshots,checks⟩

theorem failure_le_charge {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) :
    InputIndexedOracle.law {world | Failure dummy ctx chooseHelper chooseBatch memory (run (program ctx chooseHelper chooseBatch memory) world).run.2 world} ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (CheckpointCollision.loss unifSpec shape)
        ((NativeRootFamilyFreeze.compile NativeParentLedger.empty (program ctx chooseHelper chooseBatch memory)).run NativeShakeCache.empty)
        (CheckpointExecution.empty shape) := by
  have included : {world | Failure dummy ctx chooseHelper chooseBatch memory (run (program ctx chooseHelper chooseBatch memory) world).run.2 world} ⊆
      {world | NativeGoldBatchAnySourceRisk.Failure Memory dummy (run (program ctx chooseHelper chooseBatch memory) world).run.2 world} :=
    fun world failed => failure_implies_any dummy ctx chooseHelper chooseBatch memory _ world (List.Sublist.refl _) failed
  exact (measure_mono included).trans (NativeGoldBatchAnySourceRisk.failure_le_charge Memory dummy (program ctx chooseHelper chooseBatch memory))
end
end FormalProof4FHE.HasteBoots.NativeGoldLookupAvailability
