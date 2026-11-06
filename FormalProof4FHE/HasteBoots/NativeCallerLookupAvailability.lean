module

public import FormalProof4FHE.HasteBoots.NativeFramedDeferredAvailability
@[expose] public section

/-! Whole-lookup source failure bounds with framing derived from the original
caller parent. Message allocation domains remain explicit. Neither the event
nor the caller supplies intermediate or per-receipt framing certificates. -/
namespace FormalProof4FHE.HasteBoots.NativeCallerLookupAvailability
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
open NativeGoldBatchAnySourceRisk (HasSource)
open NativeMerkleShapeFamily (shape)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- Original caller framing and serialized-message domains, with no framing
predicate on a future intermediate state or accepted receipt. -/
def Domain {Memory : Type} (ctx : Context (Vector Opening)) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) : Prop :=
  NativeTranscriptFraming.Framed ctx.parent ∧
  NativeLookupBodyFraming.Domain ctx.registry ctx.requests ctx.proof ∧
  NativeGoldHelperFraming.Domain prepared.plan.calls ∧
  NativeSourceClaimFraming.Domain ctx.registry ctx.requests prepared.query ctx.proof.sources ∧
  NativeDeferredBatchFraming.Domain (batchContext ctx progress)

theorem receipt_framed {Memory : Type} (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (domain : Domain ctx prepared progress) (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts) :
    NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  have body := NativeLookupBodyFraming.prepared_body ctx chooseHelper memory world prepared origin.1 domain.1 domain.2.1
  have helper := NativeGoldHelperFraming.prepared_framed ctx chooseHelper memory world prepared origin.1 body domain.2.2.1
  have source := NativeSourceClaimFraming.program_framed NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query ctx.proof.sources
    (NativeGoldLookupVerification.initial prepared) world helper domain.2.2.2.1
  change NativeTranscriptFraming.Framed (run (NativeGoldLookupVerification.sourceProgram ctx prepared) world).run.1.progress.state.parent at source
  rw [origin.2.1] at source
  exact NativeDeferredBatchFraming.receipt_framed (batchContext ctx progress) chooseBatch prepared.helpers.memory world result origin.2.2.1 source domain.2.2.2.2 receipt member

/-- A missing frozen source of an actual emitted receipt. Static allocation
domains describe the native execution domain, not an extra verifier gate. -/
def Failure {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (history : List Observation) (world : World) : Prop :=
  ∃ (prepared : Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : Result Memory) (receipt : Receipt Memory),
    (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result) ∧
    Domain ctx prepared progress ∧ receipt ∈ result.progress.receipts ∧
    ¬HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world

theorem failure_implies_framed {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (history : List Observation) (world : World)
    (failed : Failure dummy ctx chooseHelper chooseBatch memory history world) :
    NativeGoldLookupAvailability.Failure dummy ctx chooseHelper chooseBatch memory history world := by
  obtain ⟨prepared,progress,result,receipt,executed,domain,member,missing⟩ := failed
  exact ⟨prepared,progress,result,receipt,executed,member,
    receipt_framed ctx chooseHelper chooseBatch memory world prepared progress result executed domain receipt member,missing⟩

theorem failure_implies_any {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (history : List Observation) (world : World)
    (observed : (run (program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (failed : Failure dummy ctx chooseHelper chooseBatch memory history world) : NativeGoldBatchAnySourceRisk.Failure Memory dummy history world :=
  NativeGoldLookupAvailability.failure_implies_any dummy ctx chooseHelper chooseBatch memory history world observed
    (failure_implies_framed dummy ctx chooseHelper chooseBatch memory history world failed)

theorem failure_replay {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (history : List Observation) (world other : World)
    (observed : (run (program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (agrees : ObservationReplay.Agrees other history)
    (failed : Failure dummy ctx chooseHelper chooseBatch memory history world) :
    Failure dummy ctx chooseHelper chooseBatch memory history other := by
  obtain ⟨prepared,progress,result,receipt,executed,domain,member,missing⟩ := failed
  have same := (OracleProgram.run_replay (program ctx chooseHelper chooseBatch memory)).replay world other
    (fun entry present => agrees entry (observed.subset present))
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  have framed := receipt_framed ctx chooseHelper chooseBatch memory world prepared progress result executed domain receipt member
  have accepted := NativeDeferredBatchAvailability.receipt_accepted (batchContext ctx progress) chooseBatch prepared.helpers.memory world result
    origin.2.2.1 history ((NativeGoldLookupAvailability.batch_log_sublist ctx chooseHelper chooseBatch memory world prepared progress _ executed).trans observed) receipt member framed
  have sameContext := NativeGoldBatchAnySourceRisk.accepted_context_replay world other history agrees
    (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) chooseBatch ctx.workerFuel receipt.memory receipt.work accepted
  refine ⟨prepared,progress,result,receipt,?_,domain,member,?_⟩
  · rw [same]; exact executed
  · rintro ⟨context,requests,log,hashed,computed,snapshots,checks⟩
    exact missing ⟨context,requests,log,by rw [← sameContext]; exact hashed,computed,snapshots,checks⟩

def HistoryFailure {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) (history : List Observation) : Prop :=
  ∃ world, (run (program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history ∧
    Failure dummy ctx chooseHelper chooseBatch memory history world

theorem failure_measurable {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) :
    MeasurableSet {world | Failure dummy ctx chooseHelper chooseBatch memory (run (program ctx chooseHelper chooseBatch memory) world).run.2 world} := by
  have same : {world | Failure dummy ctx chooseHelper chooseBatch memory (run (program ctx chooseHelper chooseBatch memory) world).run.2 world} =
      {world | HistoryFailure dummy ctx chooseHelper chooseBatch memory (run (program ctx chooseHelper chooseBatch memory) world).run.2} := by
    ext world
    constructor
    · intro failed; exact ⟨world,List.Sublist.refl _,failed⟩
    · rintro ⟨other,observed,failed⟩
      exact failure_replay dummy ctx chooseHelper chooseBatch memory _ other world observed
        ((OracleProgram.run_replay (program ctx chooseHelper chooseBatch memory)).truthful world) failed
  rw [same]
  exact OracleExecutionLaw.event_measurable (OracleProgram.run_replay (program ctx chooseHelper chooseBatch memory))
    (fun packet => HistoryFailure dummy ctx chooseHelper chooseBatch memory packet.2)

theorem failure_le_charge {Memory : Type} (dummy : Digest) (ctx : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : Scheduler Memory) (memory : Memory) :
    InputIndexedOracle.law {world | Failure dummy ctx chooseHelper chooseBatch memory (run (program ctx chooseHelper chooseBatch memory) world).run.2 world} ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (CheckpointCollision.loss unifSpec shape)
        ((NativeRootFamilyFreeze.compile NativeParentLedger.empty (program ctx chooseHelper chooseBatch memory)).run NativeShakeCache.empty)
        (CheckpointExecution.empty shape) := by
  exact (measure_mono (fun world failed => failure_implies_framed dummy ctx chooseHelper chooseBatch memory _ world failed)).trans
    (NativeGoldLookupAvailability.failure_le_charge dummy ctx chooseHelper chooseBatch memory)
end
end FormalProof4FHE.HasteBoots.NativeCallerLookupAvailability
