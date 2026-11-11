module
public import FormalProof4FHE.HasteBoots.CheckedPcsMetadataSize
public import FormalProof4FHE.HasteBoots.NativeGoldLookupFraming
@[expose] public section

/-! Actual completed helper calls supply their checked metadata domains.
Append-only trace invariants recover the parent of every original helper
receipt, using original caller framing and decoded proof allocation bounds. -/
namespace FormalProof4FHE.HasteBoots.HelperReceiptFramingRecovery
open NativeGoldHelperVerification (Context Progress Result Trace)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldBlockCode (Tables Stored)
open NativeBrakedownContext (Parameters)
open NativeTranscriptFraming (Framed)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def ValidProgress (tables : Tables) (parameters : Parameters Stored) (fieldFuel : ℕ)
    {Memory : Type} (progress : Progress Memory) : Prop :=
  Framed progress.lastAccepted ∧ ∀ receipt ∈ progress.receipts,
    SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context tables parameters fieldFuel receipt.before receipt.call)

theorem trace_framed {Memory : Type} {tables : Tables} {parameters : Parameters Stored} {fieldFuel : ℕ}
    {choose : NativeGoldPcsProgram.Scheduler Memory} {workerFuel : ℕ} {world : World}
    {calls : List (NativeSharedLookupHelpers.Call NativeGoldPcsOpening.Opening)} {before : Progress Memory}
    {result : Result Memory} {log : List NativeTranscript.Observation}
    (trace : Trace tables parameters fieldFuel choose workerFuel world calls before result log)
    (domain : NativeGoldHelperFraming.Domain calls) (valid : ValidProgress tables parameters fieldFuel before) :
    ValidProgress tables parameters fieldFuel result.progress := by
  revert domain valid
  induction trace with
  | done before => intro _ valid; exact valid
  | stopped before call rest outcome log executed stopped => intro _ valid; exact valid
  | passed before after call rest outcome log result later executed advanced tail ih =>
    intro domain valid
    have fits := domain call (by simp)
    obtain ⟨work,completion,next,sameOutcome,accepted,sameAfter⟩ :=
      NativeGoldHelperVerification.advance_spec before call outcome after advanced
    have completed := (congrArg Prod.fst executed).trans sameOutcome
    have extension := NativeGoldPcsTranscriptExtension.accepted
      (NativeGoldHelperVerification.context tables parameters fieldFuel before.lastAccepted call) choose workerFuel before.memory world
      work completion completed next accepted fits
    have validAfter : ValidProgress tables parameters fieldFuel after := by
      rw [sameAfter]
      constructor
      · exact NativeTranscriptFraming.of_extension valid.1 extension
      · intro receipt member
        rcases List.mem_append.mp member with old | added
        · exact valid.2 receipt old
        · obtain rfl := List.mem_singleton.mp added
          obtain ⟨frames,bytes,framed⟩ := valid.1
          exact ⟨frames,bytes,framed,fits.1⟩
    exact ih (fun call member => domain call (List.mem_cons_of_mem _ member)) validAfter

theorem registry_upper (sources : Vector NativeCanonicalLookupWire.Source)
    (fits : (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit) :
    9+128*sources.val.length < TranscriptFrame.lengthLimit := by
  have body : (sources.val.flatMap (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2)).length = 128*sources.val.length := by
    induction sources.val with
    | nil => rfl
    | cons entry tail ih => simp only [List.flatMap_cons,List.length_append,List.length_ofFn,List.length_cons,ih]; omega
  rw [NativeCanonicalLookupWire.sources_encode,List.length_append,body] at fits
  norm_num [TranscriptFrame.lengthLimit] at fits ⊢
  omega

theorem receipt_metadata_fits {Memory : Type} (tables : Tables) (parameters : Parameters Stored)
    (fieldFuel : ℕ) (choose : NativeGoldPcsProgram.Scheduler Memory) (workerFuel : ℕ) (world : World)
    (receipt : NativeGoldHelperVerification.Receipt Memory)
    (checked : NativeGoldHelperVerification.Checked tables parameters fieldFuel choose workerFuel world receipt)
    (width : parameters.width.val ≤ 4) :
    (NativeGoldPcsWire.opening receipt.call.root receipt.call.query receipt.call.values).length < TranscriptFrame.lengthLimit :=
  CheckedPcsMetadataSize.completed_fits
    (NativeGoldHelperVerification.context tables parameters fieldFuel receipt.before receipt.call)
    choose workerFuel receipt.memory world receipt.work receipt.completion checked.1 width

variable {Memory : Type} (ctx : Context (Vector Opening))
  (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
  (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
  (progress : NativeSharedSourceClaims.Progress) (after : NativeDeferredBatchVerification.Progress Memory)
  (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
    .batches lookup progress (.verification (.done after)))

include executed

theorem call_domain (width : ctx.helper.width.val ≤ 4) (proofDomain : SharedProofSerializationDomain.Domain ctx.proof) :
    NativeGoldHelperFraming.Domain lookup.plan.calls := by
  have helpers := OpeningReceiptProofSource.helper_execution ctx chooseHelper chooseBatch memory world lookup progress after executed
  have order := (NativeGoldHelperVerification.helpers_order ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers helpers).1
  intro call member
  rw [← order] at member
  obtain ⟨receipt,receiptMember,same⟩ := List.mem_map.mp member
  subst call
  have checked := (NativeGoldHelperVerification.helpers_receipts ctx chooseHelper memory world lookup.body lookup.plan (.done lookup.helpers) helpers receipt receiptMember).1
  refine ⟨?_,?_⟩
  · exact receipt_metadata_fits ctx.tables ctx.helper ctx.fieldFuel chooseHelper ctx.workerFuel world receipt checked width
  · exact proofDomain.helperResponses receipt.call.opening
      (OpeningReceiptProofSource.helper_members ctx chooseHelper chooseBatch memory world lookup progress after executed receipt receiptMember)

theorem body_framed (framed : Framed ctx.parent)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit)
    (proofDomain : SharedProofSerializationDomain.Domain ctx.proof) : Framed lookup.body.parent := by
  have helpers := OpeningReceiptProofSource.helper_execution ctx chooseHelper chooseBatch memory world lookup progress after executed
  have origin := NativeGoldHelperVerification.helpers_origin ctx chooseHelper memory world lookup.body lookup.plan (.done lookup.helpers) helpers
  have native := origin.native
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] at native
  have completed := congrArg Prod.fst native
  change (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1 = some (.bound lookup.body) at completed
  obtain ⟨sources,computed,_⟩ := NativeRegistryAncestry.bound_registration NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body completed
  have fits := registry_upper sources (registryFits sources computed)
  rw [NativeCanonicalMessageBounds.contexts_length NativeGoldBlockCode.description.row ctx.registry.val world sources.val computed] at fits
  have prepared := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) executed).1
  exact NativeLookupBodyFraming.prepared_body ctx chooseHelper memory world lookup prepared framed
    ⟨parentDomain,fits,proofDomain.groupedFits,proofDomain.flatFits⟩

theorem receipts_framed (width : ctx.helper.width.val ≤ 4) (framed : Framed ctx.parent)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit)
    (proofDomain : SharedProofSerializationDomain.Domain ctx.proof) :
    ValidProgress ctx.tables ctx.helper ctx.fieldFuel lookup.helpers := by
  have helpers := OpeningReceiptProofSource.helper_execution ctx chooseHelper chooseBatch memory world lookup progress after executed
  have origin := NativeGoldHelperVerification.helpers_origin ctx chooseHelper memory world lookup.body lookup.plan (.done lookup.helpers) helpers
  have trace := NativeGoldHelperVerification.loop_trace ctx.tables ctx.helper ctx.fieldFuel chooseHelper ctx.workerFuel lookup.plan.calls
    ⟨lookup.body.parent,memory,[]⟩ world
  rw [origin.helpers] at trace
  exact trace_framed trace (call_domain ctx chooseHelper chooseBatch memory world lookup progress after executed width proofDomain)
    ⟨body_framed ctx chooseHelper chooseBatch memory world lookup progress after executed framed parentDomain registryFits proofDomain,by simp⟩

end
end FormalProof4FHE.HasteBoots.HelperReceiptFramingRecovery
