module
public import FormalProof4FHE.HasteBoots.DecodedIdentityWork
@[expose] public section

/-! Original native receipt positions refer to the original proof opening
at the same position. Bounds for serialized packets can therefore be applied
to actual workers without independent response-size certificates. -/
namespace FormalProof4FHE.HasteBoots.OpeningReceiptProofSource
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open OracleProgram (run)

/-- A successful zip access retains the right vector's original address. -/
theorem zip_right_at {A B : Type} (left : List A) (right : List B) (position : ℕ) (pair : A × B)
    (found : (left.zip right)[position]? = some pair) : right[position]? = some pair.2 := by
  induction position generalizing left right with
  | zero =>
    cases left with
    | nil => simp at found
    | cons head tail =>
      cases right with
      | nil => simp at found
      | cons value rest =>
        simp only [List.zip_cons_cons,List.getElem?_cons_zero,Option.some.injEq] at found
        cases found
        rfl
  | succ position ih =>
    cases left with
    | nil => simp at found
    | cons head tail =>
      cases right with
      | nil => simp at found
      | cons value rest =>
        simp only [List.zip_cons_cons,List.getElem?_cons_succ] at found ⊢
        exact ih tail rest found

theorem calls_at {S : Type} (query : NativeGoldPcsWire.Query) (roots : List NativeRootMessage.Digest)
    (values : List NativeLookupRequestWire.Row) (openings : List S) (position : ℕ)
    (call : NativeSharedLookupHelpers.Call S)
    (found : (NativeSharedLookupHelpers.calls query roots values openings)[position]? = some call) :
    openings[position]? = some call.opening := by
  rw [NativeSharedLookupHelpers.calls,List.getElem?_map] at found
  obtain ⟨entry,entryAt,same⟩ := Option.map_eq_some_iff.mp found
  have original := zip_right_at _ _ position entry entryAt
  have opening := congrArg NativeSharedLookupHelpers.Call.opening same
  change entry.2 = call.opening at opening
  rw [opening] at original
  exact original

theorem batch_at {Memory : Type} (ctx : NativeDeferredBatchVerification.Context)
    (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (after : NativeDeferredBatchVerification.Progress Memory)
    (executed : (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.1 = .verification (.done after))
    (position : ℕ) (receipt : NativeDeferredBatchVerification.Receipt Memory)
    (found : after.receipts[position]? = some receipt) : ctx.proof.val[position]? = some receipt.call.opening := by
  have order := NativeDeferredBatchVerification.program_order ctx choose memory world after executed
  have atPair : (after.receipts.map (fun receipt => (receipt.call.group,receipt.call.opening)))[position]? =
      some (receipt.call.group,receipt.call.opening) := by
    rw [List.getElem?_map,found,Option.map_some]
  rw [order] at atPair
  exact zip_right_at _ _ position _ atPair

variable {Memory : Type} (ctx : Context (Vector Opening))
  (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
  (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
  (progress : NativeSharedSourceClaims.Progress) (after : NativeDeferredBatchVerification.Progress Memory)
  (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
    .batches lookup progress (.verification (.done after)))

include executed

theorem helper_execution :
    (run (NativeGoldHelperVerification.program ctx chooseHelper memory) world).run.1 =
      .helpers lookup.body lookup.plan (.done lookup.helpers) := by
  have prepared := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) executed).1
  have packet := congrArg Prod.fst (NativeGoldLookupVerification.prepare_spec _ lookup prepared).1
  have erased := congrArg Prod.fst (NativeRegisteredLookup.helpers_erasure ctx chooseHelper memory world)
  exact erased.symm.trans packet

theorem source_at (position : ℕ) (receipt : NativeDeferredBatchVerification.Receipt Memory)
    (found : after.receipts[position]? = some receipt) :
    ctx.proof.sourceOpening.val[position]? = some receipt.call.opening := by
  have batchExecuted := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) executed).2.2.1
  exact batch_at (NativeGoldLookupVerification.batchContext ctx progress) chooseBatch lookup.helpers.memory world after
    batchExecuted position receipt found

theorem helper_at (position : ℕ) (receipt : NativeGoldHelperVerification.Receipt Memory)
    (found : lookup.helpers.receipts[position]? = some receipt) :
    ctx.proof.helperOpenings.val[position]? = some receipt.call.opening := by
  have helpers := helper_execution ctx chooseHelper chooseBatch memory world lookup progress after executed
  have order := (NativeGoldHelperVerification.helpers_order ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers helpers).1
  have origin := NativeGoldHelperVerification.helpers_origin ctx chooseHelper memory world lookup.body lookup.plan (.done lookup.helpers) helpers
  have atCall : lookup.plan.calls[position]? = some receipt.call := by
    rw [← order,List.getElem?_map,found,Option.map_some]
  rw [origin.spec.ordered] at atCall
  exact calls_at _ _ _ _ position receipt.call atCall

theorem source_members : ∀ receipt ∈ after.receipts, receipt.call.opening ∈ ctx.proof.sourceOpening.val := by
  intro receipt member
  obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp member
  exact List.mem_of_getElem? (source_at ctx chooseHelper chooseBatch memory world lookup progress after executed position receipt found)

theorem helper_members : ∀ receipt ∈ lookup.helpers.receipts, receipt.call.opening ∈ ctx.proof.helperOpenings.val := by
  intro receipt member
  obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp member
  exact List.mem_of_getElem? (helper_at ctx chooseHelper chooseBatch memory world lookup progress after executed position receipt found)

theorem source_response_fits (domain : SharedProofSerializationDomain.Domain ctx.proof) :
    ∀ receipt ∈ after.receipts, (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit := by
  intro receipt member
  exact domain.sourceResponses receipt.call.opening
    (source_members ctx chooseHelper chooseBatch memory world lookup progress after executed receipt member)

theorem helper_response_fits (domain : SharedProofSerializationDomain.Domain ctx.proof) :
    ∀ receipt ∈ lookup.helpers.receipts, (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit := by
  intro receipt member
  exact domain.helperResponses receipt.call.opening
    (helper_members ctx chooseHelper chooseBatch memory world lookup progress after executed receipt member)

end FormalProof4FHE.HasteBoots.OpeningReceiptProofSource
