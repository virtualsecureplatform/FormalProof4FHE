module
public import FormalProof4FHE.HasteBoots.DeferredClaimReceiptCoverage
public import FormalProof4FHE.HasteBoots.BatchClaimShape
public import FormalProof4FHE.HasteBoots.NativeGoldLookupAvailability
@[expose] public section

/-! Every used outer source slot in a completely accepted lookup dispatcher
has an accepted original batch query/value pair. Alias equality is in the
field; owner selection still uses the complete original context/root key.
Equal context digests do not here imply parameter equality. -/
namespace FormalProof4FHE.HasteBoots.LookupSourceReceiptCoverage
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeDeferredBatchVerification (Receipt Progress)
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem source_receipt {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : Progress Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (slot : Fin ctx.registry.val.length) (used : NativeSharedSourceClaims.used ctx.requests slot = true) :
    ∃ receipt : Receipt Memory, receipt ∈ after.receipts ∧
      ∃ (index : Fin receipt.work.binding.queries.val.length) (received inserted : NativeLookupRequestWire.Row) (digest : Digest),
        ctx.proof.sources.val[slot.val]? = some received ∧
        receipt.work.binding.queries.val[index.val]? = some lookup.query ∧
        receipt.work.binding.values.val[index.val]? = some inserted ∧
        NativeGoldPcsClaim.equal inserted.val received.val = true ∧
        inserted.val.map NativeFieldRepresentation.goldValue = received.val.map NativeFieldRepresentation.goldValue ∧
        inserted.val.map NativeFieldRepresentation.goldValue = List.ofFn (fun lane : Fin receipt.call.oracle.parameters.width.val =>
          NativeFieldRepresentation.goldValue (received.val[lane.val]?.getD 0)) ∧
        (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (ctx.registry.val.get slot).parameters) world).run.1 = some digest ∧
        (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row receipt.call.oracle.parameters) world).run.1 = some digest ∧
        receipt.call.oracle.root = (ctx.registry.val.get slot).root ∧
        ctx.registry.val[receipt.call.slot]? = some receipt.call.oracle ∧ receipt.call.slot ≤ slot.val ∧
        NativeDeferredBatchVerification.Checked ctx.tables ctx.fieldFuel chooseBatch ctx.workerFuel world receipt := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress (.verification (.done after)) executed
  obtain ⟨claim,received,digest,keySlot,claimMember,queryEq,originalContext,receivedAt,matched,keyIndex,keyComputed,before⟩ :=
    NativeGoldLookupSourceInvariant.batches_source_claims ctx chooseHelper chooseBatch memory world lookup progress _ executed slot used
  obtain ⟨receipt,member,_,ownerEq,found,index,queryAt,valueAt,checked⟩ :=
    DeferredClaimReceiptCoverage.claim_receipt (NativeGoldLookupVerification.batchContext ctx progress) chooseBatch lookup.helpers.memory world after
      origin.2.2.1 claim claimMember
  have sources := NativeGoldLookupAvailability.batch_sources ctx chooseHelper chooseBatch memory world lookup progress _ executed
  have claimKey : progress.state.sources.val[claim.slot.val]? = some (digest,(ctx.registry.val.get slot).root) := by
    have atIndex := congrArg (fun sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source => sources.val[claim.slot.val]?) sources
    have metadataAt : lookup.metadata.sources.val[claim.slot.val]? = some (digest,(ctx.registry.val.get slot).root) := by
      rw [← keyIndex]
      exact (List.getElem?_eq_getElem keySlot.isLt).trans (congrArg some keyComputed)
    exact atIndex.trans metadataAt
  have ownerKey : progress.state.sources.val[(NativeSourceRegistry.owner progress.state.sources claim.slot).val]? =
      progress.state.sources.val[claim.slot.val]? := by
    rw [List.getElem?_eq_getElem (NativeSourceRegistry.owner progress.state.sources claim.slot).isLt,List.getElem?_eq_getElem claim.slot.isLt]
    exact congrArg some (NativeSourceRegistry.owner_key progress.state.sources claim.slot)
  have receiptKey : lookup.metadata.sources.val[receipt.call.slot]? = some (digest,(ctx.registry.val.get slot).root) := by
    rw [← sources,ownerEq]
    exact ownerKey.trans claimKey
  obtain ⟨owner,atOwner,_,ownerContext,ownerRoot,_⟩ := NativeGoldLookupAvailability.receipt_owner_key ctx chooseHelper chooseBatch memory world lookup progress
    (.done after) executed receipt member
  have ownerKeyAt : lookup.metadata.sources.val[receipt.call.slot]? = some (lookup.metadata.sources.val.get owner) := by
    rw [← atOwner]
    exact List.getElem?_eq_getElem owner.isLt
  have sameKey : lookup.metadata.sources.val.get owner = (digest,(ctx.registry.val.get slot).root) := Option.some.inj (ownerKeyAt.symm.trans receiptKey)
  rw [sameKey] at ownerContext ownerRoot
  have ownerBefore : receipt.call.slot ≤ slot.val := by
    rw [ownerEq]
    exact (NativeSourceRegistry.owner_le progress.state.sources claim.slot).trans before
  have nativePrepared := (NativeGoldBatchPcsProgram.completed_origin (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
    chooseBatch ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1).prepared
  have insertedWidth := BatchClaimShape.prepared_width _ world receipt.work nativePrepared index claim.values valueAt
  have sameFields := (NativeGoldPcsClaim.equal_iff _ _).mp matched
  have receivedWidth : received.val.length = receipt.call.oracle.parameters.width.val := by
    have counts := congrArg List.length sameFields
    simp only [List.length_map] at counts
    exact counts.symm.trans insertedWidth
  have encoded := sameFields.trans (BatchClaimShape.row_encoding receipt.call.oracle.parameters.width.val received receivedWidth)
  exact ⟨receipt,member,index,received,claim.values,digest,receivedAt,
    queryAt.trans (congrArg some queryEq),valueAt,matched,sameFields,encoded,
    originalContext,ownerContext,ownerRoot,found,ownerBefore,checked⟩

end
end FormalProof4FHE.HasteBoots.LookupSourceReceiptCoverage
