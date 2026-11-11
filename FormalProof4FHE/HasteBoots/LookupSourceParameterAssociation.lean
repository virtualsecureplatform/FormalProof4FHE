module
public import FormalProof4FHE.HasteBoots.LookupSourceReceiptCoverage
public import FormalProof4FHE.HasteBoots.LookupContextHistory
public import FormalProof4FHE.HasteBoots.GoldContextCollision
@[expose] public section

/-! The used original source and its first-original batch owner have the same
full retained parameters outside the existing shared hash bad event. Both
hash computations and original claim pairing are derived from execution. -/
namespace FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeDeferredBatchVerification (Receipt Progress)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def Associated {Memory : Type} (ctx : Context (Vector Opening)) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (after : Progress Memory) (slot : Fin ctx.registry.val.length) (receipt : Receipt Memory) : Prop :=
  receipt ∈ after.receipts ∧ receipt.call.oracle.parameters = (ctx.registry.val.get slot).parameters ∧
    receipt.call.oracle.root = (ctx.registry.val.get slot).root ∧ ctx.registry.val[receipt.call.slot]? = some receipt.call.oracle ∧
    receipt.call.slot ≤ slot.val ∧
    ∃ (index : Fin receipt.work.binding.queries.val.length) (received inserted : NativeLookupRequestWire.Row),
      ctx.proof.sources.val[slot.val]? = some received ∧ receipt.work.binding.queries.val[index.val]? = some lookup.query ∧
      receipt.work.binding.values.val[index.val]? = some inserted ∧ NativeGoldPcsClaim.equal inserted.val received.val = true ∧
      inserted.val.map NativeFieldRepresentation.goldValue = List.ofFn (fun lane : Fin receipt.call.oracle.parameters.width.val =>
        NativeFieldRepresentation.goldValue (received.val[lane.val]?.getD 0))

variable {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : Progress Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (slot : Fin ctx.registry.val.length) (used : NativeSharedSourceClaims.used ctx.requests slot = true)
    (dummy : Digest) (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)

include executed used truthful observed

theorem associated_no_bad (noBad : ¬NativeRootFamilyLifetime.Bad dummy history) :
    ∃ receipt : Receipt Memory, Associated ctx lookup after slot receipt := by
  obtain ⟨receipt,member,index,received,inserted,digest,receivedAt,queryAt,valueAt,matched,_,encoded,
    originalContext,ownerContext,root,found,before,_⟩ := LookupSourceReceiptCoverage.source_receipt
      ctx chooseHelper chooseBatch memory world lookup progress after executed slot used
  have leftObserved := (LookupContextHistory.receipt_context ctx chooseHelper chooseBatch memory world lookup progress (.done after) executed receipt member).trans observed
  have rightObserved := (LookupContextHistory.used_context ctx chooseHelper chooseBatch memory world lookup progress (.done after) executed slot used).trans observed
  have parameters := GoldContextCollision.parameters_eq_of_no_bad receipt.call.oracle.parameters (ctx.registry.val.get slot).parameters
    world digest ownerContext originalContext dummy history truthful leftObserved rightObserved noBad
  exact ⟨receipt,member,parameters,root,found,before,index,received,inserted,receivedAt,queryAt,valueAt,matched,encoded⟩

/-- Parameter mismatch is included in the same complete-history hash bad event;
there is no separate per-source or per-alias hash charge. -/
theorem associated_or_bad : (∃ receipt : Receipt Memory, Associated ctx lookup after slot receipt) ∨
    NativeRootFamilyLifetime.Bad dummy history := by
  by_cases bad : NativeRootFamilyLifetime.Bad dummy history
  · exact Or.inr bad
  · exact Or.inl (associated_no_bad ctx chooseHelper chooseBatch memory world lookup progress after executed slot used dummy history truthful observed bad)

omit used in
/-- One shared bad event covers every original used slot simultaneously. -/
theorem all_associated_or_bad :
    (∀ slot : Fin ctx.registry.val.length, NativeSharedSourceClaims.used ctx.requests slot = true →
      ∃ receipt : Receipt Memory, Associated ctx lookup after slot receipt) ∨ NativeRootFamilyLifetime.Bad dummy history := by
  by_cases bad : NativeRootFamilyLifetime.Bad dummy history
  · exact Or.inr bad
  · exact Or.inl (fun slot used => associated_no_bad ctx chooseHelper chooseBatch memory world lookup progress after executed
      slot used dummy history truthful observed bad)

end
end FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation
