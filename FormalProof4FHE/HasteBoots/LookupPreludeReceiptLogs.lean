module
public import FormalProof4FHE.HasteBoots.LookupBatchReceiptLogs
public import FormalProof4FHE.HasteBoots.EqualityReceiptLogs
@[expose] public section

/-! A successful original prelude logs the actual receipts for all completed
lookup jobs and every retained equality point. Pure compilation adds no reads. -/
namespace FormalProof4FHE.HasteBoots.LookupPreludeReceiptLogs
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open OracleProgram (run)
noncomputable section

theorem protocol {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → NativeSharedLookupStatement.Request)
    (n : NativeUsizeMessage.Usize) (multiplicities : List (List NativeFieldRepresentation.GoldWord))
    (roots : List NativeRootMessage.Digest) (rootFits : roots.length < 2^64) (w lookupFuel equalityFuel : ℕ)
    (transcript : Transcript) (world : World) (ready : NativeSharedLookupPrelude.Ready n.val)
    (success : (run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready) :
    (∀ completed ∈ (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis w lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.completed,
        LookupReceiptLogs.Reads world completed.selection.draws
          (run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel transcript) world).run.2) ∧
    EqualityReceiptLogs.Reads world ready.machine.draws
      (run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel transcript) world).run.2 := by
  have contract := NativeSharedLookupPrelude.protocol_contract fits requests n multiplicities roots rootFits w lookupFuel equalityFuel transcript world ready success
  obtain ⟨final,_,machine,observations⟩ := contract.lookup
  have batch := LookupBatchReceiptLogs.initialized NativeExtensionFields.goldilocksBasis w lookupFuel
    (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript world
  have equality := EqualityReceiptLogs.request NativeExtensionFields.goldilocksBasis w n.val equalityFuel final roots rootFits world
  rw [← machine] at equality
  constructor
  · intro completed member
    apply LookupReceiptLogs.mono world _ _ _ (batch.2 completed member)
    rw [NativeSharedLookupPrelude.run_protocol]
    exact List.sublist_append_left _ _
  · intro draw member
    apply (equality draw member).trans
    rw [NativeSharedLookupPrelude.run_protocol]
    dsimp only
    rw [observations]
    exact List.sublist_append_right _ _

end
end FormalProof4FHE.HasteBoots.LookupPreludeReceiptLogs
