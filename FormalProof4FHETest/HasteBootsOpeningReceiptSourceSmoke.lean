module
import all FormalProof4FHE.HasteBoots.ReceiptDerivedIdentityWork
import all FormalProof4FHETest.HasteBootsClaimReceiptCoverageSmoke

namespace HasteBootsOpeningReceiptSourceSmoke
open FormalProof4FHE.HasteBoots
open FormalProof4FHE.HasteBoots.ClaimReceiptCoverageSmoke (after executed receipt done?)
open HasteBootsDeferredAvailabilitySmoke (ctx world native)
open NativePrefixCodec (Vector)
noncomputable section

theorem receipt_at_zero : after.receipts[0]? = some receipt :=
  List.getElem?_eq_getElem (by decide +kernel)

theorem original_source_packet : ctx.proof.val[0]? = some receipt.call.opening :=
  OpeningReceiptProofSource.batch_at ctx (HasteBootsBatchPcsSmoke.choose false) () world after executed 0 receipt receipt_at_zero

-- Alias claim addresses, owner slots and packet positions remain distinct roles.
theorem alias_claims_retained : ctx.state.claims.val.map (fun claim => claim.slot.val) = [1,1,1,1] ∧
    receipt.call.slot = 0 ∧ ctx.proof.val.length = 1 := by decide +kernel

def query : NativeGoldPcsWire.Query := ⟨[],by decide⟩
def root : NativeRootMessage.Digest := fun _ => 7
def row : NativeLookupRequestWire.Row := ⟨[],by decide⟩
def calls := NativeSharedLookupHelpers.calls query [root,root,root] [row,row,row] [31,37,41]

theorem helper_same_roots_different_packets :
    (calls[0]?).map (fun call => call.root) = (calls[2]?).map (fun call => call.root) ∧
    (calls[0]?).map (fun call => call.opening) = some 31 ∧
    (calls[2]?).map (fun call => call.opening) = some 41 := by decide +kernel

theorem helper_original_index : ([31,37,41] : List ℕ)[2]? = some 41 :=
  OpeningReceiptProofSource.calls_at query [root,root,root] [row,row,row] [31,37,41] 2
    ⟨root,query,row,41⟩ (by rfl)

theorem truncated_zip_preserves_index : ([31,37,41] : List ℕ)[1]? = some 37 :=
  OpeningReceiptProofSource.calls_at query [root,root] [row,row,row] [31,37,41] 1
    ⟨root,query,row,37⟩ (by rfl)

def proof : SharedProofByteCodec.Proof :=
  ⟨⟨⟨[],by decide⟩,by decide⟩,⟨[root],by decide⟩,⟨[],by decide⟩,
    ⟨[],by decide⟩,⟨[],by decide⟩,ctx.proof,⟨[],by decide⟩⟩
def proofBytes : Vector InputIndexedOracle.Byte := ⟨SharedProofByteCodec.codec.encode proof,by decide +kernel⟩

theorem decoded_domain : SharedProofSerializationDomain.Domain proof :=
  SharedProofSerializationDomain.of_length proof (by decide +kernel)
    (SharedProofReadSize.canonical_fits proofBytes proof []
      (by simpa only [proofBytes,List.append_nil] using SharedProofByteCodec.read_prefix proof []))

theorem actual_receipt_response_fits :
    (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit :=
  decoded_domain.sourceResponses receipt.call.opening (List.mem_of_getElem? original_source_packet)

theorem canceled_not_complete : (done? (HasteBootsDeferredAvailabilitySmoke.execution true).1).isNone = true := by decide +kernel

theorem later_failure_not_complete : (done? HasteBootsDeferredAvailabilitySmoke.executionTwo.1).isNone = true := by decide +kernel

end
end HasteBootsOpeningReceiptSourceSmoke
