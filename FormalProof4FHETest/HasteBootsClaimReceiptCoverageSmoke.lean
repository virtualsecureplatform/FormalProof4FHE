module
import all FormalProof4FHE.HasteBoots.LookupSourceReceiptCoverage
import all FormalProof4FHETest.HasteBootsDeferredAvailabilitySmoke

namespace FormalProof4FHE.HasteBoots.ClaimReceiptCoverageSmoke
open HasteBootsDeferredAvailabilitySmoke (ctx world execution native)
open NativeDeferredBatchVerification (Progress Receipt)
open OracleProgram (run)
noncomputable section

def done? : NativeDeferredBatchVerification.Outcome Unit → Option (Progress Unit)
  | .verification (.done after) => some after
  | _ => none

def after := (done? (execution false).1).get (by decide +kernel)

theorem executed : (run (NativeDeferredBatchVerification.program ctx (HasteBootsBatchPcsSmoke.choose false) ()) world).run.1 = .verification (.done after) := by
  have present : (done? (execution false).1).isSome = true := by decide +kernel
  cases equal : (execution false).1 with
  | sealRejected state reason => simp only [equal,done?,Option.isSome_none,Bool.false_eq_true] at present
  | verification result =>
    cases result with
    | done actual => change (execution false).1 = _; simp only [after,equal,done?,Option.get_some]
    | stopped progress call outcome => simp only [equal,done?,Option.isSome_none,Bool.false_eq_true] at present
    | indexingUnavailable progress group slot => simp only [equal,done?,Option.isSome_none,Bool.false_eq_true] at present
    | packetUnavailable progress => simp only [equal,done?,Option.isSome_none,Bool.false_eq_true] at present

example : ctx.state.claims.val.length = 4 ∧ after.receipts.length = 1 := by decide +kernel

/-- Every actual inserted claim gets paired query/value getters at one native
batch index, including all claims inserted through the later alias slot. -/
example (claim : NativeDeferredOpeningBatch.Claim ctx.state.sources) (member : claim ∈ ctx.state.claims.val) :
    ∃ receipt : Receipt Unit, receipt ∈ after.receipts ∧
      ∃ index : Fin receipt.work.binding.queries.val.length,
        receipt.work.binding.queries.val[index.val]? = some claim.query ∧
        receipt.work.binding.values.val[index.val]? = some claim.values ∧
        NativeDeferredBatchVerification.Checked ctx.tables ctx.fieldFuel (HasteBootsBatchPcsSmoke.choose false) ctx.workerFuel world receipt := by
  obtain ⟨receipt,receiptMember,_,_,_,index,queryAt,valueAt,checked⟩ :=
    DeferredClaimReceiptCoverage.claim_receipt ctx (HasteBootsBatchPcsSmoke.choose false) () world after executed claim member
  exact ⟨receipt,receiptMember,index,queryAt,valueAt,checked⟩

/-- The first original unused alias owns the batch; all original claim pairs
retain their insertion order, rather than being replaced by the owner slot. -/
def receipt := after.receipts[0]'(by decide +kernel)
example : ctx.state.claims.val.map (fun claim => claim.slot.val) = [1,1,1,1] ∧ receipt.call.slot = 0 := by decide +kernel

example : receipt.work.binding.queries.val.zip receipt.work.binding.values.val =
    ctx.state.claims.val.map (fun claim => (claim.query,claim.values)) := by decide +kernel

/-- Native cancellation and a later rejected-root batch cannot be mistaken
for complete dispatcher acceptance by the coverage theorem. -/
example : (done? (execution true).1).isNone = true := by decide +kernel
example : (done? HasteBootsDeferredAvailabilitySmoke.executionTwo.1).isNone = true := by decide +kernel

/-- Raw-row field encoding is obtained from its length, including lazy aliases. -/
def aliasRow : NativeLookupRequestWire.Row := ⟨[⟨NativeFields.goldilocksModulus+1,by decide⟩,0,0],by decide⟩
example : aliasRow.val.map NativeFieldRepresentation.goldValue = List.ofFn (fun lane : Fin 3 =>
    NativeFieldRepresentation.goldValue (aliasRow.val[lane.val]?.getD 0)) :=
  BatchClaimShape.row_encoding 3 aliasRow rfl

/-- Actual preparation validates the original row rather than a supplied width certificate. -/
example (index : Fin receipt.work.binding.queries.val.length) (row : NativeLookupRequestWire.Row)
    (found : receipt.work.binding.values.val[index.val]? = some row) : row.val.length = receipt.call.oracle.parameters.width.val := by
  have member : receipt ∈ after.receipts := List.getElem_mem (by decide +kernel)
  have checked := (NativeDeferredBatchVerification.program_receipts ctx (HasteBootsBatchPcsSmoke.choose false) () world (.done after)
    executed receipt member).1
  have prepared := (NativeGoldBatchPcsProgram.completed_origin _ _ _ _ _ _ _ checked.1).prepared
  exact BatchClaimShape.prepared_width _ world receipt.work prepared index row found

/-- The fixture deliberately aliases unequal parameter records by digest/root.
Coverage retains the original owner and does not infer parameter equality. -/
example : (ctx.registry.val.get ⟨0,by decide⟩).parameters ≠ (ctx.registry.val.get ⟨1,by decide⟩).parameters ∧
    ctx.state.sources.val[0]? = ctx.state.sources.val[1]? := by
  constructor
  · intro same
    have impossible : (1 : ℕ) = 99 := congrArg (fun parameters => parameters.queries.val) same
    cases impossible
  · decide +kernel

end
end FormalProof4FHE.HasteBoots.ClaimReceiptCoverageSmoke
