module
import all FormalProof4FHE.HasteBoots.NativeFramedDeferredAvailability
import all FormalProof4FHETest.HasteBootsDeferredAvailabilitySmoke
import all FormalProof4FHETest.HasteBootsObservedSourceSmoke
open FormalProof4FHE.HasteBoots
open NativeDeferredBatchVerification (Context Call)
open NativeTranscriptFraming (Framed)
open OracleProgram (run)
namespace HasteBootsDeferredFramingSmoke
noncomputable section
open HasteBootsDeferredAvailabilitySmoke (ctx ctxTwo execution executionTwo world receipts receiptsOf)

def callFits (planned : Call) : Bool := decide
  (128 + (NativeGoldBatchBinding.queriesCodec.encode planned.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode planned.values).length < TranscriptFrame.lengthLimit ∧
    (NativeLookupRequestWire.rowCodec.encode planned.opening.test ++
      (NativePrefixCodec.vector NativeLookupRequestWire.rowCodec).encode planned.opening.evaluations).length < TranscriptFrame.lengthLimit)

def packetsFit (ctx : Context) : Bool :=
  ((NativeDeferredOpeningBatch.usedGroups ctx.state).zip ctx.proof.val).all (fun pair =>
    match NativeDeferredBatchVerification.call ctx.registry ctx.state pair.1 pair.2 with
    | none => true
    | some planned => callFits planned)

theorem checked_domain (ctx : Context) (checked : packetsFit ctx = true) : NativeDeferredBatchFraming.Domain ctx := by
  intro _ group opening member planned computed
  have known := List.all_eq_true.mp checked (group,opening) member
  change (match NativeDeferredBatchVerification.call ctx.registry ctx.state group opening with | none => true | some value => callFits value) = true at known
  rw [computed] at known
  unfold NativeDeferredBatchFraming.CallFits
  exact of_decide_eq_true known

example : packetsFit ctx = true := by decide +kernel
example : packetsFit ctxTwo = true := by decide +kernel

theorem parent_one : Framed ctx.state.parent := by
  rw [NativeTranscriptFraming.framed_iff_decode]
  decide +kernel

theorem parent_two : Framed ctxTwo.state.parent := by
  rw [NativeTranscriptFraming.framed_iff_decode]
  decide +kernel

-- These are emitted by the actual dispatcher, not supplied receipt certificates.
theorem receipts_framed : ∀ receipt ∈ receipts,
    NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) := by
  unfold HasteBootsDeferredAvailabilitySmoke.receipts
  cases executed : (execution false).1 with
  | sealRejected state reason => simp
  | verification result =>
    exact (NativeDeferredBatchFraming.program_framed ctx (HasteBootsBatchPcsSmoke.choose false) () world result executed
      parent_one (checked_domain ctx (by decide +kernel))).2

theorem retained_receipts_framed : ∀ receipt ∈ receiptsOf executionTwo.1,
    NativeGoldBatchSourceRisk.Framed (receipt.call.context ctxTwo.tables ctxTwo.fieldFuel receipt.before) := by
  cases executed : executionTwo.1 with
  | sealRejected state reason => simp [receiptsOf]
  | verification result =>
    exact (NativeDeferredBatchFraming.program_framed ctxTwo (HasteBootsBatchPcsSmoke.choose false) () world result executed
      parent_two (checked_domain ctxTwo (by decide +kernel))).2

example : ¬Framed ⟨[255],fun _ => 0⟩ := by
  rw [NativeTranscriptFraming.framed_iff_decode]
  decide +kernel

-- Suspension after a rejected first candidate preserves the pending field frame.
example : (match (run (NativePrimeRequest.request NativeFields.goldilocksModulus 1
    HasteBootsObservedSourceSmoke.parent .vector [] ⟨1,by decide⟩) HasteBootsObservedSourceSmoke.rejectFirst).run.1 with
    | .suspended state => some (TranscriptFrame.decodeAll state.phase.pending.input).isSome
    | .finished _ _ => none) = some true := by decide +kernel
def claimRowsFit (query : NativeGoldPcsWire.Query) (values : NativePrefixCodec.Vector NativeLookupRequestWire.Row) : Bool :=
  values.val.all (fun value => decide (18 + (NativeGoldPcsWire.queryCodec.encode query).length +
    (NativeLookupRequestWire.rowCodec.encode value).length < TranscriptFrame.lengthLimit))

theorem claims_domain {C : Type} (registry : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle C))
    (requests : NativePrefixCodec.Vector NativeLookupRequestWire.Request) (query : NativeGoldPcsWire.Query)
    (values : NativePrefixCodec.Vector NativeLookupRequestWire.Row) (checked : claimRowsFit query values = true) :
    NativeSourceClaimFraming.Domain registry requests query values := by
  intro slot _ value found
  unfold NativeSourceClaimFraming.Fits
  exact of_decide_eq_true (List.all_eq_true.mp checked value (List.mem_of_getElem? found))

theorem claims_parent : Framed HasteBootsDeferredRegistrySmoke.initial.parent := by
  rw [NativeTranscriptFraming.framed_iff_decode]
  decide +kernel

example : claimRowsFit HasteBootsDeferredRegistrySmoke.query HasteBootsDeferredRegistrySmoke.values = true := by decide +kernel
example : claimRowsFit HasteBootsDeferredRegistrySmoke.query HasteBootsDeferredRegistrySmoke.badValues = true := by decide +kernel

example : Framed (HasteBootsDeferredRegistrySmoke.collected HasteBootsDeferredRegistrySmoke.allRequests HasteBootsDeferredRegistrySmoke.values).1.progress.state.parent :=
  NativeSourceClaimFraming.program_framed HasteBootsRegistryAncestrySmoke.description HasteBootsRegistryAncestrySmoke.registry
    HasteBootsDeferredRegistrySmoke.allRequests HasteBootsDeferredRegistrySmoke.query HasteBootsDeferredRegistrySmoke.values
    HasteBootsDeferredRegistrySmoke.initial HasteBootsRegistryAncestrySmoke.world claims_parent (claims_domain _ _ _ _ (by decide +kernel))

example : Framed (HasteBootsDeferredRegistrySmoke.collected HasteBootsDeferredRegistrySmoke.allRequests HasteBootsDeferredRegistrySmoke.badValues).1.progress.state.parent :=
  NativeSourceClaimFraming.program_framed HasteBootsRegistryAncestrySmoke.description HasteBootsRegistryAncestrySmoke.registry
    HasteBootsDeferredRegistrySmoke.allRequests HasteBootsDeferredRegistrySmoke.query HasteBootsDeferredRegistrySmoke.badValues
    HasteBootsDeferredRegistrySmoke.initial HasteBootsRegistryAncestrySmoke.world claims_parent (claims_domain _ _ _ _ (by decide +kernel))

end
end HasteBootsDeferredFramingSmoke
