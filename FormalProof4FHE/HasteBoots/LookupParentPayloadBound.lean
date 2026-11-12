module
public import FormalProof4FHE.HasteBoots.LookupRequestPayloadSize
public import FormalProof4FHE.HasteBoots.RefinedCompressionKernel
public import FormalProof4FHE.HasteBoots.RebuiltLookupExecution
@[expose] public section

/-! Original validated request complexity is bounded by the exact caller
parent-seed input payload. This is a size/charging interface, not yet an
amortized work theorem across repeated jobs or different input classes. -/
namespace FormalProof4FHE.HasteBoots.LookupParentPayloadBound
open InputIndexedOracle (World)
open OracleProgram (Program)
open MeasureTheory ProbabilityTheory
open NativeLookupRequestWire (Request)
noncomputable section

theorem family {A : Type} {program : Program A} {position : ℕ} {world : World}
    (parent : OriginalParentFamily.Family program position world)
    (valid : NativeSharedLookupConfig.Valid (parent.requests.val.map Request.toModel)) :
    (parent.requests.val.map LookupRequestPayloadSize.complexity).sum ≤ parent.input.length := by
  have payload := LookupRequestPayloadSize.requests_complexities parent.requests (fun request member =>
    (valid request.toModel (List.mem_map.mpr ⟨request,member,rfl⟩)).1)
  have message := ScalarMetadataSize.message_le parent.bindings.frames (ParentBindingsView.requestFrame parent.bindings.requests)
    (by simp [ParentBindingsView.View.frames])
  change (NativeLookupRequestWire.requestsCodec.encode parent.bindings.requests).length ≤ _ at message
  rw [parent.requests_eq,← (ParentBindingsView.parse_sound _ _ parent.bindingParsed).1] at message
  have before : (TranscriptFrame.encodeMany parent.parent.before).length ≤ parent.input.length := by
    rw [(SharedParentInputView.parse_sound _ _ parent.parsed).1,SharedParentInputView.View.frames,
      SingleOpeningExposure.encodeMany_append,List.length_append]
    omega
  exact payload.trans (message.trans before)

theorem entry_le_sum (requests : List Request) (request : Request) (member : request ∈ requests) :
    LookupRequestPayloadSize.complexity request ≤ (requests.map LookupRequestPayloadSize.complexity).sum := by
  induction requests with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst request
      simp only [List.map_cons,List.sum_cons]
      omega
    · have bounded := ih later
      simp only [List.map_cons,List.sum_cons]
      omega

theorem candidate {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupSourceCandidate.Candidate program position world)
    (valid : NativeSharedLookupConfig.Valid (candidate.ctx.requests.val.map Request.toModel)) :
    RefinedCompressionKernel.complexity candidate ≤ candidate.parent.input.length := by
  have member := candidate.job.original
  rw [NativeSharedLookupParent.models_list] at member
  obtain ⟨request,member,same⟩ := List.mem_map.mp member
  have complexity : RefinedCompressionKernel.complexity candidate = LookupRequestPayloadSize.complexity request := by
    exact congrArg (fun request : NativeSharedLookupStatement.Request => request.table.length*(request.columns-1)) same.symm
  have parentValid : NativeSharedLookupConfig.Valid (candidate.parent.requests.val.map Request.toModel) := by
    rw [candidate.requests]
    exact valid
  rw [complexity]
  have inParent : request ∈ candidate.parent.requests.val := by rw [candidate.requests]; exact member
  exact (entry_le_sum candidate.parent.requests.val request inParent).trans (family candidate.parent parentValid)

variable {Memory A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupSourceCandidate.Candidate program position world)
    (policy : NativeSharedLookupValues.Policy) (original : NativePrefixCodec.Vector Request)
    (entries : List NativeGoldParameterStore.Entry) (helperHandle : ℕ) (references : NativePrefixCodec.Vector NativeGoldParameterStore.Reference)
    (template : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (OracleProgram.run (RebuiltLookupExecution.program policy original entries helperHandle references template
      chooseHelper chooseBatch memory) world).run.1 = .allocated (.verification candidate.ctx result))
include executed

theorem rebuilt_candidate : RefinedCompressionKernel.complexity candidate ≤ candidate.parent.input.length := by
  obtain ⟨_,_,_,_,valid,_⟩ := RebuiltLookupExecution.verification_origin policy original entries helperHandle references template
    chooseHelper chooseBatch memory world candidate.ctx result executed
  exact LookupParentPayloadBound.candidate candidate valid

theorem rebuilt_kernel_bound (dummy : NativeRootMessage.Digest) :
    (InputIndexedOracle.law[|{other | (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run}])
      {other | LookupCompressionKernel.Event candidate dummy other} ≤
        (candidate.parent.input.length : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) :=
  RefinedCompressionKernel.bound_of_complexity program position world candidate dummy candidate.parent.input.length
    (rebuilt_candidate candidate policy original entries helperHandle references template chooseHelper chooseBatch memory result executed)

end
end FormalProof4FHE.HasteBoots.LookupParentPayloadBound
