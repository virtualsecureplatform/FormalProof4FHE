module
public import FormalProof4FHE.HasteBoots.LookupCompressionOrdinal
public import FormalProof4FHE.HasteBoots.LookupParentPayloadBound
@[expose] public section

/-! Original compression candidates retain their literal first draw and a
complexity cap derived from validated serialized caller requests. Repeated
jobs need no repeated charge for a large shared parent payload. -/
namespace FormalProof4FHE.HasteBoots.FirstCompressionCandidate
open InputIndexedOracle (World)
open OracleProgram (Program)
noncomputable section

def budget : ℕ := 2^64

structure Candidate {A : Type} (program : Program A) (position : ℕ) (world : World)
    extends LookupSourceCandidate.Candidate program position world where
  head : job.view.producer.selection.draws.head? = some draw
  bounded : RefinedCompressionKernel.complexity toCandidate ≤ budget

theorem complexity_le_requests {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupSourceCandidate.Candidate program position world)
    (valid : NativeSharedLookupConfig.Valid (candidate.ctx.requests.val.map NativeLookupRequestWire.Request.toModel)) :
    RefinedCompressionKernel.complexity candidate ≤ (NativeLookupRequestWire.requestsCodec.encode candidate.ctx.requests).length := by
  have member := candidate.job.original
  rw [NativeSharedLookupParent.models_list] at member
  obtain ⟨request,member,same⟩ := List.mem_map.mp member
  have cost : RefinedCompressionKernel.complexity candidate = LookupRequestPayloadSize.complexity request :=
    congrArg (fun request : NativeSharedLookupStatement.Request => request.table.length*(request.columns-1)) same.symm
  rw [cost]
  exact (LookupParentPayloadBound.entry_le_sum candidate.ctx.requests.val request member).trans
    (LookupRequestPayloadSize.requests_complexities candidate.ctx.requests (fun entry present =>
      (valid entry.toModel (List.mem_map.mpr ⟨entry,present,rfl⟩)).1))

theorem budget_of_payload {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : LookupSourceCandidate.Candidate program position world)
    (valid : NativeSharedLookupConfig.Valid (candidate.ctx.requests.val.map NativeLookupRequestWire.Request.toModel))
    (fits : (NativeLookupRequestWire.requestsCodec.encode candidate.ctx.requests).length < TranscriptFrame.lengthLimit) :
    RefinedCompressionKernel.complexity candidate ≤ budget :=
  (complexity_le_requests candidate valid).trans (Nat.le_of_lt fits)

theorem ordinal {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    LookupCompressionCount.fromInput candidate.draw.coefficients.phase.pending.input = candidate.index.val :=
  LookupCompressionOrdinal.original candidate.origin candidate.job candidate.draw candidate.head

theorem ordinal_unique {A B : Type} {leftProgram : Program A} {rightProgram : Program B} {lp rp : ℕ} {world other : World}
    (left : Candidate leftProgram lp world) (right : Candidate rightProgram rp other)
    (input : left.draw.coefficients.phase.pending.input = right.draw.coefficients.phase.pending.input) : left.index.val = right.index.val := by
  have equal := congrArg LookupCompressionCount.fromInput input
  rw [ordinal left,ordinal right] at equal
  exact equal

end
end FormalProof4FHE.HasteBoots.FirstCompressionCandidate
