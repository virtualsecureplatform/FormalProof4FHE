module
public import FormalProof4FHE.HasteBoots.OffsetPositionKernel
@[expose] public section

/-! Native original wire domains give a uniform reciprocal degree budget.
This is a syntax bound; no physical attacker-work theorem is asserted here. -/
namespace FormalProof4FHE.HasteBoots.OffsetDegreeBudget
open LookupOffsetCompressionFixation (Candidate)
open InputIndexedOracle (World)
open OracleProgram (Program)
noncomputable section

def budget : ℕ := 2^65

theorem complexity {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) : LookupOffsetKernel.complexity candidate ≤ budget := by
  have member := candidate.source.job.original
  rw [NativeSharedLookupParent.models_list] at member
  obtain ⟨request,_,same⟩ := List.mem_map.mp member
  have tableFits : (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request.table.length < 2^64 := by
    rw [← same]
    change request.config.table.values.length < 2^64
    simpa only [NativeLookupRequestWire.Table.values,List.length_map] using request.config.table.property
  have logicalFits := (candidate.source.origin.ready.jobs.get candidate.source.index).tag.request.terminal.logicalLength.isLt
  unfold LookupOffsetKernel.complexity budget
  norm_num at tableFits logicalFits ⊢
  omega

theorem event {A : Type} {program : Program A} {position : ℕ} {world : World} (dummy : NativeRootMessage.Digest) :
    (∃ input ordinal cost, OffsetClassKernel.Event program position input ordinal cost dummy world) ↔
      OffsetPositionKernel.Event program position budget dummy world := by
  constructor
  · rintro ⟨input,ordinal,cost,packet,event⟩
    exact ⟨input,ordinal,cost,packet.property.2.2.1 ▸ complexity packet.val,packet,event⟩
  · rintro ⟨input,ordinal,cost,_,event⟩
    exact ⟨input,ordinal,cost,event⟩

end
end FormalProof4FHE.HasteBoots.OffsetDegreeBudget
