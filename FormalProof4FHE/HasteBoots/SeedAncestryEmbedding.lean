module
public import FormalProof4FHE.HasteBoots.NativeSeedAncestry
@[expose] public section

/-! Embed semantic native ancestry in a larger raw history. Earliest exposure
positions are recomputed there, so earlier adversarial reads are retained;
chronological order is still subject to the existing seed-order bad event. -/
namespace FormalProof4FHE.HasteBoots.SeedAncestryEmbedding
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
noncomputable section

theorem first_sublist (before after : List Observation) (included : before.Sublist after)
    (input : Input) (index : ℕ) (first : OracleFirstExposure.locate before (OracleFirstExposure.seedCoordinates input) = some index) :
    ∃ position, OracleFirstExposure.locate after (OracleFirstExposure.seedCoordinates input) = some position := by
  obtain ⟨old,entry,later,parts,_,_,hit⟩ := (OracleFirstExposure.locate_some before _ index).mp first
  obtain ⟨coordinate,observed,relevant⟩ := Finset.not_disjoint_iff.mp hit
  have present : entry ∈ before := by rw [parts]; exact List.mem_append_right _ List.mem_cons_self
  have retained : coordinate ∈ ObservationReplay.footprint after :=
    Finset.mem_biUnion.mpr ⟨entry,List.mem_toFinset.mpr (included.subset present),observed⟩
  cases found : OracleFirstExposure.locate after (OracleFirstExposure.seedCoordinates input) with
  | some position => exact ⟨position,rfl⟩
  | none => exact False.elim (Finset.disjoint_left.mp ((OracleFirstExposure.locate_none _ _).mp found) retained relevant)

/-- An interleaved containing history retains the same input/fact graph,
with each parent and child indexed at its own actual first exposure. -/
theorem realized_sublist {world : World} {before after : List Observation} (included : before.Sublist after)
    {input : Input} {index : ℕ} {fact : NativeSeedAncestry.Fact}
    (realized : NativeSeedAncestry.Realized world before input index fact) :
    ∃ position, NativeSeedAncestry.Realized world after input position fact := by
  induction realized with
  | direct input index frames parsed fact direct first =>
    obtain ⟨position,found⟩ := first_sublist before after included input index first
    exact ⟨position,.direct input position frames parsed fact direct found⟩
  | inherit input index frames parsed parent parentIndex fact previous quoted first ih =>
    obtain ⟨parentPosition,retained⟩ := ih
    obtain ⟨position,found⟩ := first_sublist before after included input index first
    exact ⟨position,.inherit input position frames parsed parent parentPosition fact retained quoted found⟩

end
end FormalProof4FHE.HasteBoots.SeedAncestryEmbedding
