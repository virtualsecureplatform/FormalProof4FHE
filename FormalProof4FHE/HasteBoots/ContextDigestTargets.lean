module
public import FormalProof4FHE.HasteBoots.NativeSeedAncestry
public import FormalProof4FHE.HasteBoots.NativeRootMentionSize
@[expose] public section

/-! Context digests named in complete raw inputs, including starts and empty
reads. These are syntax targets, not authenticated parameter preimages. -/
namespace FormalProof4FHE.HasteBoots.ContextDigestTargets
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open scoped Classical
noncomputable section

def fromInput (input : Input) : List Digest :=
  (NativeParentLedger.direct input).map Prod.fst ++ NativeParentLedger.helpers input

def targets (history : List Observation) : Finset Digest :=
  (history.flatMap (fun entry => fromInput (NativeParentCoverage.observationInput entry))).toFinset

theorem named (history : List Observation) (entry : Observation) (member : entry ∈ history) (digest : Digest)
    (mentioned : digest ∈ fromInput (NativeParentCoverage.observationInput entry)) : digest ∈ targets history :=
  List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨entry,member,mentioned⟩)

theorem mono (earlier later : List Observation) (included : earlier.Sublist later) : targets earlier ⊆ targets later := by
  intro digest member
  obtain ⟨entry,present,mentioned⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp member)
  exact named later entry (included.subset present) digest mentioned

theorem append (earlier later : List Observation) : targets (earlier ++ later) = targets earlier ∪ targets later := by
  simp only [targets,List.flatMap_append,List.toFinset_append]

/-- Every context mentioned by a chronologically known input was named in
the history, including inputs whose helper metadata was inherited. -/
theorem known_input (world : World) (history : List Observation) (input : Input) (helper digest : Digest)
    (known : NativeParentLineage.Known world history input helper) (mentioned : digest ∈ fromInput input) : digest ∈ targets history := by
  induction known with
  | direct before entry frames parsed context helper =>
    exact named _ entry (List.mem_append_right _ List.mem_cons_self) digest mentioned
  | inherit before entry frames parsed parent context earlier quoted ih =>
    exact named _ entry (List.mem_append_right _ List.mem_cons_self) digest mentioned
  | later before later input context earlier ih =>
    exact mono before _ (List.sublist_append_left _ _) (ih mentioned)

theorem helper_known (world : World) (history : List Observation) (input : Input) (digest : Digest)
    (known : NativeParentLineage.Known world history input digest) : digest ∈ targets history := by
  induction known with
  | direct before entry frames parsed context helper =>
    exact named _ entry (List.mem_append_right _ (List.mem_cons_self)) context (List.mem_append_right _ helper)
  | inherit before entry frames parsed parent context earlier quoted ih =>
    exact mono before _ (List.sublist_append_left _ _) ih
  | later before later input context earlier ih =>
    exact mono before _ (List.sublist_append_left _ _) ih

theorem source_known (world : World) (history : List Observation) (input : Input) (key : NativeCanonicalLookupWire.Source)
    (known : NativeSourceLineage.Known world history input key) : key.1 ∈ targets history := by
  induction known with
  | direct before entry frames parsed key source =>
    apply named _ entry (List.mem_append_right _ (List.mem_cons_self)) key.1
    exact List.mem_append_left _ (List.mem_map.mpr ⟨key,source,rfl⟩)
  | inherit before entry frames parsed parent key earlier quoted ih =>
    exact mono before _ (List.sublist_append_left _ _) ih
  | later before later input key earlier ih =>
    exact mono before _ (List.sublist_append_left _ _) ih


/-- A conservative syntax bound counts all naming input bytes, including
starts and empty reads. It is not a physical attacker-work estimate. -/
def inputBytes (history : List Observation) : ℕ :=
  (history.map (fun entry => (NativeParentCoverage.observationInput entry).length)).sum

theorem fromInput_length (input : Input) : (fromInput input).length ≤ 2*input.length := by
  simp only [fromInput,List.length_append,List.length_map]
  have direct := NativeRootMentionSize.direct_size input
  have helper := NativeRootMentionSize.helpers_size input
  omega

theorem card (history : List Observation) : (targets history).card ≤ 2*inputBytes history := by
  apply (List.toFinset_card_le _).trans
  induction history with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
    simp only [List.flatMap_cons,List.length_append,inputBytes,List.map_cons,List.sum_cons] at *
    have bound := fromInput_length (NativeParentCoverage.observationInput entry)
    omega

end
end FormalProof4FHE.HasteBoots.ContextDigestTargets
