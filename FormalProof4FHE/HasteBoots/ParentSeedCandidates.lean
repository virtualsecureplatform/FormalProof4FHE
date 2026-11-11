module
public import FormalProof4FHE.HasteBoots.NativeSeedAncestry
@[expose] public section

/-! All recognized parent-seed inputs in an actual raw prefix. Discovery
retains starts, empty reads, hashes and partial reads, as the native parent
ledger does. Candidate naming alone does not authenticate a seed or metadata. -/
namespace FormalProof4FHE.HasteBoots.ParentSeedCandidates
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open NativeParentCoverage (observationInput)
open scoped Classical
noncomputable section

def candidate (entry : Observation) : Option Input :=
  if (NativeParentInputView.parseParent (observationInput entry)).isSome then some (observationInput entry) else none

def inputs (history : List Observation) : Finset Input := (history.filterMap candidate).toFinset

theorem of_observation (history : List Observation) (entry : Observation) (member : entry ∈ history)
    (frames : List TranscriptFrame.Frame) (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames) :
    observationInput entry ∈ inputs history := by
  apply List.mem_toFinset.mpr
  exact List.mem_filterMap.mpr ⟨entry,member,by simp only [candidate,parsed,Option.isSome_some,ite_true]⟩

theorem parsed (history : List Observation) (input : Input) (member : input ∈ inputs history) :
    ∃ frames, NativeParentInputView.parseParent input = some frames := by
  obtain ⟨entry,_,selected⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp member)
  unfold candidate at selected
  split at selected
  next recognized =>
    obtain rfl := Option.some.inj selected
    exact Option.isSome_iff_exists.mp recognized
  next => contradiction

theorem mono (earlier later : List Observation) (included : earlier.Sublist later) : inputs earlier ⊆ inputs later := by
  intro input member
  obtain ⟨entry,present,selected⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp member)
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨entry,included.subset present,selected⟩)

theorem source_known {world : InputIndexedOracle.World} {history : List Observation} {input : Input} {key : NativeCanonicalLookupWire.Source}
    (known : NativeSourceLineage.Known world history input key) : input ∈ inputs history := by
  induction known with
  | direct before entry frames parsed key source =>
    exact of_observation _ entry (List.mem_append_right _ List.mem_cons_self) frames parsed
  | inherit before entry frames parsed parent key earlier quoted ih =>
    exact of_observation _ entry (List.mem_append_right _ List.mem_cons_self) frames parsed
  | later before later input key earlier ih =>
    exact mono before (before++later) (List.sublist_append_left _ _) ih

theorem helper_known {world : InputIndexedOracle.World} {history : List Observation} {input : Input} {context : NativeRootMessage.Digest}
    (known : NativeParentLineage.Known world history input context) : input ∈ inputs history := by
  induction known with
  | direct before entry frames parsed context helper =>
    exact of_observation _ entry (List.mem_append_right _ List.mem_cons_self) frames parsed
  | inherit before entry frames parsed parent context earlier quoted ih =>
    exact of_observation _ entry (List.mem_append_right _ List.mem_cons_self) frames parsed
  | later before later input context earlier ih =>
    exact mono before (before++later) (List.sublist_append_left _ _) ih

end
end FormalProof4FHE.HasteBoots.ParentSeedCandidates
