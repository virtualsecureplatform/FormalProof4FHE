module
public import FormalProof4FHE.HasteBoots.ReceiptGroupSegmentation
public import FormalProof4FHE.HasteBoots.LookupBatchReceiptLabels
public import FormalProof4FHE.HasteBoots.EqualityReceiptLabels
import all FormalProof4FHE.HasteBoots.NativeLookupChallenge
import all FormalProof4FHE.HasteBoots.NativeLookupEquality
import all FormalProof4FHE.HasteBoots.NativeTranscript
@[expose] public section

/-! Native receipt labels uniquely separate lookup jobs and the equality
suffix. No previous-group counts, body lengths or rejection bounds are used. -/
namespace FormalProof4FHE.HasteBoots.ReceiptLabelSegmentation
open InputIndexedOracle (World)
open TranscriptFrame (Frame)
open NativeLookupChallenge (hashLabel reciprocalLabel)
noncomputable section

theorem hash_ne_reciprocal : hashLabel ≠ reciprocalLabel := by
  unfold hashLabel reciprocalLabel NativeTranscript.utf8
  decide +kernel

theorem hash_ne_equality : hashLabel ≠ NativeLookupEquality.pointLabel := by
  unfold hashLabel NativeLookupEquality.pointLabel NativeTranscript.utf8
  decide +kernel

theorem reciprocal_ne_equality : reciprocalLabel ≠ NativeLookupEquality.pointLabel := by
  unfold reciprocalLabel NativeLookupEquality.pointLabel NativeTranscript.utf8
  decide +kernel

def Group (entries : List Frame) : Prop :=
  ∃ first rest, entries = first :: rest ∧ first.label = hashLabel ∧ ∀ entry ∈ rest, entry.label = reciprocalLabel

theorem native_group {K : Type} (world : World) (draws : List (NativeLookupChallenge.Draw K))
    (labels : LookupReceiptLabels.Group draws) : Group (draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase)) := by
  obtain ⟨first,rest,rfl,head,tail⟩ := labels
  refine ⟨_,_,rfl,head,?_⟩
  intro entry member
  obtain ⟨draw,drawMember,rfl⟩ := List.mem_map.mp member
  exact tail draw drawMember

theorem marked (entries : List Frame) (valid : Group entries) :
    ReceiptGroupSegmentation.Block (fun entry : Frame => decide (entry.label = hashLabel)) entries := by
  obtain ⟨first,rest,rfl,head,tail⟩ := valid
  refine ⟨first,rest,rfl,by simp only [head,decide_true],?_⟩
  intro entry member
  simp only [tail entry member,Ne.symm hash_ne_reciprocal,decide_false]

theorem not_equality (entries : List Frame) (valid : Group entries) (entry : Frame) (member : entry ∈ entries) :
    entry.label ≠ NativeLookupEquality.pointLabel := by
  obtain ⟨first,rest,rfl,head,tail⟩ := valid
  rcases List.mem_cons.mp member with rfl | later
  · rw [head]; exact hash_ne_equality
  · rw [tail entry later]; exact reciprocal_ne_equality

theorem groups_unique (left right : List (List Frame)) (leftValid : ∀ group ∈ left, Group group)
    (rightValid : ∀ group ∈ right, Group group) (same : left.flatten = right.flatten) : left = right :=
  ReceiptGroupSegmentation.unique _ left right (fun group member => marked group (leftValid group member))
    (fun group member => marked group (rightValid group member)) same

/-- Recover the lookup/equality boundary from the equality label, then
recover every lookup group by its unique compression head. -/
theorem prelude_unique (left right : List (List Frame)) (leftEQ rightEQ : List Frame)
    (leftValid : ∀ group ∈ left, Group group) (rightValid : ∀ group ∈ right, Group group)
    (leftLabels : ∀ entry ∈ leftEQ, entry.label = NativeLookupEquality.pointLabel)
    (rightLabels : ∀ entry ∈ rightEQ, entry.label = NativeLookupEquality.pointLabel)
    (same : left.flatten ++ leftEQ = right.flatten ++ rightEQ) : left = right ∧ leftEQ = rightEQ := by
  let marker := fun entry : Frame => decide (entry.label = NativeLookupEquality.pointLabel)
  have earlier (groups : List (List Frame)) (valid : ∀ group ∈ groups, Group group) :
      ∀ entry ∈ groups.flatten, marker entry = false := by
    intro entry member
    obtain ⟨group,present,member⟩ := List.mem_flatten.mp member
    simp only [marker,not_equality group (valid group present) entry member,decide_false]
  have boundary (entries : List Frame) (labels : ∀ entry ∈ entries, entry.label = NativeLookupEquality.pointLabel) :
      entries = [] ∨ ∃ first rest, entries = first :: rest ∧ marker first = true := by
    cases entries with
    | nil => exact Or.inl rfl
    | cons first rest => exact Or.inr ⟨first,rest,rfl,by simp only [marker,labels first List.mem_cons_self,decide_true]⟩
  have scanned := congrArg (ReceiptGroupSegmentation.front marker) same
  rw [ReceiptGroupSegmentation.front_append marker left.flatten leftEQ (earlier left leftValid) (boundary leftEQ leftLabels),
    ReceiptGroupSegmentation.front_append marker right.flatten rightEQ (earlier right rightValid) (boundary rightEQ rightLabels)] at scanned
  have grouped : left.flatten = right.flatten := congrArg Prod.fst scanned
  exact ⟨groups_unique left right leftValid rightValid grouped,congrArg Prod.snd scanned⟩

end
end FormalProof4FHE.HasteBoots.ReceiptLabelSegmentation
