module
public import FormalProof4FHE.HasteBoots.ReceiptFrameView
@[expose] public section

/-! Unique segmentation of a concatenation of marked nonempty groups.
Only group heads carry the marker. Duplicate contents and arbitrarily long
bodies are allowed; no common body lengths or retry bounds are assumed. -/
namespace FormalProof4FHE.HasteBoots.ReceiptGroupSegmentation
variable {α : Type}

def Block (marker : α → Bool) (entries : List α) : Prop :=
  ∃ first rest, entries = first :: rest ∧ marker first = true ∧ ∀ entry ∈ rest, marker entry = false

def front (marker : α → Bool) : List α → List α × List α
  | [] => ([],[])
  | first :: rest => if marker first then ([],first :: rest) else
      let later := front marker rest
      (first :: later.1,later.2)

theorem front_append (marker : α → Bool) (body suffix : List α)
    (bodyLabels : ∀ entry ∈ body, marker entry = false)
    (boundary : suffix = [] ∨ ∃ first rest, suffix = first :: rest ∧ marker first = true) :
    front marker (body ++ suffix) = (body,suffix) := by
  induction body with
  | nil =>
    rcases boundary with rfl | ⟨first,rest,rfl,label⟩
    · rfl
    · simp only [List.nil_append,front,label,ite_true]
  | cons first rest ih =>
    have label := bodyLabels first List.mem_cons_self
    have tail := ih (fun entry member => bodyLabels entry (List.mem_cons_of_mem _ member))
    simp only [List.cons_append,front,label,Bool.false_eq_true,ite_false,tail]

theorem boundary (marker : α → Bool) (groups : List (List α)) (valid : ∀ group ∈ groups, Block marker group) :
    groups.flatten = [] ∨ ∃ first rest, groups.flatten = first :: rest ∧ marker first = true := by
  cases groups with
  | nil => exact Or.inl rfl
  | cons group groups =>
    obtain ⟨first,rest,rfl,label,_⟩ := valid group List.mem_cons_self
    exact Or.inr ⟨first,rest ++ groups.flatten,rfl,label⟩

theorem unique (marker : α → Bool) (left right : List (List α))
    (leftValid : ∀ group ∈ left, Block marker group) (rightValid : ∀ group ∈ right, Block marker group)
    (same : left.flatten = right.flatten) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons group rest =>
      obtain ⟨first,tail,rfl,_,_⟩ := rightValid group List.mem_cons_self
      simp only [List.flatten_nil,List.flatten_cons,List.cons_append] at same
      contradiction
  | cons group rest ih =>
    obtain ⟨first,body,groupEq,firstLabel,bodyLabels⟩ := leftValid group List.mem_cons_self
    cases right with
    | nil =>
      simp only [List.flatten_cons,List.flatten_nil,groupEq,List.cons_append] at same
      contradiction
    | cons other remaining =>
      obtain ⟨head,tail,otherEq,headLabel,tailLabels⟩ := rightValid other List.mem_cons_self
      have full : first :: (body ++ rest.flatten) = head :: (tail ++ remaining.flatten) := by
        simpa only [List.flatten_cons,groupEq,otherEq,List.cons_append] using same
      have heads := List.cons.inj full
      have leftTail : ∀ entry ∈ rest, Block marker entry := fun entry member => leftValid entry (List.mem_cons_of_mem _ member)
      have rightTail : ∀ entry ∈ remaining, Block marker entry := fun entry member => rightValid entry (List.mem_cons_of_mem _ member)
      have scanned := congrArg (front marker) heads.2
      rw [front_append marker body rest.flatten bodyLabels (boundary marker rest leftTail),
        front_append marker tail remaining.flatten tailLabels (boundary marker remaining rightTail)] at scanned
      have bodies := congrArg Prod.fst scanned
      have suffixes := congrArg Prod.snd scanned
      change body = tail at bodies
      change rest.flatten = remaining.flatten at suffixes
      have equalGroup : group = other := by rw [groupEq,otherEq,heads.1,bodies]
      have equalRest := ih remaining leftTail rightTail suffixes
      rw [equalGroup,equalRest]

end FormalProof4FHE.HasteBoots.ReceiptGroupSegmentation
