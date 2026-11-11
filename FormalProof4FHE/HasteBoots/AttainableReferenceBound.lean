module
public import FormalProof4FHE.HasteBoots.JobReferenceFixation
@[expose] public section

/-! A reference is chosen only from an actually inhabited good witness class.
If none exists, the whole event on that region is covered by bad mass. This
pointwise outer-measure argument needs neither a measurable chooser nor a
positive lower bound on good-event or successful-run probability. -/
namespace FormalProof4FHE.HasteBoots.AttainableReferenceBound
open MeasureTheory
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem choose_or_cover (region event bad : Set Ω) (Witness : Ω → Type) (Good : (world : Ω) → Witness world → Prop)
    (witness : ∀ world ∈ region, world ∈ event → world ∉ bad → Nonempty (Witness world))
    (good : ∀ world ∈ region, world ∉ bad → ∀ candidate : Witness world, Good world candidate) :
    (∃ world ∈ region, ∃ candidate : Witness world, Good world candidate) ∨ region ∩ event ⊆ bad := by
  by_cases attained : ∃ world ∈ region, ∃ candidate : Witness world, Good world candidate
  · exact Or.inl attained
  · apply Or.inr
    rintro world ⟨member,occurred⟩
    by_contra safe
    obtain ⟨candidate⟩ := witness world member occurred safe
    exact attained ⟨world,member,candidate,good world member safe candidate⟩

theorem measure_le (measure : Measure Ω) (region event bad : Set Ω) (Witness : Ω → Type)
    (Good : (world : Ω) → Witness world → Prop) (test : (world : Ω) → Witness world → Set Ω) (risk : ENNReal)
    (witness : ∀ world ∈ region, world ∈ event → world ∉ bad → Nonempty (Witness world))
    (good : ∀ world ∈ region, world ∉ bad → ∀ candidate : Witness world, Good world candidate)
    (covered : ∀ reference ∈ region, ∀ candidate : Witness reference, Good reference candidate →
      ∀ world ∈ region, world ∈ event → world ∈ bad ∨ world ∈ test reference candidate)
    (bounded : ∀ reference ∈ region, ∀ candidate : Witness reference, Good reference candidate → measure (region ∩ test reference candidate) ≤ risk) :
    measure (region ∩ event) ≤ measure (region ∩ bad) + risk := by
  rcases choose_or_cover region event bad Witness Good witness good with ⟨reference,member,candidate,goodReference⟩ | allBad
  · have included : region ∩ event ⊆ (region ∩ bad) ∪ (region ∩ test reference candidate) := by
      rintro world ⟨inside,occurred⟩
      rcases covered reference member candidate goodReference world inside occurred with bad | tested
      · exact Or.inl ⟨inside,bad⟩
      · exact Or.inr ⟨inside,tested⟩
    exact (measure_mono included).trans ((measure_union_le _ _).trans (add_le_add le_rfl (bounded reference member candidate goodReference)))
  · have included : region ∩ event ⊆ region ∩ bad := fun _ member => ⟨member.1,allBad member⟩
    exact (measure_mono included).trans (le_add_of_nonneg_right (by exact zero_le))

end
end FormalProof4FHE.HasteBoots.AttainableReferenceBound
