module

public import FormalProof4FHE.HasteBoots.CachedOracleResponse
@[expose] public section

/-! Exact finite masked-word counting. Previously revealed coordinates are
fixed; unobserved coordinates remain independent uniform bytes. Inconsistent
targets contribute zero and compatible targets are counted without overlap. -/
namespace FormalProof4FHE.HasteBoots.OracleMaskCounting
open InputIndexedOracle (Byte)
open MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I]

def mask (known : Finset I) (saved raw : I → Byte) : I → Byte :=
  fun index => if index ∈ known then saved index else raw index

def compatible (known : Finset I) (saved target : I → Byte) : Prop :=
  ∀ index ∈ known, saved index = target index

/-- The raw mask fiber of a compatible target has one free raw byte per already-known position. -/
def fiberEquiv (known : Finset I) (saved target : I → Byte) (agrees : compatible known saved target) :
    {raw : I → Byte // mask known saved raw = target} ≃ (known → Byte) where
  toFun raw := fun index => raw.val index
  invFun values := ⟨fun index => if member : index ∈ known then values ⟨index,member⟩ else target index,by
    funext index
    by_cases member : index ∈ known
    · exact (ite_eq_left member).trans (agrees index member)
    · simp [mask,member]⟩
  left_inv raw := by
    apply Subtype.ext
    funext index
    by_cases member : index ∈ known
    · simp [member]
    · have same := congrFun raw.property index
      simpa [mask,member] using same.symm
  right_inv values := by
    funext index
    simp [index.property]

/-- Inconsistent targets have empty fibers; compatible targets have the same exact fiber cardinality. -/
theorem fiber_card (known : Finset I) (saved target : I → Byte) :
    Fintype.card {raw : I → Byte // mask known saved raw = target} =
      if compatible known saved target then 256 ^ known.card else 0 := by
  classical
  split
  · rename_i agrees
    rw [Fintype.card_congr (fiberEquiv known saved target agrees)]
    simp [Byte]
  · rename_i disagrees
    have empty : IsEmpty {raw : I → Byte // mask known saved raw = target} := by
      constructor
      rintro ⟨raw,equal⟩
      apply disagrees
      intro index member
      have same := congrFun equal index
      simpa [mask,member] using same
    exact Fintype.card_eq_zero


/-- Partition raw responses by their actual target; distinct targets have disjoint fibers. -/
def targetEquiv (known : Finset I) (saved : I → Byte) (targets : Finset (I → Byte)) :
    {raw : I → Byte // mask known saved raw ∈ targets} ≃
      (Σ target : targets, {raw : I → Byte // mask known saved raw = target.val}) where
  toFun raw := ⟨⟨mask known saved raw.val,raw.property⟩,⟨raw.val,rfl⟩⟩
  invFun pair := ⟨pair.2.val,by rw [pair.2.property]; exact pair.1.property⟩
  left_inv raw := rfl
  right_inv pair := by
    rcases pair with ⟨⟨target,member⟩,raw,equal⟩
    dsimp at equal ⊢
    subst target
    rfl

/-- Count exactly the raw responses whose masked word belongs to the target set. -/
theorem targets_card (known : Finset I) (saved : I → Byte) (targets : Finset (I → Byte)) :
    Fintype.card {raw : I → Byte // mask known saved raw ∈ targets} =
      (targets.filter (compatible known saved)).card * 256 ^ known.card := by
  classical
  rw [Fintype.card_congr (targetEquiv known saved targets),Fintype.card_sigma]
  simp only [fiber_card]
  rw [Finset.sum_coe_sort targets (fun target => if compatible known saved target then 256 ^ known.card else 0)]
  simp only [← Finset.sum_filter]
  rw [Finset.sum_const,smul_eq_mul]


/-- Exact target-hit probability, with denominator determined by the remaining unseen bytes. -/
theorem targets_probability (known : Finset I) (saved : I → Byte) (targets : Finset (I → Byte)) :
    ((uniformOn (Set.univ : Set (I → Byte))).map (mask known saved)) (targets : Set (I → Byte)) =
      ((targets.filter (compatible known saved)).card : ENNReal) /
        (256 : ENNReal) ^ (Fintype.card I-known.card) := by
  classical
  rw [Measure.map_apply (Measurable.of_discrete) targets.measurableSet]
  have preimage : (mask known saved) ⁻¹' (targets : Set (I → Byte)) =
      (↑(Finset.univ.filter (fun raw => mask known saved raw ∈ targets)) : Set (I → Byte)) := by
    ext raw
    simp
  rw [preimage,show (Set.univ : Set (I → Byte)) = (↑(Finset.univ : Finset (I → Byte)) : Set (I → Byte)) by simp,
    uniformOn_apply_finset]
  simp only [Finset.univ_inter,Finset.card_univ]
  have count := targets_card known saved targets
  rw [Fintype.card_subtype] at count
  rw [count]
  simp only [Fintype.card_fun,Fintype.card_fin,Byte,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have size : known.card ≤ Fintype.card I := Finset.card_le_univ _
  have split : (256 : ENNReal) ^ Fintype.card I =
      (256 : ENNReal) ^ (Fintype.card I-known.card) * (256 : ENNReal)^known.card := by
    rw [← pow_add]
    congr 1
    omega
  rw [split]
  exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

end
end FormalProof4FHE.HasteBoots.OracleMaskCounting
