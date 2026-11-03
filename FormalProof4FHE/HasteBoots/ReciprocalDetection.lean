module

public import FormalProof4FHE.HasteBoots.ReciprocalPolynomial
public import FormalProof4FHE.HasteBoots.PackedSumcheckProbability
public import VCVio.OracleComp.Constructions.UniformSelectMeasure

@[expose] public section

/-!
# Reciprocal detection over the native accepted challenge domain

Zero and every negative public-table hash are excluded. At most tableSize+1
values are excluded, even when public hashes coincide. Ideal uniform selection
from this domain supplies the reciprocal detection term, with all source and
public multiplicities fixed beforehand. This is a private-coin distributional
model; native rejection-loop/transcript/work refinement is not asserted here.
-/

open scoped BigOperators Classical
open OracleSpec OracleComp Polynomial

namespace FormalProof4FHE.HasteBoots.ReciprocalDetection

noncomputable section

open ReciprocalPolynomial

variable {K : Type} [Field K] [DecidableEq K] [Fintype K] {count size : ℕ}

def allowed (table : Fin size → K) : Finset K :=
  Finset.univ.filter (fun r => r ≠ 0 ∧ ∀ i, r + table i ≠ 0)

theorem mem_allowed (table : Fin size → K) (r : K) :
    r ∈ allowed table ↔ r ≠ 0 ∧ ∀ i, r + table i ≠ 0 := by simp [allowed]

theorem allowed_card_lower (table : Fin size → K) :
    Fintype.card K - size - 1 ≤ (allowed table).card := by
  classical
  let excluded : Finset K := Finset.univ.filter (fun r => ¬(r ≠ 0 ∧ ∀ i, r + table i ≠ 0))
  have subset : excluded ⊆ insert 0 (Finset.univ.image (fun i : Fin size => -table i)) := by
    intro r member
    have bad := (Finset.mem_filter.mp member).2
    by_cases zero : r = 0
    · exact Finset.mem_insert.mpr (Or.inl zero)
    · have failed : ¬∀ i, r + table i ≠ 0 := fun valid => bad ⟨zero, valid⟩
      obtain ⟨i, pole⟩ := not_forall.mp failed
      have equal : r = -table i := eq_neg_of_add_eq_zero_left (not_not.mp pole)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, equal.symm⟩))
  have imageBound := Finset.card_image_le (s := Finset.univ) (f := fun i : Fin size => -table i)
  have insertBound := Finset.card_insert_le 0 (Finset.univ.image (fun i : Fin size => -table i))
  have excludedBound := Finset.card_le_card subset
  simp only [Finset.card_univ, Fintype.card_fin] at imageBound
  have split := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K))
    (fun r => r ≠ 0 ∧ ∀ i, r + table i ≠ 0)
  simp only [Finset.card_univ] at split
  change (allowed table).card + excluded.card = Fintype.card K at split
  omega

theorem allowed_nonempty (table : Fin size → K) (enough : size + 1 < Fintype.card K) : (allowed table).Nonempty := by
  have lower := allowed_card_lower table
  apply Finset.card_pos.mp
  omega

/-- Ideal uniform law on accepted r values. Empty domains fail; native trusted
configuration will supply nonemptiness before rejection-loop refinement. -/
def sample (table : Fin size → K) : OptionT ProbComp K := $ (allowed table)

theorem sample_total (table : Fin size → K) (enough : size + 1 < Fintype.card K) :
    Pr{let _ ← sample table}[True] = 1 := by
  rw [sample, ProbComp.prEvent_uniformSelectFinset]
  simp only [Finset.filter_true]
  apply ENNReal.div_self
  · exact_mod_cast (Finset.card_pos.mpr (allowed_nonempty table enough)).ne'
  · simp

def Passes (sources : Fin count → K) (table multiplicities : Fin size → K) (r : K) : Prop :=
  ∃ helpers : Fin count → K, (∀ i, helpers i * (r + sources i) = 1) ∧
    (∑ i, helpers i) = ∑ i, multiplicities i * (r + table i)⁻¹

omit [DecidableEq K] [Fintype K] in
theorem passes_iff (sources : Fin count → K) (table multiplicities : Fin size → K) (r : K) :
    Passes sources table multiplicities r ↔ (∀ i, r + sources i ≠ 0) ∧
      (∑ i, (r + sources i)⁻¹) = ∑ i, multiplicities i * (r + table i)⁻¹ := by
  constructor
  · rintro ⟨helpers, valid, total⟩
    refine ⟨fun i => (reciprocal_forced _ _ _ (valid i)).1, ?_⟩
    rw [← total]
    exact Finset.sum_congr rfl (fun i _ => (reciprocal_forced _ _ _ (valid i)).2.symm)
  · rintro ⟨nonzero, total⟩
    exact ⟨fun i => (r + sources i)⁻¹, fun i => inv_mul_cancel₀ (nonzero i), total⟩

variable {p : ℕ} [CharP K p]

theorem passing_card (sources : Fin count → K) (table multiplicities : Fin size → K)
    (bad : ∃ i, ∀ j, sources i ≠ table j) (small : count < p) :
    ((allowed table).filter (Passes sources table multiplicities)).card ≤ count + size - 1 := by
  classical
  obtain ⟨i, outside⟩ := bad
  have positive : 0 < count := by have := i.isLt; omega
  have nonzero := numerator_ne_zero sources table multiplicities ⟨i, outside⟩ small
  have roots := PackedSumcheckProbability.agreement_card (numerator sources table multiplicities) 0 (count + size - 1)
    nonzero (numerator_degree sources table multiplicities positive) (by simp)
  have subset : (allowed table).filter (Passes sources table multiplicities) ⊆
      Finset.univ.filter (fun r => (numerator sources table multiplicities).eval r = 0) := by
    intro r member
    obtain ⟨inDomain, helpers, valid, total⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r,
      helper_identity_implies_root sources table multiplicities helpers r valid ((mem_allowed table r).mp inDomain).2 total⟩
  exact (Finset.card_le_card subset).trans (by simpa only [Polynomial.eval_zero] using roots)

theorem detection_bound (sources : Fin count → K) (table multiplicities : Fin size → K)
    (bad : ∃ i, ∀ j, sources i ≠ table j) (small : count < p) :
    Pr{let r ← sample table}[Passes sources table multiplicities r] ≤
      ((count + size - 1 : ℕ) : ENNReal) / ((Fintype.card K - size - 1 : ℕ) : ENNReal) := by
  classical
  rw [sample, ProbComp.prEvent_uniformSelectFinset]
  calc _ ≤ ((count + size - 1 : ℕ) : ENNReal) / ((allowed table).card : ENNReal) := by
         apply ENNReal.div_le_div_right
         exact_mod_cast passing_card sources table multiplicities bad small
       _ ≤ _ := by
         apply ENNReal.div_le_div_left
         exact_mod_cast allowed_card_lower table

end

end FormalProof4FHE.HasteBoots.ReciprocalDetection
