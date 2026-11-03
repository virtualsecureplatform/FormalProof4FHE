module

public import FormalProof4FHE.HasteBoots.PackedZeroFirst
public import FormalProof4FHE.HasteBoots.UniformImage

@[expose] public section

/-!
# Fresh matrix mixing in the special packed ZeroCheck round

At a point where a polynomial difference vector is nonzero, one uniform row
of the mixing matrix has an exactly uniform dot product. A selected nonzero
difference polynomial has at most D roots. Thus one fresh row/challenge pair
hides the vector with probability at most (D+1)/card(F), and k independent rows
give the kth power. The difference family is fixed before these coins.
Equality-point failure and production transcript compilation remain separate.
-/

open scoped BigOperators
open Polynomial

namespace FormalProof4FHE.HasteBoots.PackedZeroMixing

noncomputable section

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

def dot (values : Fin k → F) : (Fin k → F) →+ F where
  toFun coefficients := ∑ point, coefficients point * values point
  map_zero' := by simp
  map_add' := by intro first second; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [Fintype F] [DecidableEq F] in
theorem dot_surjective (values : Fin k → F) (nonzero : ∃ point, values point ≠ 0) :
    Function.Surjective (dot values) := by
  classical
  obtain ⟨point, nonzero⟩ := nonzero
  intro target
  refine ⟨Pi.single point (target / values point), ?_⟩
  simp [dot, Pi.single_apply, nonzero]

omit [DecidableEq F] in
/-- One nonzero entry suffices; the remaining entries may be arbitrarily
dependent. No invertibility of the complete mixing matrix is assumed. -/
theorem dot_zero_probability [SampleableType F] [SampleableType (Fin k → F)]
    (values : Fin k → F) (nonzero : ∃ point, values point ≠ 0) :
    Pr{let coefficients ← $ᵗ (Fin k → F)}[∑ point, coefficients point * values point = 0] =
      1 / (Fintype.card F : ENNReal) := by
  classical
  let : Fintype (dot values).ker := Fintype.ofFinite _
  let : SampleableType (dot values).ker := SampleableType.ofFintype _
  change Pr{let coefficients ← $ᵗ (Fin k → F)}[(dot values) coefficients = 0] = _
  simpa only [one_div] using
    (UniformImage.uniform_event (dot values) (dot_surjective values nonzero) (fun value => value = 0)).trans
      (SampleableType.prEvent_uniformSample_eq_singleton (0 : F))

/-- Independent function sampling raises any one-row event probability to
the number of rows, including repeated row outcomes. -/
theorem all_rows_probability {Row : Type} [Fintype Row] [SampleableType Row]
    [SampleableType (Fin k → Row)] (event : Row → Prop) :
    Pr{let rows ← $ᵗ (Fin k → Row)}[∀ lane, event (rows lane)] =
      (Pr{let row ← $ᵗ Row}[event row]) ^ k := by
  classical
  let good : Finset Row := Finset.univ.filter event
  have count : (Finset.univ.filter (fun rows : Fin k → Row => ∀ lane, event (rows lane))).card =
      good.card ^ k := by
    rw [← Fintype.card_subtype]
    calc _ = Fintype.card {rows : Fin k → Row // ∀ lane, rows lane ∈ good} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquivRight (fun _ => by simp only [good, Finset.mem_filter, Finset.mem_univ, true_and])
         _ = good.card ^ k := ColumnSampling.card_goodDraws good k
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample, count, Fintype.card_fun]
  simp only [Fintype.card_fin, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow, mul_pow, good]

def RowHides (difference : Fin k → F[X]) (row : (Fin k → F) × F) : Prop :=
  ∑ point, row.1 point * (difference point).eval row.2 = 0

/-- A root of one chosen nonzero component is the only exceptional point;
outside its roots the fresh row's dot product is uniformly distributed. -/
theorem row_bound [SampleableType F] [SampleableType (Fin k → F)]
    (difference : Fin k → F[X]) (degree : ℕ)
    (nonzero : ∃ point, difference point ≠ 0)
    (bounded : ∀ point, (difference point).natDegree ≤ degree) :
    Pr{let row ← $ᵗ ((Fin k → F) × F)}[RowHides difference row] ≤
      ((degree + 1 : ℕ) : ENNReal) / Fintype.card F := by
  obtain ⟨component, nonzero⟩ := nonzero
  have roots : Pr{let value ← $ᵗ F}[(difference component).eval value = 0] ≤
      (degree : ENNReal) / Fintype.card F := by
    rw [SampleableType.prEvent_uniformSample]
    apply ENNReal.div_le_div_right
    have count := PackedSumcheckProbability.agreement_card (difference component) 0 degree
      nonzero (bounded component) (by simp)
    simp only [Polynomial.eval_zero] at count
    exact_mod_cast count
  rw [← SampleableType.prEvent_uniformSample_pair_of_bijective
    (g := fun value coefficients => (coefficients, value)) (Equiv.prodComm F (Fin k → F)).bijective]
  have bound := prEvent_bind_le_prEvent_add ($ᵗ F)
    (fun value => do let coefficients ← $ᵗ (Fin k → F); pure (coefficients, value))
    (fun value => (difference component).eval value = 0) (RowHides difference)
    (ε := 1 / (Fintype.card F : ENNReal)) (by
    intro value outside
    simpa only [prEvent_norm, RowHides] using
      (dot_zero_probability (fun point => (difference point).eval value) ⟨component, outside⟩).le)
  simpa only [prEvent_norm, Nat.cast_add, Nat.cast_one, ENNReal.add_div] using
    bound.trans (add_le_add roots le_rfl)

/-- Fresh independent rows hide a fixed nonzero polynomial family only with
the kth power of the single-row bound. -/
theorem rows_bound [SampleableType F] [SampleableType (Fin k → F)]
    [SampleableType (Fin k → ((Fin k → F) × F))]
    (difference : Fin k → F[X]) (degree : ℕ)
    (nonzero : ∃ point, difference point ≠ 0)
    (bounded : ∀ point, (difference point).natDegree ≤ degree) :
    Pr{let rows ← $ᵗ (Fin k → ((Fin k → F) × F))}[∀ lane, RowHides difference (rows lane)] ≤
      ((((degree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k) := by
  rw [all_rows_probability]
  exact pow_le_pow_left₀ zero_le (row_bound difference degree nonzero bounded) k

/-- Regrouping the native matrix-then-row vector into independent row pairs. -/
def rowCoins : ((Fin k → Fin k → F) × (Fin k → F)) ≃ (Fin k → ((Fin k → F) × F)) where
  toFun coins lane := (coins.1 lane, coins.2 lane)
  invFun rows := (fun lane => (rows lane).1, fun lane => (rows lane).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- This bound uses one jointly uniform mixing matrix and challenge vector,
matching the atomic first-round phase's mathematical coin geometry. -/
theorem mixing_bound [SampleableType F] [SampleableType (Fin k → F)]
    [SampleableType (Fin k → Fin k → F)]
    [SampleableType (Fin k → ((Fin k → F) × F))]
    (sent honest : Fin k → F[X]) (degree : ℕ) (different : sent ≠ honest)
    (sentDegree : ∀ point, (sent point).natDegree ≤ degree)
    (honestDegree : ∀ point, (honest point).natDegree ≤ degree) :
    Pr{let coins ← $ᵗ ((Fin k → Fin k → F) × (Fin k → F))}[
      PackedZeroFirst.reduce sent coins.1 coins.2 = PackedZeroFirst.reduce honest coins.1 coins.2] ≤
      ((((degree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k) := by
  classical
  have nonzero : ∃ point, sent point - honest point ≠ 0 := by
    by_contra missing
    push Not at missing
    apply different
    funext point
    exact sub_eq_zero.mp (missing point)
  have bounded (point : Fin k) : (sent point - honest point).natDegree ≤ degree :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (sentDegree point) (honestDegree point))
  have bound := rows_bound (fun point => sent point - honest point) degree nonzero bounded
  rw [← SampleableType.prEvent_uniformSample_equiv (rowCoins (F := F) (k := k))
    (fun rows => ∀ lane, RowHides (fun point => sent point - honest point) (rows lane))] at bound
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro coins equal lane
  have same := congrFun equal lane
  change (∑ point, coins.1 lane point * (sent point - honest point).eval (coins.2 lane)) = 0
  simpa only [Polynomial.eval_sub, mul_sub, Finset.sum_sub_distrib, sub_eq_zero,
    PackedZeroFirst.reduce] using same

end

end FormalProof4FHE.HasteBoots.PackedZeroMixing
