module

public import FormalProof4FHE.HasteBoots.PackedSumcheckRound
public import FormalProof4FHE.HasteBoots.ColumnSampling
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# Independent-lane packed round soundness

A false running claim forces the checked message polynomial to differ from the
honest scalar round polynomial. All k new lane claims can be correct only if
all k independent field challenges are roots of this one nonzero difference.
The error is (D/card(F))^k, not a union over lanes. This is an interactive
one-round bound; adaptive round composition and production Fiat--Shamir remain
separate obligations.
-/

open scoped BigOperators
open Polynomial

namespace FormalProof4FHE.HasteBoots.PackedSumcheckProbability

noncomputable section

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

/-- Scalar agreement points of two distinct degree-bounded polynomials. -/
theorem agreement_card (sent honest : F[X]) (degree : ℕ)
    (different : sent ≠ honest) (sentDegree : sent.natDegree ≤ degree)
    (honestDegree : honest.natDegree ≤ degree) :
    (Finset.univ.filter (fun point => sent.eval point = honest.eval point)).card ≤ degree := by
  classical
  have nonzero : sent - honest ≠ 0 := sub_ne_zero.mpr different
  have subset : Finset.univ.filter (fun point => sent.eval point = honest.eval point) ⊆
      (sent - honest).roots.toFinset := by
    intro point member
    rw [Multiset.mem_toFinset, Polynomial.mem_roots nonzero]
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero] using (Finset.mem_filter.mp member).2
  exact (Finset.card_le_card subset).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans ((Polynomial.natDegree_sub_le _ _).trans (max_le sentDegree honestDegree))))

/-- Exact repeated-sample law; repeated field elements still count as k draws. -/
theorem all_agree_probability (sent honest : F[X]) (k : ℕ)
    [SampleableType (Fin k → F)] :
    Pr{let challenge ← $ᵗ (Fin k → F)}[∀ lane, sent.eval (challenge lane) = honest.eval (challenge lane)] =
      (((Finset.univ.filter (fun point => sent.eval point = honest.eval point)).card : ENNReal) /
        Fintype.card F) ^ k := by
  classical
  let good := Finset.univ.filter (fun point => sent.eval point = honest.eval point)
  have count : (Finset.univ.filter (fun challenge : Fin k → F =>
      ∀ lane, sent.eval (challenge lane) = honest.eval (challenge lane))).card = good.card ^ k := by
    rw [← Fintype.card_subtype]
    calc _ = Fintype.card {challenge : Fin k → F // ∀ lane, challenge lane ∈ good} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquivRight (fun _ => by simp only [good, Finset.mem_filter, Finset.mem_univ, true_and])
         _ = good.card ^ k := ColumnSampling.card_goodDraws good k
  rw [SampleableType.prEvent_uniformSample, count, Fintype.card_fun]
  simp only [Fintype.card_fin, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow, mul_pow, good]

/-- All independent output lanes can heal only at roots of the difference. -/
theorem all_agree_bound (sent honest : F[X]) (degree k : ℕ)
    [SampleableType (Fin k → F)] (different : sent ≠ honest)
    (sentDegree : sent.natDegree ≤ degree) (honestDegree : honest.natDegree ≤ degree) :
    Pr{let challenge ← $ᵗ (Fin k → F)}[∀ lane, sent.eval (challenge lane) = honest.eval (challenge lane)] ≤
      ((degree : ENNReal) / Fintype.card F) ^ k := by
  rw [all_agree_probability]
  apply pow_le_pow_left₀ zero_le
  apply ENNReal.div_le_div_right
  exact_mod_cast agreement_card sent honest degree different sentDegree honestDegree

omit [Fintype F] [DecidableEq F] in
/-- The actual native adjacent-node check, interpreted as a polynomial. -/
def Checks (nodes : PackedSumcheckRound.Node k ↪ F) (claimed : Fin k → F) (sent : F[X]) : Prop :=
  ∀ lane, sent.eval (nodes (false, lane)) + sent.eval (nodes (true, lane)) = claimed lane

omit [Fintype F] [DecidableEq F] in
/-- A checked false claim cannot be represented by the honest round polynomial. -/
theorem checked_distinct (nodes : PackedSumcheckRound.Node k ↪ F)
    (claimed correct : Fin k → F) (sent honest : F[X])
    (falseClaim : claimed ≠ correct) (checked : Checks nodes claimed sent)
    (truthful : Checks nodes correct honest) : sent ≠ honest := by
  intro equal
  subst sent
  apply falseClaim
  funext lane
  exact (checked lane).symm.trans (truthful lane)

/-- One packed round: a checked false running claim becomes entirely truthful
only with the independent-lane root probability. Rejection is retained. -/
theorem false_claim_healing_bound (nodes : PackedSumcheckRound.Node k ↪ F)
    (claimed correct : Fin k → F) (sent honest : F[X]) (degree : ℕ)
    [SampleableType (Fin k → F)] (falseClaim : claimed ≠ correct)
    (truthful : Checks nodes correct honest) (sentDegree : sent.natDegree ≤ degree)
    (honestDegree : honest.natDegree ≤ degree) :
    Pr{let challenge ← $ᵗ (Fin k → F)}[
      Checks nodes claimed sent ∧ ∀ lane, sent.eval (challenge lane) = honest.eval (challenge lane)] ≤
      ((degree : ENNReal) / Fintype.card F) ^ k := by
  by_cases checked : Checks nodes claimed sent
  · exact (prEvent_mono _ _ _ (fun _ accepted => accepted.2)).trans
      (all_agree_bound sent honest degree k (checked_distinct nodes claimed correct sent honest
        falseClaim checked truthful) sentDegree honestDegree)
  · exact (le_of_eq (prEvent_eq_zero_of_forall_not _ _ (fun _ accepted => checked accepted.1))).trans zero_le

/-- The honest factor-table polynomial supplies both the degree and node-check
premises, including repeated factors in a product. -/
theorem round_healing_bound {Factor Suffix Term : Type} [Fintype Suffix] [Fintype Term]
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (productDegree : ℕ)
    (bounded : ∀ term, arity term ≤ productDegree) (claimed : Fin k → F) (sent : F[X])
    [SampleableType (Fin k → F)]
    (falseClaim : claimed ≠ PackedSumcheckRound.claim arity coefficient indices tables)
    (sentDegree : sent.natDegree ≤ (2 * k - 1) * productDegree) :
    Pr{let challenge ← $ᵗ (Fin k → F)}[
      Checks nodes claimed sent ∧ ∀ lane, sent.eval (challenge lane) =
        (PackedSumcheckRound.polynomial nodes arity coefficient indices tables).eval (challenge lane)] ≤
      ((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k :=
  false_claim_healing_bound nodes claimed _ sent _ _ falseClaim
    (PackedSumcheckRound.polynomial_check nodes arity coefficient indices tables) sentDegree
    (PackedSumcheckRound.polynomial_degree nodes arity coefficient indices tables productDegree bounded)

end

end FormalProof4FHE.HasteBoots.PackedSumcheckProbability
