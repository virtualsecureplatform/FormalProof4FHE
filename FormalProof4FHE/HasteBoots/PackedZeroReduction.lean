module

public import FormalProof4FHE.HasteBoots.PackedZeroEquality

@[expose] public section

/-!
# Adaptive special-first-round reduction for packed ZeroCheck

The source relation is fixed first. The verifier samples k independent equality
points; an arbitrary probabilistic prover then chooses its first-message family.
Only afterwards are the mixing matrix and row challenges drawn jointly. A
boundary-valid first message yields a truthful reduced claim for a false source
relation with probability at most (n/card(F))^k + ((D+1)/card(F))^k.

This is the special reduction's private-coin bound, not complete ZeroCheck:
the remaining sumcheck and native suffix-layout adapters are supplied by
`PackedZeroCube` and `PackedZeroExecution`. Common authenticated sources and
production transcript execution remain composition obligations.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.PackedZeroReduction

noncomputable section

variable {F Factor Term Response : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Term] {n k : ℕ}

abbrev Points (F : Type) (n k : ℕ) := Fin k → Fin n → F
abbrev Coins (F : Type) (k : ℕ) := (Fin k → Fin k → F) × (Fin k → F)

def experiment [SampleableType (Points F n k)] [SampleableType (Coins F k)]
    (respond : Points F n k → ProbComp Response) : ProbComp ((Points F n k × Response) × Coins F k) := do
  let points ← $ᵗ (Points F n k)
  let response ← respond points
  let coins ← $ᵗ (Coins F k)
  pure ((points, response), coins)

def Healed (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → PackedZeroEquality.Cell n → Fin k → F)
    (interpret : Response → Fin k → Polynomial F)
    (outcome : (Points F n k × Response) × Coins F k) : Prop :=
  PackedZeroFirst.Boundary nodes (interpret outcome.1.2) ∧
    PackedZeroFirst.reduce (interpret outcome.1.2) outcome.2.1 outcome.2.2 =
      PackedZeroFirst.reduce (PackedZeroFirst.polynomial nodes arity coefficient indices tables
        (fun lane => PackedZeroEquality.equality (outcome.1.1 lane))) outcome.2.1 outcome.2.2

variable [SampleableType F] [SampleableType (Fin k → F)] [SampleableType (Fin n → F)]
  [SampleableType (Points F n k)] [SampleableType (Fin k → Fin k → F)]
  [SampleableType (Fin k → ((Fin k → F) × F))]

/-- The first-message procedure may correlate all its polynomial entries and
retain arbitrary probabilistic state in its response. No response enumeration
or message independence is assumed. -/
theorem healing_bound (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → PackedZeroEquality.Cell n → Fin k → F)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (respond : Points F n k → ProbComp Response) (interpret : Response → Fin k → Polynomial F)
    (messageDegree : ∀ response point, (interpret response point).natDegree ≤ (2 * k - 1) * productDegree)
    (falseRelation : ¬PackedZeroFirst.Vanishes arity coefficient indices tables) :
    Pr{let outcome ← experiment respond}[Healed nodes arity coefficient indices tables interpret outcome] ≤
      (((n : ENNReal) / Fintype.card F) ^ k) +
        ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
  let honest := fun points : Points F n k => PackedZeroFirst.polynomial nodes arity coefficient indices tables
    (fun lane => PackedZeroEquality.equality (points lane))
  have tailBound : ∀ points, ¬PackedZeroFirst.Boundary nodes (honest points) →
      Pr{let response ← respond points; let coins ← $ᵗ (Coins F k)}[
        PackedZeroFirst.Boundary nodes (interpret response) ∧
          PackedZeroFirst.reduce (interpret response) coins.1 coins.2 =
            PackedZeroFirst.reduce (honest points) coins.1 coins.2] ≤
        ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
    intro points outside
    have each (response : Response) :
        Pr{let coins ← $ᵗ (Coins F k)}[
          PackedZeroFirst.Boundary nodes (interpret response) ∧
            PackedZeroFirst.reduce (interpret response) coins.1 coins.2 =
              PackedZeroFirst.reduce (honest points) coins.1 coins.2] ≤
          ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
      by_cases checked : PackedZeroFirst.Boundary nodes (interpret response)
      · apply le_trans (prEvent_mono _ _ _ (fun _ accepted => accepted.2))
        exact PackedZeroMixing.mixing_bound (interpret response) (honest points) _
          (PackedZeroFirst.boundary_distinct nodes (interpret response) (honest points) checked outside)
          (messageDegree response)
          (PackedZeroFirst.polynomial_degree nodes arity coefficient indices tables _ productDegree bounded)
      · exact (le_of_eq (prEvent_eq_zero_of_forall_not _ _ (fun _ accepted => checked accepted.1))).trans zero_le
    simpa only [prEvent_norm] using prEvent_bind_le_of_forall_le (respond points)
      (fun response => do let coins ← $ᵗ (Coins F k); pure (response, coins))
      (fun pair => PackedZeroFirst.Boundary nodes (interpret pair.1) ∧
        PackedZeroFirst.reduce (interpret pair.1) pair.2.1 pair.2.2 =
          PackedZeroFirst.reduce (honest points) pair.2.1 pair.2.2)
      (fun response => by simpa only [prEvent_norm] using each response)
  have bound := prEvent_bind_le_prEvent_add ($ᵗ (Points F n k))
    (fun points => do
      let response ← respond points
      let coins ← $ᵗ (Coins F k)
      pure ((points, response), coins))
    (fun points => PackedZeroFirst.Boundary nodes (honest points))
    (Healed nodes arity coefficient indices tables interpret)
    (fun points outside => by simpa only [prEvent_norm, Healed] using tailBound points outside)
  exact bound.trans (add_le_add
    (PackedZeroEquality.boundary_miss_bound nodes arity coefficient indices tables falseRelation) le_rfl)

/-- Native D+1-entry vectors automatically supply every first-polynomial
degree bound. Their post-equality-point response distribution is unrestricted. -/
theorem native_healing_bound (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → PackedZeroEquality.Cell n → Fin k → F)
    (bounded : ∀ term, arity term ≤ productDegree)
    (respond : Points F n k → ProbComp (Fin k → Fin ((2 * k - 1) * productDegree + 1) → F))
    (falseRelation : ¬PackedZeroFirst.Vanishes arity coefficient indices tables) :
    Pr{let outcome ← experiment respond}[
      Healed (NativePackedInterpolation.nodes p (enough.trans small)) arity coefficient indices tables
        (fun response point => NativePackedInterpolation.messagePolynomial
          (NativePackedInterpolation.consecutive p small) (response point)) outcome] ≤
      (((n : ENNReal) / Fintype.card F) ^ k) +
        ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k)) :=
  healing_bound (NativePackedInterpolation.nodes p (enough.trans small)) arity coefficient indices tables
    productDegree bounded respond _ (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _) falseRelation

end

end FormalProof4FHE.HasteBoots.PackedZeroReduction
