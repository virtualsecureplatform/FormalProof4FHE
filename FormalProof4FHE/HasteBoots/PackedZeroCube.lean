module

public import FormalProof4FHE.HasteBoots.NativePackedZeroFirst
public import FormalProof4FHE.HasteBoots.PackedPublicEquality
public import FormalProof4FHE.HasteBoots.NativeEqualityTable

@[expose] public section

/-!
# Special first-round reduction on the ordered source cube

The equality-point probability space and the first-bit-first factor tables use
one exact coordinate bijection. Reindexing the first polynomial family gives
the earlier special-round bound for these same source tables. The truthful
reduced sum is the original factors folded once with the mixed EQ table appended.
This supplies the source identity needed for the remaining packed sumcheck.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.PackedZeroCube

noncomputable section

variable {F Factor Term Response : Type} [Field F] [Fintype Term] {n k : ℕ}

def Vanishes (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) : Prop :=
  ∀ cell lane, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables factor cell lane) = 0

def onCells (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) :
    Factor → Bool → PackedZeroEquality.Cell n → Fin k → F :=
  fun factor bit cell lane => tables factor (bit, (PackedEqualityCube.bits n).symm cell) lane

def firstPolynomials (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (points : PackedZeroReduction.Points F n k) : Fin k → Polynomial F :=
  PackedZeroFirst.polynomial nodes arity coefficient indices
    (fun factor bit suffix lane => tables factor (bit, suffix) lane)
    (fun point => PackedEqualityCube.weight (points point))

/-- Reindexing never changes either an equality-point coordinate or a factor source. -/
theorem firstPolynomials_eq (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) (points : PackedZeroReduction.Points F n k) :
    firstPolynomials nodes arity coefficient indices tables points =
      PackedZeroFirst.polynomial nodes arity coefficient indices (onCells tables)
        (fun point => PackedZeroEquality.equality (points point)) := by
  funext point
  simpa only [firstPolynomials, PackedZeroFirst.polynomial, PackedZeroFirst.cellPolynomial, PackedEqualityCube.weight, onCells,
    Equiv.symm_apply_apply] using
    (PackedEqualityCube.bits n).sum_comp (fun cell =>
      Polynomial.C (PackedZeroEquality.equality (points point) cell) *
        PackedZeroFirst.cellPolynomial nodes arity coefficient indices (onCells tables) cell)

theorem vanishes_onCells_iff (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) :
    PackedZeroFirst.Vanishes arity coefficient indices (onCells tables) ↔ Vanishes arity coefficient indices tables := by
  constructor
  · intro zero
    rintro ⟨bit, suffix⟩ lane
    simpa only [onCells, Equiv.symm_apply_apply] using zero bit (PackedEqualityCube.bits n suffix) lane
  · intro zero bit cell lane
    exact zero (bit, (PackedEqualityCube.bits n).symm cell) lane

/-- The appended EQ factor is public, while every original factor is folded
once by the same challenge pair returned in the first-round subclaim. -/
def reducedTables (nodes : PackedSumcheckRound.Node k ↪ F)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (points : PackedZeroReduction.Points F n k) (coins : PackedZeroReduction.Coins F k) :
    PackedSumcheckExecution.Tables F (Factor ⊕ Unit) n k :=
  Sum.elim (PackedSumcheckExecution.fold nodes tables coins.2)
    (fun _ => PackedPublicEquality.mixedTable points coins.1)

theorem reducedSum_eq (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) (points : PackedZeroReduction.Points F n k)
    (coins : PackedZeroReduction.Coins F k) :
    PackedSumcheckExecution.sum (fun term => arity term + 1) coefficient
      (PackedZeroFirst.reducedIndices arity indices) (reducedTables nodes tables points coins) =
        PackedZeroFirst.reduce (firstPolynomials nodes arity coefficient indices tables points) coins.1 coins.2 := by
  funext lane
  have truthful := PackedZeroFirst.reduce_honest nodes arity coefficient indices
    (fun factor bit suffix inLane => tables factor (bit, suffix) inLane)
    (fun point => PackedEqualityCube.weight (points point)) coins.1 coins.2 lane
  rw [firstPolynomials, truthful]
  apply Finset.sum_congr rfl
  intro suffix _
  have valuesEq : (fun factor => reducedTables nodes tables points coins factor suffix lane) =
      Sum.elim (fun factor => PackedSumcheckExecution.fold nodes tables coins.2 factor suffix lane)
        (fun _ => PackedPublicEquality.mixedTable points coins.1 suffix lane) := by
    funext factor
    cases factor <;> rfl
  rw [valuesEq, PackedZeroFirst.reduced_expression]
  rfl

section Probability

variable [Fintype F] [DecidableEq F] [SampleableType F]
  [SampleableType (Fin k → F)] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n k)] [SampleableType (Fin k → Fin k → F)]
  [SampleableType (Fin k → ((Fin k → F) × F))]

/-- Special-round healing on exactly the ordered cube sources used by the
remaining sumcheck, with an arbitrary adaptive probabilistic first message. -/
theorem healing_bound (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree)
    (respond : PackedZeroReduction.Points F n k → ProbComp Response)
    (interpret : Response → Fin k → Polynomial F)
    (messageDegree : ∀ response point, (interpret response point).natDegree ≤ (2 * k - 1) * productDegree)
    (falseRelation : ¬Vanishes arity coefficient indices tables) :
    Pr{let outcome ← PackedZeroReduction.experiment respond}[
      PackedZeroFirst.Boundary nodes (interpret outcome.1.2) ∧
        PackedZeroFirst.reduce (interpret outcome.1.2) outcome.2.1 outcome.2.2 =
          PackedSumcheckExecution.sum (fun term => arity term + 1) coefficient
            (PackedZeroFirst.reducedIndices arity indices) (reducedTables nodes tables outcome.1.1 outcome.2)] ≤
      (((n : ENNReal) / Fintype.card F) ^ k) +
        ((((((2 * k - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ k)) := by
  have falseCells : ¬PackedZeroFirst.Vanishes arity coefficient indices (onCells tables) :=
    fun zero => falseRelation ((vanishes_onCells_iff arity coefficient indices tables).mp zero)
  have bound := PackedZeroReduction.healing_bound nodes arity coefficient indices (onCells tables)
    productDegree bounded respond interpret messageDegree falseCells
  change Pr{let outcome ← PackedZeroReduction.experiment respond}[
    PackedZeroFirst.Boundary nodes (interpret outcome.1.2) ∧
      PackedZeroFirst.reduce (interpret outcome.1.2) outcome.2.1 outcome.2.2 =
        PackedZeroFirst.reduce (PackedZeroFirst.polynomial nodes arity coefficient indices (onCells tables)
          (fun point => PackedZeroEquality.equality (outcome.1.1 point))) outcome.2.1 outcome.2.2] ≤ _ at bound
  simpa only [reducedSum_eq, firstPolynomials_eq] using bound

end Probability

end

end FormalProof4FHE.HasteBoots.PackedZeroCube
