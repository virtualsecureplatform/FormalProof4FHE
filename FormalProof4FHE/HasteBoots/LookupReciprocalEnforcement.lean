module

public import FormalProof4FHE.HasteBoots.ExtensionLookupIdentity
public import FormalProof4FHE.HasteBoots.ReciprocalDetection

@[expose] public section

/-!
# Lookup arithmetic forced by truthful Boolean identities and helper sums

The helper is interpreted in its original scalar Boolean order. Exact masked
identities and its full sum imply the active-source reciprocal event used by
the hash/reciprocal pair bound. Thus failure of that event leaves a false sum
or a false Boolean identity for sumcheck/ZeroCheck to detect. Neither original
source padding nor an accepted lookup flag is supplied as a soundness premise.
The operational sumcheck and original-root openings still need composition.
-/

open scoped BigOperators Classical

namespace FormalProof4FHE.HasteBoots.LookupReciprocalEnforcement

noncomputable section

variable {K : Type} [Field K] {n count padding size : ℕ}

def cells (shape : count + padding = 2 ^ n) : Fin (count + padding) ≃ MatrixFold.Cube n :=
  (finCongr shape).trans (FlatMatrixFold.index n).symm

theorem cells_address (shape : count + padding = 2 ^ n) (i : Fin (count + padding)) :
    (FlatMatrixFold.index n (cells shape i)).val = i.val := by simp [cells]

def activeSource (shape : count + padding = 2 ^ n) (sources : MatrixFold.Cube n → K) : Fin count → K :=
  fun i => sources (cells shape (i.castAdd padding))

/-- Literal helper sum and pointwise masked relations force the pair's
semantic reciprocal event, including zero inactive helpers for nonzero r. -/
theorem passes_of_checks (shape : count + padding = 2 ^ n) (r : K)
    (sources helpers : MatrixFold.Cube n → K) (table multiplicities : Fin size → K)
    (rNonzero : r ≠ 0)
    (valid : ∀ cell, ReciprocalMask.residual r (sources cell) (helpers cell)
      (decide ((FlatMatrixFold.index n cell).val < count)) = 0)
    (total : (∑ cell, helpers cell) = ∑ i, multiplicities i * (r + table i)⁻¹) :
    ReciprocalDetection.Passes (activeSource shape sources) table multiplicities r := by
  have flatValid (i : Fin (count + padding)) :
      ReciprocalMask.residual r (sources (cells shape i)) (helpers (cells shape i)) (decide (i.val < count)) = 0 := by
    simpa only [cells_address] using valid (cells shape i)
  have flatTotal : (∑ i : Fin (count + padding), helpers (cells shape i)) =
      ∑ i, multiplicities i * (r + table i)⁻¹ := (cells shape).sum_comp helpers |>.trans total
  apply (ReciprocalDetection.passes_iff _ _ _ _).mpr
  constructor
  · intro i
    have check := flatValid (i.castAdd padding)
    have flag : decide ((i.castAdd padding).val < count) = true := by simp
    rw [flag] at check
    exact (ReciprocalMask.active_forced _ _ _ check).1
  · exact (ReciprocalMask.prefix_sum r (fun i => sources (cells shape i)) (fun i => helpers (cells shape i))
      rNonzero flatValid).symm.trans flatTotal

/-- No probabilistic certificate is assumed: a nonpassing pair concretely
forces one of the two exact source relations to be false. -/
theorem not_passes_obstruction (shape : count + padding = 2 ^ n) (r : K)
    (sources helpers : MatrixFold.Cube n → K) (table multiplicities : Fin size → K) (rNonzero : r ≠ 0)
    (notPasses : ¬ReciprocalDetection.Passes (activeSource shape sources) table multiplicities r) :
    (∑ cell, helpers cell) ≠ ∑ i, multiplicities i * (r + table i)⁻¹ ∨
      ∃ cell, ReciprocalMask.residual r (sources cell) (helpers cell)
        (decide ((FlatMatrixFold.index n cell).val < count)) ≠ 0 := by
  by_cases total : (∑ cell, helpers cell) = ∑ i, multiplicities i * (r + table i)⁻¹
  · right
    by_contra noBad
    have valid : ∀ cell, ReciprocalMask.residual r (sources cell) (helpers cell)
        (decide ((FlatMatrixFold.index n cell).val < count)) = 0 := by
      simpa only [not_exists, not_not] using noBad
    exact notPasses (passes_of_checks shape r sources helpers table multiplicities rNonzero valid total)
  · exact Or.inl total

/-- After the pair and helper are fixed, a nonpassing pair with a truthful
helper sum survives a fresh EQ reduction with probability at most n/card(K). -/
theorem equality_bound {F : Type} [Field F] [Algebra F K] [Fintype K] [SampleableType K]
    [SampleableType (Fin n → K)] {width : ℕ}
    (shape : count + padding = 2 ^ n) (r y : K) (sources : Fin width → MatrixFold.Cube n → F)
    (helpers : MatrixFold.Cube n → K) (table multiplicities : Fin size → K) (rNonzero : r ≠ 0)
    (notPasses : ¬ReciprocalDetection.Passes
      (activeSource shape (ExtensionLookupIdentity.hashTable y sources)) table multiplicities r)
    (total : (∑ cell, helpers cell) = ∑ i, multiplicities i * (r + table i)⁻¹) :
    Pr{let eqPoint ← $ᵗ (Fin n → K)}[
      (∑ cell, PackedSumcheckRound.expression ExtensionLookupIdentity.partialArity
        (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
        (fun factor => ExtensionLookupIdentity.factors eqPoint y sources helpers count factor cell)) = 0] ≤
      (n : ENNReal) / Fintype.card K := by
  have bad := (not_passes_obstruction shape r (ExtensionLookupIdentity.hashTable y sources) helpers
    table multiplicities rNonzero notPasses).resolve_left (not_not.mpr total)
  exact ExtensionLookupIdentity.equality_miss_bound r y sources helpers count bad

end

end FormalProof4FHE.HasteBoots.LookupReciprocalEnforcement
