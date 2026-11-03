module

public import ArkLib.Data.CodingTheory.ProximityGap.AHIV22

@[expose] public section

/-!
# Fixed-word row-span proximity bound

A checked specialization of AHIV22 Lemma 4.5 to the minimum-distance interface
used here. The sampler is UNIFORM ON THE ROW SPAN of an available fixed word.
The production matrix challenge samples base-field coefficients instead:
`SymbolLift` and `RowSpanSampling` prove its interactive pushforward to this
law. The production XOF and authenticated-word bridges remain separate.
No Fiat--Shamir freshness or Merkle availability claim is made here.
-/

open Code ProbabilityTheory
open scoped ProbabilityTheory

namespace FormalProof4FHE.HasteBoots.RowSpanProximity

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {Position : Type} [Fintype Position] {Row : Type*} [Fintype Row]

/-- A far interleaved word has few close uniformly sampled row-span elements. -/
theorem fixedWord_bound (domain : Position ↪ K) (m radius : ℕ)
    (word : WordStack (A := K) Row Position)
    [SampleableType (Matrix.rowSpan word)]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code domain m : Set (Position → K)) : ℚ≥0) / 3)
    (far : radius < Code.distFromCode (⋈|word)
      ((ReedSolomon.code domain m)^⋈Row)) :
    Pr{let sampled ← $ᵗ (Matrix.rowSpan word)}[
      Code.distFromCode (sampled : Position → K)
        (ReedSolomon.code domain m : Set (Position → K)) ≤ radius] ≤
      (Code.minDist (ReedSolomon.code domain m : Set (Position → K)) : ENNReal) /
        Fintype.card K := by
  have h := ProximityToRS.prob_of_bad_pts (U_star := word)
    (by simpa only [Code.dist_eq_minDist] using small) far
  simpa only [Code.dist_eq_minDist, ← Nat.card_eq_fintype_card] using h

end

end FormalProof4FHE.HasteBoots.RowSpanProximity
