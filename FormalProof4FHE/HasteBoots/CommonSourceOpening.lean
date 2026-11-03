module

public import FormalProof4FHE.HasteBoots.ProximityOpening
public import FormalProof4FHE.HasteBoots.StructuredOpening

@[expose] public section

/-!
# Interactive opening soundness for a fixed available word

There is one decoded source per available word, used by every structured
response. The random matrix and all responses precede one shared column draw.
The two branches use a maximum of column losses, not an independence product.
This theorem concerns available words and encoded response checks; Merkle
availability, matrix-query finishing, and the production transcript law still
need their own refinement proofs.
-/

open ProbabilityTheory

namespace FormalProof4FHE.HasteBoots.CommonSourceOpening

noncomputable section

variable {F K Row Position Test Output : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fintype Row] [Fintype Position] [DecidableEq Position] {m b : ℕ}

/-- Responses are arbitrary functions of the earlier matrix. The shared column
draw is fresh only after those functions have selected their responses. -/
def experiment (b queries : ℕ) [SampleableType (Fin b → Row → F)]
    [SampleableType (Fin queries → Position)] :
    ProbComp ((Fin b → Row → F) × (Fin queries → Position)) := do
  let matrix ← $ᵗ (Fin b → Row → F)
  let draw ← $ᵗ (Fin queries → Position)
  pure (matrix, draw)

/-- Fixed-word soundness against responses depending on the random test matrix.
False values are measured against one total common decoder, including its
specified zero fallback in the far branch. -/
theorem soundness_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (radius queries : ℕ) (word : Position → Row → Fin b → F)
    (weights : Test → Row → F)
    (randomClaim : (Fin b → Row → F) → Position → K)
    (structuredClaim : (Fin b → Row → F) → Test → Position → Fin b → F)
    (finish : (Test → Position → Fin b → F) → Output)
    [SampleableType (Fin b → Row → F)] [SampleableType (Row → K)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3)
    (randomC : ∀ matrix, randomClaim matrix ∈
      ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m)
    (structuredC : ∀ matrix test, structuredClaim matrix test ∈ BlockCode.code domain m b) :
    let source := CommonSource.decode (BlockCode.code domain m b) radius word
    Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) b queries}[
      finish (structuredClaim pair.1) ≠
        finish (fun test => StructuredOpening.combine (weights test) source) ∧
      ColumnOpening.Agrees (ProximityOpening.randomWord basis word pair.1)
        (randomClaim pair.1) pair.2 ∧
      ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word)
        (structuredClaim pair.1 test) pair.2] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius))
        (ColumnOpening.missBound Position queries (radius + 1)) := by
  dsimp only
  let source := CommonSource.decode (BlockCode.code domain m b) radius word
  let nearEvent := fun (pair : (Fin b → Row → F) × (Fin queries → Position)) =>
    finish (structuredClaim pair.1) ≠
      finish (fun test => StructuredOpening.combine (weights test) source) ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word)
      (structuredClaim pair.1 test) pair.2
  let randomEvent := fun (pair : (Fin b → Row → F) × (Fin queries → Position)) =>
    ColumnOpening.Agrees (ProximityOpening.randomWord basis word pair.1)
      (randomClaim pair.1) pair.2
  let event := fun (pair : (Fin b → Row → F) × (Fin queries → Position)) =>
    finish (structuredClaim pair.1) ≠
      finish (fun test => StructuredOpening.combine (weights test) source) ∧
    randomEvent pair ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word)
      (structuredClaim pair.1 test) pair.2
  change Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) b queries}[
    event pair] ≤ _
  by_cases near : ∃ source, CommonSource.RowsIn (BlockCode.code domain m b) source ∧
      hammingDist word source ≤ radius
  · have decoded := CommonSource.decode_nearby (BlockCode.code domain m b) radius word near
    have bound := StructuredOpening.adaptive_near_falseValue_bound
      ($ᵗ (Fin b → Row → F)) (BlockCode.code domain m b) radius queries word
      (CommonSource.decode (BlockCode.code domain m b) radius word)
      weights structuredClaim finish decoded.1 decoded.2 structuredC
    have normalizedBound :
        Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) b queries}[
          nearEvent pair] ≤ ColumnOpening.missBound Position queries
            (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius) := by
      simpa only [experiment, nearEvent, source, ColumnOpening.missBound, prEvent_norm] using bound
    have reduced := (prEvent_mono (experiment b queries) event nearEvent
      (fun pair accepted => ⟨accepted.1, accepted.2.2⟩)).trans normalizedBound
    exact reduced.trans (by
      change ColumnOpening.missBound Position queries _ ≤ _
      calc _ = 0 + ColumnOpening.missBound Position queries _ := (zero_add _).symm
           _ ≤ _ := add_le_add zero_le (le_max_left _ _))
  · have bound := ProximityOpening.far_bound basis domain radius queries word randomClaim
      small near randomC
    have normalizedBound :
        Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) b queries}[
          randomEvent pair] ≤
        (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
          Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
        ColumnOpening.missBound Position queries (radius + 1) := by
      simpa only [experiment, randomEvent, ColumnOpening.missBound, prEvent_norm] using bound
    have reduced := (prEvent_mono (experiment b queries) event randomEvent
      (fun pair accepted => accepted.2.1)).trans normalizedBound
    exact reduced.trans (add_le_add le_rfl (le_max_right _ _))

end

end FormalProof4FHE.HasteBoots.CommonSourceOpening
