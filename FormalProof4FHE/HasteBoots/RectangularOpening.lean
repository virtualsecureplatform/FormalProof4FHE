module

public import FormalProof4FHE.HasteBoots.RectangularBaseProximity
public import FormalProof4FHE.HasteBoots.BlockEncoder

@[expose] public section

/-! Fixed-available-word opening soundness with independent test and symbol
widths. All response families use one ordered column vector. Only the random
test rows are independent; their column-acceptance events are not multiplied.
Production transcript freshness and authenticated availability remain open. -/
namespace FormalProof4FHE.HasteBoots.RectangularOpening

open ProbabilityTheory

noncomputable section

variable {F Row Position Test Output : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Row] [Fintype Position] [DecidableEq Position] {codeWidth : ℕ}

def experiment (testWidth queries : ℕ) [SampleableType (Fin testWidth → Row → F)]
    [SampleableType (Fin queries → Position)] :
    ProbComp ((Fin testWidth → Row → F) × (Fin queries → Position)) := do
  let matrix ← $ᵗ (Fin testWidth → Row → F)
  let draw ← $ᵗ (Fin queries → Position)
  pure (matrix,draw)

/-- Responses may be arbitrary coded functions of the preceding random matrix.
One far row suffices to bound all checks on the shared draw vector. -/
theorem far_bound (domain : Position ↪ F) (m radius testWidth queries : ℕ)
    (word : Position → Row → Fin codeWidth → F)
    (claimed : (Fin testWidth → Row → F) → Fin testWidth → Position → Fin codeWidth → F)
    [SampleableType (Row → F)] [SampleableType (Fin testWidth → Row → F)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F)
      (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)))
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧
      hammingDist word source ≤ radius)
    (coded : ∀ matrix lane, claimed matrix lane ∈ BlockCode.code domain m codeWidth) :
    Pr{let matrix ← $ᵗ (Fin testWidth → Row → F); let draw ← $ᵗ (Fin queries → Position)}[
      ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (matrix lane) word) (claimed matrix lane) draw] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) /
        Fintype.card F)^testWidth + ColumnOpening.missBound Position queries (radius+1) := by
  classical
  let bad := fun matrix : Fin testWidth → Row → F => ∀ lane,
    Code.distFromCode (StructuredOpening.combine (matrix lane) word)
      (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) ≤ radius
  have columns := ColumnOpening.adaptive_shared_bound ($ᵗ (Fin testWidth → Row → F))
    (fun matrix lane => StructuredOpening.combine (matrix lane) word) claimed bad queries (radius+1)
    (fun matrix outside => by
      simp only [bad,not_forall] at outside
      obtain ⟨lane,notClose⟩ := outside
      exact ⟨lane,ColumnOpening.farResponse_distance (BlockCode.code domain m codeWidth)
        radius _ _ (coded matrix lane) (lt_of_not_ge notClose)⟩)
  exact columns.trans (add_le_add
    (RectangularBaseProximity.matrix_bound domain m radius testWidth word large small far) le_rfl)

/-- Code membership is derived from every malicious response's coefficient
array, with the retained code width independent of the number of test rows. -/
theorem encoded_far_bound [NeZero codeWidth]
    (domain : Position ↪ F) (m radius testWidth queries : ℕ)
    (word : Position → Row → Fin codeWidth → F)
    (response : (Fin testWidth → Row → F) → Fin testWidth → Fin m → Fin codeWidth → F)
    [SampleableType (Row → F)] [SampleableType (Fin testWidth → Row → F)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F)
      (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)))
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧
      hammingDist word source ≤ radius) :
    Pr{let matrix ← $ᵗ (Fin testWidth → Row → F); let draw ← $ᵗ (Fin queries → Position)}[
      ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (matrix lane) word)
        (BlockEncoder.encode domain (response matrix lane)) draw] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) /
        Fintype.card F)^testWidth + ColumnOpening.missBound Position queries (radius+1) :=
  far_bound domain m radius testWidth queries word _ large small far
    (fun matrix lane => BlockEncoder.encode_mem_code domain (response matrix lane))

/-- A single common decoder supplies every structured response. Near and far
column losses are combined by a maximum, without an independence premise. -/
theorem soundness_bound (domain : Position ↪ F) (m radius testWidth queries : ℕ)
    (word : Position → Row → Fin codeWidth → F) (weights : Test → Row → F)
    (randomClaim : (Fin testWidth → Row → F) → Fin testWidth → Position → Fin codeWidth → F)
    (structuredClaim : (Fin testWidth → Row → F) → Test → Position → Fin codeWidth → F)
    (finish : (Test → Position → Fin codeWidth → F) → Output)
    [SampleableType (Row → F)] [SampleableType (Fin testWidth → Row → F)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F)
      (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)))
    (randomC : ∀ matrix lane, randomClaim matrix lane ∈ BlockCode.code domain m codeWidth)
    (structuredC : ∀ matrix test, structuredClaim matrix test ∈ BlockCode.code domain m codeWidth) :
    let source := CommonSource.decode (BlockCode.code domain m codeWidth) radius word
    Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) testWidth queries}[
      finish (structuredClaim pair.1) ≠ finish (fun test => StructuredOpening.combine (weights test) source) ∧
      (∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (pair.1 lane) word) (randomClaim pair.1 lane) pair.2) ∧
      ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word) (structuredClaim pair.1 test) pair.2] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) /
        Fintype.card F)^testWidth +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius))
        (ColumnOpening.missBound Position queries (radius+1)) := by
  dsimp only
  let source := CommonSource.decode (BlockCode.code domain m codeWidth) radius word
  let nearEvent := fun pair : (Fin testWidth → Row → F) × (Fin queries → Position) =>
    finish (structuredClaim pair.1) ≠ finish (fun test => StructuredOpening.combine (weights test) source) ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word) (structuredClaim pair.1 test) pair.2
  let randomEvent := fun pair : (Fin testWidth → Row → F) × (Fin queries → Position) =>
    ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (pair.1 lane) word) (randomClaim pair.1 lane) pair.2
  let event := fun pair : (Fin testWidth → Row → F) × (Fin queries → Position) =>
    finish (structuredClaim pair.1) ≠ finish (fun test => StructuredOpening.combine (weights test) source) ∧
    randomEvent pair ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word) (structuredClaim pair.1 test) pair.2
  change Pr{let pair ← experiment testWidth queries}[event pair] ≤ _
  by_cases near : ∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧
      hammingDist word source ≤ radius
  · have decoded := CommonSource.decode_nearby (BlockCode.code domain m codeWidth) radius word near
    have bound := StructuredOpening.adaptive_near_falseValue_bound
      ($ᵗ (Fin testWidth → Row → F)) (BlockCode.code domain m codeWidth) radius queries word
      (CommonSource.decode (BlockCode.code domain m codeWidth) radius word)
      weights structuredClaim finish decoded.1 decoded.2 structuredC
    have normalizedBound : Pr{let pair ← experiment testWidth queries}[nearEvent pair] ≤
        ColumnOpening.missBound Position queries
          (Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius) := by
      simpa only [experiment,nearEvent,source,ColumnOpening.missBound,prEvent_norm] using bound
    have reduced := (prEvent_mono (experiment testWidth queries) event nearEvent
      (fun pair accepted => ⟨accepted.1,accepted.2.2⟩)).trans normalizedBound
    exact reduced.trans (by
      calc _ = 0 + ColumnOpening.missBound Position queries _ := (zero_add _).symm
           _ ≤ _ := add_le_add zero_le (le_max_left _ _))
  · have bound := far_bound domain m radius testWidth queries word randomClaim large small near randomC
    have normalizedBound : Pr{let pair ← experiment testWidth queries}[randomEvent pair] ≤
        ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) /
          Fintype.card F)^testWidth + ColumnOpening.missBound Position queries (radius+1) := by
      simpa only [experiment,randomEvent,prEvent_norm] using bound
    have reduced := (prEvent_mono (experiment testWidth queries) event randomEvent
      (fun pair accepted => accepted.2.1)).trans normalizedBound
    exact reduced.trans (add_le_add le_rfl (le_max_right _ _))

end
end FormalProof4FHE.HasteBoots.RectangularOpening
