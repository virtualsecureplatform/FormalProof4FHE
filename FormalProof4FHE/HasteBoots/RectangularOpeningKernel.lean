module

public import FormalProof4FHE.HasteBoots.RectangularOpening
public import FormalProof4FHE.HasteBoots.AdaptiveResponse
@[expose] public section

/-! Rectangular fixed-word soundness with probabilistic adaptive responses.
The uniform test matrix precedes the response computation; one fresh ordered
column vector follows it. Response state/private coins need no enumerated or
lossless law. Production Fiat–Shamir freshness remains a separate obligation. -/
namespace FormalProof4FHE.HasteBoots.RectangularOpeningKernel
open ProbabilityTheory OracleComp
noncomputable section
variable {F Row Position Test Output Response : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Row] [Fintype Position] [DecidableEq Position] {codeWidth : ℕ}

def experiment (testWidth queries : ℕ) [SampleableType (Fin testWidth → Row → F)]
    [SampleableType (Fin queries → Position)] (respond : (Fin testWidth → Row → F) → ProbComp Response) :
    ProbComp (((Fin testWidth → Row → F) × Response) × (Fin queries → Position)) := do
  let pair ← AdaptiveResponse.choose ($ᵗ (Fin testWidth → Row → F)) respond
  let draw ← $ᵗ (Fin queries → Position)
  pure (pair,draw)

theorem far_bound (domain : Position ↪ F) (m radius testWidth queries : ℕ)
    (word : Position → Row → Fin codeWidth → F)
    (respond : (Fin testWidth → Row → F) → ProbComp Response)
    (claimed : (Fin testWidth → Row → F) → Response → Fin testWidth → Position → Fin codeWidth → F)
    [SampleableType (Row → F)] [SampleableType (Fin testWidth → Row → F)] [SampleableType (Fin queries → Position)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)))
    (far : ¬∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧ hammingDist word source ≤ radius)
    (coded : ∀ matrix response lane, claimed matrix response lane ∈ BlockCode.code domain m codeWidth) :
    Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) testWidth queries respond}[
      ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (pair.1.1 lane) word) (claimed pair.1.1 pair.1.2 lane) pair.2] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) /
        Fintype.card F)^testWidth + ColumnOpening.missBound Position queries (radius+1) := by
  classical
  let coins := AdaptiveResponse.choose ($ᵗ (Fin testWidth → Row → F)) respond
  let bad := fun matrix : Fin testWidth → Row → F => ∀ lane,
    Code.distFromCode (StructuredOpening.combine (matrix lane) word)
      (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) ≤ radius
  have columns := ColumnOpening.adaptive_shared_bound coins
    (fun pair lane => StructuredOpening.combine (pair.1 lane) word) (fun pair lane => claimed pair.1 pair.2 lane)
    (fun pair => bad pair.1) queries (radius+1) (fun pair outside => by
      simp only [bad,not_forall] at outside
      obtain ⟨lane,notClose⟩ := outside
      exact ⟨lane,ColumnOpening.farResponse_distance (BlockCode.code domain m codeWidth)
        radius _ _ (coded pair.1 pair.2 lane) (lt_of_not_ge notClose)⟩)
  have proximity := (AdaptiveResponse.event_le ($ᵗ (Fin testWidth → Row → F)) respond bad).trans
    (RectangularBaseProximity.matrix_bound domain m radius testWidth word large small far)
  have result := columns.trans (add_le_add proximity le_rfl)
  simpa only [experiment,coins,ColumnOpening.missBound,prEvent_norm] using result

/-- Near and far branches use one decoded source and the maximum of shared
column losses. The proximity term is `(distance / field size)^testWidth`. -/
theorem soundness_bound (domain : Position ↪ F) (m radius testWidth queries : ℕ)
    (word : Position → Row → Fin codeWidth → F) (weights : Test → Row → F)
    (respond : (Fin testWidth → Row → F) → ProbComp Response)
    (randomClaim : (Fin testWidth → Row → F) → Response → Fin testWidth → Position → Fin codeWidth → F)
    (structuredClaim : (Fin testWidth → Row → F) → Response → Test → Position → Fin codeWidth → F)
    (finish : (Test → Position → Fin codeWidth → F) → Output)
    [SampleableType (Row → F)] [SampleableType (Fin testWidth → Row → F)] [SampleableType (Fin queries → Position)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)))
    (randomC : ∀ matrix response lane, randomClaim matrix response lane ∈ BlockCode.code domain m codeWidth)
    (structuredC : ∀ matrix response test, structuredClaim matrix response test ∈ BlockCode.code domain m codeWidth) :
    let source := CommonSource.decode (BlockCode.code domain m codeWidth) radius word
    Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) testWidth queries respond}[
      finish (structuredClaim pair.1.1 pair.1.2) ≠ finish (fun test => StructuredOpening.combine (weights test) source) ∧
      (∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (pair.1.1 lane) word) (randomClaim pair.1.1 pair.1.2 lane) pair.2) ∧
      ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word) (structuredClaim pair.1.1 pair.1.2 test) pair.2] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) /
        Fintype.card F)^testWidth +
      max (ColumnOpening.missBound Position queries (Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius))
        (ColumnOpening.missBound Position queries (radius+1)) := by
  dsimp only
  let source := CommonSource.decode (BlockCode.code domain m codeWidth) radius word
  let nearEvent := fun pair : ((Fin testWidth → Row → F) × Response) × (Fin queries → Position) =>
    finish (structuredClaim pair.1.1 pair.1.2) ≠ finish (fun test => StructuredOpening.combine (weights test) source) ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word) (structuredClaim pair.1.1 pair.1.2 test) pair.2
  let randomEvent := fun pair : ((Fin testWidth → Row → F) × Response) × (Fin queries → Position) =>
    ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (pair.1.1 lane) word) (randomClaim pair.1.1 pair.1.2 lane) pair.2
  let event := fun pair : ((Fin testWidth → Row → F) × Response) × (Fin queries → Position) =>
    finish (structuredClaim pair.1.1 pair.1.2) ≠ finish (fun test => StructuredOpening.combine (weights test) source) ∧
    randomEvent pair ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word) (structuredClaim pair.1.1 pair.1.2 test) pair.2
  change Pr{let pair ← experiment testWidth queries respond}[event pair] ≤ _
  by_cases near : ∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧ hammingDist word source ≤ radius
  · have decoded := CommonSource.decode_nearby (BlockCode.code domain m codeWidth) radius word near
    have bound := StructuredOpening.adaptive_near_falseValue_bound
      (AdaptiveResponse.choose ($ᵗ (Fin testWidth → Row → F)) respond)
      (BlockCode.code domain m codeWidth) radius queries word source weights
      (fun pair => structuredClaim pair.1 pair.2) finish decoded.1 decoded.2 (fun pair test => structuredC pair.1 pair.2 test)
    have normalized : Pr{let pair ← experiment testWidth queries respond}[nearEvent pair] ≤
        ColumnOpening.missBound Position queries (Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius) := by
      simpa only [experiment,nearEvent,source,ColumnOpening.missBound,prEvent_norm] using bound
    have reduced := (prEvent_mono _ event nearEvent (fun pair accepted => ⟨accepted.1,accepted.2.2⟩)).trans normalized
    exact reduced.trans (by
      calc _ = 0 + ColumnOpening.missBound Position queries _ := (zero_add _).symm
           _ ≤ _ := add_le_add zero_le (le_max_left _ _))
  · have bound := far_bound domain m radius testWidth queries word respond randomClaim large small near randomC
    have normalized : Pr{let pair ← experiment testWidth queries respond}[randomEvent pair] ≤
        ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) / Fintype.card F)^testWidth +
          ColumnOpening.missBound Position queries (radius+1) := by
      simpa only [randomEvent] using bound
    have reduced := (prEvent_mono _ event randomEvent (fun pair accepted => accepted.2.1)).trans normalized
    exact reduced.trans (add_le_add le_rfl (le_max_right _ _))
end
end FormalProof4FHE.HasteBoots.RectangularOpeningKernel
