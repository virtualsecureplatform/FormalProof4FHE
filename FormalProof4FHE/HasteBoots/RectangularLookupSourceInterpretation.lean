module
public import FormalProof4FHE.HasteBoots.RectangularSourceSquareView
public import FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources
@[expose] public section

/-! Rectangular comparison columns are canonical original-source views.
Square family transfer checks only original source widths, leaving helper
packing and symbol widths independent. -/
namespace FormalProof4FHE.HasteBoots.RectangularLookupSourceInterpretation
open PaddedMixedWidthLookupOpeningFamily
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest]
  {d padding c row count repetitions : ℕ}
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg} {g : Geometry c row count repetitions}
  {symbolWidth : Root count repetitions → ℕ}

def parameters (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root count repetitions → ℕ) (source : Fin count) :
    RecordedRectangularSource.Parameters F Cfg heights (d+padding) (symbolWidth (.inl source)) :=
  ⟨g.front (.inl source),g.suffix (.inl source),g.m (.inl source),tag (.inl source),
    domain (.inl source),capacity (.inl source),radius (.inl source)⟩

def squareParameters (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root count repetitions → ℕ) (sourceSymbols : ∀ source, symbolWidth (.inl source) = d+padding)
    (source : Fin count) : RecordedPaddedSource.Parameters F Cfg heights (d+padding) :=
  RectangularSourceSquareView.parameters (parameters domain capacity radius source) (sourceSymbols source)

theorem columns (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root count repetitions → ℕ)
    (owner : RectangularOwnedLookupSources.Owners Input Digest heights tag) (source : Fin count) :
    RectangularOwnedLookupSources.columns (d := d) (padding := padding) enc dummy domain capacity radius owner source =
      RecordedRectangularSource.logical (parameters domain capacity radius source) enc dummy row (owner source) :=
  RecordedRectangularSource.padded_eq_logical (parameters domain capacity radius source) enc dummy
    (g.extra (.inl source)) (g.sourceArity source) (owner source)

theorem square_columns (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root count repetitions → ℕ) (sourceSymbols : ∀ source, symbolWidth (.inl source) = d+padding)
    (owner : RectangularOwnedLookupSources.Owners Input Digest heights tag) (source : Fin count) :
    RectangularOwnedLookupSources.columns (d := d) (padding := padding) enc dummy domain capacity radius owner source =
      RecordedPaddedSource.logical (squareParameters domain capacity radius sourceSymbols source) enc dummy row (owner source) :=
  (columns enc dummy domain capacity radius owner source).trans
    (RectangularSourceSquareView.logical (parameters domain capacity radius source) (sourceSymbols source) enc dummy row (owner source))

end
end FormalProof4FHE.HasteBoots.RectangularLookupSourceInterpretation
