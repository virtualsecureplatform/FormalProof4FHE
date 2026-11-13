module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSource
public import FormalProof4FHE.HasteBoots.PaddedMixedWidthOwnedLookupSources
@[expose] public section

/-! Shared comparisons read the same native-address private-source view as
NTT, reconstruction and product checks. Helper widths remain independent;
only the original source columns need this semantic interpretation. -/
namespace FormalProof4FHE.HasteBoots.PaddedLookupSourceInterpretation
open PaddedMixedWidthLookupOpeningFamily
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest]
  {d padding helperPadding c row count repetitions : ℕ}
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg} {g : Geometry c row count repetitions}

def parameters (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * packedWidth (d+padding) (d+helperPadding) root)
    (radius : Root count repetitions → ℕ) (source : Fin count) :
    RecordedPaddedSource.Parameters F Cfg heights (d+padding) :=
  ⟨g.front (.inl source),g.suffix (.inl source),g.m (.inl source),tag (.inl source),
    domain (.inl source),capacity (.inl source),radius (.inl source)⟩

/-- The literal owned-comparison source columns normalize to a canonical
logical view of the original physical decoder, without source-value premises. -/
theorem columns (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * packedWidth (d+padding) (d+helperPadding) root)
    (radius : Root count repetitions → ℕ)
    (owner : PaddedMixedWidthOwnedLookupSources.Owners Input Digest heights tag) (source : Fin count) :
    PaddedMixedWidthOwnedLookupSources.columns enc dummy domain capacity radius owner source =
      RecordedPaddedSource.logical (parameters domain capacity radius source) enc dummy row (owner source) :=
  RecordedPaddedSource.padded_eq_logical (parameters domain capacity radius source) enc dummy
    (g.extra (.inl source)) (g.sourceArity source) (owner source)

end
end FormalProof4FHE.HasteBoots.PaddedLookupSourceInterpretation
