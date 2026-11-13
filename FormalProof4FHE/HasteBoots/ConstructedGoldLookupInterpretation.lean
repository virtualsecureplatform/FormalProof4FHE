module
public import FormalProof4FHE.HasteBoots.ConstructedGoldLookupProtocol
public import FormalProof4FHE.HasteBoots.RectangularLookupSourceInterpretation
@[expose] public section

/-! Native comparison columns use exactly the original source descriptors
already used by NTT, reconstruction and product families. Only sources are
square; no helper packing/code-width equality or private-value premise occurs. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldLookupInterpretation
open PaddedMixedWidthLookupOpeningFamily (Root)
open ConstructedGoldLookupProtocol (Context geometry tag domain capacity)
open ConstructedGoldSourceDescriptor (Configuration heights)
noncomputable section
variable {row count jobs : ℕ}

theorem source_parameters (ctx : Context row count jobs) (radius : Root count jobs → ℕ) (source : Fin count) :
    RectangularLookupSourceInterpretation.squareParameters (d := 3) (padding := 1)
      (g := geometry ctx) (heights := heights) (tag := tag ctx) (symbolWidth := fun _ => 4)
      (domain ctx) (capacity ctx) radius (fun _ => rfl) source =
    ConstructedGoldRoleSourceDescriptors.descriptor ctx.bundle (ctx.sources source) (ctx.sourceRoles source) (radius (.inl source)) := rfl

variable {Input Digest : Type} [DecidableEq Digest]

theorem source_columns (ctx : Context row count jobs) (radius : Root count jobs → ℕ)
    (enc : MerkleOracle.Encoding Input Digest (List NativeFields.Goldilocks)) (dummy : Digest)
    (owner : RectangularOwnedLookupSources.Owners Input Digest heights (tag ctx)) (source : Fin count) :
    RectangularOwnedLookupSources.columns (d := 3) (padding := 1)
      (g := geometry ctx) (heights := heights) (tag := tag ctx) (symbolWidth := fun _ => 4)
      enc dummy (domain ctx) (capacity ctx) radius owner source =
    RecordedPaddedSource.logical
      (ConstructedGoldRoleSourceDescriptors.descriptor ctx.bundle (ctx.sources source) (ctx.sourceRoles source) (radius (.inl source)))
      enc dummy row (owner source) := by
  have interpreted := RectangularLookupSourceInterpretation.square_columns (d := 3) (padding := 1)
    (g := geometry ctx) (heights := heights) (tag := tag ctx) (symbolWidth := fun _ => 4)
    enc dummy (domain ctx) (capacity ctx) radius (fun _ => rfl) owner source
  simpa only [source_parameters] using interpreted

end
end FormalProof4FHE.HasteBoots.ConstructedGoldLookupInterpretation
