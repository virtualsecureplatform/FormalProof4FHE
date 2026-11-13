module
public import FormalProof4FHE.HasteBoots.ConstructedGoldKeySwitchRouting
public import FormalProof4FHE.HasteBoots.ConstructedGoldLookupInterpretation
@[expose] public section

/-! The final rectangular comparison borrows the same native original-source
allocation as the key-switch arithmetic stages. Its helpers keep their separate
three-test/four-symbol allocation and are not used as original source geometry. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldFinalComparisonRouting
open ConstructedGoldSourceDescriptor (Configuration heights)
open PaddedMixedWidthLookupOpeningFamily (Root)
noncomputable section
variable {row count jobs : ℕ}

/-- Native final source/helper routing with checked logical-shape fit. -/
def context (bundle : ClassicalGoldRoleBundle.Bundle)
    (sourceFits : row ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val)
    (helperFits : 2+row ≤ (ClassicalGoldRoleBundle.parameters bundle .finalHelper).numVariables.val) :
    ConstructedGoldLookupProtocol.Context row count jobs where
  bundle := bundle
  sources := fun _ => .finalCoefficients
  helpers := fun _ => .finalHelper
  sourceRoles := fun _ => Or.inr rfl
  helperRoles := fun _ => Or.inr rfl
  sourceFits := fun _ => sourceFits
  helperFits := fun _ => helperFits

/-- Every original comparison column has exactly the arithmetic stages'
canonical descriptor, with no helper-width equality or private-value premise. -/
theorem source_parameters (bundle : ClassicalGoldRoleBundle.Bundle)
    (sourceFits : row ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val)
    (helperFits : 2+row ≤ (ClassicalGoldRoleBundle.parameters bundle .finalHelper).numVariables.val)
    (radius : ℕ) (source : Fin count) :
    let ctx := context (count := count) (jobs := jobs) bundle sourceFits helperFits
    RectangularLookupSourceInterpretation.squareParameters (d := 3) (padding := 1)
      (g := ConstructedGoldLookupProtocol.geometry ctx) (heights := heights)
      (tag := ConstructedGoldLookupProtocol.tag ctx) (symbolWidth := fun _ => 4)
      (ConstructedGoldLookupProtocol.domain ctx) (ConstructedGoldLookupProtocol.capacity ctx)
      (fun _ => radius) (fun _ => rfl) source =
      ConstructedGoldKeySwitchRouting.descriptor bundle radius := rfl

/-- The final context retains the native asymmetric helper layout. -/
theorem widths (bundle : ClassicalGoldRoleBundle.Bundle)
    (sourceFits : row ≤ (ClassicalGoldRoleBundle.parameters bundle .finalCoefficients).numVariables.val)
    (helperFits : 2+row ≤ (ClassicalGoldRoleBundle.parameters bundle .finalHelper).numVariables.val)
    (root : Root count jobs) :
    let ctx := context bundle sourceFits helperFits
    (ConstructedGoldLookupProtocol.tag ctx root).width.val =
        PaddedMixedWidthLookupOpeningFamily.packedWidth 4 3 root ∧
      (ConstructedGoldLookupProtocol.tag ctx root).code.blockWidth.val = 4 :=
  ConstructedGoldLookupProtocol.native_widths (context bundle sourceFits helperFits) root

end
end FormalProof4FHE.HasteBoots.ConstructedGoldFinalComparisonRouting
