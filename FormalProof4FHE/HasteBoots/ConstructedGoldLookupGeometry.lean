module
public import FormalProof4FHE.HasteBoots.ConstructedGoldRectangularSource
public import FormalProof4FHE.HasteBoots.RectangularPaddedLookupOpeningFamily
@[expose] public section

/-! Padded source/helper lookup geometry and rectangular capacity derived from
actual allocated native roles. Logical source and helper arities may differ;
all native code symbols retain four lanes, including three-lane helpers. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldLookupGeometry
open ClassicalGoldRoleBundle (Bundle Stage roleIndex entry parameters)
open ConstructedGoldSourceDescriptor (Configuration heights layout)
open PaddedMixedWidthLookupOpeningFamily (Root Geometry)
noncomputable section
variable {c row count repetitions : ℕ}

def stage (sources : Fin count → Stage) (helpers : Fin repetitions → Stage) : Root count repetitions → Stage
  | .inl source => sources source
  | .inr helper => helpers helper

def physical (bundle : Bundle) (sources : Fin count → Stage) (helpers : Fin repetitions → Stage)
    (root : Root count repetitions) := layout (parameters bundle (stage sources helpers root))

def geometry (bundle : Bundle) (sources : Fin count → Stage) (helpers : Fin repetitions → Stage)
    (sourceFits : ∀ source, row ≤ (parameters bundle (sources source)).numVariables.val)
    (helperFits : ∀ helper, c+row ≤ (parameters bundle (helpers helper)).numVariables.val) : Geometry c row count repetitions where
  front := fun root => (physical bundle sources helpers root).front
  suffix := fun root => (physical bundle sources helpers root).suffix
  m := fun root => (physical bundle sources helpers root).m
  queries := fun root => (parameters bundle (stage sources helpers root)).queries.val
  extra := fun root => (parameters bundle (stage sources helpers root)).numVariables.val -
    (match root with | .inl _ => row | .inr _ => c+row)
  sourceArity := fun source => ConstructedGoldSourceDescriptor.logical_padding _
    (ClassicalGoldRoleBundle.entry_good bundle (roleIndex (sources source))) row (sourceFits source)
  helperArity := fun helper => ConstructedGoldSourceDescriptor.logical_padding _
    (ClassicalGoldRoleBundle.entry_good bundle (roleIndex (helpers helper))) (c+row) (helperFits helper)

def tag (bundle : Bundle) (sources : Fin count → Stage) (helpers : Fin repetitions → Stage)
    (root : Root count repetitions) : Configuration := parameters bundle (stage sources helpers root)

def domain (bundle : Bundle) (sources : Fin count → Stage) (helpers : Fin repetitions → Stage)
    (root : Root count repetitions) : Fin (2^heights (tag bundle sources helpers root)) ↪ NativeFields.Goldilocks :=
  (ConstructedGoldRectangularSource.descriptor bundle (stage sources helpers root) 0).domain

theorem capacity (bundle : Bundle) (sources : Fin count → Stage) (helpers : Fin repetitions → Stage)
    (root : Root count repetitions) :
    2^(physical bundle sources helpers root).suffix ≤ (physical bundle sources helpers root).m * 4 := by
  have bounded := ConstructedGoldRectangularSource.capacity (entry bundle (roleIndex (stage sources helpers root)))
    (ClassicalGoldRoleBundle.entry_good bundle (roleIndex (stage sources helpers root)))
  change 2^(physical bundle sources helpers root).suffix ≤ (physical bundle sources helpers root).m *
    (parameters bundle (stage sources helpers root)).code.blockWidth.val at bounded
  rw [ConstructedGoldRoleSourceDescriptors.block_width bundle (stage sources helpers root)] at bounded
  exact bounded

theorem geometry_capacity (bundle : Bundle) (sources : Fin count → Stage) (helpers : Fin repetitions → Stage)
    (sourceFits : ∀ source, row ≤ (parameters bundle (sources source)).numVariables.val)
    (helperFits : ∀ helper, c+row ≤ (parameters bundle (helpers helper)).numVariables.val)
    (root : Root count repetitions) :
    2^(geometry bundle sources helpers sourceFits helperFits).suffix root ≤
      (geometry bundle sources helpers sourceFits helperFits).m root * 4 := capacity bundle sources helpers root

/-- The actual retained packing policy agrees with the lookup's four source
lanes and three helper lanes; symbol width remains four on both sides. -/
theorem native_widths (bundle : Bundle) (sources : Fin count → Stage) (helpers : Fin repetitions → Stage)
    (sourceRoles : ∀ source, roleIndex (sources source) = 0 ∨ roleIndex (sources source) = 2)
    (helperRoles : ∀ helper, roleIndex (helpers helper) = 1 ∨ roleIndex (helpers helper) = 3)
    (root : Root count repetitions) :
    (tag bundle sources helpers root).width.val = PaddedMixedWidthLookupOpeningFamily.packedWidth 4 3 root ∧
      (tag bundle sources helpers root).code.blockWidth.val = 4 := by
  cases root with
  | inl source => exact ⟨ConstructedGoldRoleSourceDescriptors.source_width bundle (sources source) (sourceRoles source),
      ConstructedGoldRoleSourceDescriptors.block_width bundle (sources source)⟩
  | inr helper => exact ConstructedGoldRoleSourceDescriptors.helper_widths bundle (helpers helper) (helperRoles helper)

end
end FormalProof4FHE.HasteBoots.ConstructedGoldLookupGeometry
