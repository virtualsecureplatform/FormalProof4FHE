module
public import FormalProof4FHE.HasteBoots.ConstructedGoldSourceBorrowing
public import FormalProof4FHE.HasteBoots.ClassicalGoldRoleBundle
public import FormalProof4FHE.HasteBoots.PaddedSourceGeometry
@[expose] public section

/-! Canonical source-role descriptors from the retained classical allocation
bundle. Role admission here is the existing explicit configuration policy, not
a claim that current production profiles achieve the final security target. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldRoleSourceDescriptors
open ClassicalGoldRoleBundle (Bundle Stage roleIndex entry parameters)
noncomputable section

theorem entry_admitted (bundle : Bundle) (index : Fin 4) :
    ConstructedGoldTargets.admitted (ClassicalGoldDescriptor.calibrationRole index)
      (entry bundle index).request (entry bundle index).header = true := by
  rw [ClassicalGoldRoleBundle.entry_request,ClassicalGoldRoleBundle.entry_header]
  exact ClassicalGoldDescriptor.admitted_at bundle.plans
    (ClassicalGoldDescriptor.prepared_admitted bundle.specification bundle.plans bundle.prepared bundle.accepted) index

/-- Code symbols have four Goldilocks lanes in every retained role. -/
theorem block_width (bundle : Bundle) (stage : Stage) :
    (parameters bundle stage).code.blockWidth.val = 4 := by
  let actual := entry bundle (roleIndex stage)
  have good := ClassicalGoldRoleBundle.entry_good bundle (roleIndex stage)
  have built := NativeGoldBlockCode.build_spec (ConstructedGoldTargets.tables actual good)
    actual.request.message actual.request.block actual.request.blowup actual.initialized.parameters.code
    (ConstructedGoldTargets.entry_build actual good)
  have policy := (ConstructedGoldTargets.admitted_iff _ _ _).mp (entry_admitted bundle (roleIndex stage))
  exact (congrArg (fun value : NativeUsizeMessage.Usize => value.val) built.blockEq).trans policy.block

/-- Original-source roles use the same four lanes for tests and symbols. -/
theorem source_width (bundle : Bundle) (stage : Stage)
    (isSource : roleIndex stage = 0 ∨ roleIndex stage = 2) :
    (parameters bundle stage).width.val = 4 := by
  have width := (ClassicalGoldRoleBundle.stage_geometry bundle stage).2.1
  rcases isSource with first | final
  · simpa [first,ClassicalGoldDescriptor.calibrationRole,NativeBrakedownCalibration.testWidth,
      NativeBrakedownCalibration.codeWidth] using width
  · simpa [final,ClassicalGoldDescriptor.calibrationRole,NativeBrakedownCalibration.testWidth,
      NativeBrakedownCalibration.codeWidth] using width

/-- Helpers retain their literal three test lanes and four code-symbol lanes. -/
theorem helper_widths (bundle : Bundle) (stage : Stage)
    (isHelper : roleIndex stage = 1 ∨ roleIndex stage = 3) :
    (parameters bundle stage).width.val = 3 ∧ (parameters bundle stage).code.blockWidth.val = 4 := by
  refine ⟨?_,block_width bundle stage⟩
  have width := (ClassicalGoldRoleBundle.stage_geometry bundle stage).2.1
  rcases isHelper with first | final
  · simpa [first,ClassicalGoldDescriptor.calibrationRole,NativeBrakedownCalibration.testWidth] using width
  · simpa [final,ClassicalGoldDescriptor.calibrationRole,NativeBrakedownCalibration.testWidth] using width

theorem helper_not_square (bundle : Bundle) (stage : Stage)
    (isHelper : roleIndex stage = 1 ∨ roleIndex stage = 3) :
    (parameters bundle stage).width.val ≠ (parameters bundle stage).code.blockWidth.val := by
  obtain ⟨tests,symbols⟩ := helper_widths bundle stage isHelper
  rw [tests,symbols]
  decide +kernel

/-- Original-source descriptors are derived from actual allocated entries and
their checked public dimensions, domains and message capacity. -/
def descriptor (bundle : Bundle) (stage : Stage)
    (isSource : roleIndex stage = 0 ∨ roleIndex stage = 2) (radius : ℕ) :=
  ConstructedGoldSourceDescriptor.source (entry bundle (roleIndex stage))
    (ClassicalGoldRoleBundle.entry_good bundle (roleIndex stage))
    (source_width bundle stage isSource) (block_width bundle stage) radius

theorem descriptor_tag (bundle : Bundle) (stage : Stage)
    (isSource : roleIndex stage = 0 ∨ roleIndex stage = 2) (radius : ℕ) :
    (descriptor bundle stage isSource radius).tag = parameters bundle stage := rfl

theorem descriptor_height (bundle : Bundle) (stage : Stage)
    (isSource : roleIndex stage = 0 ∨ roleIndex stage = 2) (radius : ℕ) :
    ConstructedGoldSourceDescriptor.heights (descriptor bundle stage isSource radius).tag =
      (entry bundle (roleIndex stage)).initialized.geometry.height :=
  (ConstructedGoldSourceDescriptor.geometry_height _ (ClassicalGoldRoleBundle.entry_good bundle (roleIndex stage))).symm

/-- Shared immutable role allocation determines the entire descriptor at a
fixed radius, without equality of private source values or their roots. -/
theorem descriptor_eq_of_role (bundle : Bundle) (left right : Stage)
    (leftSource : roleIndex left = 0 ∨ roleIndex left = 2)
    (rightSource : roleIndex right = 0 ∨ roleIndex right = 2)
    (same : roleIndex left = roleIndex right) (radius : ℕ) :
    descriptor bundle left leftSource radius = descriptor bundle right rightSource radius := by
  apply ConstructedGoldSourceDescriptor.source_congr
  exact congrArg (fun index => (entry bundle index).initialized.parameters) same

/-- All final original-source roles borrow the same native parameter object. -/
theorem final_source_aliases (bundle : Bundle) (radius : ℕ) :
    descriptor bundle .finalCoefficients (Or.inr rfl) radius = descriptor bundle .finalEvaluations (Or.inr rfl) radius ∧
    descriptor bundle .finalCoefficients (Or.inr rfl) radius = descriptor bundle .finalKey (Or.inr rfl) radius ∧
    descriptor bundle .finalCoefficients (Or.inr rfl) radius = descriptor bundle .finalInput (Or.inr rfl) radius ∧
    descriptor bundle .finalCoefficients (Or.inr rfl) radius = descriptor bundle .finalBorrows (Or.inr rfl) radius :=
  ⟨rfl,rfl,rfl,rfl⟩

variable {Index LeftIndex RightIndex : Type}
/-- Build stage geometry from native allocated source roles. Logical arity
changes only the derived high-zero padding, not the decoder descriptor. -/
def geometry (bundle : Bundle) (stages : Index → Stage)
    (sources : ∀ index, roleIndex (stages index) = 0 ∨ roleIndex (stages index) = 2)
    (logical : ℕ) (fits : ∀ index, logical ≤ (parameters bundle (stages index)).numVariables.val) (radius : ℕ) :
    PaddedSourceGeometry.Geometry NativeFields.Goldilocks ConstructedGoldSourceDescriptor.Configuration Index
      ConstructedGoldSourceDescriptor.heights 4 logical where
  parameters := fun index => descriptor bundle (stages index) (sources index) radius
  queries := fun index => (parameters bundle (stages index)).queries.val
  fits := by
    intro index
    change logical ≤ (ConstructedGoldSourceDescriptor.layout (entry bundle (roleIndex (stages index))).initialized.parameters).front +
      (ConstructedGoldSourceDescriptor.layout (entry bundle (roleIndex (stages index))).initialized.parameters).suffix
    rw [ConstructedGoldSourceDescriptor.physical_dimensions _ (ClassicalGoldRoleBundle.entry_good bundle (roleIndex (stages index)))]
    exact fits index

theorem geometry_parameters (bundle : Bundle) (stages : Index → Stage)
    (sources : ∀ index, roleIndex (stages index) = 0 ∨ roleIndex (stages index) = 2)
    (logical : ℕ) (fits : ∀ index, logical ≤ (parameters bundle (stages index)).numVariables.val)
    (radius : ℕ) (index : Index) :
    (geometry bundle stages sources logical fits radius).parameters index =
      descriptor bundle (stages index) (sources index) radius := rfl

/-- Native allocation routing identifies descriptors across stage geometries
and logical arities, under one fixed decoder radius. -/
theorem geometry_aliases (bundle : Bundle) (leftStages : LeftIndex → Stage) (rightStages : RightIndex → Stage)
    (leftSources : ∀ index, roleIndex (leftStages index) = 0 ∨ roleIndex (leftStages index) = 2)
    (rightSources : ∀ index, roleIndex (rightStages index) = 0 ∨ roleIndex (rightStages index) = 2)
    (leftLogical rightLogical : ℕ)
    (leftFits : ∀ index, leftLogical ≤ (parameters bundle (leftStages index)).numVariables.val)
    (rightFits : ∀ index, rightLogical ≤ (parameters bundle (rightStages index)).numVariables.val)
    (radius : ℕ) (left : LeftIndex) (right : RightIndex)
    (same : roleIndex (leftStages left) = roleIndex (rightStages right)) :
    (geometry bundle leftStages leftSources leftLogical leftFits radius).parameters left =
      (geometry bundle rightStages rightSources rightLogical rightFits radius).parameters right :=
  descriptor_eq_of_role bundle (leftStages left) (rightStages right) (leftSources left) (rightSources right) same radius

end
end FormalProof4FHE.HasteBoots.ConstructedGoldRoleSourceDescriptors
