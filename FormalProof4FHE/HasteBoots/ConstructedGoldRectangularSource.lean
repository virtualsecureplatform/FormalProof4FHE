module
public import FormalProof4FHE.HasteBoots.ConstructedGoldRoleSourceDescriptors
public import FormalProof4FHE.HasteBoots.RecordedRectangularSource
@[expose] public section

/-! Rectangular source descriptors from completed native allocations. The
packing width is the retained native test width and the symbol width is the
retained code width. In particular helpers retain three packed lanes and four
code symbols. Existing role admission remains an explicit conditional policy. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldRectangularSource
open NativeGoldParameterStore (Entry GoodEntry)
open ConstructedGoldSourceDescriptor (Configuration heights layout)
open ClassicalGoldRoleBundle (Bundle Stage roleIndex entry parameters)
noncomputable section

theorem capacity (actual : Entry) (good : GoodEntry actual) :
    2^(layout actual.initialized.parameters).suffix ≤
      (layout actual.initialized.parameters).m * actual.initialized.parameters.code.blockWidth.val := by
  rw [← ConstructedGoldSourceDescriptor.message_length actual good]
  exact ConstructedGoldSourceDescriptor.symbol_capacity actual good

def source (actual : Entry) (good : GoodEntry actual) (radius : ℕ) :
    RecordedRectangularSource.Parameters NativeFields.Goldilocks Configuration heights
      actual.initialized.parameters.width.val actual.initialized.parameters.code.blockWidth.val :=
  ⟨(layout actual.initialized.parameters).front,(layout actual.initialized.parameters).suffix,
    (layout actual.initialized.parameters).m,actual.initialized.parameters,
    NTTButterfly.domain (heights actual.initialized.parameters)
      (NativeFieldRepresentation.goldValue actual.initialized.parameters.code.domainRoot)
      (NativeGoldParameterInitialization.code_primitive actual.header actual.request actual.config good.1 actual.initialized good.2),
    capacity actual good,radius⟩

def descriptor (bundle : Bundle) (stage : Stage) (radius : ℕ) :=
  source (entry bundle (roleIndex stage)) (ClassicalGoldRoleBundle.entry_good bundle (roleIndex stage)) radius

theorem descriptor_tag (bundle : Bundle) (stage : Stage) (radius : ℕ) :
    (descriptor bundle stage radius).tag = parameters bundle stage := rfl

theorem descriptor_height (bundle : Bundle) (stage : Stage) (radius : ℕ) :
    heights (descriptor bundle stage radius).tag = (entry bundle (roleIndex stage)).initialized.geometry.height :=
  (ConstructedGoldSourceDescriptor.geometry_height _ (ClassicalGoldRoleBundle.entry_good bundle (roleIndex stage))).symm

/-- Equality of retained native role allocations identifies the full descriptor;
heterogeneous equality only transports its two public width indices. -/
theorem descriptor_eq_of_role (bundle : Bundle) (left right : Stage)
    (same : roleIndex left = roleIndex right) (radius : ℕ) :
    HEq (descriptor bundle left radius) (descriptor bundle right radius) := by
  have indexed (a b : Fin 4) (equal : a = b) :
      HEq (source (entry bundle a) (ClassicalGoldRoleBundle.entry_good bundle a) radius)
        (source (entry bundle b) (ClassicalGoldRoleBundle.entry_good bundle b) radius) := by
    cases equal
    rfl
  exact indexed _ _ same

/-- Fixed-width views transport only the public width indices, keeping the
actual constructor-derived domain, capacity and decoder radius. -/
def reindex {packing symbols leftPacking leftSymbols : ℕ}
    (p : RecordedRectangularSource.Parameters NativeFields.Goldilocks Configuration heights packing symbols)
    (packed : packing = leftPacking) (coded : symbols = leftSymbols) :
    RecordedRectangularSource.Parameters NativeFields.Goldilocks Configuration heights leftPacking leftSymbols :=
  packed ▸ coded ▸ p

theorem reindex_tag {packing symbols leftPacking leftSymbols : ℕ}
    (p : RecordedRectangularSource.Parameters NativeFields.Goldilocks Configuration heights packing symbols)
    (packed : packing = leftPacking) (coded : symbols = leftSymbols) :
    (reindex p packed coded).tag = p.tag := by
  subst leftPacking leftSymbols
  rfl

theorem reindex_geometry {packing symbols leftPacking leftSymbols : ℕ}
    (p : RecordedRectangularSource.Parameters NativeFields.Goldilocks Configuration heights packing symbols)
    (packed : packing = leftPacking) (coded : symbols = leftSymbols) :
    ((reindex p packed coded).front,(reindex p packed coded).suffix,(reindex p packed coded).degree) =
      (p.front,p.suffix,p.degree) := by
  subst leftPacking leftSymbols
  rfl

def helper (bundle : Bundle) (stage : Stage) (isHelper : roleIndex stage = 1 ∨ roleIndex stage = 3) (radius : ℕ) :
    RecordedRectangularSource.Parameters NativeFields.Goldilocks Configuration heights 3 4 :=
  reindex (descriptor bundle stage radius)
    (ConstructedGoldRoleSourceDescriptors.helper_widths bundle stage isHelper).1
    (ConstructedGoldRoleSourceDescriptors.block_width bundle stage)

theorem helper_tag (bundle : Bundle) (stage : Stage)
    (isHelper : roleIndex stage = 1 ∨ roleIndex stage = 3) (radius : ℕ) :
    (helper bundle stage isHelper radius).tag = parameters bundle stage := reindex_tag _ _ _

end
end FormalProof4FHE.HasteBoots.ConstructedGoldRectangularSource
