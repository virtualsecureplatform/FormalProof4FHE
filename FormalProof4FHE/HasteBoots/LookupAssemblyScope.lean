module
public import FormalProof4FHE.HasteBoots.LookupMembershipWork
@[expose] public section

/-! Dynamic caller templates share one original immutable assembly scope.
Registry order/root and helper parameters follow from actual assembly; proof,
requests, table functions, parent input and analysis fuels may vary. -/
namespace FormalProof4FHE.HasteBoots.LookupAssemblyScope
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeBrakedownCalibration (Role)
noncomputable section

structure Scope where
  anchor : Context (Vector Opening)
  allocation : AllocatedFamilyFunctions.Allocation anchor

structure View (scope : Scope) where
  ctx : Context (Vector Opening)
  template : Context (Vector Opening)
  assembled : AllocatedLookupContext.assemble scope.allocation.entries scope.allocation.helperHandle scope.allocation.references template = some ctx
  profile : ctx.parent.profile = scope.anchor.parent.profile

def View.allocation {scope : Scope} (view : View scope) : AllocatedFamilyFunctions.Allocation view.ctx :=
  ⟨scope.allocation.entries,scope.allocation.reachable,scope.allocation.helperHandle,scope.allocation.references,view.template,view.assembled⟩

def anchorView (scope : Scope) : View scope :=
  ⟨scope.anchor,scope.allocation.template,scope.allocation.assembled,rfl⟩

theorem registry {scope : Scope} (view : View scope) : view.ctx.registry = scope.anchor.registry := by
  have left := (AllocatedLookupContext.assemble_spec _ _ _ _ _ view.assembled).1
  have right := (AllocatedLookupContext.assemble_spec _ _ _ _ _ scope.allocation.assembled).1
  exact Option.some.inj (left.symm.trans right)

theorem helper {scope : Scope} (view : View scope) : view.ctx.helper = scope.anchor.helper := by
  obtain ⟨left,leftAt,_,leftValue⟩ := AllocatedLookupContext.helper_entry _ scope.allocation.reachable _ _ _ _ view.assembled
  obtain ⟨right,rightAt,_,rightValue⟩ := AllocatedLookupContext.helper_entry _ scope.allocation.reachable _ _ _ _ scope.allocation.assembled
  have same := Option.some.inj (leftAt.symm.trans rightAt)
  subst right
  exact (congrArg Context.helper leftValue).trans (congrArg Context.helper rightValue).symm

/-- One successful original assembly proves that every later template is
assembled by collecting the same registry and borrowing the same helper. -/
theorem retemplate (scope : Scope) (template : Context (Vector Opening)) :
    AllocatedLookupContext.assemble scope.allocation.entries scope.allocation.helperHandle scope.allocation.references template =
      some {template with registry := scope.anchor.registry,helper := scope.anchor.helper} := by
  have collected := (AllocatedLookupContext.assemble_spec _ _ _ _ _ scope.allocation.assembled).1
  obtain ⟨entry,found,_,returned⟩ := AllocatedLookupContext.helper_entry _ scope.allocation.reachable _ _ _ _ scope.allocation.assembled
  have parameters : entry.initialized.parameters = scope.anchor.helper := (congrArg Context.helper returned).symm
  simp only [AllocatedLookupContext.assemble,collected,Option.bind_some,AllocatedHelperContext.borrow,found,Option.map_some,parameters]

def ofTemplate (scope : Scope) (template : Context (Vector Opening)) (profile : template.parent.profile = scope.anchor.parent.profile) : View scope :=
  ⟨{template with registry := scope.anchor.registry,helper := scope.anchor.helper},template,retemplate scope template,profile⟩

theorem context_eq {scope : Scope} (view : View scope) :
    view.ctx = {view.template with registry := scope.anchor.registry,helper := scope.anchor.helper} :=
  Option.some.inj (view.assembled.symm.trans (retemplate scope view.template))

def anchorSlot {scope : Scope} (view : View scope) (slot : Fin view.ctx.registry.val.length) : Fin scope.anchor.registry.val.length :=
  ⟨slot.val,by rw [← registry view]; exact slot.isLt⟩

theorem source_parameters {scope : Scope} (view : View scope) (slot : Fin view.ctx.registry.val.length) :
    (RegistryPublicSource.context view.ctx slot).parameters = (RegistryPublicSource.context scope.anchor (anchorSlot view slot)).parameters := by
  have same := OriginalPackedFamily.entry_eq view.ctx.registry scope.anchor.registry (registry view) slot (anchorSlot view slot) rfl
  exact congrArg (fun entry => entry.parameters) same

theorem matches_of_parameters (left right : NativeGoldBatchPcsProgram.Context) (same : left.parameters = right.parameters)
    (role : Role) (valid : NativeGoldBatchCalibration.Matches right role) : NativeGoldBatchCalibration.Matches left role := by
  constructor
  · rw [same]; exact valid.width
  · rw [same]; exact valid.height
  · rw [same]; exact valid.message
  · rw [same]; exact valid.queries

abbrev SourceIndex (scope : Scope) := Σ view : View scope, Fin view.ctx.registry.val.length

def source (scope : Scope) (index : SourceIndex scope) : NativeGoldBatchPcsProgram.Context := RegistryPublicSource.context index.1.ctx index.2

def sourceOrigin (scope : Scope) (index : SourceIndex scope) : CacheBackedCodeOrigin.Origin (source scope index) :=
  RegistryPublicSource.origin index.1.ctx scope.allocation.entries scope.allocation.reachable scope.allocation.references
    (AllocatedLookupContext.assemble_spec _ _ _ _ _ index.1.assembled).1 index.2

def sourceRole {scope : Scope} (role : Fin scope.anchor.registry.val.length → Role) (index : SourceIndex scope) : Role :=
  role (anchorSlot index.1 index.2)

theorem source_admitted {scope : Scope} (role : Fin scope.anchor.registry.val.length → Role)
    (valid : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context scope.anchor slot) (role slot)) :
    ∀ index, NativeGoldBatchCalibration.Matches (source scope index) (sourceRole role index) := by
  intro index
  exact matches_of_parameters _ _ (source_parameters index.1 index.2) _ (valid (anchorSlot index.1 index.2))

theorem profiles (scope : Scope) : ∀ index, (source scope index).parent.profile = scope.anchor.parent.profile := fun index => index.1.profile

end
end FormalProof4FHE.HasteBoots.LookupAssemblyScope
