module
import all FormalProof4FHE.HasteBoots.DynamicLookupMembershipWork
import all FormalProof4FHE.HasteBoots.ScopedRebuiltLookup

namespace HasteBootsDynamicLookupScopeSmoke
open FormalProof4FHE.HasteBoots
open LookupAssemblyScope (Scope ofTemplate)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
noncomputable section

/-- Distinct proof objects remain distinct assembled caller contexts. Their
original source references nevertheless coincide when only proof data vary. -/
theorem different_proofs_same_original_sources (scope : Scope)
    (left right : NativeSharedLookupProofData.Proof NativeGoldPcsOpening.Opening (Vector Opening)) (different : left ≠ right) :
    (ofTemplate scope {scope.anchor with proof := left} rfl).ctx ≠ (ofTemplate scope {scope.anchor with proof := right} rfl).ctx ∧
      ∀ slot : Fin scope.anchor.registry.val.length,
        RegistryPublicSource.context (ofTemplate scope {scope.anchor with proof := left} rfl).ctx slot =
          RegistryPublicSource.context (ofTemplate scope {scope.anchor with proof := right} rfl).ctx slot := by
  constructor
  · intro same
    exact different (congrArg Context.proof same)
  · intro slot
    rfl

/-- Varying the parent input and all analysis fuels preserves the original
registry/helper while retaining the actual later caller metadata. -/
theorem changing_parent_and_fuels (scope : Scope) (parent : NativeTranscript.Transcript)
    (profile : parent.profile = scope.anchor.parent.profile) :
    let view := ofTemplate scope {scope.anchor with parent := parent,lookupFuel := 11,equalityFuel := 13,scalarFuel := 17,fieldFuel := 19,workerFuel := 23} profile
    view.ctx.parent = parent ∧ view.ctx.lookupFuel = 11 ∧ view.ctx.equalityFuel = 13 ∧ view.ctx.scalarFuel = 17 ∧
      view.ctx.fieldFuel = 19 ∧ view.ctx.workerFuel = 23 ∧ view.ctx.registry = scope.anchor.registry ∧ view.ctx.helper = scope.anchor.helper := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- An unavailable original helper cannot have a successful scoped anchor.
Later proof/template changes do not bypass the actual immutable-store borrow. -/
theorem missing_helper_excludes_scope (scope : Scope)
    (missing : scope.allocation.entries[scope.allocation.helperHandle]? = none) : False := by
  have rejected := AllocatedLookupContext.missing_helper scope.allocation.entries scope.allocation.helperHandle scope.allocation.references scope.allocation.template missing
  rw [scope.allocation.assembled] at rejected
  contradiction

end
end HasteBootsDynamicLookupScopeSmoke
