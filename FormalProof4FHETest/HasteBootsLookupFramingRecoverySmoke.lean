module
import all FormalProof4FHE.HasteBoots.RecoveredParentIdentityWork
import all FormalProof4FHETest.HasteBootsParentFramingSmoke

namespace HasteBootsLookupFramingRecoverySmoke
open FormalProof4FHE.HasteBoots
open HasteBootsRegistryAncestrySmoke
open HasteBootsParentFramingSmoke (original_domain parent_framed)
open NativePrefixCodec (Vector)
open OracleProgram (run)
noncomputable section

theorem registry_domain : ∀ sources : Vector NativeCanonicalLookupWire.Source,
    (run (NativeSharedLookupParent.contexts description registry.val) world).run.1 = some sources.val →
      (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit := by
  intro sources computed
  have same : sources = expected := Subtype.ext (Option.some.inj (computed.symm.trans contexts_computed))
  rw [same]
  decide +kernel

def recoverFor (candidate : NativeBrakedownContext.Parameters (Fin 2))
    (success : ∃ geometry, (run (NativeSharedLookupParent.prepare description registry candidate parent requests) world).run.1.2 = some geometry) :
    LookupFramingRecovery.Parents description registry candidate parent requests world :=
  Classical.choice (by
    obtain ⟨geometry,accepted⟩ := success
    obtain ⟨before,bytes,valid⟩ := parent_framed
    exact LookupFramingRecovery.parents description registry candidate parent requests world geometry accepted
      (by decide +kernel) before bytes valid original_domain registry_domain)

def recovered := recoverFor helper prepared_exists

theorem recovered_decodes :
    TranscriptFrame.decodeAll preparation.1.1.input = some recovered.parentFrames := by
  change TranscriptFrame.decodeAll (run (NativeSharedLookupParent.prepare description registry helper parent requests) world).run.1.1.input = _
  rw [recovered.parentBytes]
  exact TranscriptFrame.decodeAll_encodeMany _ recovered.parentValid

theorem helper_binding_present : ParentBindingTrace.frame recovered.binding ∈ recovered.parentFrames := recovered.bound

theorem actual_helper : recovered.binding.helper = digest 0 := by
  have computed := recovered.helperComputed
  have actual : (run (NativeBrakedownContext.context description helper) world).run.1 = some (digest 0) := by decide +kernel
  exact Option.some.inj (computed.symm.trans actual)

-- Changing only the helper's serialized code changes the recovered context.
def otherHelper := {helper with code := (1 : Fin 2)}
theorem other_prepared : ∃ geometry,
    (run (NativeSharedLookupParent.prepare description registry otherHelper parent requests) world).run.1.2 = some geometry := by
  have accepted : (run (NativeSharedLookupParent.prepare description registry otherHelper parent requests) world).run.1.2.isSome = true := by decide +kernel
  cases computed : (run (NativeSharedLookupParent.prepare description registry otherHelper parent requests) world).run.1.2 with
  | none => simp only [computed,Option.isSome_none,Bool.false_eq_true] at accepted
  | some geometry => exact ⟨geometry,rfl⟩

def otherRecovered := recoverFor otherHelper other_prepared

theorem helper_substitution_rejected : otherRecovered.binding.helper ≠ recovered.binding.helper := by
  have computed := otherRecovered.helperComputed
  have actual : (run (NativeBrakedownContext.context description otherHelper) world).run.1 = some (digest 1) := by decide +kernel
  have same := Option.some.inj (computed.symm.trans actual)
  rw [same,actual_helper]
  intro equal
  have values := congrFun equal (0 : Fin 64)
  change (1 : InputIndexedOracle.Byte) = 0 at values
  contradiction

-- All three original slots are retained although the request uses only slot 1.
theorem original_registry_retained : recovered.sources = expected ∧
    (⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode expected⟩ : TranscriptFrame.Frame) ∈ recovered.parentFrames := by
  have same : recovered.sources = expected :=
    Subtype.ext (Option.some.inj (recovered.sourcesComputed.symm.trans contexts_computed))
  exact ⟨same,by rw [← same]; exact recovered.registryBound⟩

theorem unused_aliases_retained : recovered.sources.val.length = 3 ∧
    request.toModel.terminal.sourceSlots = [1] ∧ recovered.sources.val[0]? = recovered.sources.val[1]? := by
  rw [original_registry_retained.1]
  exact ⟨rfl,rfl,rfl⟩

-- A framed prefix does not imply that registration succeeded.
theorem failed_registration :
    (run (NativeSharedLookupParent.prepare failingDescription registry helper parent requests) world).run.1.2 = none := by decide +kernel

end
end HasteBootsLookupFramingRecoverySmoke
