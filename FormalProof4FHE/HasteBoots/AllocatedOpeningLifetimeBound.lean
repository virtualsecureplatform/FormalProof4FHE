module
public import FormalProof4FHE.HasteBoots.AllocatedOpeningLifetimeCoverage
@[expose] public section

/-! The shared lifetime-family bound instantiated with original allocated
helper/source constructor provenance and native packing-width evidence. -/
namespace FormalProof4FHE.HasteBoots.AllocatedOpeningLifetimeBound
open InputIndexedOracle (World law)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open MeasureTheory
noncomputable section

variable (ctx : Context (Vector Opening)) (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)

def helperOrigin (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters) :
    CacheBackedSingleOpening.Origin target :=
  AllocatedSingleOpeningOrigin.ofFound entries reachable helperHandle
    (AllocatedScalarHelper.entry entries reachable helperHandle references template ctx assembled)
    (AllocatedScalarHelper.entry_spec entries reachable helperHandle references template ctx assembled).1 target
    (parameters.symm.trans (AllocatedScalarHelper.entry_spec entries reachable helperHandle references template ctx assembled).2.2)

abbrev sourceOrigin := RegistryPublicSource.origin ctx entries reachable references
  (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1

theorem bound {A : Type} (HelperMemory SourceMemory : Type) (dummy : Digest) (program : Program A)
    (world : World) (body : NativeSharedLookupBody.Bound) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (helperRadius : ℕ) (sourceRadius : Fin ctx.registry.val.length → ℕ)
    (helperSmall : 3*helperRadius < ctx.helper.code.blocks.val-ctx.helper.code.messageBlocks.val+1)
    (sourceSmall : ∀ slot, 3*sourceRadius slot < (ctx.registry.val.get slot).parameters.code.blocks.val-
      (ctx.registry.val.get slot).parameters.code.messageBlocks.val+1) :
    law {other | SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step other ∨
      OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy target (RegistryPublicSource.context ctx)
        (sourceOrigin ctx entries reachable helperHandle references template assembled) helperRadius sourceRadius program OracleProgramMachine.step other} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure program) OracleProgramMachine.step fuel) +
      (SingleOpeningLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean program) id dummy target
        (helperOrigin ctx entries reachable helperHandle references template assembled target parameters) helperRadius OracleProgramMachine.step +
        ∑' slot, NativeGoldBatchLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean program) id dummy
          (RegistryPublicSource.context ctx slot) ((sourceOrigin ctx entries reachable helperHandle references template assembled slot).primitiveAt _ rfl)
          (sourceRadius slot) OracleProgramMachine.step) := by
  have helperWidth : 3 ≤ target.parameters.width.val := by
    rw [← parameters,AllocatedLookupTables.helperWidth origin]
    omega
  have sourceWidth : ∀ slot : Fin ctx.registry.val.length, 3 ≤ (RegistryPublicSource.context ctx slot).parameters.width.val := by
    intro slot
    change 3 ≤ (ctx.registry.val.get slot).parameters.width.val
    rw [(origin.registry_dimensions slot).2]
    omega
  apply OpeningLifetimeFamily.bound HelperMemory SourceMemory dummy target
    (helperOrigin ctx entries reachable helperHandle references template assembled target parameters) (RegistryPublicSource.context ctx)
    (sourceOrigin ctx entries reachable helperHandle references template assembled) helperRadius sourceRadius helperWidth sourceWidth
    program OracleProgramMachine.step
  · rw [← parameters]
    exact helperSmall
  · exact sourceSmall

end
end FormalProof4FHE.HasteBoots.AllocatedOpeningLifetimeBound
