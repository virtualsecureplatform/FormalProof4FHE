module
public import FormalProof4FHE.HasteBoots.JointIdentityLifetimeBound
@[expose] public section

/-! Joint scalar/PCS lifetime bound instantiated with the actual allocated
helper and complete original registry source family. Charges remain logical
exposure scores; physical-work coupling is a separate obligation. -/
namespace FormalProof4FHE.HasteBoots.AllocatedJointIdentityBound
open InputIndexedOracle (World law)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open AllocatedOpeningLifetimeBound (helperOrigin sourceOrigin)
open MeasureTheory
noncomputable section
variable (ctx : Context (Vector Opening)) (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)

theorem bound {A : Type} (HelperMemory SourceMemory : Type) (dummy : Digest) (program : Program A)
    (world : World) (body : NativeSharedLookupBody.Bound) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (scalarRadius helperRadius : ℕ) (sourceRadius : Fin ctx.registry.val.length → ℕ)
    (helperSmall : 3*helperRadius < ctx.helper.code.blocks.val-ctx.helper.code.messageBlocks.val+1)
    (sourceSmall : ∀ slot, 3*sourceRadius slot < (ctx.registry.val.get slot).parameters.code.blocks.val-
      (ctx.registry.val.get slot).parameters.code.messageBlocks.val+1) :
    law {other | ScalarLifetimeComposition.Event program dummy scalarRadius other ∨
      SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step other ∨
      OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy target (RegistryPublicSource.context ctx)
        (sourceOrigin ctx entries reachable helperHandle references template assembled) helperRadius sourceRadius program OracleProgramMachine.step other} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure program) OracleProgramMachine.step fuel) +
      (SingleOpeningLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean program) id dummy target
        (helperOrigin ctx entries reachable helperHandle references template assembled target parameters) helperRadius OracleProgramMachine.step +
        ∑' slot, NativeGoldBatchLifetimeSoundness.exposureCharge (SingleOpeningLifetimeSoundness.clean program) id dummy
          (RegistryPublicSource.context ctx slot) ((sourceOrigin ctx entries reachable helperHandle references template assembled slot).primitiveAt _ rfl)
          (sourceRadius slot) OracleProgramMachine.step) +
      (GlobalReferenceBad.otherCharge program + ∫⁻ other, ScalarLifetimeComposition.totalCharge program other ∂law) := by
  have helperWidth : 3 ≤ target.parameters.width.val := by
    rw [← parameters,AllocatedLookupTables.helperWidth origin]
    omega
  have sourceWidth : ∀ slot : Fin ctx.registry.val.length, 3 ≤ (RegistryPublicSource.context ctx slot).parameters.width.val := by
    intro slot
    change 3 ≤ (ctx.registry.val.get slot).parameters.width.val
    rw [(origin.registry_dimensions slot).2]
    omega
  apply JointIdentityLifetimeBound.bound HelperMemory SourceMemory dummy program target
    (helperOrigin ctx entries reachable helperHandle references template assembled target parameters) (RegistryPublicSource.context ctx)
    (sourceOrigin ctx entries reachable helperHandle references template assembled) scalarRadius helperRadius sourceRadius helperWidth sourceWidth
  · rw [← parameters]
    exact helperSmall
  · exact sourceSmall


end
end FormalProof4FHE.HasteBoots.AllocatedJointIdentityBound
