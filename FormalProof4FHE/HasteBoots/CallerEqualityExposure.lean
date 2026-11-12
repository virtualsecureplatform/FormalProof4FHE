module
public import FormalProof4FHE.HasteBoots.CallerEqualityFamily
@[expose] public section

/-! Successful original native preparation places the coefficient reads of
each completed positive-dimensional equality draw in the enclosing caller.
The earliest read is recovered from that log, including adversarial prequeries. -/
namespace FormalProof4FHE.HasteBoots.CallerEqualityExposure
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open OracleProgram (Program run)
noncomputable section

theorem first {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}
    (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupEquality.Draw data.origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (member : draw ∈ data.origin.ready.machine.draws) (positive : 0 < data.origin.geometry.geometry.1.val) :
    Nonempty (ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input) := by
  have contract := NativeSharedLookupPrelude.protocol_contract ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    data.origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.roots.val ctx.proof.roots.property
    7 ctx.lookupFuel ctx.equalityFuel _ world data.origin.ready data.origin.prepared
  obtain ⟨transcript,_,machine,observations⟩ := contract.lookup
  have traced := EqualityCollectorLogs.request data.origin.geometry.geometry.1.val ctx.equalityFuel transcript
    ctx.proof.roots.val ctx.proof.roots.property world
  rw [← machine] at traced
  have source := traced.2 draw member
  have inPrelude : (run (NativeLookupEquality.request NativeExtensionFields.goldilocksBasis 7 data.origin.geometry.geometry.1.val
      ctx.equalityFuel transcript ctx.proof.roots.val ctx.proof.roots.property) world).run.2.Sublist
      (run (NativeSharedLookupPrelude.protocol ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
        data.origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.roots.val ctx.proof.roots.property
        7 ctx.lookupFuel ctx.equalityFuel (LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row
          ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world)) world).run.2 := by
    rw [NativeSharedLookupPrelude.run_protocol]
    dsimp only
    rw [observations]
    exact List.sublist_append_right _ _
  have native := CallerEqualityFamily.native data
  have logged := (LookupPreludeTrace.logged_of_success data.origin native.1).trans native.2
  exact EqualityCollectorLogs.source_first draw.coefficients world program
    (EqualityCollectorLogs.mono source.1 (inPrelude.trans logged)) source.2 positive

end
end FormalProof4FHE.HasteBoots.CallerEqualityExposure
