module
public import FormalProof4FHE.HasteBoots.EqualityCollectorTrace
@[expose] public section

/-! Original retained native lookup jobs expose their actual equality-point
collector. Initializer, budget, decoded values and vector order are recovered
from the successful original prelude, not supplied as sampling certificates. -/
namespace FormalProof4FHE.HasteBoots.LookupEqualityExposure
open InputIndexedOracle (World)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFieldWire (goldExtensionValue)
noncomputable section

/-- Native geometry dimension and scalar full-point dimension are deliberately
kept distinct here; the existing job.view.dimension identifies them. -/
theorem original {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) {index : Fin origin.ready.jobs.length}
    (job : LookupExecutionJob.Job origin index) :
    ∃ draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val Goldilocks3,
      origin.ready.machine.draws[index.val]? = some draw ∧
      (∃ budget, GoldEqualityPointLaw.values origin.geometry.geometry.1.val budget
        (EqualityCollectorTrace.start draw.coefficients) world = some draw.point) ∧
      List.ofFn draw.point = (List.ofFn job.view.eqPoint).map goldExtensionValue := by
  obtain ⟨draw,found,evidence⟩ := job.equality
  have contract := NativeSharedLookupPrelude.protocol_contract ctx.requests.property.le
    (NativeSharedLookupParent.models ctx.requests) origin.geometry.geometry.1
    ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property
    7 ctx.lookupFuel ctx.equalityFuel _ world origin.ready origin.prepared
  obtain ⟨transcript,_,machine,_⟩ := contract.lookup
  have member := List.mem_of_getElem? found
  simp only [machine,NativeLookupEquality.request,NativeLookupEquality.run_steps] at member
  exact ⟨draw,found,EqualityCollectorTrace.draw_point ctx.equalityFuel transcript ctx.proof.values.roots
    ctx.proof.roots.property world draw member,evidence.value.symm⟩

end
end FormalProof4FHE.HasteBoots.LookupEqualityExposure
