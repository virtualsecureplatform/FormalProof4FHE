module
public import FormalProof4FHE.HasteBoots.EqualityLookupReadStability
@[expose] public section

/-! Every source column keeps its own parameter-derived radius at an actual
equality read. Helper decoding has its independent radius and the seed-order
exception is shared across the complete family. -/
namespace FormalProof4FHE.HasteBoots.CanonicalEqualityReadStability
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open OracleProgram (Program run)
open AllocatedFamilyFunctions (Allocation)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}

theorem program_read {A : Type} (allocation : Allocation ctx)
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) (geometry : AllocatedLookupTables.Geometry origin index job)
    (dummy : Digest) (program : Program A)
    (ancestry : AllocatedLookupReadStability.Ancestry origin index job (run program world).run.2)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (member : draw ∈ origin.ready.machine.draws)
    (position offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (run program world).run.2[position]? = some (.output draw.coefficients.phase.pending.input offset values)) :
    (CanonicalAllocatedTables.sources allocation origin index job geometry dummy (run program world).run.2 =
        CanonicalAllocatedTables.sources allocation origin index job geometry dummy ((run program world).run.2.take position) ∧
      CanonicalAllocatedTables.helpers allocation origin index job geometry dummy (run program world).run.2 =
        CanonicalAllocatedTables.helpers allocation origin index job geometry dummy ((run program world).run.2.take position)) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world := by
  by_cases safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world
  · left
    constructor
    · funext column
      have stable := (EqualityLookupReadStability.program_read origin index job allocation.entries allocation.reachable allocation.helperHandle
        allocation.references allocation.template allocation.assembled geometry dummy
        (CanonicalAllocatedTables.sourceRadius ctx (job.slots.slot column)) program ancestry rootsFit draw member
        position offset values positive positioned).resolve_right safe
      exact congrFun stable.1 column
    · exact ((EqualityLookupReadStability.program_read origin index job allocation.entries allocation.reachable allocation.helperHandle
        allocation.references allocation.template allocation.assembled geometry dummy (CanonicalAllocatedTables.helperRadius ctx)
        program ancestry rootsFit draw member position offset values positive positioned).resolve_right safe).2
  · exact Or.inr (not_not.mp safe)

end
end FormalProof4FHE.HasteBoots.CanonicalEqualityReadStability
