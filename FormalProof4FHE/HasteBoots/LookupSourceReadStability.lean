module
public import FormalProof4FHE.HasteBoots.LookupDrawSeedQuote
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedTables
public import FormalProof4FHE.HasteBoots.AllocatedLookupReadStability
@[expose] public section

/-! Original decoded source columns are fixed at any positive original
lookup-stream read. Every column retains its own decoding radius. Helper
commitments and later equality roots are not needed for this source theorem. -/
namespace FormalProof4FHE.HasteBoots.LookupSourceReadStability
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open OracleProgram (Program run)
noncomputable section

theorem program_read {A : Type} {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (allocation : AllocatedFamilyFunctions.Allocation ctx) (origin : AllocatedLookupIdentity.NativeOrigin ctx world body)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (program : Program A)
    (ancestry : AllocatedLookupReadStability.Ancestry origin index job (run program world).run.2)
    (draw : NativeLookupChallenge.Draw NativeExtensionFields.Goldilocks3)
    (member : draw ∈ job.view.producer.selection.draws)
    (position offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (run program world).run.2[position]? = some (.output draw.coefficients.phase.pending.input offset values)) :
    CanonicalAllocatedTables.sources allocation origin index job geometry dummy (run program world).run.2 =
        CanonicalAllocatedTables.sources allocation origin index job geometry dummy ((run program world).run.2.take position) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world := by
  by_cases safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world
  · left
    funext column
    obtain ⟨parentPosition,realized⟩ := ancestry.sources column
    obtain ⟨fuel,completed⟩ := OracleProgramMachine.complete program world
    have logs := congrArg Prod.snd completed
    have native : NativeSeedAncestry.Realized world (run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2
        (LookupScalarSeedQuote.forkInput ctx world) parentPosition
        (.source (AllocatedLookupFrontier.sourceKey (ctx := ctx) (world := world) (job.slots.slot column))) := by
      rw [logs]
      exact realized
    have resolved := native.before_read_resolves OracleProgramMachine.step fuel program world safe position
      draw.coefficients.phase.pending.input offset values positive (by rw [logs]; exact positioned)
      (LookupDrawSeedQuote.quote origin job draw member) _ (List.mem_singleton_self _)
    have found : AllocatedLookupFrontier.resolved dummy ((run program world).run.2.take position)
        draw.coefficients.phase.pending.input
        (AllocatedLookupFrontier.sourceKey (ctx := ctx) (world := world) (job.slots.slot column)) := by
      simpa only [logs,AllocatedLookupFrontier.resolved,NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial,
        NativeRootFamilyState.fold_parent] using resolved
    have parts := List.take_append_drop position (run program world).run.2
    obtain ⟨bound,atPosition⟩ := List.getElem?_eq_some_iff.mp positioned
    rw [List.drop_eq_getElem_cons bound,atPosition] at parts
    rw [CanonicalAllocatedTables.source_at_radius,CanonicalAllocatedTables.source_at_radius]
    have stable := AllocatedLookupFrontier.sourceAt_read origin allocation.entries allocation.reachable allocation.helperHandle
      allocation.references allocation.template allocation.assembled dummy (CanonicalAllocatedTables.sourceRadius ctx (job.slots.slot column))
      (job.slots.slot column) (geometry.source column) ((run program world).run.2.take position)
      ((run program world).run.2.drop (position+1)) draw.coefficients.phase.pending.input offset values positive found
    rw [parts] at stable
    exact stable
  · exact Or.inr (not_not.mp safe)

end
end FormalProof4FHE.HasteBoots.LookupSourceReadStability
