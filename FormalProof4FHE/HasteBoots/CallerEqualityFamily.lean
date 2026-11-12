module
public import FormalProof4FHE.HasteBoots.CallerPairedPreparation
public import FormalProof4FHE.HasteBoots.EqualityCollectorLogs
public import FormalProof4FHE.HasteBoots.EqualityFactorCandidate
@[expose] public section

/-! Recover the equality-prefix family for the same retained caller job.
Allocation and native execution are reconstructed from original provenance;
no alternate source/helper table or independently chosen job is introduced. -/
namespace FormalProof4FHE.HasteBoots.CallerEqualityFamily
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World)
open OracleProgram (Program run)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

def allocated (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :=
  AllocatedLookupExecution.program allocation.entries allocation.helperHandle allocation.references allocation.template
    data.chooseHelper data.chooseBatch data.memory

theorem execution (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    (run (allocated data) world).run =
      (.verification ctx (run (NativeGoldLookupVerification.program ctx data.chooseHelper data.chooseBatch data.memory) world).run.1,
        (run (NativeGoldLookupVerification.program ctx data.chooseHelper data.chooseBatch data.memory) world).run.2) := by
  simp only [allocated,AllocatedLookupExecution.program,allocation.assembled,OracleProgram.run_bind,
    ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem observed (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    (run (allocated data) world).run.2.Sublist (run program world).run.2 := by
  rw [execution]
  exact data.observed

theorem native (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1 = some (.bound data.lookup.body) ∧
    (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.2.Sublist (run program world).run.2 := by
  have native := AllocatedRegistrySeed.native_execution allocation.entries allocation.helperHandle allocation.references allocation.template
    data.chooseHelper data.chooseBatch data.memory world ctx _ (congrArg Prod.fst (execution data))
    data.lookup data.progress data.after data.executed
  exact ⟨native.1,native.2.trans (observed data)⟩

structure Recovery (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupEquality.Draw data.origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input) where
  family : OriginalScalarFamily.Family program first.position world
  registry : family.parent.registry = ctx.registry
  helper : family.parent.helper = ctx.helper
  requests : family.parent.requests = ctx.requests
  input : family.input = draw.coefficients.phase.pending.input
  roots : family.roots = ctx.proof.roots
  ancestry : AllocatedLookupReadStability.Ancestry data.origin data.index data.job (run program world).run.2

def candidate (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupEquality.Draw data.origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (drawAt : data.origin.ready.machine.draws[data.index.val]? = some draw) (recovered : Recovery data draw first) :
    EqualityFamilyCandidate.Candidate program first.position world :=
  ⟨⟨ctx,data.lookup.body,allocation,data.origin,data.index,data.job,data.geometry,recovered.family,
      recovered.registry,recovered.helper,recovered.requests,recovered.roots⟩,
    draw,drawAt,recovered.input,
    ⟨first.position,first.offset,first.count,first.next,by rw [recovered.input]; exact first.active,
      first.history,by rw [recovered.input]; exact first.fresh,first.positive,by rw [recovered.input]; exact first.outputAt⟩,
    rfl,recovered.ancestry,(CallerFramedAllocatedJob.domain data).rootsFit⟩

theorem recover (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupEquality.Draw data.origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (member : draw ∈ data.origin.ready.machine.draws)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests) : Nonempty (Recovery data draw first) := by
  obtain ⟨family,registry,helper,requests,input,roots⟩ := AllocatedEqualityParentFamily.with_roots
    allocation.entries allocation.helperHandle allocation.references allocation.template data.chooseHelper data.chooseBatch data.memory
    _ (congrArg Prod.fst (execution data)) data.lookup data.progress data.after data.executed data.origin
    (CallerFramedAllocatedJob.domain data).rootsFit draw member program (observed data) framing first safe before bytes valid parentDomain
  have ancestry := AllocatedLookupReadStability.allocated_ancestry allocation.entries allocation.helperHandle allocation.references allocation.template
    data.chooseHelper data.chooseBatch data.memory _ (congrArg Prod.fst (execution data)) data.lookup data.progress data.after data.executed
    data.origin data.index data.job framing (run program world).run.2 (observed data)
  exact ⟨⟨family,registry,helper,requests,input,roots,ancestry⟩⟩

end
end FormalProof4FHE.HasteBoots.CallerEqualityFamily
