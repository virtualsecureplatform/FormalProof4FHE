module
public import FormalProof4FHE.HasteBoots.AllocatedEqualityParentFamily
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedFamilyFixation
public import FormalProof4FHE.HasteBoots.CanonicalEqualityReadStability
@[expose] public section

/-! Equality-prefix candidates retain the original allocated job and complete
canonical decoded families. No later scalar reader or equality receipt is
stored. Family comparison retains the original parent/root/context exceptions. -/
namespace FormalProof4FHE.HasteBoots.EqualityFamilyCandidate
open InputIndexedOracle (World)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open NativeExtensionFields (Goldilocks3)
noncomputable section

structure Candidate {A : Type} (program : Program A) (position : ℕ) (world : World) where
  selection : AllocatedJobFamily.Selection program position world
  draw : NativeLookupEquality.Draw selection.origin.geometry.geometry.1.val Goldilocks3
  drawAt : selection.origin.ready.machine.draws[selection.index.val]? = some draw
  input : selection.family.input = draw.coefficients.phase.pending.input
  first : ProgramFirstStreamRead.First program world selection.family.input
  first_position : first.position = position
  ancestry : AllocatedLookupReadStability.Ancestry selection.origin selection.index selection.job
    (OracleProgram.run program world).run.2
  rootsFit : (NativeRootMessage.encode selection.ctx.proof.roots.val selection.ctx.proof.roots.property).length < TranscriptFrame.lengthLimit

def sources {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) :=
  CanonicalAllocatedTables.sources candidate.selection.allocation candidate.selection.origin candidate.selection.index
    candidate.selection.job candidate.selection.geometry dummy (runPrefix position program world).run.2

def helpers {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) :=
  CanonicalAllocatedTables.helpers candidate.selection.allocation candidate.selection.origin candidate.selection.index
    candidate.selection.job candidate.selection.geometry dummy (runPrefix position program world).run.2

theorem families_on_fiber {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.selection.family.input = right.selection.family.input) (ordinal : left.selection.index.val = right.selection.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    (HEq (sources left dummy) (sources right dummy) ∧ HEq (helpers left dummy) (helpers right dummy)) ∨
      ProgramParentSeedCollision.Bad program world ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
        ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other :=
  CanonicalAllocatedFamilyFixation.families_on_fiber left.selection.allocation right.selection.allocation
    left.selection.origin right.selection.origin program position left.selection.family right.selection.family
    left.selection.registry right.selection.registry left.selection.helper right.selection.helper
    left.selection.requests right.selection.requests left.selection.roots right.selection.roots input same
    left.selection.index right.selection.index ordinal left.selection.job right.selection.job left.selection.geometry right.selection.geometry dummy

open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open OracleProgram (run)
variable {ctx : Context (Vector Opening)} {world : World}

/-- Successful original execution and its equality first read construct the
candidate, with the retained original job geometry. -/
theorem recover {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (program : Program A)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (run program world).run.2)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (geometry : AllocatedLookupTables.Geometry origin index job)
    (drawAt : origin.ready.machine.draws[index.val]? = some draw) :
    ∃ candidate : Candidate program first.position world,
      candidate.selection.ctx = ctx ∧ candidate.selection.index.val = index.val ∧
        candidate.selection.family.input = draw.coefficients.phase.pending.input ∧
        HEq candidate.selection.origin origin ∧ HEq candidate.selection.job job := by
  obtain ⟨family,registry,helper,requests,input,roots⟩ := AllocatedEqualityParentFamily.with_roots entries helperHandle references template
    chooseHelper chooseBatch memory result executed lookup progress after phase origin rootsFit draw (List.mem_of_getElem? drawAt) program observed framing first safe
    before bytes valid parentDomain
  let allocation : AllocatedFamilyFunctions.Allocation ctx := ⟨entries,reachable,helperHandle,references,template,
    (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1⟩
  let selection : AllocatedJobFamily.Selection program first.position world :=
    ⟨ctx,lookup.body,allocation,origin,index,job,geometry,family,registry,helper,requests,roots⟩
  let named : ProgramFirstStreamRead.First program world family.input :=
    ⟨first.position,first.offset,first.count,first.next,by rw [input]; exact first.active,
      first.history,by rw [input]; exact first.fresh,first.positive,by rw [input]; exact first.outputAt⟩
  have position : named.position = first.position := by rfl
  have ancestry := AllocatedLookupReadStability.allocated_ancestry entries helperHandle references template
    chooseHelper chooseBatch memory result executed lookup progress after phase origin index job framing (run program world).run.2 observed
  exact ⟨⟨selection,draw,drawAt,input,named,position,ancestry,rootsFit⟩,rfl,rfl,input,HEq.rfl,HEq.rfl⟩

/-- The complete-run decoded functions equal those of the same candidate at
its original equality first read, with each original decoding radius intact. -/
theorem tables_at_first {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    sources candidate dummy = CanonicalAllocatedTables.sources candidate.selection.allocation candidate.selection.origin candidate.selection.index
      candidate.selection.job candidate.selection.geometry dummy (run program world).run.2 ∧
    helpers candidate dummy = CanonicalAllocatedTables.helpers candidate.selection.allocation candidate.selection.origin candidate.selection.index
      candidate.selection.job candidate.selection.geometry dummy (run program world).run.2 := by
  have positive : InputIndexedOracle.bytes world candidate.draw.coefficients.phase.pending.input candidate.first.offset candidate.first.count ≠ [] := by
    simpa only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length] using Nat.ne_of_gt candidate.first.positive
  have positioned := Eq.mp (congrArg (fun key : InputIndexedOracle.Input =>
    (run program world).run.2[candidate.first.position]? = some
      (NativeTranscript.Observation.output key candidate.first.offset
        (InputIndexedOracle.bytes world key candidate.first.offset candidate.first.count))) candidate.input) candidate.first.outputAt
  have stable := (CanonicalEqualityReadStability.program_read candidate.selection.allocation candidate.selection.origin candidate.selection.index
    candidate.selection.job candidate.selection.geometry dummy program candidate.ancestry candidate.rootsFit candidate.draw
    (List.mem_of_getElem? candidate.drawAt) candidate.first.position candidate.first.offset _ positive positioned).resolve_right safe
  rw [← candidate.first.history,candidate.first_position] at stable
  exact ⟨stable.1.symm,stable.2.symm⟩

end
end FormalProof4FHE.HasteBoots.EqualityFamilyCandidate
