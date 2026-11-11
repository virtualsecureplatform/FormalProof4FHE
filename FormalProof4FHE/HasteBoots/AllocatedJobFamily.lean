module
public import FormalProof4FHE.HasteBoots.AllocatedFamilyFunctions
@[expose] public section

/-! A selected job carries its actual original allocated functions, ordinal,
geometry and scalar-family provenance. The execution constructor obtains
geometry through original PCS ownership or the shared lifetime hash event. -/
namespace FormalProof4FHE.HasteBoots.AllocatedJobFamily
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open OracleProgram (Program run runPrefix)
noncomputable section

structure Selection {A : Type} (program : Program A) (position : ℕ) (world : World) where
  ctx : Context (Vector Opening)
  body : NativeSharedLookupBody.Bound
  allocation : AllocatedFamilyFunctions.Allocation ctx
  origin : AllocatedLookupIdentity.NativeOrigin ctx world body
  index : Fin origin.ready.jobs.length
  job : LookupExecutionJob.Job origin index
  geometry : AllocatedLookupTables.Geometry origin index job
  family : OriginalScalarFamily.Family program position world
  registry : family.parent.registry = ctx.registry
  helper : family.parent.helper = ctx.helper
  requests : family.parent.requests = ctx.requests
  roots : family.roots = ctx.proof.roots

def Selection.sources {A : Type} {program : Program A} {position : ℕ} {world : World}
    (selection : Selection program position world) (dummy : Digest) (radius : ℕ) :=
  AllocatedFamilyFunctions.sources selection.allocation selection.origin selection.index selection.job selection.geometry dummy
    (runPrefix position program world).run.2 radius

def Selection.helpers {A : Type} {program : Program A} {position : ℕ} {world : World}
    (selection : Selection program position world) (dummy : Digest) (radius : ℕ) :=
  AllocatedFamilyFunctions.helpers selection.allocation selection.origin selection.index selection.job selection.geometry dummy
    (runPrefix position program world).run.2 radius

theorem compare {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Selection program position world) (right : Selection program position other)
    (input : left.family.input = right.family.input) (ordinal : left.index.val = right.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) (dummy : Digest) (radius : ℕ) :
    (HEq (left.sources dummy radius) (right.sources dummy radius) ∧ HEq (left.helpers dummy radius) (right.helpers dummy radius)) ∨
      ProgramParentSeedCollision.Bad program world ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
        ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other :=
  AllocatedFamilyFunctions.families_on_fiber left.allocation right.allocation left.origin right.origin program position left.family right.family
    left.registry right.registry left.helper right.helper left.requests right.requests left.roots right.roots input same left.index right.index ordinal
    left.job right.job left.geometry right.geometry dummy radius

variable {ctx : Context (Vector Opening)} {world : World}

theorem recover_at_first {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed)
    (program : Program A)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (run program world).run.2)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (first : ProgramFirstStreamRead.First program world entry.coefficients.phase.pending.input)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index) (dummy : Digest) (radius : ℕ) :
    (∃ geometry : AllocatedLookupTables.Geometry origin index job, ∃ selection : Selection program first.position world,
      selection.ctx = ctx ∧ selection.body = lookup.body ∧ selection.index.val = index.val ∧
      selection.family.input = entry.coefficients.phase.pending.input ∧
      HEq (selection.sources dummy radius)
        (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template
          (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
          geometry dummy (run program world).run.2 radius) ∧
      HEq (selection.helpers dummy radius)
        (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template
          (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
          geometry dummy (run program world).run.2 radius)) ∨
      NativeRootFamilyLifetime.Bad dummy (run program world).run.2 := by
  rcases AllocatedLookupTables.geometry_or_bad entries reachable helperHandle references template chooseHelper chooseBatch memory result executed lookup progress after phase
      origin index job dummy (run program world).run.2 (OracleProgram.run_replay program |>.truthful world) observed with geometry | bad
  · obtain ⟨family,registry,helper,requests,_,roots,input⟩ := AllocatedScalarFamily.at_scalar_first entries helperHandle references template
      chooseHelper chooseBatch memory result executed lookup progress after phase origin rootsFit statementFits domain entry member program observed framing first safe
      before bytes valid parentDomain
    let allocation : AllocatedFamilyFunctions.Allocation ctx := ⟨entries,reachable,helperHandle,references,template,
      (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1⟩
    have positive : InputIndexedOracle.bytes world entry.coefficients.phase.pending.input first.offset first.count ≠ [] := by
      simpa only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length] using Nat.ne_of_gt first.positive
    have stability := AllocatedLookupReadStability.allocated_program_read entries reachable helperHandle references template chooseHelper chooseBatch memory result executed
      lookup progress after phase origin index job allocation.assembled geometry dummy radius program observed framing rootsFit statementFits domain entry member
      first.position first.offset _ positive first.outputAt
    have stable := stability.resolve_right safe
    rw [← first.history] at stable
    exact Or.inl ⟨geometry,⟨ctx,lookup.body,allocation,origin,index,job,geometry,family,registry,helper,requests,roots⟩,rfl,rfl,rfl,input,
      heq_of_eq stable.1.symm,heq_of_eq stable.2.symm⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.AllocatedJobFamily
