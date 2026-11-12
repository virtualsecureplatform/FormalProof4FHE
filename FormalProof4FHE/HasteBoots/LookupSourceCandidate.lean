module
public import FormalProof4FHE.HasteBoots.LookupSourceReadStability
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedFamilyFixation
@[expose] public section

/-! An original lookup read carries its allocated source family and original
parent provenance before helper roots exist. Complete decoded source columns
are stable at the read and comparable on the existing parent-completed fiber. -/
namespace FormalProof4FHE.HasteBoots.LookupSourceCandidate
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open OracleProgram (Program run runPrefix)
noncomputable section

structure Candidate {A : Type} (program : Program A) (position : ℕ) (world : World) where
  ctx : Context (Vector Opening)
  body : NativeSharedLookupBody.Bound
  allocation : AllocatedFamilyFunctions.Allocation ctx
  origin : AllocatedLookupIdentity.NativeOrigin ctx world body
  index : Fin origin.ready.jobs.length
  job : LookupExecutionJob.Job origin index
  geometry : AllocatedLookupTables.Geometry origin index job
  parent : OriginalParentFamily.Family program position world
  registry : parent.registry = ctx.registry
  helper : parent.helper = ctx.helper
  requests : parent.requests = ctx.requests
  parentInput : parent.input = LookupScalarSeedQuote.forkInput ctx world
  draw : NativeLookupChallenge.Draw NativeExtensionFields.Goldilocks3
  member : draw ∈ job.view.producer.selection.draws
  first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input
  first_position : first.position = position
  ancestry : AllocatedLookupReadStability.Ancestry origin index job (run program world).run.2

def sources {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) :=
  CanonicalAllocatedTables.sources candidate.allocation candidate.origin candidate.index candidate.job candidate.geometry dummy
    (runPrefix position program world).run.2

theorem sources_full {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    sources candidate dummy = CanonicalAllocatedTables.sources candidate.allocation candidate.origin candidate.index candidate.job candidate.geometry dummy
      (run program world).run.2 := by
  have positive : InputIndexedOracle.bytes world candidate.draw.coefficients.phase.pending.input candidate.first.offset candidate.first.count ≠ [] := by
    simpa only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length] using Nat.ne_of_gt candidate.first.positive
  have stable := (LookupSourceReadStability.program_read candidate.allocation candidate.origin candidate.index candidate.job candidate.geometry dummy
    program candidate.ancestry candidate.draw candidate.member candidate.first.position candidate.first.offset _ positive candidate.first.outputAt).resolve_right safe
  rw [← candidate.first.history,candidate.first_position] at stable
  exact stable.symm

theorem compare {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest)
    (input : left.draw.coefficients.phase.pending.input = right.draw.coefficients.phase.pending.input)
    (ordinal : left.index.val = right.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) :
    (left.ctx.registry = right.ctx.registry ∧ left.ctx.helper = right.ctx.helper ∧ left.ctx.requests = right.ctx.requests ∧
      HEq (sources left dummy) (sources right dummy)) ∨
      ProgramParentSeedCollision.Bad program world ∨ NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨
        ProgramContextTarget.Bad program world ∨ ProgramContextTarget.Bad program other := by
  have leftQuote : NativeChildSeedView.quote left.draw.coefficients.phase.pending.input =
      some (InputIndexedOracle.block world left.parent.input 0 64) := by
    rw [left.parentInput]
    exact LookupDrawSeedQuote.quote left.origin left.job left.draw left.member
  have rightQuote : NativeChildSeedView.quote left.draw.coefficients.phase.pending.input =
      some (InputIndexedOracle.block other right.parent.input 0 64) := by
    rw [input,right.parentInput]
    exact LookupDrawSeedQuote.quote right.origin right.job right.draw right.member
  rcases OriginalParentFamily.compare program position world other left.parent right.parent _ dummy leftQuote rightQuote same with agree | bad
  · have registry := left.registry.symm.trans (agree.1.trans right.registry)
    have helper := left.helper.symm.trans (agree.2.1.trans right.helper)
    have requests := left.requests.symm.trans (agree.2.2.1.trans right.requests)
    have leftComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row left.ctx.registry.val) world).run.1 =
        some left.parent.parent.sources.val := by rw [← left.registry]; exact left.parent.computed
    have rightComputed : (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row right.ctx.registry.val) other).run.1 =
        some left.parent.parent.sources.val := by rw [← right.registry,agree.2.2.2.1]; exact right.parent.computed
    exact Or.inl ⟨registry,helper,requests,CanonicalAllocatedFamilyFixation.sources_on_fiber left.allocation right.allocation left.origin right.origin
      program position registry requests _ leftComputed rightComputed same left.index right.index ordinal left.job right.job left.geometry right.geometry dummy⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.LookupSourceCandidate
