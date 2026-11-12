module
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparison
@[expose] public section

/-! Erase comparison/reconstruction snapshots without changing the computed
linear guard, root array, opening memory, callback work or shared full state. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedComparisonExecution
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
open RetainedPaddedComparison
noncomputable section
variable {F Before RawBefore Cfg Input Response Memory CommitMemory : Type}
  [Field F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {d b n : ℕ} {Helper Result : Memory → Type}

abbrev RawReconstruction (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n) :=
  Sigma (fun incoming => ((Fin (2*d+2) → Digest) × CommitMemory) × PaddedLinear.ActualResult (base incoming))

variable (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
  (comparison : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (Helper memory) (Result memory) d)

abbrev RawChild (Memory : Type) (Helper Result : Memory → Type) (d : ℕ) :=
  Sigma (fun incoming => ((Fin (2*d+1) → Digest) × Memory) × Helper incoming × Result incoming)

def eraseReconstruction (reconstructed : Reconstruction base) : RawReconstruction base :=
  ⟨reconstructed.1,(reconstructed.2.1.1,reconstructed.2.2.1)⟩

def eraseChild (result : Sigma (Child base comparison)) : RawChild Memory Helper Result d :=
  ⟨result.1.1,PackedPBSComparisonStage.erase
    (PaddedReconstructionComparison.stage (base result.1.1) (comparison result.1.1)) result.2⟩

/-- Literal native continuation. Only an actual accepted linear result enables
comparison, using its emitted roots and returned opening memory. -/
def program (getRaw : RawBefore → Option (RawReconstruction base)) (before : RawBefore) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (RawBefore × Option (RawChild Memory Helper Result d)) := do
  match getRaw before with
  | none => pure (before,none)
  | some reconstructed =>
    if PaddedLinear.accepted (base reconstructed.1) reconstructed.2.2 then
      let result ← PackedPBSComparisonStage.program
        (PaddedReconstructionComparison.stage (base reconstructed.1) (comparison reconstructed.1))
        reconstructed.2.1.1 reconstructed.2.2.2.memory
      pure (before,some ⟨reconstructed.1,result⟩)
    else pure (before,none)

/-- Snapshot erasure preserves the whole local execution, including a later
comparison rejection and earlier skipped paths. No new oracle calls appear. -/
theorem project_finish
    (get : Before → Option (Reconstruction base))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (eraseBefore : Before → RawBefore) (getRaw : RawBefore → Option (RawReconstruction base))
    (getErases : ∀ before, getRaw (eraseBefore before) = (get before).map (eraseReconstruction base))
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sameEncoding : ∀ memory, (base memory).encoding = enc) (before : Before) :
    (fun outcome => ((eraseBefore outcome.1,outcome.2.map (eraseChild base comparison)),
      RetainedPaddedComparison.finalState base comparison state outcome)) <$>
      finish base comparison get state dummy before =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (program base comparison getRaw (eraseBefore before))).run (state before) := by
  rw [program,getErases]
  cases found : get before with
  | none =>
    simp only [finish,DependentStageContinuation.program,select,found,Option.bind_none,Option.map_none,
      RetainedPaddedComparison.finalState,DependentStageContinuation.finalState,map_pure,simulateQ_pure,StateT.run_pure]
  | some reconstructed =>
    simp only [Option.map_some,eraseReconstruction]
    by_cases passed : PaddedLinear.accepted (base reconstructed.1) reconstructed.2.2.1 = true
    · simp only [finish,DependentStageContinuation.program,select,found,Option.bind_some,passed,ite_true,
        map_bind,map_pure,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
        Option.map_some,RetainedPaddedComparison.finalState,DependentStageContinuation.finalState]
      have projected := PackedPBSComparisonStage.project_witness (base reconstructed.1).encoding dummy
        (PaddedReconstructionComparison.stage (base reconstructed.1) (comparison reconstructed.1))
        reconstructed.2.1.1.1 reconstructed.2.2.1.2.memory (state before)
      rw [sameEncoding] at projected
      simp only [child,sameEncoding]
      rw [←projected]
      simp only [bind_map_left,eraseChild,PackedPBSComparisonStage.erase]
    · have rejected : PaddedLinear.accepted (base reconstructed.1) reconstructed.2.2.1 = false := Bool.eq_false_iff.mpr passed
      simp only [finish,DependentStageContinuation.program,select,found,Option.bind_some,rejected,
        Bool.false_eq_true,ite_false,RetainedPaddedComparison.finalState,DependentStageContinuation.finalState,
        map_pure,Option.map_none,simulateQ_pure,StateT.run_pure]

/-- Compose an already proved predecessor erasure with the native comparison
projection while keeping the predecessor experiment opaque. -/
theorem project_bind
    (get : Before → Option (Reconstruction base))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (eraseBefore : Before → RawBefore) (getRaw : RawBefore → Option (RawReconstruction base))
    (getErases : ∀ before, getRaw (eraseBefore before) = (get before).map (eraseReconstruction base))
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sameEncoding : ∀ memory, (base memory).encoding = enc)
    (prior : ProbComp Before) (rawPrior : OracleComp (SharedSequence.Shared Cfg Input Digest) RawBefore)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (projectPrior : (fun before => (eraseBefore before,state before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) rawPrior).run initial) :
    (fun outcome => ((eraseBefore outcome.1,outcome.2.map (eraseChild base comparison)),
      RetainedPaddedComparison.finalState base comparison state outcome)) <$>
      (prior >>= finish base comparison get state dummy) =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (rawPrior >>= program base comparison getRaw)).run initial := by
  simp only [simulateQ_bind,StateT.run_bind]
  rw [←projectPrior]
  simp only [map_bind,bind_map_left]
  congr 1
  funext before
  exact project_finish base comparison get state eraseBefore getRaw getErases enc dummy sameEncoding before

/-- One execution-hazard charge for the entire operational prefix. The charge
includes all actually reached comparison calls and all earlier rejected work. -/
theorem failure_from_empty [Fintype Digest]
    (get : Before → Option (Reconstruction base))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (eraseBefore : Before → RawBefore) (getRaw : RawBefore → Option (RawReconstruction base))
    (getErases : ∀ before, getRaw (eraseBefore before) = (get before).map (eraseReconstruction base))
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sameEncoding : ∀ memory, (base memory).encoding = enc)
    (prior : ProbComp Before) (rawPrior : OracleComp (SharedSequence.Shared Cfg Input Digest) RawBefore)
    (projectPrior : (fun before => (eraseBefore before,state before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) rawPrior).run
        (CheckpointExecution.empty (AmbientMatrixSource.Shape H))) :
    Pr{let outcome ← (prior >>= finish base comparison get state dummy)}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (RetainedPaddedComparison.finalState base comparison state outcome)] ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape H))
      (rawPrior >>= program base comparison getRaw) (CheckpointExecution.empty (AmbientMatrixSource.Shape H)) := by
  have projected := project_bind base comparison get state eraseBefore getRaw getErases enc dummy sameEncoding
    prior rawPrior (CheckpointExecution.empty (AmbientMatrixSource.Shape H)) projectPrior
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape H) (rawPrior >>= program base comparison getRaw)
  rw [←projected,prEvent_map] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.RetainedPaddedComparisonExecution
