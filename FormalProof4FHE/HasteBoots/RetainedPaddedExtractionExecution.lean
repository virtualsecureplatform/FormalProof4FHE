module
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtraction
@[expose] public section

/-! Erase extraction snapshots and the retained predecessor's ghost state.
The extraction factory factors through the raw predecessor, so the public
endpoint, comparison gate and opening memory remain operational data. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedExtractionExecution
open OracleSpec OracleComp BinaryTree
open RetainedPaddedExtraction
noncomputable section
variable {F Before RawBefore Cfg Input Digest Response Memory CommitMemory Term FirstMessage Message : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {H : Cfg → ℕ} {b n : ℕ}

variable (rawBase : RawBefore → Memory → PaddedPublicZeroCheck.Scheme F Unit Bool Term FirstMessage Message
    Input Digest Cfg Response Memory CommitMemory H b n)
  (eraseBefore : Before → RawBefore)

abbrev ghostBase (before : Before) (memory : Memory) := rawBase (eraseBefore before) memory

abbrev RawChild := Sigma (fun selected : RawBefore × Memory =>
  ((Unit → Digest) × CommitMemory) × PaddedPublicZeroCheck.ActualResult (rawBase selected.1 selected.2))

def eraseChild (result : Sigma (Child (ghostBase rawBase eraseBefore))) : RawChild rawBase :=
  ⟨(eraseBefore result.1.1,result.1.2),result.2.1.1,result.2.2.1⟩

variable [SampleableType Digest] [SampleableType (Fin b → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [∀ before memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^((rawBase before memory).code factor).front) b)]
  [∀ before memory factor, SampleableType (Fin ((rawBase before memory).code factor).queries → Fin (2^H ((rawBase before memory).tag factor)))]

/-- Literal final continuation, including commitment work, prepared singleton
openings and all rejected or skipped branches. -/
def program (getRaw : RawBefore → Option (Bool × Memory)) (before : RawBefore) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (RawBefore × Option (RawChild rawBase)) := do
  match getRaw before with
  | none => pure (before,none)
  | some returned =>
    if returned.1 then
      let result ← PaddedPublicZeroCheck.program (rawBase before returned.2)
      pure (before,some ⟨(before,returned.2),result⟩)
    else pure (before,none)

/-- Removing ghost snapshots leaves the same complete shared-state execution. -/
theorem project_finish
    (get : Before → Option (Bool × Memory))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (getRaw : RawBefore → Option (Bool × Memory))
    (getErases : ∀ before, getRaw (eraseBefore before) = get before)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sameEncoding : ∀ before memory, (rawBase before memory).encoding = enc) (before : Before) :
    (fun outcome => ((eraseBefore outcome.1,outcome.2.map (eraseChild rawBase eraseBefore)),
      RetainedPaddedExtraction.finalState (ghostBase rawBase eraseBefore) state outcome)) <$>
      finish (ghostBase rawBase eraseBefore) get state dummy before =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (program rawBase getRaw (eraseBefore before))).run (state before) := by
  rw [program,getErases]
  cases found : get before with
  | none =>
    simp only [finish,DependentStageContinuation.program,select,found,Option.bind_none,
      RetainedPaddedExtraction.finalState,DependentStageContinuation.finalState,map_pure,
      Option.map_none,simulateQ_pure,StateT.run_pure]
  | some returned =>
    by_cases passed : returned.1 = true
    · simp only [finish,DependentStageContinuation.program,select,found,Option.bind_some,passed,ite_true,
        map_bind,map_pure,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
        Option.map_some,RetainedPaddedExtraction.finalState,DependentStageContinuation.finalState]
      have projected := PaddedPublicZeroCheck.project_witness (rawBase (eraseBefore before) returned.2) dummy (state before)
      rw [sameEncoding] at projected
      simp only [child,ghostBase]
      rw [←projected]
      simp only [bind_map_left,eraseChild]
    · have rejected : returned.1 = false := Bool.eq_false_iff.mpr passed
      simp only [finish,DependentStageContinuation.program,select,found,Option.bind_some,rejected,
        Bool.false_eq_true,ite_false,RetainedPaddedExtraction.finalState,DependentStageContinuation.finalState,
        map_pure,Option.map_none,simulateQ_pure,StateT.run_pure]

/-- Compose the actual predecessor projection without expanding its program. -/
theorem project_bind
    (get : Before → Option (Bool × Memory))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (getRaw : RawBefore → Option (Bool × Memory))
    (getErases : ∀ before, getRaw (eraseBefore before) = get before)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sameEncoding : ∀ before memory, (rawBase before memory).encoding = enc)
    (prior : ProbComp Before) (rawPrior : OracleComp (SharedSequence.Shared Cfg Input Digest) RawBefore)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (projectPrior : (fun before => (eraseBefore before,state before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) rawPrior).run initial) :
    (fun outcome => ((eraseBefore outcome.1,outcome.2.map (eraseChild rawBase eraseBefore)),
      RetainedPaddedExtraction.finalState (ghostBase rawBase eraseBefore) state outcome)) <$>
      (prior >>= finish (ghostBase rawBase eraseBefore) get state dummy) =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (rawPrior >>= program rawBase getRaw)).run initial := by
  simp only [simulateQ_bind,StateT.run_bind]
  rw [←projectPrior]
  simp only [map_bind,bind_map_left]
  congr 1
  funext before
  exact project_finish rawBase eraseBefore get state getRaw getErases enc dummy sameEncoding before

/-- One hazard charge for the entire extended program, including the final
extraction and all preceding reached or rejected oracle work. -/
theorem failure_from_empty [Fintype Digest]
    (get : Before → Option (Bool × Memory))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (getRaw : RawBefore → Option (Bool × Memory))
    (getErases : ∀ before, getRaw (eraseBefore before) = get before)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sameEncoding : ∀ before memory, (rawBase before memory).encoding = enc)
    (prior : ProbComp Before) (rawPrior : OracleComp (SharedSequence.Shared Cfg Input Digest) RawBefore)
    (projectPrior : (fun before => (eraseBefore before,state before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) rawPrior).run
        (CheckpointExecution.empty (AmbientMatrixSource.Shape H))) :
    Pr{let outcome ← (prior >>= finish (ghostBase rawBase eraseBefore) get state dummy)}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (RetainedPaddedExtraction.finalState (ghostBase rawBase eraseBefore) state outcome)] ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape H))
      (rawPrior >>= program rawBase getRaw) (CheckpointExecution.empty (AmbientMatrixSource.Shape H)) := by
  have projected := project_bind rawBase eraseBefore get state getRaw getErases enc dummy sameEncoding
    prior rawPrior (CheckpointExecution.empty (AmbientMatrixSource.Shape H)) projectPrior
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape H) (rawPrior >>= program rawBase getRaw)
  rw [←projected,prEvent_map] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.RetainedPaddedExtractionExecution
