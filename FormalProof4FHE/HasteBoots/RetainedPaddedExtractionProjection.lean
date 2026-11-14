module
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtraction
public import FormalProof4FHE.HasteBoots.ExpectedChargeComposition
@[expose] public section

/-! Project retained extraction into the same raw oracle program and monitored
history as its predecessor, retaining reached, rejected and skipped branches. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProjection
open OracleSpec OracleComp
noncomputable section
variable {F Before Erased Cfg Input Digest Response Memory CommitMemory Term FirstMessage Message : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {H : Cfg → ℕ} {b n : ℕ}
variable (base : Erased → Memory → PaddedPublicZeroCheck.Scheme F Unit Bool Term FirstMessage Message
    Input Digest Cfg Response Memory CommitMemory H b n)
  (erase : Before → Erased)
  (get : Before → Option (Bool × Memory))
  (getErased : Erased → Option (Bool × Memory))
variable [SampleableType Digest] [SampleableType (Fin b → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [∀ before memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^((base before memory).code factor).front) b)]
  [∀ before memory factor, SampleableType (Fin ((base before memory).code factor).queries → Fin (2^H ((base before memory).tag factor)))]

/-- The raw return retains emitted commitments and verifier packets. -/
abbrev Child (selected : Erased × Memory) := ((Unit → Digest) × CommitMemory) ×
  PaddedPublicZeroCheck.ActualResult (base selected.1 selected.2)

def childProgram (selected : Erased × Memory) := PaddedPublicZeroCheck.program (base selected.1 selected.2)

def select (before : Erased) : Option (Erased × Memory) :=
  (getErased before).bind fun returned => if returned.1 then some (before,returned.2) else none

def program (before : Erased) : OracleComp (SharedSequence.Shared Cfg Input Digest)
    (Erased × Option (Sigma (Child base))) :=
  match select getErased before with
  | none => pure (before,none)
  | some selected => do
    let result ← childProgram base selected
    pure (before,some ⟨selected,result⟩)

/-- Erase snapshots while retaining the selected predecessor and memory. -/
def eraseOutcome (outcome : Before × Option (Sigma (RetainedPaddedExtraction.Child
    (fun before memory => base (erase before) memory)))) : Erased × Option (Sigma (Child base)) :=
  (erase outcome.1,outcome.2.map fun selected =>
    ⟨(erase selected.1.1,selected.1.2),(selected.2.1.1,selected.2.2.1)⟩)

/-- The accepting gate and literal child project to one raw continuation. -/
theorem project_finish (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (encoding : ∀ before memory, (base before memory).encoding = enc)
    (law : ∀ before, getErased (erase before) = get before)
    (start : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (before : Before) :
    (fun outcome => (eraseOutcome base erase outcome,
      RetainedPaddedExtraction.finalState (fun before memory => base (erase before) memory) start outcome)) <$>
      RetainedPaddedExtraction.finish (fun before memory => base (erase before) memory) get start dummy before =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (program base getErased (erase before))).run (start before) := by
  simp only [program,select,law,RetainedPaddedExtraction.finish,
    DependentStageContinuation.program,RetainedPaddedExtraction.select]
  cases got : get before with
  | none =>
    simp only [Option.bind_none,Option.map_none,map_pure,simulateQ_pure,StateT.run_pure,
      eraseOutcome,RetainedPaddedExtraction.finalState,DependentStageContinuation.finalState]
  | some returned =>
    simp only [Option.bind_some]
    by_cases passed : returned.1 = true
    · simp only [passed,↓reduceIte,map_bind,map_pure,simulateQ_bind,StateT.run_bind,
        simulateQ_pure,StateT.run_pure,eraseOutcome,Option.map_some,
        RetainedPaddedExtraction.finalState,DependentStageContinuation.finalState]
      have projected := PaddedPublicZeroCheck.project_witness (base (erase before) returned.2) dummy (start before)
      rw [encoding] at projected
      unfold childProgram RetainedPaddedExtraction.child
      rw [←projected]
      simp only [bind_pure_comp,Functor.map_map]
    · have rejected : returned.1 = false := Bool.eq_false_iff.mpr passed
      simp only [rejected,Bool.false_eq_true,↓reduceIte,map_pure,Option.map_none,
        simulateQ_pure,StateT.run_pure,eraseOutcome,RetainedPaddedExtraction.finalState,
        DependentStageContinuation.finalState]

/-- A factual predecessor projection composes with extraction under one handler. -/
theorem project_bind (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (encoding : ∀ before memory, (base before memory).encoding = enc)
    (law : ∀ before, getErased (erase before) = get before)
    (start : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (prior : ProbComp Before)
    (priorProgram : OracleComp (SharedSequence.Shared Cfg Input Digest) Erased)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (projection : (fun before => (erase before,start before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) priorProgram).run initial) :
    (fun outcome => (eraseOutcome base erase outcome,
      RetainedPaddedExtraction.finalState (fun before memory => base (erase before) memory) start outcome)) <$>
      (prior >>= RetainedPaddedExtraction.finish (fun before memory => base (erase before) memory) get start dummy) =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (priorProgram >>= program base getErased)).run initial := by
  rw [simulateQ_bind,StateT.run_bind,←projection]
  simp only [map_bind,bind_map_left]
  apply bind_congr
  intro before
  exact project_finish base erase get getErased enc dummy encoding law start before

/-- The final authentication event belongs to that same complete raw execution. -/
theorem bad_event_eq (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (encoding : ∀ before memory, (base before memory).encoding = enc)
    (law : ∀ before, getErased (erase before) = get before)
    (start : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (prior : ProbComp Before)
    (priorProgram : OracleComp (SharedSequence.Shared Cfg Input Digest) Erased)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (projection : (fun before => (erase before,start before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) priorProgram).run initial) :
    Pr{let outcome ← (prior >>= RetainedPaddedExtraction.finish (fun before memory => base (erase before) memory) get start dummy)}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H)
        (RetainedPaddedExtraction.finalState (fun before memory => base (erase before) memory) start outcome)] =
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (priorProgram >>= program base getErased)).run initial}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) outcome.2] := by
  rw [←project_bind base erase get getErased enc dummy encoding law start prior priorProgram initial projection,prEvent_map]

/-- Charge the whole predecessor and extraction history, including work on
rejected and skipped branches, without a per-stage probability premise. -/
theorem bad_le_charge [Fintype Digest]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (encoding : ∀ before memory, (base before memory).encoding = enc)
    (law : ∀ before, getErased (erase before) = get before)
    (start : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (prior : ProbComp Before)
    (priorProgram : OracleComp (SharedSequence.Shared Cfg Input Digest) Erased)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (projection : (fun before => (erase before,start before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) priorProgram).run initial)
    (valid : CheckpointCollision.Safe enc dummy (AmbientMatrixSource.Shape H) initial) :
    Pr{let outcome ← (prior >>= RetainedPaddedExtraction.finish (fun before memory => base (erase before) memory) get start dummy)}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H)
        (RetainedPaddedExtraction.finalState (fun before memory => base (erase before) memory) start outcome)] ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape H))
      (priorProgram >>= program base getErased) initial := by
  rw [bad_event_eq base erase get getErased enc dummy encoding law start prior priorProgram initial projection]
  exact CheckpointCollision.failure_le_charge (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape H) _ initial valid

end
end FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProjection
