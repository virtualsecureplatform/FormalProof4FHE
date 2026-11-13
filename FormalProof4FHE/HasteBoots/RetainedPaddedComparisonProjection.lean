module
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparison
public import FormalProof4FHE.HasteBoots.ExpectedChargeComposition
@[expose] public section

/-! Erase retained comparison snapshots into the same shared oracle program.
The selected reconstruction, computed gate and private memory are preserved. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedComparisonProjection
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {F Before Erased Cfg Input Response Memory CommitMemory : Type}
  [Field F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {d b n : ℕ} {Helper Result : Memory → Type}

variable (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
  (comparison : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (Helper memory) (Result memory) d)

abbrev Index := Sigma (fun memory => ((Fin (2*d+2) → Digest) × CommitMemory) × PaddedLinear.ActualResult (base memory))
abbrev Child (memory : Memory) := ((Fin (2*d+1) → Digest) × Memory) × Helper memory × Result memory

def eraseIndex (selected : RetainedPaddedComparison.Reconstruction base) : Index base :=
  ⟨selected.1,selected.2.1.1,selected.2.2.1⟩

def eraseChild (selected : RetainedPaddedComparison.Reconstruction base)
    (result : RetainedPaddedComparison.Child base comparison selected) : Child (d := d) (Helper := Helper) (Result := Result) selected.1 :=
  PackedPBSComparisonStage.erase (PaddedReconstructionComparison.stage (base selected.1) (comparison selected.1)) result

/-- The pure program uses the actual emitted roots and returned opening memory. -/
def childProgram (selected : Index base) :=
  PackedPBSComparisonStage.program (PaddedReconstructionComparison.stage (base selected.1) (comparison selected.1))
    selected.2.1.1 selected.2.2.2.memory

/-- Erasing a reached child retains its entire final monitored state. -/
theorem project_child (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (encoding : ∀ memory, (base memory).encoding = enc)
    (selected : RetainedPaddedComparison.Reconstruction base)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) :
    (fun result => (eraseChild base comparison selected result,result.2.2.2)) <$>
      RetainedPaddedComparison.child base comparison dummy selected initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (childProgram base comparison (eraseIndex base selected))).run initial := by
  unfold RetainedPaddedComparison.child
  rw [encoding]
  exact PackedPBSComparisonStage.project_witness enc dummy
    (PaddedReconstructionComparison.stage (base selected.1) (comparison selected.1))
    selected.2.1.1.1 selected.2.2.1.2.memory initial

variable (erase : Before → Erased)
  (get : Before → Option (RetainedPaddedComparison.Reconstruction base))
  (getErased : Erased → Option (Index base))

/-- The same verifier-computed linear guard, evaluated on the retained packet. -/
def select (before : Erased) : Option (Index base) :=
  (getErased before).bind fun selected =>
    if PaddedLinear.accepted (base selected.1) selected.2.2 then some selected else none

omit [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] in
theorem select_erase (law : ∀ before, getErased (erase before) = (get before).map (eraseIndex base))
    (before : Before) :
    select base getErased (erase before) = (RetainedPaddedComparison.select base get before).map (eraseIndex base) := by
  unfold select RetainedPaddedComparison.select
  rw [law]
  cases got : get before with
  | none => rfl
  | some selected =>
    simp only [Option.map_some, Option.bind_some, eraseIndex]
    split <;> rfl

/-- Every skipped and reached branch is represented by the oracle program. -/
def program (before : Erased) : OracleComp (SharedSequence.Shared Cfg Input Digest)
    (Erased × Option (Sigma (Child (d := d) (Helper := Helper) (Result := Result)))) :=
  match select base getErased before with
  | none => pure (before,none)
  | some selected => do
    let result ← childProgram base comparison selected
    pure (before,some ⟨selected.1,result⟩)

/-- Erasing proof snapshots keeps the selected memory and real comparison return. -/
def eraseOutcome (outcome : Before × Option (Sigma (RetainedPaddedComparison.Child base comparison))) :
    Erased × Option (Sigma (Child (d := d) (Helper := Helper) (Result := Result))) :=
  (erase outcome.1,outcome.2.map fun selected => ⟨selected.1.1,eraseChild base comparison selected.1 selected.2⟩)

/-- Exact projection through the computed guard, including rejected/skipped paths. -/
theorem project_finish (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (encoding : ∀ memory, (base memory).encoding = enc)
    (law : ∀ before, getErased (erase before) = (get before).map (eraseIndex base))
    (start : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (before : Before) :
    (fun outcome => (eraseOutcome base comparison erase outcome,
      RetainedPaddedComparison.finalState base comparison start outcome)) <$>
      RetainedPaddedComparison.finish base comparison get start dummy before =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (program base comparison getErased (erase before))).run (start before) := by
  simp only [program, select, law, RetainedPaddedComparison.finish,
    DependentStageContinuation.program, RetainedPaddedComparison.select]
  cases got : get before with
  | none =>
    simp only [Option.map_none, Option.bind_none, map_pure, simulateQ_pure,
      StateT.run_pure, eraseOutcome, RetainedPaddedComparison.finalState,
      DependentStageContinuation.finalState]
  | some selected =>
    simp only [Option.map_some, Option.bind_some, eraseIndex]
    by_cases passed : PaddedLinear.accepted (base selected.1) selected.2.2.1 = true
    · simp only [passed, ite_true, map_bind, map_pure, simulateQ_bind, StateT.run_bind,
        simulateQ_pure, StateT.run_pure, eraseOutcome, Option.map_some,
        RetainedPaddedComparison.finalState, DependentStageContinuation.finalState]
      have projected := project_child base comparison enc dummy encoding selected (start before)
      dsimp only [eraseIndex] at projected
      rw [← projected]
      simp only [bind_pure_comp, Functor.map_map]
    · have rejected : PaddedLinear.accepted (base selected.1) selected.2.2.1 = false := Bool.eq_false_iff.mpr passed
      simp only [rejected, Bool.false_eq_true, ite_false, map_pure, Option.map_none, simulateQ_pure, StateT.run_pure,
        eraseOutcome, RetainedPaddedComparison.finalState, DependentStageContinuation.finalState]

/-- Compose a factual predecessor projection with the comparison program.
The intermediate state is the actual predecessor return, not a fresh state. -/
theorem project_bind (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (encoding : ∀ memory, (base memory).encoding = enc)
    (law : ∀ before, getErased (erase before) = (get before).map (eraseIndex base))
    (start : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (prior : ProbComp Before)
    (priorProgram : OracleComp (SharedSequence.Shared Cfg Input Digest) Erased)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (projection : (fun before => (erase before,start before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) priorProgram).run initial) :
    (fun outcome => (eraseOutcome base comparison erase outcome,
      RetainedPaddedComparison.finalState base comparison start outcome)) <$>
      (prior >>= RetainedPaddedComparison.finish base comparison get start dummy) =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (priorProgram >>= program base comparison getErased)).run initial := by
  rw [simulateQ_bind, StateT.run_bind, ← projection]
  simp only [map_bind, bind_map_left]
  apply bind_congr
  intro before
  exact project_finish base comparison erase get getErased enc dummy encoding law start before

/-- The final exception is observed on the same complete oracle execution. -/
theorem bad_event_eq (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (encoding : ∀ memory, (base memory).encoding = enc)
    (law : ∀ before, getErased (erase before) = (get before).map (eraseIndex base))
    (start : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (prior : ProbComp Before)
    (priorProgram : OracleComp (SharedSequence.Shared Cfg Input Digest) Erased)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (projection : (fun before => (erase before,start before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) priorProgram).run initial) :
    Pr{let outcome ← (prior >>= RetainedPaddedComparison.finish base comparison get start dummy)}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (RetainedPaddedComparison.finalState base comparison start outcome)] =
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (priorProgram >>= program base comparison getErased)).run initial}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) outcome.2] := by
  rw [← project_bind base comparison erase get getErased enc dummy encoding law start prior priorProgram initial projection,
    prEvent_map]

/-- One charge over the whole predecessor/comparison program bounds the
actual final exception; no per-stage security bound or losslessness is assumed. -/
theorem bad_le_charge [Fintype Digest]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (encoding : ∀ memory, (base memory).encoding = enc)
    (law : ∀ before, getErased (erase before) = (get before).map (eraseIndex base))
    (start : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (prior : ProbComp Before)
    (priorProgram : OracleComp (SharedSequence.Shared Cfg Input Digest) Erased)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (projection : (fun before => (erase before,start before)) <$> prior =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H)) priorProgram).run initial)
    (valid : CheckpointCollision.Safe enc dummy (AmbientMatrixSource.Shape H) initial) :
    Pr{let outcome ← (prior >>= RetainedPaddedComparison.finish base comparison get start dummy)}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (RetainedPaddedComparison.finalState base comparison start outcome)] ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (AmbientMatrixSource.Shape H))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape H))
      (priorProgram >>= program base comparison getErased) initial := by
  rw [bad_event_eq base comparison erase get getErased enc dummy encoding law start prior priorProgram initial projection]
  exact CheckpointCollision.failure_le_charge (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape H) _ initial valid

end
end FormalProof4FHE.HasteBoots.RetainedPaddedComparisonProjection
