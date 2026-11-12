module
public import FormalProof4FHE.HasteBoots.AmbientCommittedBatchSafeBound
public import FormalProof4FHE.HasteBoots.AuthenticatedLinear
public import FormalProof4FHE.HasteBoots.SequentialStageHistory
@[expose] public section

/-! Authenticated linear soundness on a mixed-height inherited shared history.
Every checkpoint and monitor remains in the actual ambient handler. -/
namespace FormalProof4FHE.HasteBoots.AmbientLinear
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening AuthenticatedLinear
noncomputable section
variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Digest]
  {count b front suffix m queries height : ℕ}

abbrev Prefix (heights : Cfg → ℕ) := ((Fin count → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

abbrev RunResult (heights : Cfg → ℕ) :=
  (PackedLinearOracle.Packet F (Fin count) Memory b (front+suffix) ×
    ShortCircuitSequence.Outcome (Fin count) (JointMatrixOpening.Data F Digest Response (2^front) b height queries) Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

def sources (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (first : Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) (count := count)) :=
  fun factor => SubclaimSourceLayout.decodedSource (front := front) (suffix := suffix) s.domain capacity radius
    (AmbientCommittedBatchSafeBound.frozen s.encoding dummy heights s.tag first factor)

def originalSources (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) :=
  fun factor => AmbientMatrixSource.source (front := front) s.encoding dummy heights s.domain capacity radius (s.tag factor) (owner factor)

def TruthRisk (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (count := count) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (front := front) (suffix := suffix) (queries := queries) (height := height)) : Prop :=
  ¬PackedLinear.Holds s.relations (sources heights s dummy capacity radius outcome.1) ∧
    PackedLinearOracle.Truthful (sources heights s dummy capacity radius outcome.1) outcome.2.1.1

def OpeningRisk (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (count := count) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (front := front) (suffix := suffix) (queries := queries) (height := height)) : Prop :=
  outcome.2.1.2.accepted = true ∧ ∃ factor,
    outcome.2.1.1.values factor ≠ outcome.2.1.1.query.fold (sources heights s dummy capacity radius outcome.1 factor)

def OriginalRisk (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (count := count) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor),
    (∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬PackedLinear.Holds s.relations (originalSources heights s dummy capacity radius owner) ∧
    accepted outcome.2.1 = true
theorem accepted_implies_risks (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (count := count) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (front := front) (suffix := suffix) (queries := queries) (height := height))
    (falseClaim : ¬PackedLinear.Holds s.relations (sources heights s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) :
    TruthRisk heights s dummy capacity radius outcome ∨ OpeningRisk heights s dummy capacity radius outcome := by
  classical
  have flags := Bool.and_eq_true_iff.mp passes
  by_cases correct : ∀ factor, outcome.2.1.1.values factor = outcome.2.1.1.query.fold (sources heights s dummy capacity radius outcome.1 factor)
  · exact Or.inl ⟨falseClaim, flags.1, correct⟩
  · exact Or.inr ⟨flags.2, not_forall.mp correct⟩

variable [Fintype F] [DecidableEq Input] [SampleableType Digest]
  [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

def witness (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag (factors count)) s.commit (AuthenticatedLinear.continuation s) initial

/-- This witness runs the original linear program on the complete ambient state. -/
theorem project_witness (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => ((outcome.1.1,outcome.2.1),outcome.2.2)) <$> witness heights s dummy initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (AmbientMatrixSource.Shape heights)) (AuthenticatedLinear.program s)).run initial :=
  MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag (factors count)) s.commit (AuthenticatedLinear.continuation s) initial

/-- Every earlier mixed-height owner, including a comparison helper, remains
recorded through the linear stage even if its monitor has already failed. -/
theorem retains (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (count := count) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_retains s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag (factors count)) s.commit (AuthenticatedLinear.continuation s)
    initial outcome supported tag saved recorded

/-- The inherited exception persists through all linear-stage work and rejects. -/
theorem bad_persistent (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) initial)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (count := count) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (AmbientMatrixSource.Shape heights)) (AuthenticatedLinear.program s)).run initial) := by
    rw [←project_witness heights s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (AuthenticatedLinear.program s) initial bad _ actual

/-- Original recording is retained from the actual arbitrary incoming state. -/
theorem fresh_recorded (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (count := count) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) (factor : Fin count) :
    ⟨s.tag factor,AmbientCommittedBatchSafeBound.snapshots heights s.tag outcome.1 factor⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag (factors count)) s.commit (AuthenticatedLinear.continuation s) initial outcome supported
    (s.tag factor,outcome.1.1.1 factor) (List.mem_map_of_mem (factors_complete factor))

theorem audited_witness (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (count := count) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) :
    CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have projected : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (AmbientMatrixSource.Shape heights)) (AuthenticatedLinear.program s)).run initial) := by
    unfold AuthenticatedLinear.program
    rw [←MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
      (requests s.tag (factors count)) s.commit (AuthenticatedLinear.continuation s) initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (AuthenticatedLinear.program s) initial audited _ projected

/-- Fresh-source failure is included, so the owner event does not narrow the
accepted false-source event when no earlier owner is selected. -/
theorem fresh_risk_implies_original (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix heights (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (count := count) ×
      RunResult heights (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (falseClaim : ¬PackedLinear.Holds s.relations (sources heights s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) : OriginalRisk heights s dummy capacity radius outcome :=
  ⟨AmbientCommittedBatchSafeBound.snapshots heights s.tag outcome.1,fun factor => ⟨rfl,fresh_recorded heights s dummy initial outcome supported factor⟩,falseClaim,passes⟩

/-- Arithmetic error is averaged over actual commitment prefixes at the inherited state. -/
theorem truth_risk_bound (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← witness heights s dummy initial}[TruthRisk heights s dummy capacity radius outcome] ≤
      ((front + suffix : ℕ) : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : ¬PackedLinear.Holds s.relations (sources heights s dummy capacity radius first)
  · let initial := RecordRoots.state (AmbientMatrixSource.Shape heights) (requests s.tag (factors count) first.1) first.2
    have retained := SharedContinuation.earlier_event_le s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if packet.accepted then
        ShortCircuitSequence.program
          (fun factor => NativeBatchVerifier.step (CommittedBatchOpening.protocol s.encoding s.domain (build s) first.1 packet factor))
          (factors count) packet.memory else pure ⟨[], packet.memory, false⟩) initial
      (PackedLinearOracle.Truthful (sources heights s dummy capacity radius first))
    have arithmetic := PackedLinearOracle.truthful_bound s.encoding dummy (AmbientMatrixSource.Shape heights)
      s.nodes s.relations (preflight s) (s.bindRelations first.1 (s.initial first.1))
      (s.receive first.1) (s.initial first.1) (sources heights s dummy capacity radius first) initial falseClaim
    simpa [AuthenticatedLinear.continuation, CommittedBatchOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim]
      using retained.trans arithmetic
  · simp [TruthRisk, falseClaim, prEvent_norm]

variable [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

theorem opening_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← witness heights s dummy initial}[OpeningRisk heights s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum := by
  have bound := AmbientCommittedBatchSafeBound.soundness basis s.encoding dummy heights s.tag (factors count) factors_complete geometry
    s.domain enough capacity radius (build s) s.commit (select s)
    (fun _ packet => packet.accepted) (fun _ packet => packet.memory) small initial audited
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome risk
  refine ⟨?_,risk.2⟩
  obtain ⟨passed, factor, wrong⟩ := risk.1
  refine ⟨passed, factor, 0, ?_⟩
  change outcome.2.1.1.values factor ≠ _
  rw [sources, SubclaimSourceLayout.fold_decodedSource] at wrong
  exact wrong

/-- Reconstruction relations and all original registry openings share the
caller's final collision exclusion from any audited incoming state. -/
theorem original_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights s dummy initial)}[
      OriginalRisk heights s dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum := by
  have arithmetic := truth_risk_bound heights s dummy capacity radius initial
  have opening := opening_safe_bound heights s geometry basis dummy enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support _ _
    (fun outcome => TruthRisk heights s dummy capacity radius outcome ∨
      (OpeningRisk heights s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2)) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic opening)
  · intro outcome supported event
    obtain ⟨risk,safe⟩ := event
    obtain ⟨owner,recorded,falseOriginal,passes⟩ := risk
    have audit := audited_witness heights s dummy initial audited outcome supported
    have same : originalSources heights s dummy capacity radius owner =
        sources heights s dummy capacity radius outcome.1 := by
      funext factor
      rcases AmbientMatrixSource.source_eq_or_bad s.encoding dummy heights (s.tag factor) (geometry factor)
          s.domain capacity radius outcome.2.2 audit (owner factor) (AmbientCommittedBatchSafeBound.snapshots heights s.tag outcome.1 factor) (recorded factor).2
          (fresh_recorded heights s dummy initial outcome supported factor) (recorded factor).1 with equal | bad
      · exact equal
      · exact False.elim (safe bad)
    have falseFresh : ¬PackedLinear.Holds s.relations (sources heights s dummy capacity radius outcome.1) := by
      intro relation
      exact falseOriginal (same.symm ▸ relation)
    rcases accepted_implies_risks heights s dummy capacity radius outcome falseFresh passes with truth | wrong
    · exact Or.inl truth
    · exact Or.inr ⟨wrong,safe⟩

end
end FormalProof4FHE.HasteBoots.AmbientLinear
