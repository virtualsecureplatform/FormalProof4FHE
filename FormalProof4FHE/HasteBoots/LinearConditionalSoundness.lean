module
public import FormalProof4FHE.HasteBoots.CommittedBatchSafeBound
public import FormalProof4FHE.HasteBoots.OwnedLinearSoundness
public import FormalProof4FHE.HasteBoots.SequentialStageHistory
@[expose] public section

/-! Original-registry linear soundness from an arbitrary audited incoming
history, outside the caller's final collision event. -/
namespace FormalProof4FHE.HasteBoots.LinearConditionalSoundness
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening AuthenticatedLinear
noncomputable section
variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype F] [DecidableEq Input] [DecidableEq Digest]
  {count b front suffix m queries height : ℕ}
  [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType Digest]

def witness
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag (factors count)) s.commit (AuthenticatedLinear.continuation s) initial

/-- Original recording is retained from the actual arbitrary incoming state. -/
theorem fresh_recorded
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy initial)) (factor : Fin count) :
    ⟨s.tag factor,snapshots s.tag outcome.1 factor⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag (factors count)) s.commit (AuthenticatedLinear.continuation s) initial outcome supported
    (s.tag factor,outcome.1.1.1 factor) (List.mem_map_of_mem (factors_complete factor))

theorem audited_witness
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy initial)) :
    CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) outcome.2.2 := by
  have projected : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (fun _ : Cfg => Skeleton.perfect height)) (AuthenticatedLinear.program s)).run initial) := by
    unfold AuthenticatedLinear.program
    rw [←MultiCommitmentPrefix.project_witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (requests s.tag (factors count)) s.commit (AuthenticatedLinear.continuation s) initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (fun _ : Cfg => Skeleton.perfect height) (AuthenticatedLinear.program s) initial audited _ projected

/-- Fresh-source failure is included, so the owner event does not narrow the
accepted false-source event when no earlier owner is selected. -/
theorem fresh_risk_implies_original
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (supported : outcome ∈ support (witness s dummy initial))
    (falseClaim : ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) : OwnedLinearSoundness.OriginalRisk s dummy capacity radius outcome :=
  ⟨snapshots s.tag outcome.1,fun factor => ⟨rfl,fresh_recorded s dummy initial outcome supported factor⟩,falseClaim,passes⟩

/-- Arithmetic error is averaged over actual commitment prefixes at the inherited state. -/
theorem truth_risk_bound
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) :
    Pr{let outcome ← witness s dummy initial}[TruthRisk s dummy capacity radius outcome] ≤
      ((front + suffix : ℕ) : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : ¬PackedLinear.Holds s.relations (sources s dummy capacity radius first)
  · let initial := RecordRoots.state (fun _ : Cfg => Skeleton.perfect height) (requests s.tag (factors count) first.1) first.2
    have retained := SharedContinuation.earlier_event_le s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (select s first.1) (fun packet => if packet.accepted then
        ShortCircuitSequence.program
          (fun factor => NativeBatchVerifier.step (CommittedBatchOpening.protocol s.encoding s.domain (build s) first.1 packet factor))
          (factors count) packet.memory else pure ⟨[], packet.memory, false⟩) initial
      (PackedLinearOracle.Truthful (sources s dummy capacity radius first))
    have arithmetic := PackedLinearOracle.truthful_bound s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      s.nodes s.relations (preflight s) (s.bindRelations first.1 (s.initial first.1))
      (s.receive first.1) (s.initial first.1) (sources s dummy capacity radius first) initial falseClaim
    simpa [AuthenticatedLinear.continuation, CommittedBatchOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim]
      using retained.trans arithmetic
  · simp [TruthRisk, falseClaim, prEvent_norm]

variable [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

theorem opening_safe_bound [NeZero m] [NeZero b]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial) :
    Pr{let outcome ← witness s dummy initial}[OpeningRisk s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum := by
  have bound := CommittedBatchSafeBound.soundness basis s.encoding dummy s.tag (factors count) factors_complete
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
theorem original_safe_bound [NeZero m] [NeZero b]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial) :
    Pr{let outcome ← (witness s dummy initial)}[
      OwnedLinearSoundness.OriginalRisk s dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum := by
  have arithmetic := truth_risk_bound s dummy capacity radius initial
  have opening := opening_safe_bound s basis dummy enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support _ _
    (fun outcome => TruthRisk s dummy capacity radius outcome ∨
      (OpeningRisk s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2)) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic opening)
  · intro outcome supported event
    obtain ⟨risk,safe⟩ := event
    obtain ⟨owner,recorded,falseOriginal,passes⟩ := risk
    have audit := audited_witness s dummy initial audited outcome supported
    have same : OwnedLinearSoundness.originalSources s dummy capacity radius owner =
        sources s dummy capacity radius outcome.1 := by
      funext factor
      rcases RecordedSourceCoherence.source_eq_or_bad s.encoding dummy s.domain capacity radius outcome.2.2 audit
          (s.tag factor) (owner factor) (snapshots s.tag outcome.1 factor) (recorded factor).2
          (fresh_recorded s dummy initial outcome supported factor) (recorded factor).1 with equal | bad
      · exact equal
      · exact False.elim (safe bad)
    have falseFresh : ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1) := by
      intro relation
      exact falseOriginal (same.symm ▸ relation)
    rcases accepted_implies_risks s dummy capacity radius outcome falseFresh passes with truth | wrong
    · exact Or.inl truth
    · exact Or.inr ⟨wrong,safe⟩

end
end FormalProof4FHE.HasteBoots.LinearConditionalSoundness
