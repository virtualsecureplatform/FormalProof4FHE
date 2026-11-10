module
public import FormalProof4FHE.HasteBoots.AuthenticatedLinear
public import FormalProof4FHE.HasteBoots.CommittedBatchException
public import FormalProof4FHE.HasteBoots.RecordedSourceCoherence
@[expose] public section

/-! Authenticated linear checks on any matching recorded original registry.
One common-query linear error, all original-column PCS errors and source reuse
share one whole-program hash charge. -/
namespace FormalProof4FHE.HasteBoots.OwnedLinearSoundness
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening AuthenticatedLinear
noncomputable section
variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype F] [DecidableEq Input] [DecidableEq Digest]
  {count b front suffix m queries height : ℕ}
  [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType Digest]

def originalSources
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor)) :=
  fun factor => RecordedSourceCoherence.source (front := front) s.encoding dummy s.domain capacity radius (s.tag factor) (owner factor)

def OriginalRisk
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor),
    (∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬PackedLinear.Holds s.relations (originalSources s dummy capacity radius owner) ∧
    accepted outcome.2.1 = true

theorem fresh_recorded
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy)) (factor : Fin count) :
    ⟨s.tag factor,snapshots s.tag outcome.1 factor⟩ ∈ outcome.2.2.checkpoints.checkpoints := by
  simp only [witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,_,last,lastSupported,equal⟩ := supported
  subst outcome
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (fun _ : Cfg => Skeleton.perfect height) (s.tag factor) (snapshots s.tag first factor)
    (continuation s first.1) (RecordRoots.state _ (requests s.tag (factors count) first.1) first.2)
    (snapshots_recorded s.tag (factors count) factors_complete first factor) last lastSupported

/-- Fresh-source failure is included, so the owner event does not narrow the
accepted false-source event when no earlier owner is selected. -/
theorem fresh_risk_implies_original
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy))
    (falseClaim : ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) : OriginalRisk s dummy capacity radius outcome :=
  ⟨snapshots s.tag outcome.1,fun factor => ⟨rfl,fresh_recorded s dummy outcome supported factor⟩,falseClaim,passes⟩

theorem original_risk_reduction
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (suffix := suffix) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy)) (risk : OriginalRisk s dummy capacity radius outcome) :
    (¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1) ∧ accepted outcome.2.1 = true) ∨
      CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2 := by
  classical
  by_cases bad : CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2
  · exact Or.inr bad
  · obtain ⟨owner,recorded,falseOriginal,passes⟩ := risk
    have audited := CommitmentExceptionUnion.audited_witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (requests s.tag (factors count)) s.commit (continuation s) outcome supported
    have same : originalSources s dummy capacity radius owner = sources s dummy capacity radius outcome.1 := by
      funext factor
      rcases RecordedSourceCoherence.source_eq_or_bad (front := front) (suffix := suffix) (b := b) (m := m) (height := height)
        s.encoding dummy s.domain capacity radius outcome.2.2 audited (s.tag factor) (owner factor) (snapshots s.tag outcome.1 factor)
        (recorded factor).2 (fresh_recorded s dummy outcome supported factor) (recorded factor).1 with equal | failed
      · exact equal
      · exact False.elim (bad failed)
    refine Or.inl ⟨?_,passes⟩
    intro relation
    exact falseOriginal (same.symm ▸ relation)

variable [Fintype Digest] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

theorem opening_risk_or_bad_bound [NeZero m] [NeZero b]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3) :
    Pr{let outcome ← (witness s dummy)}[
      OpeningRisk s dummy capacity radius outcome ∨ CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have bound := CommittedBatchException.soundness_from_empty basis s.encoding dummy s.tag (factors count) factors_complete
    s.domain enough capacity radius (build s) s.commit (select s)
    (fun _ packet => packet.accepted) (fun _ packet => packet.memory) small
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome event
  rcases event with risk | bad
  · obtain ⟨passed,factor,wrong⟩ := risk
    refine Or.inl ⟨passed,factor,0,?_⟩
    change outcome.2.1.1.values factor ≠ _
    rw [sources,SubclaimSourceLayout.fold_decodedSource] at wrong
    exact wrong
  · exact Or.inr bad

/-- Original registry reuse and native opening exceptions share one terminal
history event and one whole-program charge. -/
theorem original_soundness_from_empty [NeZero m] [NeZero b]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3) :
    Pr{let outcome ← (witness s dummy)}[OriginalRisk s dummy capacity radius outcome] ≤
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b)) +
        ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have arithmetic := truth_risk_bound s dummy capacity radius
  have opening := opening_risk_or_bad_bound s basis dummy enough capacity radius small
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    TruthRisk s dummy capacity radius outcome ∨ (OpeningRisk s dummy capacity radius outcome ∨
      CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2)) ?_)
  · exact (prEvent_or_le _ _ _).trans ((add_le_add arithmetic opening).trans_eq (add_assoc _ _ _).symm)
  · intro outcome supported risk
    rcases original_risk_reduction s dummy capacity radius outcome supported risk with fresh | bad
    · rcases accepted_implies_risks s dummy capacity radius outcome fresh.1 fresh.2 with truth | wrong
      · exact Or.inl truth
      · exact Or.inr (Or.inl wrong)
    · exact Or.inr (Or.inr bad)

end
end FormalProof4FHE.HasteBoots.OwnedLinearSoundness
