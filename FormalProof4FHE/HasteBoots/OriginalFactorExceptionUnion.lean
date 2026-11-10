module
public import FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck
public import FormalProof4FHE.HasteBoots.OpeningExceptionBound
public import FormalProof4FHE.HasteBoots.RecordedSourceCoherence
@[expose] public section

/-! Original-factor ZeroCheck with recorded owner reuse. The actual native
worker still opens every original factor, including public setup key roots.
Reuse and opening exceptions share one whole-program hash charge. No verifier
computed key folds replace native key openings. -/
namespace FormalProof4FHE.HasteBoots.OriginalFactorExceptionUnion
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening AuthenticatedZeroCheck
noncomputable section
variable {F K Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {b n front suffix m queries height : ℕ}
  [SampleableType (Fin b → F)] [SampleableType F] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [SampleableType (Fin b → ((Fin b → F) × F))]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType Digest]

def originalSources
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor)) :=
  fun factor => QueryReindex.source s.dimensions
    (RecordedSourceCoherence.source (front := front) s.encoding dummy s.domain capacity radius (s.tag factor) (owner factor))

/-- Any matching recorded owner family, even selected after the complete run.
The event supplies structural membership/root facts, never a safety flag. -/
def OriginalRisk
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ owner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag factor),
    (∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (originalSources s dummy capacity radius owner) ∧
    accepted outcome.2.1 = true

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
theorem fresh_recorded
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (complete : ∀ factor, factor ∈ s.factors)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy)) (factor : Factor) :
    ⟨s.tag factor,snapshots s.tag outcome.1 factor⟩ ∈ outcome.2.2.checkpoints.checkpoints := by
  simp only [witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,_,last,lastSupported,equal⟩ := supported
  subst outcome
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (fun _ : Cfg => Skeleton.perfect height) (s.tag factor) (snapshots s.tag first factor)
    (continuation s first.1) (RecordRoots.state _ (requests s.tag s.factors first.1) first.2)
    (snapshots_recorded s.tag s.factors complete first factor) last lastSupported

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- The owner-family event includes the actual fresh source case; it is not
restricted to a smaller set of accepted false relations. -/
theorem fresh_risk_implies_original
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (complete : ∀ factor, factor ∈ s.factors) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy))
    (falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) : OriginalRisk s dummy capacity radius outcome := by
  refine ⟨snapshots s.tag outcome.1,fun factor => ⟨rfl,fresh_recorded s dummy complete outcome supported factor⟩,?_,passes⟩
  intro valid
  exact falseClaim valid

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
theorem original_risk_reduction
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (complete : ∀ factor, factor ∈ s.factors) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy)) (risk : OriginalRisk s dummy capacity radius outcome) :
    (¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) ∧ accepted outcome.2.1 = true) ∨
      CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2 := by
  classical
  by_cases bad : CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2
  · exact Or.inr bad
  · obtain ⟨owner,recorded,falseOriginal,passes⟩ := risk
    have audited := CommitmentExceptionUnion.audited_witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (requests s.tag s.factors) s.commit (continuation s) outcome supported
    simp only [witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
    obtain ⟨first,_,last,lastSupported,equal⟩ := supported
    subst outcome
    have same : originalSources s dummy capacity radius owner = sources s dummy capacity radius first := by
      funext factor
      have freshRecorded := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (fun _ : Cfg => Skeleton.perfect height) (s.tag factor) (snapshots s.tag first factor)
        (continuation s first.1) (RecordRoots.state _ (requests s.tag s.factors first.1) first.2)
        (snapshots_recorded s.tag s.factors complete first factor) last lastSupported
      rcases RecordedSourceCoherence.source_eq_or_bad (front := front) (suffix := suffix) (b := b) (m := m) (height := height)
        s.encoding dummy s.domain capacity radius last.2 audited
        (s.tag factor) (owner factor) (snapshots s.tag first factor) (recorded factor).2 freshRecorded (recorded factor).1 with same | failed
      · exact congrArg (QueryReindex.source s.dimensions) same
      · exact False.elim (bad failed)
    exact Or.inl ⟨fun valid => falseOriginal (same.symm ▸ valid),passes⟩

variable [Fintype Digest] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Concrete PCS soundness removes the accepted wrong-factor event, with one
charge on this same complete committed/guarded/native-worker execution. -/
theorem opening_risk_or_bad_bound [NeZero m] [NeZero b]
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness s dummy)}[OpeningRisk s dummy capacity radius outcome ∨ CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have bound := OpeningExceptionBound.soundness_from_empty basis s.encoding dummy s.tag s.factors complete
    s.domain enough capacity radius (left s) (right s) (build s) s.commit (select s)
    (fun _ packet => packet.data.enabled) (fun _ packet => packet.data.memory) small
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome event
  rcases event with risk | bad
  · left
    obtain ⟨accepted, factor, different⟩ := risk
    refine ⟨accepted, factor, ?_⟩
    change outcome.2.1.1.data.values factor ≠ _
    rw [AuthenticatedZeroCheck.sources, QueryReindex.fold, SubclaimSourceLayout.fold_decodedSource] at different
    exact different
  · exact Or.inr bad

/-- Authenticated packed-ZeroCheck soundness on one complete native-worker
execution: ZeroCheck error plus PCS arithmetic error plus one expected hash
charge. No wrong-opening, safety or replay certificate remains in the result. -/
theorem false_relation_or_bad_bound [NeZero m] [NeZero b]
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2 * b - 1) * productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2 * b - 1) * (productDegree + 1))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness s dummy)}[
      ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) ∧
      accepted outcome.2.1 = true ∨ CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      (((n : ENNReal) / Fintype.card F) ^ b +
        ((((((2 * b - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (n : ENNReal) * ((((((2 * b - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have arithmetic := truth_risk_bound s dummy capacity radius productDegree bounded firstDegree messageDegree
  have opening := opening_risk_or_bad_bound s basis dummy complete enough capacity radius small
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    TruthRisk s dummy capacity radius outcome ∨ (OpeningRisk s dummy capacity radius outcome ∨
      CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2)) ?_)
  · exact (prEvent_or_le _ _ _).trans ((add_le_add arithmetic opening).trans_eq (add_assoc _ _ _).symm)
  · intro outcome supported event
    rcases event with event | bad
    · rcases accepted_implies_risks s dummy capacity radius outcome supported event.1 event.2 with truth | opening
      · exact Or.inl truth
      · exact Or.inr (Or.inl opening)
    · exact Or.inr (Or.inr bad)



theorem original_soundness_from_empty [NeZero m] [NeZero b]
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2 * b - 1) * productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2 * b - 1) * (productDegree + 1))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness s dummy)}[
      OriginalRisk s dummy capacity radius outcome] ≤
      (((n : ENNReal) / Fintype.card F) ^ b +
        ((((((2 * b - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (n : ENNReal) * ((((((2 * b - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  apply le_trans (prEvent_mono_of_support _ _ _ ?_)
    (false_relation_or_bad_bound s basis dummy complete enough capacity radius productDegree bounded firstDegree messageDegree small)
  intro outcome supported risk
  exact original_risk_reduction s dummy complete capacity radius outcome supported risk

end
end FormalProof4FHE.HasteBoots.OriginalFactorExceptionUnion
