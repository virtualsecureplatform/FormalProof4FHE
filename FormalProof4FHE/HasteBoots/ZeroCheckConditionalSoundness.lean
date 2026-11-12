module
public import FormalProof4FHE.HasteBoots.CommittedOpeningSafeBound
public import FormalProof4FHE.HasteBoots.OriginalFactorExceptionUnion
public import FormalProof4FHE.HasteBoots.SequentialStageHistory
@[expose] public section

/-! Original-source ZeroCheck soundness outside the final shared collision event.
All bounds use the actual incoming audited state and retained private memory. -/
namespace FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening AuthenticatedZeroCheck
noncomputable section
variable {F K Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {b n front suffix m queries height : ℕ}

variable [SampleableType (Fin b → F)] [SampleableType F] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [SampleableType (Fin b → ((Fin b → F) × F))]

variable [SampleableType (TestMatrix F (2 ^ front) b)]
  [SampleableType (Fin queries → Fin (2 ^ height))]

variable [SampleableType Digest]

def witness (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag s.factors) s.commit (AuthenticatedZeroCheck.continuation s) initial

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Every accepted false fixed-source zero relation exposes one of the two actual
arithmetic events. Source selection uses the prefix snapshot throughout. -/
theorem accepted_implies_risks
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (supported : outcome ∈ support (witness s dummy initial))
    (falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices
      (sources s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) :
    TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome := by
  simp only [witness, MultiCommitmentPrefix.witness, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at supported
  obtain ⟨first, _, last, lastSupported, equal⟩ := supported
  subst outcome
  obtain ⟨selected, selectedSupported, opened, _, lastEqual⟩ :=
    (SharedContinuation.support_program s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (select s first.1) (fun packet => if packet.data.enabled then
        ShortCircuitSequence.program (NativeMatrixVerifier.step
          (NativeCommittedOpening.protocol s.encoding s.domain (left s) (right s) (build s) first.1 packet))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩)
      (RecordRoots.state _ (requests s.tag s.factors first.1) first.2) last).mp lastSupported
  subst last
  have flags := Bool.and_eq_true_iff.mp passes
  obtain ⟨entry, earlier, checked⟩ := PreparedZeroTerminal.select_sound s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond first.1) (s.afterFirst first.1)
      (s.send first.1) (s.afterChallenge first.1) (s.initial first.1))
    s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1)
    (RecordRoots.state _ (requests s.tag s.factors first.1) first.2) selected selectedSupported flags.1
  obtain truthful | wrong := PreparedZeroTerminal.checked_truthful_or_wrong s.nodes s.arity s.coefficient s.indices
    (sources s dummy capacity radius first) selected.1 entry earlier checked
  · exact Or.inl ⟨falseClaim, truthful⟩
  · exact Or.inr ⟨flags.2, wrong⟩

/-- The earlier ZeroCheck error is averaged over actual commitment outcomes,
including arbitrary private commitment memory and the real root-recorded state. -/
theorem truth_risk_bound [Fintype F]
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2 * b - 1) * productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2 * b - 1) * (productDegree + 1))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) :
    Pr{let outcome ← (witness s dummy initial)}[TruthRisk s dummy capacity radius outcome] ≤
      ((n : ENNReal) / Fintype.card F) ^ b +
        ((((((2 * b - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (n : ENNReal) * ((((((2 * b - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices
      (sources s dummy capacity radius first)
  · let initial := RecordRoots.state (fun _ : Cfg => Skeleton.perfect height) (requests s.tag s.factors first.1) first.2
    have afterNative := SharedContinuation.earlier_event_le s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (select s first.1) (fun packet => if packet.data.enabled then
        ShortCircuitSequence.program (NativeMatrixVerifier.step
          (NativeCommittedOpening.protocol s.encoding s.domain (left s) (right s) (build s) first.1 packet))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩) initial
      (fun packet => PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices
        (sources s dummy capacity radius first) packet.earlier)
    have afterPrepare := PreparedZeroTerminal.earlier_event_le s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond first.1) (s.afterFirst first.1)
        (s.send first.1) (s.afterChallenge first.1) (s.initial first.1))
      s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1) initial
      (PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices (sources s dummy capacity radius first))
    have arithmetic := PackedZeroSharedSoundness.soundness_bound s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      s.nodes s.arity s.coefficient s.indices (sources s dummy capacity radius first) productDegree bounded
      s.interpretFirst s.interpret firstDegree messageDegree (s.firstRespond first.1) (s.afterFirst first.1)
      (s.send first.1) (s.afterChallenge first.1) (s.initial first.1) initial falseClaim
    have bound := afterNative.trans (afterPrepare.trans arithmetic)
    simpa [AuthenticatedZeroCheck.continuation, NativeCommittedOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim] using bound
  · have valid := Classical.not_not.mp falseClaim
    simp [TruthRisk, valid, prEvent_norm]

variable [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- PCS error on the actual guarded worker run outside the final collision event. -/
theorem opening_safe_bound [NeZero m] [NeZero b]
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial) :
    Pr{let outcome ← (witness s dummy initial)}[OpeningRisk s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum := by
  have bound := CommittedOpeningSafeBound.soundness basis s.encoding dummy s.tag s.factors complete
    s.domain enough capacity radius (left s) (right s) (build s) s.commit (select s)
    (fun _ packet => packet.data.enabled) (fun _ packet => packet.data.memory) small initial audited
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome risk
  refine ⟨?_, risk.2⟩
  obtain ⟨accepted, factor, different⟩ := risk.1
  refine ⟨accepted, factor, ?_⟩
  change outcome.2.1.1.data.values factor ≠ _
  rw [sources, QueryReindex.fold, SubclaimSourceLayout.fold_decodedSource] at different
  exact different

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] [Fintype F] in
/-- Original recording is retained from the actual arbitrary incoming state. -/
theorem fresh_recorded
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (complete : ∀ factor, factor ∈ s.factors)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy initial)) (factor : Factor) :
    ⟨s.tag factor,snapshots s.tag outcome.1 factor⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag s.factors) s.commit (AuthenticatedZeroCheck.continuation s) initial outcome supported
    (s.tag factor,outcome.1.1.1 factor) (List.mem_map_of_mem (complete factor))

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] [Fintype F] in
theorem audited_witness
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial)
    (outcome : Prefix (Factor := Factor) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Factor := Factor) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness s dummy initial)) :
    CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) outcome.2.2 := by
  have projected : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (fun _ : Cfg => Skeleton.perfect height)) (AuthenticatedZeroCheck.program s)).run initial) := by
    unfold AuthenticatedZeroCheck.program
    rw [←MultiCommitmentPrefix.project_witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (requests s.tag s.factors) s.commit (AuthenticatedZeroCheck.continuation s) initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (fun _ : Cfg => Skeleton.perfect height) (AuthenticatedZeroCheck.program s) initial audited _ projected

/-- Original-owner reuse, ZeroCheck arithmetic and all factor openings share
the caller's final collision exclusion from any audited incoming state. -/
theorem original_safe_bound [NeZero m] [NeZero b]
    (s : Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (complete : ∀ factor, factor ∈ s.factors) (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2*b-1)*productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2*b-1)*(productDegree+1))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited s.encoding dummy (fun _ : Cfg => Skeleton.perfect height) initial) :
    Pr{let outcome ← (witness s dummy initial)}[
      OriginalFactorExceptionUnion.OriginalRisk s dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      (((n : ENNReal) / Fintype.card F)^b +
        (((((2*b-1)*productDegree+1 : ℕ) : ENNReal) / Fintype.card F)^b) +
        (n : ENNReal)*(((((2*b-1)*(productDegree+1) : ℕ) : ENNReal) / Fintype.card F)^b)) +
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum := by
  have arithmetic := truth_risk_bound s dummy capacity radius productDegree bounded firstDegree messageDegree initial
  have opening := opening_safe_bound s basis dummy complete enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support _ _
    (fun outcome => TruthRisk s dummy capacity radius outcome ∨
      (OpeningRisk s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2)) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic opening)
  · intro outcome supported event
    obtain ⟨risk,safe⟩ := event
    obtain ⟨owner,recorded,falseOriginal,passes⟩ := risk
    have audit := audited_witness s dummy initial audited outcome supported
    have same : OriginalFactorExceptionUnion.originalSources s dummy capacity radius owner =
        sources s dummy capacity radius outcome.1 := by
      funext factor
      rcases RecordedSourceCoherence.source_eq_or_bad s.encoding dummy s.domain capacity radius outcome.2.2 audit
          (s.tag factor) (owner factor) (snapshots s.tag outcome.1 factor) (recorded factor).2
          (fresh_recorded s dummy complete initial outcome supported factor) (recorded factor).1 with equal | bad
      · exact congrArg (QueryReindex.source s.dimensions) equal
      · exact False.elim (safe bad)
    have falseFresh : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices
        (sources s dummy capacity radius outcome.1) := by
      intro relation
      exact falseOriginal (same.symm ▸ relation)
    rcases accepted_implies_risks s dummy capacity radius outcome initial supported falseFresh passes with truth | wrong
    · exact Or.inl truth
    · exact Or.inr ⟨wrong,safe⟩

end
end FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness
