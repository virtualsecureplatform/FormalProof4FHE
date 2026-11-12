module
public import FormalProof4FHE.HasteBoots.AuthenticatedPublicZeroCheck
public import FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound
@[expose] public section

/-! ZeroCheck with verifier-computed public factors on the entire inherited
ambient history. Only private original factors are committed and opened. -/
namespace FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening AuthenticatedPublicZeroCheck
noncomputable section
variable {F K Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {b n front suffix m queries height : ℕ}

/-- All factors use one pre-query decoded source per public root/context. -/
def privateSources (heights : Cfg → ℕ)
    (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : ((Private → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  fun factor => QueryReindex.source s.dimensions (SubclaimSourceLayout.decodedSource (front := front) (suffix := suffix) s.domain capacity radius
    (AmbientCommittedBatchSafeBound.frozen s.encoding dummy heights s.tag first factor))

/-- Private factors use the root-recorded decoder; public factors are the
fixed verifier tables from the same pre-query emission. -/
def sources (heights : Cfg → ℕ)
    (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : ((Private → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  Sum.elim (privateSources heights s dummy capacity radius first) (s.publicTables first.1)

abbrev Prefix (heights : Cfg → ℕ) := ((Private → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

abbrev RunResult (heights : Cfg → ℕ) := (PreparedPublicZeroTerminal.Packet F Private Memory b n ×
  ShortCircuitSequence.Outcome Private (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

/-- Terminal checking and the complete native factor loop both succeed. -/
def accepted (result : PreparedPublicZeroTerminal.Packet F Private Memory b n ×
    ShortCircuitSequence.Outcome Private (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) : Bool :=
  result.1.data.enabled && result.2.accepted

/-- Earlier arithmetic risk, restricted to prefixes whose fixed decoded sources
violate the original zero relation. No false-prefix certificate is supplied. -/
def TruthRisk (heights : Cfg → ℕ)
    (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix heights (Private := Private) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Private := Private) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height)) : Prop :=
  ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources heights s dummy capacity radius outcome.1) ∧
  PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices (sources heights s dummy capacity radius outcome.1)
    outcome.2.1.1.earlier

/-- Accepted wrong supplied values on the actual native factor loop. -/
def OpeningRisk (heights : Cfg → ℕ)
    (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix heights (Private := Private) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Private := Private) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height)) : Prop :=
  outcome.2.1.2.accepted = true ∧ ∃ factor, outcome.2.1.1.data.values factor ≠
    (PreparedPublicZeroTerminal.query s.nodes outcome.2.1.1).fold (privateSources heights s dummy capacity radius outcome.1 factor)

def originalPrivateSources (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) :=
  fun factor => QueryReindex.source s.dimensions
    (AmbientMatrixSource.source (front := front) s.encoding dummy heights s.domain capacity radius (s.tag factor) (owner factor))

def originalSources (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (emission : (Private → Digest) × CommitMemory) :=
  Sum.elim (originalPrivateSources heights s dummy capacity radius owner) (s.publicTables emission)

def OriginalRisk (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : Prefix heights (Private := Private) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Private := Private) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (n := n) (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor),
    (∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (originalSources heights s dummy capacity radius owner outcome.1.1) ∧
    accepted outcome.2.1 = true

variable [SampleableType (Fin b → F)] [SampleableType F] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [SampleableType (Fin b → ((Fin b → F) × F))]
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType Digest]

def witness (heights : Cfg → ℕ)
    (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag s.factors) s.commit (AuthenticatedPublicZeroCheck.continuation s) initial

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Erasure preserves the exact actual native-worker program and final state. -/
theorem project_witness (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => ((outcome.1.1,outcome.2.1),outcome.2.2)) <$> witness heights s dummy initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights))
        (AuthenticatedPublicZeroCheck.program s)).run initial :=
  MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag s.factors) s.commit (AuthenticatedPublicZeroCheck.continuation s) initial

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Every private original root is actually recorded before its query. -/
theorem fresh_recorded (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) (outcome : Prefix heights (Private := Private) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Private := Private) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (complete : ∀ factor, factor ∈ s.factors) (factor : Private) :
    ⟨s.tag factor,AmbientCommittedBatchSafeBound.snapshots heights s.tag outcome.1 factor⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag s.factors) s.commit (AuthenticatedPublicZeroCheck.continuation s) initial outcome supported
    (s.tag factor,outcome.1.1.1 factor) (List.mem_map_of_mem (complete factor))

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Earlier owners remain recorded through successful and rejected paths. -/
theorem retains (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) (outcome : Prefix heights (Private := Private) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Private := Private) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_retains s.encoding dummy (AmbientMatrixSource.Shape heights)
    (requests s.tag s.factors) s.commit (AuthenticatedPublicZeroCheck.continuation s) initial outcome supported tag saved recorded

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- The whole public-factor ZeroCheck inherits the caller's actual audit. -/
theorem audited_witness (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) (outcome : Prefix heights (Private := Private) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Private := Private) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial)) :
    CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights))
        (AuthenticatedPublicZeroCheck.program s)).run initial) := by
    rw [←project_witness heights s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (AuthenticatedPublicZeroCheck.program s) initial audited _ actual

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- No ZeroCheck, value binding or native worker call clears an earlier failure. -/
theorem bad_persistent (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) (outcome : Prefix heights (Private := Private) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Private := Private) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) initial) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights))
        (AuthenticatedPublicZeroCheck.program s)).run initial) := by
    rw [←project_witness heights s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
    (AmbientMatrixSource.Shape heights) (AuthenticatedPublicZeroCheck.program s) initial bad _ actual

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- The original-owner risk includes every accepted false fresh-source claim. -/
theorem fresh_risk_implies_original (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) (outcome : Prefix heights (Private := Private) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      RunResult heights (F := F) (Private := Private) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (complete : ∀ factor, factor ∈ s.factors) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources heights s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) : OriginalRisk heights s dummy capacity radius outcome :=
  ⟨AmbientCommittedBatchSafeBound.snapshots heights s.tag outcome.1,
    fun factor => ⟨rfl,fresh_recorded heights s dummy initial outcome supported complete factor⟩,falseClaim,passes⟩

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Every accepted false fixed-source zero relation exposes one of the two actual
arithmetic events. Source selection uses the prefix snapshot throughout. -/
theorem accepted_implies_risks (heights : Cfg → ℕ)
    (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Prefix heights (Private := Private) (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) ×
      RunResult heights (F := F) (Private := Private) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (n := n) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (witness heights s dummy initial))
    (falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices
      (sources heights s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) :
    TruthRisk heights s dummy capacity radius outcome ∨ OpeningRisk heights s dummy capacity radius outcome := by
  simp only [witness, MultiCommitmentPrefix.witness, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at supported
  obtain ⟨first, _, last, lastSupported, equal⟩ := supported
  subst outcome
  obtain ⟨selected, selectedSupported, opened, _, lastEqual⟩ :=
    (SharedContinuation.support_program s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if packet.data.enabled then
        ShortCircuitSequence.program (NativeMatrixVerifier.step
          (NativeCommittedOpening.protocol s.encoding s.domain (left s) (right s) (build s) first.1 packet))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩)
      (RecordRoots.state _ (requests s.tag s.factors first.1) first.2) last).mp lastSupported
  subst last
  have flags := Bool.and_eq_true_iff.mp passes
  obtain ⟨entry, earlier, checked⟩ := PreparedPublicZeroTerminal.select_sound s.nodes (s.publicTables first.1) s.encoding dummy (AmbientMatrixSource.Shape heights)
    (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond first.1) (s.afterFirst first.1)
      (s.send first.1) (s.afterChallenge first.1) (s.initial first.1))
    s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1)
    (RecordRoots.state _ (requests s.tag s.factors first.1) first.2) selected selectedSupported flags.1
  obtain truthful | wrong := PreparedPublicZeroTerminal.checked_truthful_or_wrong_private s.nodes (s.publicTables first.1) s.arity s.coefficient s.indices
    (privateSources heights s dummy capacity radius first) selected.1 entry earlier checked
  · exact Or.inl ⟨falseClaim, truthful⟩
  · exact Or.inr ⟨flags.2, wrong⟩

/-- The earlier ZeroCheck error is averaged over actual commitment outcomes,
including arbitrary private commitment memory and the real root-recorded state. -/
theorem truth_risk_bound [Fintype F]
    (heights : Cfg → ℕ)
    (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2 * b - 1) * productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2 * b - 1) * (productDegree + 1))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness heights s dummy initial)}[TruthRisk heights s dummy capacity radius outcome] ≤
      ((n : ENNReal) / Fintype.card F) ^ b +
        ((((((2 * b - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (n : ENNReal) * ((((((2 * b - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices
      (sources heights s dummy capacity radius first)
  · let initial := RecordRoots.state (AmbientMatrixSource.Shape heights) (requests s.tag s.factors first.1) first.2
    have afterNative := SharedContinuation.earlier_event_le s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if packet.data.enabled then
        ShortCircuitSequence.program (NativeMatrixVerifier.step
          (NativeCommittedOpening.protocol s.encoding s.domain (left s) (right s) (build s) first.1 packet))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩) initial
      (fun packet => PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices
        (sources heights s dummy capacity radius first) packet.earlier)
    have afterPrepare := PreparedPublicZeroTerminal.earlier_event_le s.nodes (s.publicTables first.1) s.encoding dummy (AmbientMatrixSource.Shape heights)
      (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond first.1) (s.afterFirst first.1)
        (s.send first.1) (s.afterChallenge first.1) (s.initial first.1))
      s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1) initial
      (PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices (sources heights s dummy capacity radius first))
    have arithmetic := PackedZeroSharedSoundness.soundness_bound s.encoding dummy (AmbientMatrixSource.Shape heights)
      s.nodes s.arity s.coefficient s.indices (sources heights s dummy capacity radius first) productDegree bounded
      s.interpretFirst s.interpret firstDegree messageDegree (s.firstRespond first.1) (s.afterFirst first.1)
      (s.send first.1) (s.afterChallenge first.1) (s.initial first.1) initial falseClaim
    have bound := afterNative.trans (afterPrepare.trans arithmetic)
    simpa [AuthenticatedPublicZeroCheck.continuation, NativeCommittedOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim] using bound
  · have valid := Classical.not_not.mp falseClaim
    simp [TruthRisk, valid, prEvent_norm]


variable [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Private-factor opening errors have their derived PCS sum outside the
caller's final ambient exception, without another local hash charge. -/
theorem opening_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest) (complete : ∀ factor, factor ∈ s.factors)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights s dummy initial)}[OpeningRisk heights s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum := by
  have bound := AmbientCommittedOpeningSafeBound.soundness basis s.encoding dummy heights s.tag s.factors complete geometry
    s.domain enough capacity radius (left s) (right s) (build s) s.commit (select s)
    (fun _ packet => packet.data.enabled) (fun _ packet => packet.data.memory) small initial audited
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome risk
  refine ⟨?_,risk.2⟩
  obtain ⟨passed,factor,different⟩ := risk.1
  refine ⟨passed,factor,?_⟩
  change outcome.2.1.1.data.values factor ≠ _
  rw [privateSources,QueryReindex.fold,SubclaimSourceLayout.fold_decodedSource] at different
  exact different

/-- Private original owners and fixed verifier public tables share one
ZeroCheck/PCS bound on the actual inherited execution. -/
theorem original_safe_bound [NeZero m] [NeZero b] (heights : Cfg → ℕ) (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest) (complete : ∀ factor, factor ∈ s.factors)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2*b-1)*productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2*b-1)*(productDegree+1))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights s dummy initial)}[OriginalRisk heights s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (((n : ENNReal)/Fintype.card F)^b + ((((((2*b-1)*productDegree+1 : ℕ) : ENNReal)/Fintype.card F)^b)) +
        (n : ENNReal)*((((((2*b-1)*(productDegree+1) : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum := by
  have arithmetic := truth_risk_bound heights s dummy capacity radius productDegree bounded firstDegree messageDegree initial
  have opening := opening_safe_bound heights s geometry basis dummy complete enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support (witness heights s dummy initial) _
    (fun outcome => TruthRisk heights s dummy capacity radius outcome ∨
      (OpeningRisk heights s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2)) ?_)
    ((prEvent_or_le _ _ _).trans (add_le_add arithmetic opening))
  intro outcome supported event
  obtain ⟨⟨owner,recorded,falseOriginal,passes⟩,clear⟩ := event
  have audit := audited_witness heights s dummy initial audited outcome supported
  have samePrivate : originalPrivateSources heights s dummy capacity radius owner = privateSources heights s dummy capacity radius outcome.1 := by
    funext factor
    rcases AmbientMatrixSource.source_eq_or_bad s.encoding dummy heights (s.tag factor) (geometry factor)
        s.domain capacity radius outcome.2.2 audit (owner factor) (AmbientCommittedBatchSafeBound.snapshots heights s.tag outcome.1 factor)
        (recorded factor).2 (fresh_recorded heights s dummy initial outcome supported complete factor) (recorded factor).1 with equal | bad
    · exact congrArg (QueryReindex.source s.dimensions) equal
    · exact False.elim (clear bad)
  have same : originalSources heights s dummy capacity radius owner outcome.1.1 = sources heights s dummy capacity radius outcome.1 := by
    simp only [originalSources,sources,samePrivate]
  have falseFresh : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources heights s dummy capacity radius outcome.1) := by
    intro holds
    exact falseOriginal (same.symm ▸ holds)
  rcases accepted_implies_risks heights s dummy capacity radius initial outcome supported falseFresh passes with truth | wrong
  · exact Or.inl truth
  · exact Or.inr ⟨wrong,clear⟩


/-- Typed native evaluation vectors derive both message degree bounds. The
original-owner ZeroCheck/private-opening rate needs no supplied degree or
terminal/EQ/worker-success security certificate and no local hash charge. -/
theorem native_original_safe_bound [NeZero m] [NeZero b]
    (characteristic productDegree : ℕ) [CharP F characteristic]
    (firstSmall : (2*b-1)*productDegree+1 ≤ characteristic)
    (roundSmall : (2*b-1)*(productDegree+1)+1 ≤ characteristic)
    (nodesEnough : 2*b ≤ (2*b-1)*productDegree+1)
    (heights : Cfg → ℕ)
    (s : Scheme F Private Public Term (Fin b → Fin ((2*b-1)*productDegree+1) → F)
      (Fin ((2*b-1)*(productDegree+1)+1) → F) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest) (complete : ∀ factor, factor ∈ s.factors)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness heights (nativeScheme characteristic productDegree firstSmall roundSmall nodesEnough s) dummy initial)}[
      OriginalRisk heights (nativeScheme characteristic productDegree firstSmall roundSmall nodesEnough s) dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (((n : ENNReal)/Fintype.card F)^b + ((((((2*b-1)*productDegree+1 : ℕ) : ENNReal)/Fintype.card F)^b)) +
        (n : ENNReal)*((((((2*b-1)*(productDegree+1) : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (s.factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum :=
  original_safe_bound heights (nativeScheme characteristic productDegree firstSmall roundSmall nodesEnough s)
    geometry basis dummy complete enough capacity radius productDegree bounded
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) small initial audited

end
end FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck
