module
public import FormalProof4FHE.HasteBoots.AuthenticatedPublicZeroCheck
public import FormalProof4FHE.HasteBoots.AmbientHeterogeneousBatchOpening
public import FormalProof4FHE.HasteBoots.SingletonOpening
public import FormalProof4FHE.HasteBoots.HeterogeneousSingleOpening
public import FormalProof4FHE.HasteBoots.QueryHighZeroPadding
public import FormalProof4FHE.HasteBoots.AmbientMatrixSource
@[expose] public section

/-! Packed public-factor ZeroCheck on padded private logical views. Public
tables are verifier-computed; only private roots are committed and opened.
Native single openings retain their preparation step and exact worker work. -/
namespace FormalProof4FHE.HasteBoots.PaddedPublicZeroCheck
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening
noncomputable section
structure Scheme (F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type) [Field F]
    (heights : Cfg → ℕ) (b n : ℕ) where
  code : Private → HeterogeneousSingleOpening.Layout
  padding : Private → ℕ
  dimensions : ∀ factor, padding factor+(n+1) = (code factor).front+(code factor).suffix
  encoding : MerkleOracle.Encoding Input Digest (List F)
  tag : Private → Cfg
  domain : ∀ factor, Fin (2^heights (tag factor)) ↪ F
  factors : List Private
  nodes : PackedSumcheckRound.Node b ↪ F
  arity : Term → ℕ
  coefficient : Term → F
  indices : (term : Term) → Fin (arity term) → Sum Private Public
  publicTables : ((Private → Digest) × CommitMemory) → Public → MatrixFold.Cube (n+1) → Fin b → F
  interpretFirst : FirstMessage → Fin b → Polynomial F
  interpret : Message → Polynomial F
  commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Private → Digest) × CommitMemory)
  initial : ((Private → Digest) × CommitMemory) → Memory
  firstRespond : ((Private → Digest) × CommitMemory) → PackedZeroReduction.Points F n b → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (FirstMessage × Memory)
  afterFirst : ((Private → Digest) × CommitMemory) → PackedZeroReduction.Points F n b → FirstMessage × Memory →
    PackedZeroReduction.Coins F b → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  send : ((Private → Digest) × CommitMemory) → ℕ → Memory → (Fin b → F) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Message × Memory)
  afterChallenge : ((Private → Digest) × CommitMemory) → Memory → (Fin b → F) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  receiveValues : ((Private → Digest) × CommitMemory) → PackedZeroOracle.Subclaim F b n → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) ((Private → Fin b → F) × Memory)
  bindValues : ((Private → Digest) × CommitMemory) → PackedZeroOracle.Subclaim F b n →
    (Private → Fin b → F) → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  build : ((Private → Digest) × CommitMemory) → PreparedPublicZeroTerminal.Packet F Private Memory b n → (factor : Private) →
    SingletonOpening.Protocol F Input Digest Cfg Response Memory b (code factor).front (code factor).suffix (code factor).m
      (code factor).queries (heights (tag factor))

variable {F K Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {heights : Cfg → ℕ} {b n : ℕ}
local notation "S" => Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory heights b n

abbrev layouts (s : S) := fun factor =>
  (⟨(s.code factor).front,(s.code factor).suffix,1,(s.code factor).m,(s.code factor).queries⟩ : HeterogeneousBatchOpening.Layout)

abbrev Prefix (heights : Cfg → ℕ) := ((Private → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)
abbrev ActualResult (s : S) := PreparedPublicZeroTerminal.Packet F Private Memory b n ×
  ShortCircuitSequence.Outcome Private (Sigma (HeterogeneousBatchOpening.Data F Digest Response b heights s.tag (layouts s))) Memory
abbrev RunResult (s : S) := ActualResult s ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)
local notation "Pfx" => Prefix (Private := Private) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights

def query (s : S) (packet : PreparedPublicZeroTerminal.Packet F Private Memory b n) (factor : Private) :=
  QueryReindex.query (s.dimensions factor) (QueryHighZeroPadding.query (s.padding factor) (PreparedPublicZeroTerminal.query s.nodes packet))

/-- The checked private value and padded query override the callback's fields;
its prepare/response/attachment/worker work remains literal. -/
def single (s : S) (emission : (Private → Digest) × CommitMemory)
    (packet : PreparedPublicZeroTerminal.Packet F Private Memory b n) (factor : Private) :
    SingletonOpening.Protocol F Input Digest Cfg Response Memory b (s.code factor).front (s.code factor).suffix
      (s.code factor).m (s.code factor).queries (heights (s.tag factor)) :=
  {s.build emission packet factor with
    encoding := s.encoding
    domain := s.domain factor
    root := emission.1 factor
    query := query s packet factor
    value := packet.data.values factor}

def build (s : S) (emission : (Private → Digest) × CommitMemory)
    (packet : PreparedPublicZeroTerminal.Packet F Private Memory b n) (factor : Private) :=
  SingletonOpening.toBatch (single s emission packet factor)

def originalSources (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) :=
  fun factor => QueryHighZeroPadding.source (s.padding factor) (QueryReindex.source (s.dimensions factor)
    (AmbientMatrixSource.source (front := (s.code factor).front) s.encoding dummy heights (s.domain factor) (capacity factor) (radius factor) (s.tag factor) (owner factor)))

def privateSources (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ) (first : Pfx) :=
  originalSources s dummy capacity radius (HeterogeneousBatchOpening.snapshots heights s.tag first)

def sources (s : S) (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ) (first : Pfx) :=
  Sum.elim (privateSources s dummy capacity radius first) (s.publicTables first.1)

def accepted (s : S) (result : ActualResult s) : Bool := result.1.data.enabled && result.2.accepted

def TruthRisk (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (outcome : Pfx × RunResult s) : Prop :=
  ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) ∧
  PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) outcome.2.1.1.earlier

def OpeningRisk (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (outcome : Pfx × RunResult s) : Prop :=
  HeterogeneousBatchOpening.Wrong (heights := heights) (tag := s.tag) (layout := layouts s)
    s.encoding dummy s.domain capacity radius (build s) outcome.1 outcome.2

def OriginalRisk (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (outcome : Pfx × RunResult s) : Prop :=
  ∃ owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor),
    (∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (Sum.elim (originalSources s dummy capacity radius owner) (s.publicTables outcome.1.1)) ∧
    accepted s outcome.2.1 = true

omit [DecidableEq Input] [Fintype Term] in
/-- A logical table evaluation equals its own padded physical PCS evaluation. -/
theorem source_evaluation (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (first : Pfx) (packet : PreparedPublicZeroTerminal.Packet F Private Memory b n) (factor : Private) (claim : Fin 1) :
    (PreparedPublicZeroTerminal.query s.nodes packet).fold (privateSources s dummy capacity radius first factor) =
      matrixEvaluation (NativeBatchChecks.left (build s first.1 packet factor).query claim)
        (NativeBatchChecks.right (build s first.1 packet factor).query claim)
        (MatrixOpeningSecurity.extract (s.domain factor) (capacity factor) (radius factor)
          (InteractiveAuthenticatedOpening.word s.encoding dummy heights (s.tag factor) (HeterogeneousBatchOpening.snapshots heights s.tag first factor))) := by
  rw [privateSources,originalSources,QueryHighZeroPadding.fold,QueryReindex.fold,AmbientMatrixSource.source,SubclaimSourceLayout.fold_decodedSource]
  rfl

variable (s : Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory heights b n)
  [SampleableType (Fin b → F)] [SampleableType F] [SampleableType (Fin n → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [SampleableType (Fin b → ((Fin b → F) × F))] [SampleableType Digest]
  [∀ factor, SampleableType (TestMatrix F (2^(s.code factor).front) b)]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]

def select (emission : (Private → Digest) × CommitMemory) :=
  PreparedPublicZeroTerminal.select s.nodes (s.publicTables emission)
    (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond emission) (s.afterFirst emission)
      (s.send emission) (s.afterChallenge emission) (s.initial emission))
    s.arity s.coefficient s.indices (s.receiveValues emission) (s.bindValues emission) (s.initial emission)
def continuation := HeterogeneousBatchOpening.continuation (heights := heights) (tag := s.tag) (layout := layouts s)
  s.encoding s.domain (build s) (select s) (fun _ packet => packet.data.enabled) (fun _ packet => packet.data.memory) s.factors
def program := MultiCommitmentPrefix.program (HeterogeneousBatchOpening.requests s.tag s.factors) s.commit (continuation s)
def witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag s.factors) s.commit (continuation s) initial

omit [DecidableEq Input] [SampleableType Digest] [SampleableType F]
  [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- The executed openings retain each singleton's preparation before its test draw. -/
theorem continuation_single (emission : (Private → Digest) × CommitMemory) :
    continuation s emission = SharedContinuation.program (select s emission) (fun packet => if packet.data.enabled then
      DependentShortCircuitSequence.program (fun factor => SingletonOpening.step (single s emission packet factor))
        s.factors packet.data.memory else pure ⟨[],packet.data.memory,false⟩) := by
  have trusted (packet : PreparedPublicZeroTerminal.Packet F Private Memory b n) (factor : Private) :
      HeterogeneousBatchOpening.protocol s.encoding heights s.tag (layouts s) s.domain (build s) emission packet factor =
        SingletonOpening.toBatch (single s emission packet factor) := rfl
  have transition (packet : PreparedPublicZeroTerminal.Packet F Private Memory b n) (factor : Private) :
      NativeBatchVerifier.step (SingletonOpening.toBatch (single s emission packet factor)) =
        SingletonOpening.step (single s emission packet factor) := funext (SingletonOpening.step_eq _)
  simp only [continuation,HeterogeneousBatchOpening.continuation,trusted,transition]

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
theorem project_witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => ((outcome.1.1,outcome.2.1),outcome.2.2)) <$> witness s dummy initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights))
        (program s)).run initial :=
  MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag s.factors) s.commit (continuation s) initial


omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Every original physical source is recorded before ZeroCheck query selection. -/
theorem fresh_recorded (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial)) (complete : ∀ factor, factor ∈ s.factors) (side : Private) :
    ⟨s.tag side,HeterogeneousBatchOpening.snapshots heights s.tag outcome.1 side⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag s.factors) s.commit (continuation s) initial outcome supported
    (s.tag side,outcome.1.1.1 side) (List.mem_map_of_mem (complete side))

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Earlier owners survive all physical single openings, even on rejection. -/
theorem retains (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_retains s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag s.factors) s.commit (continuation s) initial outcome supported tag saved recorded

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Full-state projection derives the final audit without resetting any history. -/
theorem audited_witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial)
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial)) :
    CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights)) (program s)).run initial) := by
    rw [←project_witness s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights)
    (program s) initial audited _ actual

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- All earlier exceptions persist through the actual single-opening continuation. -/
theorem bad_persistent (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) initial) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2 := by
  have actual : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights)) (program s)).run initial) := by
    rw [←project_witness s dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights)
    (program s) initial bad _ actual

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Actual accepted false logical relations expose ZeroCheck arithmetic
or an incorrect original-root native single opening. -/
theorem accepted_implies_risks (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial))
    (falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1))
    (passes : accepted s outcome.2.1 = true) :
    TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome := by
  simp only [witness, MultiCommitmentPrefix.witness, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at supported
  obtain ⟨first, _, last, lastSupported, equal⟩ := supported
  subst outcome
  obtain ⟨selected, selectedSupported, opened, _, lastEqual⟩ :=
    (SharedContinuation.support_program s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if packet.data.enabled then
        DependentShortCircuitSequence.program
          (fun factor => NativeBatchVerifier.step
            (HeterogeneousBatchOpening.protocol s.encoding heights s.tag (layouts s) s.domain (build s) first.1 packet factor))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩)
      (RecordRoots.state _ (HeterogeneousBatchOpening.requests s.tag s.factors first.1) first.2) last).mp lastSupported
  subst last
  have flags := Bool.and_eq_true_iff.mp passes
  obtain ⟨entry, earlier, checked⟩ := PreparedPublicZeroTerminal.select_sound s.nodes (s.publicTables first.1) s.encoding dummy (AmbientMatrixSource.Shape heights)
    (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond first.1) (s.afterFirst first.1)
      (s.send first.1) (s.afterChallenge first.1) (s.initial first.1))
    s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1)
    (RecordRoots.state _ (HeterogeneousBatchOpening.requests s.tag s.factors first.1) first.2) selected selectedSupported flags.1
  obtain truthful | wrong := PreparedPublicZeroTerminal.checked_truthful_or_wrong_private s.nodes (s.publicTables first.1) s.arity s.coefficient s.indices
    (privateSources s dummy capacity radius first) selected.1 entry earlier checked
  · exact Or.inl ⟨falseClaim, truthful⟩
  · obtain ⟨factor,different⟩ := wrong
    refine Or.inr ⟨flags.2,factor,0,?_⟩
    change selected.1.data.values factor ≠ _
    rwa [source_evaluation s dummy capacity radius first selected.1 factor 0] at different


theorem truth_risk_bound [Fintype F]
    (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b)
    (radius : Private → ℕ) (productDegree : ℕ)
    (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2 * b - 1) * productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2 * b - 1) * (productDegree + 1))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness s dummy initial)}[TruthRisk s dummy capacity radius outcome] ≤
      ((n : ENNReal) / Fintype.card F) ^ b +
        ((((((2 * b - 1) * productDegree + 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (n : ENNReal) * ((((((2 * b - 1) * (productDegree + 1) : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices
      (sources s dummy capacity radius first)
  · let initial := RecordRoots.state (AmbientMatrixSource.Shape heights) (HeterogeneousBatchOpening.requests s.tag s.factors first.1) first.2
    have afterNative := SharedContinuation.earlier_event_le s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if packet.data.enabled then
        DependentShortCircuitSequence.program
          (fun factor => NativeBatchVerifier.step
            (HeterogeneousBatchOpening.protocol s.encoding heights s.tag (layouts s) s.domain (build s) first.1 packet factor))
          s.factors packet.data.memory else pure ⟨[], packet.data.memory, false⟩) initial
      (fun packet => PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices
        (sources s dummy capacity radius first) packet.earlier)
    have afterPrepare := PreparedPublicZeroTerminal.earlier_event_le s.nodes (s.publicTables first.1) s.encoding dummy (AmbientMatrixSource.Shape heights)
      (PackedZeroOracle.program s.nodes s.interpretFirst s.interpret (s.firstRespond first.1) (s.afterFirst first.1)
        (s.send first.1) (s.afterChallenge first.1) (s.initial first.1))
      s.arity s.coefficient s.indices (s.receiveValues first.1) (s.bindValues first.1) (s.initial first.1) initial
      (PackedZeroOracle.TruthfulResult s.nodes s.arity s.coefficient s.indices (sources s dummy capacity radius first))
    have arithmetic := PackedZeroSharedSoundness.soundness_bound s.encoding dummy (AmbientMatrixSource.Shape heights)
      s.nodes s.arity s.coefficient s.indices (sources s dummy capacity radius first) productDegree bounded
      s.interpretFirst s.interpret firstDegree messageDegree (s.firstRespond first.1) (s.afterFirst first.1)
      (s.send first.1) (s.afterChallenge first.1) (s.initial first.1) initial falseClaim
    have bound := afterNative.trans (afterPrepare.trans arithmetic)
    simpa [continuation, HeterogeneousBatchOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim] using bound
  · have valid := Classical.not_not.mp falseClaim
    simp [TruthRisk, valid, prEvent_norm]


omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Actual fresh snapshots already provide matching recorded original owners. -/
theorem fresh_risk_implies_original (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial))
    (complete : ∀ factor, factor ∈ s.factors)
    (wrong : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1))
    (passes : accepted s outcome.2.1 = true) : OriginalRisk s dummy capacity radius outcome :=
  ⟨HeterogeneousBatchOpening.snapshots heights s.tag outcome.1,
    (fun factor => ⟨rfl,fresh_recorded s dummy initial outcome supported complete factor⟩),wrong,passes⟩

variable [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [∀ factor, SampleableType ((Fin (2^(s.code factor).front) × Fin b) → K)]

omit [SampleableType F] [SampleableType (Fin n → F)] [SampleableType (Fin b → ((Fin b → F) × F))] in
/-- Each physical original source pays its own native single-opening PCS error
under the same final exclusion, without an additional collision charge. -/
theorem opening_safe_bound [NeZero b] [∀ factor, NeZero (s.code factor).m]
    (basis : Module.Basis (Fin b) F K) (dummy : Digest) (complete : ∀ factor, factor ∈ s.factors)
    (enough : ∀ factor, (s.code factor).m ≤ Fintype.card (Fin (2^heights (s.tag factor))))
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain factor)) (s.code factor).m :
        Set (Fin (2^heights (s.tag factor)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness s dummy initial)}[OpeningRisk s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (s.factors.map (fun factor => JointMatrixOpening.error (K := K) (m := (s.code factor).m) (b := b)
        (queries := (s.code factor).queries) (s.domain factor) (radius factor))).sum :=
  AmbientHeterogeneousBatchOpening.soundness (heights := heights) (tag := s.tag) (layout := layouts s) basis s.encoding dummy s.factors complete s.domain enough capacity radius (build s)
    s.commit (select s) (fun _ packet => packet.data.enabled) (fun _ packet => packet.data.memory) small initial audited

/-- Original logical-source ZeroCheck plus source-specific physical PCS rates
on the actual inherited audited execution. -/
theorem original_safe_bound [NeZero b] [∀ factor, NeZero (s.code factor).m]
    (basis : Module.Basis (Fin b) F K) (dummy : Digest) (complete : ∀ factor, factor ∈ s.factors)
    (enough : ∀ factor, (s.code factor).m ≤ Fintype.card (Fin (2^heights (s.tag factor))))
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (productDegree : ℕ) (bounded : ∀ term, s.arity term ≤ productDegree)
    (firstDegree : ∀ message point, (s.interpretFirst message point).natDegree ≤ (2*b-1)*productDegree)
    (messageDegree : ∀ message, (s.interpret message).natDegree ≤ (2*b-1)*(productDegree+1))
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain factor)) (s.code factor).m :
        Set (Fin (2^heights (s.tag factor)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness s dummy initial)}[OriginalRisk s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (((n : ENNReal)/Fintype.card F)^b + ((((((2*b-1)*productDegree+1 : ℕ) : ENNReal)/Fintype.card F)^b)) +
        (n : ENNReal)*((((((2*b-1)*(productDegree+1) : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (s.factors.map (fun factor => JointMatrixOpening.error (K := K) (m := (s.code factor).m) (b := b)
        (queries := (s.code factor).queries) (s.domain factor) (radius factor))).sum := by
  have arithmetic := truth_risk_bound s dummy capacity radius productDegree bounded firstDegree messageDegree initial
  have opening := opening_safe_bound s basis dummy complete enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support (witness s dummy initial) _
    (fun outcome => TruthRisk s dummy capacity radius outcome ∨
      (OpeningRisk s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2)) ?_)
    ((prEvent_or_le _ _ _).trans (add_le_add arithmetic opening))
  intro outcome supported event
  obtain ⟨⟨owner,recorded,falseOriginal,passes⟩,clear⟩ := event
  have audit := audited_witness s dummy initial audited outcome supported
  have samePrivate : originalSources s dummy capacity radius owner = privateSources s dummy capacity radius outcome.1 := by
    funext factor
    rcases AmbientMatrixSource.source_eq_or_bad s.encoding dummy heights (s.tag factor) rfl (s.domain factor)
        (capacity factor) (radius factor) outcome.2.2 audit (owner factor)
        (HeterogeneousBatchOpening.snapshots heights s.tag outcome.1 factor) (recorded factor).2
        (fresh_recorded s dummy initial outcome supported complete factor) (recorded factor).1 with equal | bad
    · exact congrArg (fun physical => QueryHighZeroPadding.source (s.padding factor) (QueryReindex.source (s.dimensions factor) physical)) equal
    · exact False.elim (clear bad)
  have same : Sum.elim (originalSources s dummy capacity radius owner) (s.publicTables outcome.1.1) =
      sources s dummy capacity radius outcome.1 := by
    rw [sources, samePrivate]
  have falseFresh : ¬PackedZeroCube.Vanishes s.arity s.coefficient s.indices (sources s dummy capacity radius outcome.1) := by
    intro holds
    exact falseOriginal (same.symm ▸ holds)
  rcases accepted_implies_risks s dummy capacity radius initial outcome supported falseFresh passes with truth | wrong
  · exact Or.inl truth
  · exact Or.inr ⟨wrong,clear⟩

end
end FormalProof4FHE.HasteBoots.PaddedPublicZeroCheck
