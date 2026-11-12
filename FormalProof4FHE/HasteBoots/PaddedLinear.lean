module
public import FormalProof4FHE.HasteBoots.AuthenticatedLinear
public import FormalProof4FHE.HasteBoots.AmbientHeterogeneousBatchOpening
public import FormalProof4FHE.HasteBoots.HeterogeneousSingleOpening
public import FormalProof4FHE.HasteBoots.QueryReindex
public import FormalProof4FHE.HasteBoots.QueryHighZeroPadding
public import FormalProof4FHE.HasteBoots.AmbientMatrixSource
@[expose] public section

/-! Packed linear identities on logical tables with source-specific physical
PCS layouts and padding. Each opening is the exact native singleton step,
including its prepare-before-test phase, with no extra batching challenge. -/
namespace FormalProof4FHE.HasteBoots.PaddedLinear
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening
noncomputable section

structure Scheme (F Input Digest Cfg Response Memory CommitMemory : Type) [Field F]
    (heights : Cfg → ℕ) (count b n : ℕ) where
  code : Fin count → HeterogeneousSingleOpening.Layout
  padding : Fin count → ℕ
  dimensions : ∀ factor, padding factor+n = (code factor).front+(code factor).suffix
  encoding : MerkleOracle.Encoding Input Digest (List F)
  tag : Fin count → Cfg
  domain : ∀ factor, Fin (2^heights (tag factor)) ↪ F
  relations : List (PackedLinear.Relation F (Fin count))
  nodes : PackedSumcheckRound.Node b ↪ F
  commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Fin count → Digest) × CommitMemory)
  initial : ((Fin count → Digest) × CommitMemory) → Memory
  bindRelations : ((Fin count → Digest) × CommitMemory) → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  receive : ((Fin count → Digest) × CommitMemory) → Memory → PackedSumcheckSubclaim.Query F b n →
    OracleComp (SharedSequence.Shared Cfg Input Digest) ((Fin count → Fin b → F) × Memory)
  build : ((Fin count → Digest) × CommitMemory) → PackedLinearOracle.Packet F (Fin count) Memory b n → (factor : Fin count) →
    SingletonOpening.Protocol F Input Digest Cfg Response Memory b (code factor).front (code factor).suffix (code factor).m
      (code factor).queries (heights (tag factor))

variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {heights : Cfg → ℕ} {count b n : ℕ}
local notation "S" => Scheme F Input Digest Cfg Response Memory CommitMemory heights count b n

abbrev layouts (s : S) := fun factor => (⟨(s.code factor).front,(s.code factor).suffix,1,(s.code factor).m,(s.code factor).queries⟩ : HeterogeneousBatchOpening.Layout)
abbrev Prefix (heights : Cfg → ℕ) := ((Fin count → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)
abbrev ActualResult (s : S) := PackedLinearOracle.Packet F (Fin count) Memory b n ×
  ShortCircuitSequence.Outcome (Fin count) (Sigma (HeterogeneousBatchOpening.Data F Digest Response b heights s.tag (layouts s))) Memory
abbrev RunResult (s : S) := ActualResult s ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)
local notation "Pfx" => Prefix (count := count) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights

def preflight [Fintype F] (s : S) : Bool :=
  decide (0 < count) && (!s.relations.isEmpty) && s.relations.all (fun relation => !relation.isEmpty) &&
    decide (0 < b ∧ 2*b < Fintype.card F)

def query (s : S) (packet : PackedLinearOracle.Packet F (Fin count) Memory b n) (factor : Fin count) :=
  QueryReindex.query (s.dimensions factor) (QueryHighZeroPadding.query (s.padding factor) packet.query)

/-- Root, context, query and checked value are verifier-selected; the original
prepare/response/worker programs and their returned memory are retained. -/
def single (s : S) (emission : (Fin count → Digest) × CommitMemory)
    (packet : PackedLinearOracle.Packet F (Fin count) Memory b n) (factor : Fin count) :
    SingletonOpening.Protocol F Input Digest Cfg Response Memory b (s.code factor).front (s.code factor).suffix (s.code factor).m
      (s.code factor).queries (heights (s.tag factor)) :=
  {s.build emission packet factor with
    encoding := s.encoding, domain := s.domain factor, root := emission.1 factor,
    query := query s packet factor, value := packet.values factor}

def build (s : S) (emission : (Fin count → Digest) × CommitMemory)
    (packet : PackedLinearOracle.Packet F (Fin count) Memory b n) (factor : Fin count) :=
  SingletonOpening.toBatch (single s emission packet factor)

def originalSources (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) :=
  fun factor => QueryHighZeroPadding.source (s.padding factor) (QueryReindex.source (s.dimensions factor)
    (AmbientMatrixSource.source (front := (s.code factor).front) s.encoding dummy heights (s.domain factor) (capacity factor) (radius factor) (s.tag factor) (owner factor)))

def sources (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ) (first : Pfx) :=
  originalSources s dummy capacity radius (HeterogeneousBatchOpening.snapshots heights s.tag first)

def accepted (s : S) (result : ActualResult s) : Bool := result.1.accepted && result.2.accepted

def TruthRisk (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (outcome : Pfx × RunResult s) : Prop :=
  ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1) ∧
    PackedLinearOracle.Truthful (sources s dummy capacity radius outcome.1) outcome.2.1.1

def OpeningRisk (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (outcome : Pfx × RunResult s) : Prop :=
  HeterogeneousBatchOpening.Wrong (heights := heights) (tag := s.tag) (layout := layouts s)
    s.encoding dummy s.domain capacity radius (build s) outcome.1 outcome.2

def OriginalRisk (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (outcome : Pfx × RunResult s) : Prop :=
  ∃ owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor),
    (∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬PackedLinear.Holds s.relations (originalSources s dummy capacity radius owner) ∧ accepted s outcome.2.1 = true

omit [DecidableEq Input] in
/-- The same logical table is evaluated by its own zero-extended physical query. -/
theorem source_evaluation (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (first : Pfx) (packet : PackedLinearOracle.Packet F (Fin count) Memory b n) (factor : Fin count) (claim : Fin 1) :
    packet.query.fold (sources s dummy capacity radius first factor) =
      matrixEvaluation (NativeBatchChecks.left (build s first.1 packet factor).query claim)
        (NativeBatchChecks.right (build s first.1 packet factor).query claim)
        (MatrixOpeningSecurity.extract (s.domain factor) (capacity factor) (radius factor)
          (InteractiveAuthenticatedOpening.word s.encoding dummy heights (s.tag factor) (HeterogeneousBatchOpening.snapshots heights s.tag first factor))) := by
  rw [sources,originalSources,QueryHighZeroPadding.fold,QueryReindex.fold,AmbientMatrixSource.source,SubclaimSourceLayout.fold_decodedSource]
  rfl

omit [DecidableEq Input] in
/-- An accepted false logical identity yields truthful false linear checking
or an incorrect native source claim; neither is supplied as a premise. -/
theorem accepted_implies_risks (s : S) (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (outcome : Pfx × RunResult s)
    (wrong : ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1))
    (passes : accepted s outcome.2.1 = true) : TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome := by
  classical
  have flags := Bool.and_eq_true_iff.mp passes
  by_cases correct : ∀ factor, outcome.2.1.1.values factor = outcome.2.1.1.query.fold (sources s dummy capacity radius outcome.1 factor)
  · exact Or.inl ⟨wrong,flags.1,correct⟩
  · obtain ⟨factor,different⟩ := not_forall.mp correct
    refine Or.inr ⟨flags.2,factor,0,?_⟩
    change outcome.2.1.1.values factor ≠ _
    rwa [source_evaluation s dummy capacity radius outcome.1 outcome.2.1.1 factor 0] at different

variable (s : Scheme F Input Digest Cfg Response Memory CommitMemory heights count b n)
  [Fintype F] [SampleableType (Fin b → F)] [SampleableType Digest]
  [∀ factor, SampleableType (TestMatrix F (2^(s.code factor).front) b)]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]

def select (emission : (Fin count → Digest) × CommitMemory) :=
  PackedLinearOracle.program s.nodes s.relations (preflight s)
    (s.bindRelations emission (s.initial emission)) (s.receive emission) (s.initial emission)
def continuation := HeterogeneousBatchOpening.continuation (heights := heights) (tag := s.tag) (layout := layouts s)
  s.encoding s.domain (build s) (select s) (fun _ packet => packet.accepted) (fun _ packet => packet.memory) (AuthenticatedLinear.factors count)
def program := MultiCommitmentPrefix.program (HeterogeneousBatchOpening.requests s.tag (AuthenticatedLinear.factors count)) s.commit (continuation s)
def witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag (AuthenticatedLinear.factors count)) s.commit (continuation s) initial

omit [DecidableEq Input] [SampleableType Digest] in
/-- Exact native singleton transitions retain prepare-before-test, private
memory, rejection, column checks and workers; there is no resampling step. -/
theorem continuation_single (emission : (Fin count → Digest) × CommitMemory) :
    continuation s emission = SharedContinuation.program (select s emission) (fun packet => if packet.accepted then
      DependentShortCircuitSequence.program (fun factor => SingletonOpening.step (single s emission packet factor))
        (AuthenticatedLinear.factors count) packet.memory else pure ⟨[],packet.memory,false⟩) := by
  have trusted (packet : PackedLinearOracle.Packet F (Fin count) Memory b n) (factor : Fin count) :
      HeterogeneousBatchOpening.protocol s.encoding heights s.tag (layouts s) s.domain (build s) emission packet factor =
        SingletonOpening.toBatch (single s emission packet factor) := rfl
  have transition (packet : PackedLinearOracle.Packet F (Fin count) Memory b n) (factor : Fin count) :
      NativeBatchVerifier.step (SingletonOpening.toBatch (single s emission packet factor)) =
        SingletonOpening.step (single s emission packet factor) := funext (SingletonOpening.step_eq _)
  simp only [continuation,HeterogeneousBatchOpening.continuation,trusted,transition]

theorem project_witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => ((outcome.1.1,outcome.2.1),outcome.2.2)) <$> witness s dummy initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights))
        (program s)).run initial :=
  MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag (AuthenticatedLinear.factors count)) s.commit (continuation s) initial


/-- Every original physical source is recorded before linear query selection. -/
theorem fresh_recorded (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial)) (side : Fin count) :
    ⟨s.tag side,HeterogeneousBatchOpening.snapshots heights s.tag outcome.1 side⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag (AuthenticatedLinear.factors count)) s.commit (continuation s) initial outcome supported
    (s.tag side,outcome.1.1.1 side) (List.mem_map_of_mem (AuthenticatedLinear.factors_complete side))

/-- Earlier owners survive all physical singleton openings, even when a later step rejects. -/
theorem retains (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_retains s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag (AuthenticatedLinear.factors count)) s.commit (continuation s) initial outcome supported tag saved recorded

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

/-- All earlier exceptions persist through the actual singleton continuation. -/
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

/-- One logical-query compression error is averaged over the actual
commitment outcomes and inherited root-recorded state. -/
theorem truth_risk_bound (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness s dummy initial)}[TruthRisk s dummy capacity radius outcome] ≤
      (n : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : ¬PackedLinear.Holds s.relations (sources s dummy capacity radius first)
  · let initial := RecordRoots.state (AmbientMatrixSource.Shape heights) (HeterogeneousBatchOpening.requests s.tag (AuthenticatedLinear.factors count) first.1) first.2
    have retained := SharedContinuation.earlier_event_le s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if packet.accepted then
        DependentShortCircuitSequence.program
          (fun factor => NativeBatchVerifier.step (HeterogeneousBatchOpening.protocol s.encoding heights s.tag (layouts s) s.domain (build s) first.1 packet factor))
          (AuthenticatedLinear.factors count) packet.memory else pure ⟨[], packet.memory, false⟩) initial
      (PackedLinearOracle.Truthful (sources s dummy capacity radius first))
    have arithmetic := PackedLinearOracle.truthful_bound s.encoding dummy (AmbientMatrixSource.Shape heights)
      s.nodes s.relations (preflight s) (s.bindRelations first.1 (s.initial first.1))
      (s.receive first.1) (s.initial first.1) (sources s dummy capacity radius first) initial falseClaim
    simpa [continuation, HeterogeneousBatchOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim]
      using retained.trans arithmetic
  · simp [TruthRisk, falseClaim, prEvent_norm]

/-- Actual fresh snapshots already provide matching recorded original owners. -/
theorem fresh_risk_implies_original (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial))
    (wrong : ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1))
    (passes : accepted s outcome.2.1 = true) : OriginalRisk s dummy capacity radius outcome :=
  ⟨HeterogeneousBatchOpening.snapshots heights s.tag outcome.1,
    (fun factor => ⟨rfl,fresh_recorded s dummy initial outcome supported factor⟩),wrong,passes⟩

variable [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [∀ factor, SampleableType ((Fin (2^(s.code factor).front) × Fin b) → K)]

/-- Each physical original source pays its own native single-opening PCS error
under the same final exclusion, without an additional collision charge. -/
theorem opening_safe_bound [NeZero b] [∀ factor, NeZero (s.code factor).m]
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : ∀ factor, (s.code factor).m ≤ Fintype.card (Fin (2^heights (s.tag factor))))
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain factor)) (s.code factor).m :
        Set (Fin (2^heights (s.tag factor)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness s dummy initial)}[OpeningRisk s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      ((AuthenticatedLinear.factors count).map (fun factor => JointMatrixOpening.error (K := K) (m := (s.code factor).m) (b := b)
        (queries := (s.code factor).queries) (s.domain factor) (radius factor))).sum :=
  AmbientHeterogeneousBatchOpening.soundness (heights := heights) (tag := s.tag) (layout := layouts s) basis s.encoding dummy (AuthenticatedLinear.factors count) AuthenticatedLinear.factors_complete s.domain enough capacity radius (build s)
    s.commit (select s) (fun _ packet => packet.accepted) (fun _ packet => packet.memory) small initial audited

/-- Original logical-source linear checking plus source-specific physical PCS rates
on the actual inherited audited execution. -/
theorem original_safe_bound [NeZero b] [∀ factor, NeZero (s.code factor).m]
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : ∀ factor, (s.code factor).m ≤ Fintype.card (Fin (2^heights (s.tag factor))))
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain factor)) (s.code factor).m :
        Set (Fin (2^heights (s.tag factor)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness s dummy initial)}[OriginalRisk s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (n : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b)) +
      ((AuthenticatedLinear.factors count).map (fun factor => JointMatrixOpening.error (K := K) (m := (s.code factor).m) (b := b)
        (queries := (s.code factor).queries) (s.domain factor) (radius factor))).sum := by
  have arithmetic := truth_risk_bound s dummy capacity radius initial
  have opening := opening_safe_bound s basis dummy enough capacity radius small initial audited
  apply le_trans (prEvent_mono_of_support (witness s dummy initial) _
    (fun outcome => TruthRisk s dummy capacity radius outcome ∨
      (OpeningRisk s dummy capacity radius outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2)) ?_)
    ((prEvent_or_le _ _ _).trans (add_le_add arithmetic opening))
  intro outcome supported event
  obtain ⟨⟨owner,recorded,falseOriginal,passes⟩,clear⟩ := event
  have audit := audited_witness s dummy initial audited outcome supported
  have same : originalSources s dummy capacity radius owner = sources s dummy capacity radius outcome.1 := by
    funext factor
    rcases AmbientMatrixSource.source_eq_or_bad s.encoding dummy heights (s.tag factor) rfl (s.domain factor)
        (capacity factor) (radius factor) outcome.2.2 audit (owner factor)
        (HeterogeneousBatchOpening.snapshots heights s.tag outcome.1 factor) (recorded factor).2
        (fresh_recorded s dummy initial outcome supported factor) (recorded factor).1 with equal | bad
    · exact congrArg (fun physical => QueryHighZeroPadding.source (s.padding factor) (QueryReindex.source (s.dimensions factor) physical)) equal
    · exact False.elim (clear bad)
  have falseFresh : ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1) := by
    intro holds
    exact falseOriginal (same.symm ▸ holds)
  rcases accepted_implies_risks s dummy capacity radius outcome falseFresh passes with truth | wrong
  · exact Or.inl truth
  · exact Or.inr ⟨wrong,clear⟩

end
end FormalProof4FHE.HasteBoots.PaddedLinear
