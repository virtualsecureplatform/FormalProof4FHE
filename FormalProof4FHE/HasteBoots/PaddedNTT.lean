module
public import FormalProof4FHE.HasteBoots.AmbientHeterogeneousBatchOpening
public import FormalProof4FHE.HasteBoots.QueryHighZeroPadding
public import FormalProof4FHE.HasteBoots.PackedNTT
public import FormalProof4FHE.HasteBoots.AmbientMatrixSource
@[expose] public section

/-! Native NTT links on logical tables, with separate physical PCS layouts and
high-zero query extensions for each original source. No virtual root or handler
reset is introduced. The row/compression query remains common to both sides. -/
namespace FormalProof4FHE.HasteBoots.PaddedNTT
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening
noncomputable section

structure Code where
  front : ℕ
  suffix : ℕ
  m : ℕ
  queries : ℕ

abbrev Code.layout (code : Code) (claims : ℕ) : HeterogeneousBatchOpening.Layout :=
  ⟨code.front,code.suffix,claims,code.m,code.queries⟩

structure Scheme (F Input Digest Cfg Response Memory CommitMemory : Type) [Field F]
    (heights : Cfg → ℕ) (b c r k : ℕ) where
  encoding : MerkleOracle.Encoding Input Digest (List F)
  tag : Bool → Cfg
  code : Bool → Code
  padding : Bool → ℕ
  dimensions : ∀ side, padding side+(r+c) = (code side).front+(code side).suffix
  domain : ∀ side, Fin (2^heights (tag side)) ↪ F
  nodes : PackedSumcheckRound.Node b ↪ F
  transform : (NTTCompression.Position c b → F) →ₗ[F] (NTTCompression.Position c b → F)
  commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Bool → Digest) × CommitMemory)
  initial : ((Bool → Digest) × CommitMemory) → Memory
  receive : ((Bool → Digest) × CommitMemory) → (Fin k → Fin r → F) → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (NTTRowOracle.Proposal F (NTTCompression.Position c b) Memory k)
  bindRows : ((Bool → Digest) × CommitMemory) → (Fin k → Fin r → F) → NTTRowOracle.Proposal F (NTTCompression.Position c b) Memory k →
    OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  afterQuery : ((Bool → Digest) × CommitMemory) → NTTCompression.Prefix F Memory c b r k →
    PackedSumcheckSubclaim.Query F b c → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  build : ((Bool → Digest) × CommitMemory) → AuthenticatedNTT.Packet F Memory c b r k → (side : Bool) →
    NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b (code side).front (code side).suffix k (code side).m
      (code side).queries (heights (tag side))

variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {heights : Cfg → ℕ} {b c r k : ℕ}
local notation "S" => Scheme F Input Digest Cfg Response Memory CommitMemory heights b c r k

abbrev layouts (s : S) := fun side => (s.code side).layout k
abbrev Prefix (heights : Cfg → ℕ) := ((Bool → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)
abbrev ActualResult (s : S) := AuthenticatedNTT.Packet F Memory c b r k ×
  ShortCircuitSequence.Outcome Bool (Sigma (HeterogeneousBatchOpening.Data F Digest Response b heights s.tag (layouts s))) Memory
abbrev RunResult (s : S) := ActualResult s ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)
local notation "Pfx" => Prefix (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights

/-- Logical coefficient/row order is preserved before selecting each source's
own zero-padding slice and physical PCS tensor split. -/
def query (s : S) (packet : AuthenticatedNTT.Packet F Memory c b r k) (side : Bool) (repetition : Fin k) :=
  QueryReindex.query (s.dimensions side) (QueryHighZeroPadding.query (s.padding side)
    (NTTCompression.sourceQuery packet.1 (AuthenticatedNTT.compressionQuery packet) (side,repetition)))

/-- Both the query family and every supplied row claim are verifier-computed. -/
def build (s : S) (emission : (Bool → Digest) × CommitMemory) (packet : AuthenticatedNTT.Packet F Memory c b r k) (side : Bool) :
    NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b (s.code side).front (s.code side).suffix k (s.code side).m
      (s.code side).queries (heights (s.tag side)) :=
  {s.build emission packet side with query := query s packet side, values := AuthenticatedNTT.values packet side}

def originalSources (s : S) (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side)) :=
  fun side => QueryHighZeroPadding.source (s.padding side) (QueryReindex.source (s.dimensions side)
    (AmbientMatrixSource.source (front := (s.code side).front) s.encoding dummy heights (s.domain side) (capacity side) (radius side) (s.tag side) (owner side)))

def sources (s : S) (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (first : Pfx) :=
  originalSources s dummy capacity radius (HeterogeneousBatchOpening.snapshots heights s.tag first)

def FalseRelation (s : S) (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (first : Pfx) : Prop :=
  ¬NTTRowCheck.Relation s.transform (NTTCompression.sourceRows c r (sources s dummy capacity radius first false))
    (NTTCompression.sourceRows c r (sources s dummy capacity radius first true))

def accepted (s : S) (result : ActualResult s) : Bool := AuthenticatedNTT.enabled result.1 && result.2.accepted

def TruthRisk (s : S) (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (outcome : Pfx × RunResult s) : Prop :=
  FalseRelation s dummy capacity radius outcome.1 ∧ NTTCompression.TruthfulTerminals
    (sources s dummy capacity radius outcome.1 false) (sources s dummy capacity radius outcome.1 true) outcome.2.1.1

def OpeningRisk (s : S) (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (outcome : Pfx × RunResult s) : Prop :=
  HeterogeneousBatchOpening.Wrong (heights := heights) (tag := s.tag) (layout := layouts s) s.encoding dummy s.domain capacity radius (build s) outcome.1 outcome.2

def OriginalRisk (s : S) (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (outcome : Pfx × RunResult s) : Prop :=
  ∃ owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side),
    (∀ side, (owner side).root = outcome.1.1.1 side ∧ ⟨s.tag side,owner side⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬NTTRowCheck.Relation s.transform (NTTCompression.sourceRows c r (originalSources s dummy capacity radius owner false))
      (NTTCompression.sourceRows c r (originalSources s dummy capacity radius owner true)) ∧
    accepted s outcome.2.1 = true

omit [DecidableEq Input] in
/-- Native physical matrix evaluation equals the logical row/compression
query on the original source, with both padding and bit order accounted for. -/
theorem source_evaluation (s : S) (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (first : Pfx) (packet : AuthenticatedNTT.Packet F Memory c b r k) (side : Bool) (repetition : Fin k) :
    (NTTCompression.sourceQuery packet.1 (AuthenticatedNTT.compressionQuery packet) (side,repetition)).fold
      (sources s dummy capacity radius first side) =
      matrixEvaluation (NativeBatchChecks.left (front := (s.code side).front) (suffix := (s.code side).suffix) (query s packet side) repetition)
        (NativeBatchChecks.right (front := (s.code side).front) (suffix := (s.code side).suffix) (query s packet side) repetition)
        (MatrixOpeningSecurity.extract (s.domain side) (capacity side) (radius side)
          (InteractiveAuthenticatedOpening.word s.encoding dummy heights (s.tag side) (HeterogeneousBatchOpening.snapshots heights s.tag first side))) := by
  rw [sources,originalSources,QueryHighZeroPadding.fold,QueryReindex.fold,AmbientMatrixSource.source,SubclaimSourceLayout.fold_decodedSource]
  rfl

omit [DecidableEq Input] in
/-- Computed native acceptance entails truthful logical NTT terminals or a
wrong physical-root batch value; there is no supplied worker-success flag. -/
theorem accepted_implies_risks (s : S) (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (outcome : Pfx × RunResult s) (falseClaim : FalseRelation s dummy capacity radius outcome.1)
    (passes : accepted s outcome.2.1 = true) :
    TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome := by
  classical
  by_cases wrong : OpeningRisk s dummy capacity radius outcome
  · exact Or.inr wrong
  · left
    refine ⟨falseClaim,?_⟩
    have flags := Bool.and_eq_true_iff.mp passes
    have gate := Bool.and_eq_true_iff.mp flags.1
    refine ⟨gate.1,?_⟩
    cases terminal : outcome.2.1.1.2 with
    | none => simp [terminal] at gate
    | some entry =>
      intro row
      have correct : ∀ side repetition, AuthenticatedNTT.values outcome.2.1.1 side repetition =
          (NTTCompression.sourceQuery outcome.2.1.1.1 (AuthenticatedNTT.compressionQuery outcome.2.1.1) (side,repetition)).fold
            (sources s dummy capacity radius outcome.1 side) := by
        intro side repetition
        by_contra different
        apply wrong
        refine ⟨flags.2,side,repetition,?_⟩
        change AuthenticatedNTT.values outcome.2.1.1 side repetition ≠ _
        rwa [source_evaluation s dummy capacity radius outcome.1 outcome.2.1.1 side repetition] at different
      have same := correct row.1 row.2
      cases row with
      | mk side repetition =>
        cases side <;> simpa only [AuthenticatedNTT.values,AuthenticatedNTT.compressionQuery,terminal,
          NTTCompression.source,Bool.false_eq_true,reduceIte] using same

/-- Trusted caller roots/encoding and exact native nodes/butterflies replace
factory fields, preserving commitment work and returned commitment memory. -/
abbrev nativeScheme (s : S) (enc : MerkleOracle.Encoding Input Digest (List F)) (roots : Bool → Digest)
    (characteristic : ℕ) [CharP F characteristic] (small : 2*b ≤ characteristic)
    {log : ℕ} (length : 2^c*b = 2^log) (psi : F) (primitive : IsPrimitiveRoot psi (2^(log+1))) : S :=
  {s with
    encoding := enc
    nodes := NativePackedInterpolation.nodes characteristic small
    transform := PackedNTT.butterflyLinear length psi primitive
    commit := do
      let original ← s.commit
      pure (roots,original.2)}

omit [DecidableEq Input] in
/-- The trusted transform is the exact packed butterfly relation on the two
logical views of the original physical decoders. -/
theorem native_relation (s : S) (enc : MerkleOracle.Encoding Input Digest (List F)) (roots : Bool → Digest)
    (characteristic : ℕ) [CharP F characteristic] (small : 2*b ≤ characteristic)
    {log : ℕ} (length : 2^c*b = 2^log) (psi : F) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side)) :
    NTTRowCheck.Relation (nativeScheme s enc roots characteristic small length psi primitive).transform
      (NTTCompression.sourceRows c r (originalSources (nativeScheme s enc roots characteristic small length psi primitive) dummy capacity radius owner false))
      (NTTCompression.sourceRows c r (originalSources (nativeScheme s enc roots characteristic small length psi primitive) dummy capacity radius owner true)) ↔
    PackedNTT.Relation length psi
      (NTTCompression.sourceRows c r (originalSources (nativeScheme s enc roots characteristic small length psi primitive) dummy capacity radius owner false))
      (NTTCompression.sourceRows c r (originalSources (nativeScheme s enc roots characteristic small length psi primitive) dummy capacity radius owner true)) := Iff.rfl

variable (s : Scheme F Input Digest Cfg Response Memory CommitMemory heights b c r k)
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)] [SampleableType Digest]
  [∀ side, SampleableType (TestMatrix F (2^(s.code side).front) b)]
  [∀ side, SampleableType (Fin (s.code side).queries → Fin (2^heights (s.tag side)))]

def select (emission : (Bool → Digest) × CommitMemory) :=
  NTTCompression.program s.nodes s.transform (s.receive emission) (s.bindRows emission) (s.initial emission) (s.afterQuery emission)
def continuation := HeterogeneousBatchOpening.continuation (heights := heights) (tag := s.tag) (layout := layouts s) s.encoding s.domain (build s) (select s)
  (fun _ => AuthenticatedNTT.enabled) (fun _ => AuthenticatedNTT.memory) [false,true]
def program := MultiCommitmentPrefix.program (HeterogeneousBatchOpening.requests s.tag [false,true]) s.commit (continuation s)
def witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :=
  MultiCommitmentPrefix.witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag [false,true]) s.commit (continuation s) initial

theorem project_witness (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => ((outcome.1.1,outcome.2.1),outcome.2.2)) <$> witness s dummy initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (AmbientMatrixSource.Shape heights))
        (program s)).run initial :=
  MultiCommitmentPrefix.project_witness s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag [false,true]) s.commit (continuation s) initial


/-- Every original physical source is recorded before NTT query selection. -/
theorem fresh_recorded (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial)) (side : Bool) :
    ⟨s.tag side,HeterogeneousBatchOpening.snapshots heights s.tag outcome.1 side⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_recorded s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag [false,true]) s.commit (continuation s) initial outcome supported
    (s.tag side,outcome.1.1.1 side) (by cases side <;> simp [HeterogeneousBatchOpening.requests])

/-- Earlier owners survive both physical batches, even when a later step rejects. -/
theorem retains (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.2.checkpoints.checkpoints :=
  SequentialStageHistory.witness_retains s.encoding dummy (AmbientMatrixSource.Shape heights)
    (HeterogeneousBatchOpening.requests s.tag [false,true]) s.commit (continuation s) initial outcome supported tag saved recorded

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

/-- All earlier exceptions persist through the actual two-batch continuation. -/
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

/-- Row detection and fresh common compression concern the logical sources,
independently of their separate physical padding/code geometries. -/
theorem truth_risk_bound [Fintype F] [SampleableType F] [SampleableType (Fin r → F)]
    (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness s dummy initial)}[TruthRisk s dummy capacity radius outcome] ≤
      (((r : ENNReal)/Fintype.card F)^k) + (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : FalseRelation s dummy capacity radius first
  · let state := RecordRoots.state (AmbientMatrixSource.Shape heights) (HeterogeneousBatchOpening.requests s.tag [false,true] first.1) first.2
    have retained := SharedContinuation.earlier_event_le s.encoding dummy (AmbientMatrixSource.Shape heights)
      (select s first.1) (fun packet => if AuthenticatedNTT.enabled packet then
        DependentShortCircuitSequence.program
          (fun side => NativeBatchVerifier.step (HeterogeneousBatchOpening.protocol s.encoding heights s.tag (layouts s) s.domain (build s) first.1 packet side))
          [false,true] (AuthenticatedNTT.memory packet) else pure ⟨[],AuthenticatedNTT.memory packet,false⟩) state
      (fun packet => NTTCompression.TruthfulTerminals (sources s dummy capacity radius first false) (sources s dummy capacity radius first true) packet)
    have arithmetic := NTTCompression.truthful_bound s.encoding dummy (AmbientMatrixSource.Shape heights)
      s.nodes s.transform (sources s dummy capacity radius first false) (sources s dummy capacity radius first true)
      (s.receive first.1) (s.bindRows first.1) (s.initial first.1) (s.afterQuery first.1) state falseClaim
    simpa [continuation,HeterogeneousBatchOpening.continuation,state,TruthRisk,prEvent_norm,falseClaim] using retained.trans arithmetic
  · simp [TruthRisk,falseClaim,prEvent_norm]

/-- Every reached native call retains its caller roots, including a call
whose rows, compression or physical batches later reject. Commitment work and
returned private commitment memory are not discarded. -/
theorem native_witness_roots (enc : MerkleOracle.Encoding Input Digest (List F)) (roots : Bool → Digest)
    (characteristic : ℕ) [CharP F characteristic] (small : 2*b ≤ characteristic)
    {log : ℕ} (length : 2^c*b = 2^log) (psi : F) (primitive : IsPrimitiveRoot psi (2^(log+1))) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult (nativeScheme s enc roots characteristic small length psi primitive))
    (supported : outcome ∈ support (witness (nativeScheme s enc roots characteristic small length psi primitive) dummy initial)) :
    outcome.1.1.1 = roots := by
  simp only [witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨original,_,same⟩ := firstSupported
  subst first
  rfl

/-- A false accepted link on its actual prefix-frozen logical views already
provides matching original physical owners. Owner recording is derived from
execution rather than supplied as an authentication certificate. -/
theorem fresh_risk_implies_original (dummy : Digest)
    (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Pfx × RunResult s) (supported : outcome ∈ support (witness s dummy initial))
    (wrong : FalseRelation s dummy capacity radius outcome.1) (passes : accepted s outcome.2.1 = true) :
    OriginalRisk s dummy capacity radius outcome :=
  ⟨HeterogeneousBatchOpening.snapshots heights s.tag outcome.1,
    (fun side => ⟨rfl,fresh_recorded s dummy initial outcome supported side⟩),wrong,passes⟩

variable [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [∀ side, SampleableType ((Fin (2^(s.code side).front) × Fin b) → K)]

/-- Exactly one PCS error per source; no repetition-count multiplier or local
hash charge is introduced by heterogeneous physical layouts. -/
theorem opening_safe_bound [NeZero b] [∀ side, NeZero (s.code side).m]
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : ∀ side, (s.code side).m ≤ Fintype.card (Fin (2^heights (s.tag side))))
    (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (small : ∀ side, (radius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain side)) (s.code side).m : Set (Fin (2^heights (s.tag side)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness s dummy initial)}[OpeningRisk s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      JointMatrixOpening.error (K := K) (m := (s.code false).m) (b := b) (queries := (s.code false).queries) (s.domain false) (radius false) +
      JointMatrixOpening.error (K := K) (m := (s.code true).m) (b := b) (queries := (s.code true).queries) (s.domain true) (radius true) := by
  have bound := AmbientHeterogeneousBatchOpening.soundness (heights := heights) (tag := s.tag) (layout := layouts s)
    basis s.encoding dummy [false,true] (fun side => by cases side <;> simp) s.domain enough capacity radius (build s) s.commit (select s)
    (fun _ => AuthenticatedNTT.enabled) (fun _ => AuthenticatedNTT.memory) small initial audited
  simpa only [witness,continuation,OpeningRisk,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using bound

/-- Original-owner row/compression soundness and both physical openings share
one inherited final exclusion, with no child soundness/replay certificate. -/
theorem original_safe_bound [NeZero b] [∀ side, NeZero (s.code side).m] [SampleableType F] [SampleableType (Fin r → F)]
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : ∀ side, (s.code side).m ≤ Fintype.card (Fin (2^heights (s.tag side))))
    (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (small : ∀ side, (radius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain side)) (s.code side).m : Set (Fin (2^heights (s.tag side)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness s dummy initial)}[OriginalRisk s dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      ((((r : ENNReal)/Fintype.card F)^k) + (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (JointMatrixOpening.error (K := K) (m := (s.code false).m) (b := b) (queries := (s.code false).queries) (s.domain false) (radius false) +
        JointMatrixOpening.error (K := K) (m := (s.code true).m) (b := b) (queries := (s.code true).queries) (s.domain true) (radius true)) := by
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
    funext side
    rcases AmbientMatrixSource.source_eq_or_bad s.encoding dummy heights (s.tag side) rfl (s.domain side) (capacity side) (radius side) outcome.2.2 audit
        (owner side) (HeterogeneousBatchOpening.snapshots heights s.tag outcome.1 side) (recorded side).2
        (fresh_recorded s dummy initial outcome supported side) (recorded side).1 with equal | bad
    · exact congrArg (fun physical => QueryHighZeroPadding.source (s.padding side) (QueryReindex.source (s.dimensions side) physical)) equal
    · exact False.elim (clear bad)
  have falseFresh : FalseRelation s dummy capacity radius outcome.1 := by
    intro relation
    exact falseOriginal (same.symm ▸ relation)
  rcases accepted_implies_risks s dummy capacity radius outcome falseFresh passes with truth | wrong
  · exact Or.inl truth
  · exact Or.inr ⟨wrong,clear⟩


/-- Native nodes, caller roots and exact butterflies have the derived padded
original-owner rate. Both physical codes keep their own parameters, and the
caller pays only its shared final exception. -/
theorem native_original_safe_bound [NeZero b] [∀ side, NeZero (s.code side).m]
    [SampleableType F] [SampleableType (Fin r → F)]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (roots : Bool → Digest)
    (characteristic : ℕ) [CharP F characteristic] (nodesSmall : 2*b ≤ characteristic)
    {log : ℕ} (length : 2^c*b = 2^log) (psi : F) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : ∀ side, (s.code side).m ≤ Fintype.card (Fin (2^heights (s.tag side))))
    (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (small : ∀ side, (radius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain side)) (s.code side).m : Set (Fin (2^heights (s.tag side)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness (nativeScheme s enc roots characteristic nodesSmall length psi primitive) dummy initial)}[
      OriginalRisk (nativeScheme s enc roots characteristic nodesSmall length psi primitive) dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      ((((r : ENNReal)/Fintype.card F)^k) + (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (JointMatrixOpening.error (K := K) (m := (s.code false).m) (b := b) (queries := (s.code false).queries) (s.domain false) (radius false) +
        JointMatrixOpening.error (K := K) (m := (s.code true).m) (b := b) (queries := (s.code true).queries) (s.domain true) (radius true)) :=
  original_safe_bound (nativeScheme s enc roots characteristic nodesSmall length psi primitive) basis dummy enough capacity radius small initial audited

end
end FormalProof4FHE.HasteBoots.PaddedNTT
