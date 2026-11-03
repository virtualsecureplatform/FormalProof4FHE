module

public import FormalProof4FHE.HasteBoots.NTTCompression
public import FormalProof4FHE.HasteBoots.QueryReindex
public import FormalProof4FHE.HasteBoots.CommittedBatchOpening

@[expose] public section

/-!
# NTT checks authenticated against the original two commitments

The actual row/check/compression execution supplies every query and expected
value to two stopped native batches. The opening factory cannot replace those
claims. Sources freeze at the commitment prefix, before row and compression
challenges. This module treats the public linear transform semantically;
native roots, bit reversal, field arithmetic and Rust refinement remain open.
-/

open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening

namespace FormalProof4FHE.HasteBoots.AuthenticatedNTT

noncomputable section

abbrev Packet (F Memory : Type) (c b r k : ℕ) :=
  NTTCompression.Prefix F Memory c b r k × Option (Query F b c × Memory)

structure Scheme (F Input Digest Cfg Response Memory CommitMemory : Type) [Field F]
    (b c r k front suffix m queries height : ℕ) where
  dimensions : r + c = front + suffix
  encoding : MerkleOracle.Encoding Input Digest (List F)
  domain : Fin (2 ^ height) ↪ F
  tag : Bool → Cfg
  nodes : PackedSumcheckRound.Node b ↪ F
  transform : (NTTCompression.Position c b → F) →ₗ[F] (NTTCompression.Position c b → F)
  commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Bool → Digest) × CommitMemory)
  initial : ((Bool → Digest) × CommitMemory) → Memory
  receive : ((Bool → Digest) × CommitMemory) → (Fin k → Fin r → F) → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (NTTRowOracle.Proposal F (NTTCompression.Position c b) Memory k)
  bindRows : ((Bool → Digest) × CommitMemory) → (Fin k → Fin r → F) →
    NTTRowOracle.Proposal F (NTTCompression.Position c b) Memory k →
    OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  afterQuery : ((Bool → Digest) × CommitMemory) → NTTCompression.Prefix F Memory c b r k → Query F b c →
    OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  build : ((Bool → Digest) × CommitMemory) → Packet F Memory c b r k → Bool →
    NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix k m queries height

variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k front suffix m queries height : ℕ}

/-- Used only for disabled packets, for which no opening step runs. -/
def zeroQuery : (n : ℕ) → Query F b n
  | 0 => .nil
  | n + 1 => .cons (fun _ => 0) (zeroQuery n)

def compressionQuery (packet : Packet F Memory c b r k) : Query F b c :=
  match packet.2 with
  | none => zeroQuery c
  | some entry => entry.1

def enabled (packet : Packet F Memory c b r k) : Bool :=
  packet.1.2.accepted && packet.2.isSome

def memory (packet : Packet F Memory c b r k) : Memory :=
  match packet.2 with
  | none => packet.1.2.proposal.memory
  | some entry => entry.2

def query (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (packet : Packet F Memory c b r k) (repetition : Fin k) :=
  QueryReindex.query s.dimensions (NTTCompression.sourceQuery packet.1 (compressionQuery packet) (false, repetition))

def values (packet : Packet F Memory c b r k) (side : Bool) (repetition : Fin k) :=
  (compressionQuery packet).fold (NTTCompression.proposed packet.1 (side, repetition))

/-- Verifier-computed claims replace both factory fields, for every repetition
and both original commitments. Per-root binding still executes inside step. -/
def build (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (emission : (Bool → Digest) × CommitMemory) (packet : Packet F Memory c b r k) (side : Bool) :
    NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix k m queries height :=
  { s.build emission packet side with query := query s packet, values := values packet side }

variable [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]

def select (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (emission : (Bool → Digest) × CommitMemory) :=
  NTTCompression.program s.nodes s.transform (s.receive emission) (s.bindRows emission)
    (s.initial emission) (s.afterQuery emission)

variable [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]

def continuation (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height) :=
  CommittedBatchOpening.continuation s.encoding s.domain (build s) (select s)
    (fun _ => enabled) (fun _ => memory) [false, true]

def program (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height) :=
  MultiCommitmentPrefix.program (requests s.tag [false, true]) s.commit (continuation s)

variable [SampleableType Digest]

def witness (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height) (dummy : Digest) :=
  MultiCommitmentPrefix.witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag [false, true]) s.commit (continuation s)
    (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height))

/-- The recorded prefix is analysis-only; erasure preserves actual work,
including received/bound rejected rows and skipped opening batches. -/
theorem project_witness
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height) (dummy : Digest) :
    (fun outcome => ((outcome.1.1, outcome.2.1), outcome.2.2)) <$> witness s dummy =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (fun _ : Cfg => Skeleton.perfect height)) (program s)).run
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) :=
  CommittedBatchOpening.project_witness s.encoding dummy s.tag s.domain (build s) s.commit (select s)
    (fun _ => enabled) (fun _ => memory) [false, true]

abbrev Prefix := ((Bool → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)

abbrev RunResult := (Packet F Memory c b r k ×
  ShortCircuitSequence.Outcome Bool (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)

def sources (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height)) :=
  fun side => QueryReindex.source s.dimensions
    (SubclaimSourceLayout.decodedSource (front := front) (suffix := suffix) s.domain capacity radius
      (JointMatrixOpening.frozen s.encoding dummy s.tag (snapshots s.tag first) side))

def FalseRelation
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height)) : Prop :=
  ¬NTTRowCheck.Relation s.transform
    (NTTCompression.sourceRows c r (sources s dummy capacity radius first false))
    (NTTCompression.sourceRows c r (sources s dummy capacity radius first true))

def accepted (result : Packet F Memory c b r k ×
    ShortCircuitSequence.Outcome Bool (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) : Bool :=
  enabled result.1 && result.2.accepted

def TruthRisk
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)) : Prop :=
  FalseRelation s dummy capacity radius outcome.1 ∧
    NTTCompression.TruthfulTerminals (sources s dummy capacity radius outcome.1 false)
      (sources s dummy capacity radius outcome.1 true) outcome.2.1.1

def OpeningRisk
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)) : Prop :=
  CommittedBatchOpening.Wrong s.encoding dummy s.tag s.domain capacity radius (build s) outcome.1 outcome.2

omit [DecidableEq Input] [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType Digest] in
/-- Every original-source compressed row value is exactly its native batch
matrix evaluation. This equality also fixes the low-coefficient/high-row order. -/
theorem source_evaluation
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height))
    (packet : Packet F Memory c b r k) (side : Bool) (repetition : Fin k) :
    (NTTCompression.sourceQuery packet.1 (compressionQuery packet) (side, repetition)).fold
      (sources s dummy capacity radius first side) =
      matrixEvaluation (NativeBatchChecks.left (front := front) (suffix := suffix) (query s packet) repetition)
        (NativeBatchChecks.right (front := front) (suffix := suffix) (query s packet) repetition)
        (MatrixOpeningSecurity.extract s.domain capacity radius
          (JointMatrixOpening.frozen s.encoding dummy s.tag (snapshots s.tag first) side)) := by
  rw [sources, QueryReindex.fold, SubclaimSourceLayout.fold_decodedSource]
  rfl

omit [DecidableEq Input] [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType Digest] in
/-- A successful batch loop against a false fixed-source relation has either
truthful NTT terminals or a wrong native batch value; no flag is supplied. -/
theorem accepted_implies_risks
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (falseClaim : FalseRelation s dummy capacity radius outcome.1)
    (passes : accepted outcome.2.1 = true) :
    TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome := by
  classical
  by_cases wrong : OpeningRisk s dummy capacity radius outcome
  · exact Or.inr wrong
  · left
    refine ⟨falseClaim, ?_⟩
    have flags := Bool.and_eq_true_iff.mp passes
    have gate := Bool.and_eq_true_iff.mp flags.1
    refine ⟨gate.1, ?_⟩
    cases terminal : outcome.2.1.1.2 with
    | none => simp [terminal] at gate
    | some entry =>
      intro row
      have correct : ∀ side repetition,
          values outcome.2.1.1 side repetition =
            (NTTCompression.sourceQuery outcome.2.1.1.1 (compressionQuery outcome.2.1.1) (side, repetition)).fold
              (sources s dummy capacity radius outcome.1 side) := by
        intro side repetition
        by_contra different
        apply wrong
        refine ⟨flags.2, side, repetition, ?_⟩
        change values outcome.2.1.1 side repetition ≠ _
        rwa [source_evaluation s dummy capacity radius outcome.1 outcome.2.1.1 side repetition] at different
      have same := correct row.1 row.2
      cases row with
      | mk side repetition =>
        cases side <;>
          simpa only [values, compressionQuery, terminal, NTTCompression.source, Bool.false_eq_true,
            reduceIte] using same

/-- Row detection and fresh compression retain their bound through the actual
native batches. The arithmetic error is averaged over real commitment prefixes. -/
theorem truth_risk_bound [Fintype F] [SampleableType F] [SampleableType (Fin r → F)]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ) :
    Pr{let outcome ← (witness s dummy)}[TruthRisk s dummy capacity radius outcome] ≤
      (((r : ENNReal) / Fintype.card F) ^ k) +
        (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  unfold witness MultiCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases falseClaim : FalseRelation s dummy capacity radius first
  · let initial := RecordRoots.state (fun _ : Cfg => Skeleton.perfect height) (requests s.tag [false, true] first.1) first.2
    have retained := SharedContinuation.earlier_event_le s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      (select s first.1) (fun packet => if enabled packet then
        ShortCircuitSequence.program
          (fun side => NativeBatchVerifier.step (CommittedBatchOpening.protocol s.encoding s.domain (build s) first.1 packet side))
          [false, true] (memory packet) else pure ⟨[], memory packet, false⟩) initial
      (fun packet => NTTCompression.TruthfulTerminals (sources s dummy capacity radius first false)
        (sources s dummy capacity radius first true) packet)
    have arithmetic := NTTCompression.truthful_bound s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
      s.nodes s.transform (sources s dummy capacity radius first false) (sources s dummy capacity radius first true)
      (s.receive first.1) (s.bindRows first.1) (s.initial first.1) (s.afterQuery first.1) initial falseClaim
    simpa [continuation, CommittedBatchOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim]
      using retained.trans arithmetic
  · simp [TruthRisk, falseClaim, prEvent_norm]

variable [Fintype Digest] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

/-- No per-repetition PCS loss: the coefficient root and evaluation root each
pay once for their whole batch, with one hash charge for the complete run. -/
theorem opening_risk_bound [NeZero m] [NeZero b]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness s dummy)}[OpeningRisk s dummy capacity radius outcome] ≤
      (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have complete : ∀ side : Bool, side ∈ [false, true] := by intro side; cases side <;> simp
  have bound := CommittedBatchOpening.soundness_from_empty basis s.encoding dummy s.tag [false, true] complete
    s.domain enough capacity radius (build s) s.commit (select s) (fun _ => enabled) (fun _ => memory) small
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at bound
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome risk
  exact risk

/-- Complete from-empty authenticated NTT soundness for the public linear
transform. Original-source terminals are discharged by concrete native batches;
there is no residual wrong-opening event or supplied replay/safety certificate. -/
theorem soundness_from_empty [NeZero m] [NeZero b] [SampleableType F] [SampleableType (Fin r → F)]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (witness s dummy)}[
      FalseRelation s dummy capacity radius outcome.1 ∧ accepted outcome.2.1 = true] ≤
      ((((r : ENNReal) / Fintype.card F) ^ k) +
        (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius +
          JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have arithmetic := truth_risk_bound s dummy capacity radius
  have opening := opening_risk_bound s basis dummy enough capacity radius small
  apply le_trans (prEvent_mono _ _ (fun outcome =>
    TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome) ?_)
  · exact (prEvent_or_le _ _ _).trans ((add_le_add arithmetic opening).trans_eq (add_assoc _ _ _).symm)
  · intro outcome event
    exact accepted_implies_risks s dummy capacity radius outcome event.1 event.2

end

end FormalProof4FHE.HasteBoots.AuthenticatedNTT
