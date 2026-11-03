module

public import FormalProof4FHE.HasteBoots.PackedLinearOracle
public import FormalProof4FHE.HasteBoots.SingletonOpening
public import FormalProof4FHE.HasteBoots.CommittedBatchOpening
public import FormalProof4FHE.HasteBoots.NativePackedInterpolation

@[expose] public section

/-!
# Authenticated canonical packed linear identities

Trusted roots/relations precede one common query; all supplied values are
checked before any source opening. Original sources then open in native array
order, with binding-before-test, exact column attachment and single-column
workers. The one-claim batch interface is proved equal to these single steps.
The from-empty bound contains one linear-compression term, a PCS sum over
sources and one expected hash charge for this complete stopped execution.
Full PBS relations/composition, raw preflight, honest scheduler completion,
production Fiat--Shamir and Rust/work refinement remain open.
-/

open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening

namespace FormalProof4FHE.HasteBoots.AuthenticatedLinear

noncomputable section

structure Scheme (F Input Digest Cfg Response Memory CommitMemory : Type) [Field F]
    (count b front suffix m queries height : ℕ) where
  encoding : MerkleOracle.Encoding Input Digest (List F)
  domain : Fin (2 ^ height) ↪ F
  tag : Fin count → Cfg
  relations : List (PackedLinear.Relation F (Fin count))
  nodes : PackedSumcheckRound.Node b ↪ F
  commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Fin count → Digest) × CommitMemory)
  initial : ((Fin count → Digest) × CommitMemory) → Memory
  bindRelations : ((Fin count → Digest) × CommitMemory) → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  receive : ((Fin count → Digest) × CommitMemory) → Memory → Query F b (front + suffix) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) ((Fin count → Fin b → F) × Memory)
  build : ((Fin count → Digest) × CommitMemory) → PackedLinearOracle.Packet F (Fin count) Memory b (front + suffix) →
    Fin count → SingletonOpening.Protocol F Input Digest Cfg Response Memory b front suffix m queries height

variable {F K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [Fintype F] [DecidableEq Input] [DecidableEq Digest]
  {count b front suffix m queries height : ℕ}

def factors (count : ℕ) : List (Fin count) := List.ofFn id

theorem factors_complete (factor : Fin count) : factor ∈ factors count :=
  List.mem_ofFn.mpr ⟨factor, rfl⟩

/-- Raw out-of-range indices and incompatible array dimensions are excluded
by typed inputs. All remaining trusted-shape failures precede relation binding. -/
def preflight (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height) : Bool :=
  decide (0 < count) && (!s.relations.isEmpty) &&
    s.relations.all (fun relation => !relation.isEmpty) && decide (0 < b ∧ 2 * b < Fintype.card F)

/-- Trusted query/value/encoding/domain/root fields replace factory claims. -/
def single (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (emission : (Fin count → Digest) × CommitMemory)
    (packet : PackedLinearOracle.Packet F (Fin count) Memory b (front + suffix)) (factor : Fin count) :
    SingletonOpening.Protocol F Input Digest Cfg Response Memory b front suffix m queries height :=
  { s.build emission packet factor with
    encoding := s.encoding, domain := s.domain, root := emission.1 factor,
    query := packet.query, value := packet.values factor }

def build (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (emission : (Fin count → Digest) × CommitMemory)
    (packet : PackedLinearOracle.Packet F (Fin count) Memory b (front + suffix)) (factor : Fin count) :=
  SingletonOpening.toBatch (single s emission packet factor)

variable [SampleableType (Fin b → F)]

def select (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (emission : (Fin count → Digest) × CommitMemory) :=
  PackedLinearOracle.program s.nodes s.relations (preflight s)
    (s.bindRelations emission (s.initial emission)) (s.receive emission) (s.initial emission)

variable [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]

def continuation (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height) :=
  CommittedBatchOpening.continuation s.encoding s.domain (build s) (select s)
    (fun _ packet => packet.accepted) (fun _ packet => packet.memory) (factors count)

omit [DecidableEq Input] in
/-- The actual factor loop has single-opening transitions, including its own
per-root binding and all failure branches. No resampling equivalence is assumed. -/
theorem continuation_single
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (emission : (Fin count → Digest) × CommitMemory) :
    continuation s emission = SharedContinuation.program (select s emission) (fun packet =>
      if packet.accepted then
        ShortCircuitSequence.program (fun factor => SingletonOpening.step (single s emission packet factor))
          (factors count) packet.memory
      else pure ⟨[], packet.memory, false⟩) := by
  have trusted (packet : PackedLinearOracle.Packet F (Fin count) Memory b (front + suffix)) (factor : Fin count) :
      CommittedBatchOpening.protocol s.encoding s.domain (build s) emission packet factor =
        SingletonOpening.toBatch (single s emission packet factor) := rfl
  have transition (packet : PackedLinearOracle.Packet F (Fin count) Memory b (front + suffix)) (factor : Fin count) :
      NativeBatchVerifier.step (SingletonOpening.toBatch (single s emission packet factor)) =
        SingletonOpening.step (single s emission packet factor) :=
    funext (SingletonOpening.step_eq _)
  simp only [continuation, CommittedBatchOpening.continuation, trusted, transition]

def program (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height) :=
  MultiCommitmentPrefix.program (requests s.tag (factors count)) s.commit (continuation s)

variable [SampleableType Digest]

def witness (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height) (dummy : Digest) :=
  MultiCommitmentPrefix.witness s.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests s.tag (factors count)) s.commit (continuation s)
    (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height))

theorem project_witness
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height) (dummy : Digest) :
    (fun outcome => ((outcome.1.1, outcome.2.1), outcome.2.2)) <$> witness s dummy =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy
        (fun _ : Cfg => Skeleton.perfect height)) (program s)).run
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) :=
  CommittedBatchOpening.project_witness s.encoding dummy s.tag s.domain (build s) s.commit (select s)
    (fun _ packet => packet.accepted) (fun _ packet => packet.memory) (factors count)

abbrev Prefix := ((Fin count → Digest) × CommitMemory) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)

abbrev RunResult := (PackedLinearOracle.Packet F (Fin count) Memory b (front + suffix) ×
  ShortCircuitSequence.Outcome (Fin count) (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)

def sources (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count)) :=
  fun factor => SubclaimSourceLayout.decodedSource (front := front) (suffix := suffix) s.domain capacity radius
    (JointMatrixOpening.frozen s.encoding dummy s.tag (snapshots s.tag first) factor)

def accepted (result : PackedLinearOracle.Packet F (Fin count) Memory b (front + suffix) ×
    ShortCircuitSequence.Outcome (Fin count) (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) : Bool :=
  result.1.accepted && result.2.accepted

def TruthRisk
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (front := front) (suffix := suffix) (queries := queries) (height := height)) : Prop :=
  ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1) ∧
    PackedLinearOracle.Truthful (sources s dummy capacity radius outcome.1) outcome.2.1.1

def OpeningRisk
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (front := front) (suffix := suffix) (queries := queries) (height := height)) : Prop :=
  outcome.2.1.2.accepted = true ∧ ∃ factor,
    outcome.2.1.1.values factor ≠ outcome.2.1.1.query.fold (sources s dummy capacity radius outcome.1 factor)

omit [Fintype F] [DecidableEq Input] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType Digest] in
theorem accepted_implies_risks
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (outcome : Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height) (count := count) ×
      RunResult (F := F) (Memory := Memory) (Response := Response) (Input := Input) (Digest := Digest) (Cfg := Cfg)
        (b := b) (count := count) (front := front) (suffix := suffix) (queries := queries) (height := height))
    (falseClaim : ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1))
    (passes : accepted outcome.2.1 = true) :
    TruthRisk s dummy capacity radius outcome ∨ OpeningRisk s dummy capacity radius outcome := by
  classical
  have flags := Bool.and_eq_true_iff.mp passes
  by_cases correct : ∀ factor, outcome.2.1.1.values factor = outcome.2.1.1.query.fold (sources s dummy capacity radius outcome.1 factor)
  · exact Or.inl ⟨falseClaim, flags.1, correct⟩
  · exact Or.inr ⟨flags.2, not_forall.mp correct⟩

theorem truth_risk_bound
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ) :
    Pr{let outcome ← witness s dummy}[TruthRisk s dummy capacity radius outcome] ≤
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
    simpa [continuation, CommittedBatchOpening.continuation, initial, prEvent_norm, TruthRisk, falseClaim]
      using retained.trans arithmetic
  · simp [TruthRisk, falseClaim, prEvent_norm]

variable [Fintype Digest] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

theorem opening_risk_bound [NeZero m] [NeZero b]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← witness s dummy}[OpeningRisk s dummy capacity radius outcome] ≤
      ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height)) (program s)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have bound := CommittedBatchOpening.soundness_from_empty basis s.encoding dummy s.tag (factors count) factors_complete
    s.domain enough capacity radius (build s) s.commit (select s)
    (fun _ packet => packet.accepted) (fun _ packet => packet.memory) small
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome risk
  obtain ⟨passed, factor, wrong⟩ := risk
  refine ⟨passed, factor, 0, ?_⟩
  change outcome.2.1.1.values factor ≠ _
  rw [sources, SubclaimSourceLayout.fold_decodedSource] at wrong
  exact wrong

/-- One complete shared execution, with no terminal-truthfulness, replay,
safe-prefix, PCS-security or caller-supplied acceptance certificate. -/
theorem soundness_from_empty [NeZero m] [NeZero b]
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← witness s dummy}[
      ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1) ∧ accepted outcome.2.1 = true] ≤
      (((front + suffix : ℕ) : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
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

/-- Literal consecutive interpolation nodes used by native challenge_pair. -/
def nativeScheme (characteristic : ℕ) [CharP F characteristic] (enough : 2 * b ≤ characteristic)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height) :
    Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height :=
  { s with nodes := NativePackedInterpolation.nodes characteristic enough }

/-- Native-node specialization, still checking the public strict field-size
guard before any query or relation-binding work. -/
theorem native_soundness_from_empty [NeZero m] [NeZero b]
    (characteristic : ℕ) [CharP F characteristic] (nodesEnough : 2 * b ≤ characteristic)
    (s : Scheme F Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← witness (nativeScheme characteristic nodesEnough s) dummy}[
      ¬PackedLinear.Holds s.relations (sources s dummy capacity radius outcome.1) ∧ accepted outcome.2.1 = true] ≤
      (((front + suffix : ℕ) : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        ((factors count).map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)).sum) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (program (nativeScheme characteristic nodesEnough s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) :=
  soundness_from_empty (nativeScheme characteristic nodesEnough s) basis dummy enough capacity radius small

end

end FormalProof4FHE.HasteBoots.AuthenticatedLinear
