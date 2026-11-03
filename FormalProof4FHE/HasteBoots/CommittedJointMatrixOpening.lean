module

public import FormalProof4FHE.HasteBoots.JointMatrixOpening
public import FormalProof4FHE.HasteBoots.MultiCommitmentPrefix

@[expose] public section

/-!
# Joint factor openings after an adaptive multi-root commitment prefix

The program starts from empty initialization. Commitment work emits the root
family and arbitrary private memory. Every root is frozen at that actual log,
then arbitrary shared work selects the matrix queries before the sequential
factor-opening loop. Arithmetic losses sum over factors; authentication uses
one expected hash charge for commitment, query selection and every opening.
No safe-prefix certificate, assumed PCS security, or query cutoff is supplied.
The statement is for homogeneous typed PCS layouts and private verifier coins;
full ZeroCheck/terminal orchestration, Fiat--Shamir and Rust refinement remain.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening

noncomputable section

variable {F K Factor Cfg Input Digest Response QueryData CommitMemory Memory : Type}
  [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
  [DecidableEq F] [DecidableEq K] [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] [Fintype Digest]
  {leftCount b m size queries height : ℕ}
  [SampleableType (TestMatrix F leftCount b)]
  [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType ((Fin leftCount × Fin b) → K)]

/-- Trusted factor/context pairs, instantiated with the emitted public roots. -/
def requests (tag : Factor → Cfg) (indices : List Factor)
    (emission : (Factor → Digest) × CommitMemory) : List (Cfg × Digest) :=
  indices.map (fun factor => (tag factor, emission.1 factor))

/-- One query-independent source checkpoint for each factor. -/
def snapshots (tag : Factor → Cfg)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (factor : Factor) : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) (tag factor) :=
  ⟨first.1.1 factor, first.2.hash.log⟩

omit [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] [Fintype Digest]
  [SampleableType (TestMatrix F leftCount b)] [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType ((Fin leftCount × Fin b) → K)] in
/-- Root recording preserves the real commitment log, for all factors including
repeated roots or aliased context tags. -/
theorem snapshots_recorded (tag : Factor → Cfg) (indices : List Factor)
    (complete : ∀ factor, factor ∈ indices)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (factor : Factor) :
    ⟨tag factor, snapshots tag first factor⟩ ∈
      (RecordRoots.state (fun _ : Cfg => Skeleton.perfect height) (requests tag indices first.1)
        first.2).checkpoints.checkpoints :=
  RecordRoots.recorded _ _ first.2 (tag factor, first.1.1 factor)
    (List.mem_map_of_mem (complete factor))

/-- Query selection receives retained commitment memory. Every later factor
receives the actual private memory returned by its predecessor. -/
def continuation
    (selectQuery : ((Factor → Digest) × CommitMemory) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (respond : ((Factor → Digest) × CommitMemory) → QueryData → Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : ((Factor → Digest) × CommitMemory) → QueryData → Factor → Memory →
      SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Columns F Digest leftCount b height × Memory))
    (indices : List Factor) (emission : (Factor → Digest) × CommitMemory) :=
  SharedContinuation.program (selectQuery emission) (fun query =>
    SharedSequence.program (JointMatrixOpening.step (respond emission query) (next emission query))
      indices (start emission query))

/-- Full joint private-coin opening bound from empty initialization. The
availability charge occurs once, even if many factors are incorrectly opened. -/
theorem soundness_from_empty [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (tag : Factor → Cfg) (indices : List Factor) (complete : ∀ factor, factor ∈ indices)
    (domain : Fin (2 ^ height) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : size ≤ m * b) (radius : ℕ)
    (left : QueryData → Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : QueryData → Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (respond : ((Factor → Digest) × CommitMemory) → QueryData → Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : ((Factor → Digest) × CommitMemory) → QueryData → Factor → Memory →
      SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Columns F Digest leftCount b height × Memory))
    (testResponse structuredResponse : ((Factor → Digest) × CommitMemory) → QueryData → Factor →
      TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy (fun _ : Cfg => Skeleton.perfect height)
      (requests tag indices) commit (continuation selectQuery start respond next indices)
      (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)))}[
        JointMatrixOpening.AnyAcceptedWrong enc dummy tag (snapshots tag outcome.1) domain capacity radius
          (left outcome.2.1.1) (right outcome.2.1.1) (testResponse outcome.1.1 outcome.2.1.1)
          (structuredResponse outcome.1.1 outcome.2.1.1) (outcome.2.1.2, outcome.2.2)] ≤
      (indices.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius)).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (MultiCommitmentPrefix.program (requests tag indices) commit (continuation selectQuery start respond next indices))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  let arithmetic := fun first query (data : JointMatrixOpening.Data F Digest Response leftCount b height queries) factor =>
    SharedMatrixSampling.ArithmeticBad domain capacity radius
      (JointMatrixOpening.frozen enc dummy tag (snapshots tag first) factor)
      (left query factor) (right query factor) (testResponse first.1 query factor)
      (structuredResponse first.1 query factor) data.1
  apply MultiCommitmentPrefix.event_bound enc dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests tag indices) commit (continuation selectQuery start respond next indices)
    (fun first last => JointMatrixOpening.AnyAcceptedWrong enc dummy tag (snapshots tag first) domain capacity radius
      (left last.1.1) (right last.1.1) (testResponse first.1 last.1.1)
      (structuredResponse first.1 last.1.1) (last.1.2, last.2))
    (fun first last => SharedSequence.AnyBad (fun factor data => arithmetic first last.1.1 data factor) last.1.2.1) _
  · intro first
    apply SharedContinuation.later_event_le enc dummy (fun _ : Cfg => Skeleton.perfect height)
      (selectQuery first.1) (fun query => SharedSequence.program
        (JointMatrixOpening.step (respond first.1 query) (next first.1 query)) indices (start first.1 query))
      (RecordRoots.state _ (requests tag indices first.1) first.2)
      (fun query outcome => SharedSequence.AnyBad (fun factor data => arithmetic first query data factor) outcome.1.1)
    intro query initial
    exact JointMatrixOpening.arithmetic_union_bound basis enc dummy domain enough capacity radius
      (JointMatrixOpening.frozen enc dummy tag (snapshots tag first)) (left query) (right query)
      (respond first.1 query) (next first.1 query) (testResponse first.1 query) (structuredResponse first.1 query)
      indices (start first.1 query) initial small
  · intro first last supported accepted
    obtain ⟨entry, member, wrong⟩ := accepted
    have present := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun _ : Cfg => Skeleton.perfect height) (tag entry.1) (snapshots tag first entry.1)
      (continuation selectQuery start respond next indices first.1)
      (RecordRoots.state _ (requests tag indices first.1) first.2)
      (snapshots_recorded tag indices complete first entry.1) last supported
    obtain failed | unavailable := final_checks_imply_failure enc dummy (fun _ : Cfg => height)
      (tag entry.1) (snapshots tag first entry.1) domain capacity radius
      (left last.1.1 entry.1) (right last.1.1 entry.1)
      (testResponse first.1 last.1.1 entry.1) (structuredResponse first.1 last.1.1 entry.1)
      (entry.2, last.2) present wrong
    · exact Or.inl ⟨entry, member, failed⟩
    · exact Or.inr unavailable

end

end FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening
