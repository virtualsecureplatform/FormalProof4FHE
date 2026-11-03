module

public import FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
public import FormalProof4FHE.HasteBoots.CommitmentPrefix

@[expose] public section

/-!
# Authenticated interactive opening after an arbitrary commitment prefix

The experiment starts with an empty shared cache and checkpoint history. The
prover chooses its root after arbitrary adaptive shared-oracle work. One source
is frozen there, before either private verifier sample. False acceptance is
bounded by the matrix arithmetic error plus the expected hash charge of the
entire program, including commitment. No safe-prefix certificate is supplied.
The snapshot in the analysis distribution is ghost state: erasing it gives the
exact original program by `CommitmentPrefix.project_witness`.

This still uses private ideal coins, typed columns and native-verifier replay.
It is not yet a theorem about production Fiat--Shamir or Rust execution.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.CommittedMatrixOpening

noncomputable section

variable {F K Cfg Input Digest Response : Type}
  [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
  [DecidableEq F] [DecidableEq K] [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] [Fintype Digest]
  {leftCount b m size queries : ℕ} {height : Cfg → ℕ} {tag : Cfg}
  [SampleableType (TestMatrix F leftCount b)]
  [SampleableType (Fin queries → Fin (2 ^ height tag))]
  [SampleableType ((Fin leftCount × Fin b) → K)]

/-- A complete empty-cache private-coin matrix-opening bound, with all
commitment and verification hash work charged on the same actual execution. -/
theorem soundness_from_empty [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2 ^ height tag) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height tag)))
    (capacity : size ≤ m * b) (radius : ℕ)
    (left : Fin leftCount → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (commit : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Digest)
    (respond : Digest → TestMatrix F leftCount b →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (next : Digest → SampleData F Response leftCount b (height tag) queries →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Columns F Digest leftCount b (height tag)))
    (testResponse structuredResponse : Digest → TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height tag) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (CommitmentPrefix.witness (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun tag => Skeleton.perfect (height tag)) tag commit (fun root => game (respond root) (next root))
      (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))))}[
      AcceptedWrong enc dummy height tag
        (CommitmentPrefix.snapshot (fun tag => Skeleton.perfect (height tag)) tag outcome.1)
        domain capacity radius left right (testResponse outcome.1.1) (structuredResponse outcome.1.1) outcome.2] ≤
      ((Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height tag) → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound (Fin (2 ^ height tag)) queries
        (Code.minDist (BlockCode.code domain m b : Set (Fin (2 ^ height tag) → Fin b → F)) - radius))
        (ColumnOpening.missBound (Fin (2 ^ height tag)) queries (radius + 1))) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss unifSpec (fun tag => Skeleton.perfect (height tag)))
        (CommitmentPrefix.program tag commit (fun root => game (respond root) (next root)))
        (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))) := by
  classical
  apply CommitmentPrefix.event_bound (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (fun tag => Skeleton.perfect (height tag)) tag commit (fun root => game (respond root) (next root))
    (fun first last => AcceptedWrong enc dummy height tag (CommitmentPrefix.snapshot _ tag first)
      domain capacity radius left right (testResponse first.1) (structuredResponse first.1) last)
    (fun first last => SharedMatrixSampling.ArithmeticBad domain capacity radius
      (word enc dummy height tag (CommitmentPrefix.snapshot _ tag first)) left right
        (testResponse first.1) (structuredResponse first.1) last.1.1) _
  · intro first
    let source := word (leftCount := leftCount) (b := b) enc dummy height tag
      (CommitmentPrefix.snapshot _ tag first)
    let : Fintype (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) := Fintype.ofFinite _
    let : SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) :=
      SampleableType.ofFintype _
    let : Fintype (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker :=
      Fintype.ofFinite _
    let : SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker :=
      SampleableType.ofFintype _
    exact SharedMatrixSampling.arithmetic_after_bound basis domain enough capacity radius source left right enc dummy
      (fun tag => Skeleton.perfect (height tag)) (respond first.1) (testResponse first.1)
      (structuredResponse first.1) (next first.1) (CheckpointExecution.record _ first.2 tag first.1) small
  · intro first last reached accepted
    exact accepted_wrong_implies_failure enc dummy (CommitmentPrefix.snapshot _ tag first) domain capacity radius
      left right (respond first.1) (next first.1) (testResponse first.1) (structuredResponse first.1)
      (CheckpointExecution.record _ first.2 tag first.1) (CommitmentPrefix.snapshot_recorded _ tag first)
      last reached accepted

end

end FormalProof4FHE.HasteBoots.CommittedMatrixOpening
