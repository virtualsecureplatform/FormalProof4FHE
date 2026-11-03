module

public import FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
public import FormalProof4FHE.HasteBoots.StatefulCommitmentPrefix
public import FormalProof4FHE.HasteBoots.SharedContinuation

@[expose] public section

/-!
# Authenticated opening after adaptive query selection

The root is recorded before arbitrary shared work selects the opening query.
Private commitment memory passes to query selection. Private matrix and column
sampling then follow the existing opening schedule.
Arithmetic error averages over the real query-selection state, while one
availability charge covers commitment, query selection and the complete opening.
The source stays frozen at the earlier commitment. This is a private-coin,
typed-column theorem; production Fiat--Shamir and Rust refinement remain open.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.AdaptiveMatrixOpening

noncomputable section

variable {F K Cfg Input Digest Response QueryData Memory : Type}
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
    (left : QueryData → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : QueryData → Fin size → Matrix (Fin b) (Fin b) F)
    (commit : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Digest × Memory))
    (selectQuery : (Digest × Memory) → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) QueryData)
    (respond : (Digest × Memory) → QueryData → TestMatrix F leftCount b →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (next : (Digest × Memory) → QueryData → SampleData F Response leftCount b (height tag) queries →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Columns F Digest leftCount b (height tag)))
    (testResponse structuredResponse : (Digest × Memory) → QueryData → TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height tag) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (StatefulCommitmentPrefix.witness (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun tag => Skeleton.perfect (height tag)) tag commit (fun root => SharedContinuation.program (selectQuery root) (fun query => game (respond root query) (next root query)))
      (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))))}[
      AcceptedWrong enc dummy height tag
        (StatefulCommitmentPrefix.snapshot (fun tag => Skeleton.perfect (height tag)) tag outcome.1)
        domain capacity radius (left outcome.2.1.1) (right outcome.2.1.1)
          (testResponse outcome.1.1 outcome.2.1.1) (structuredResponse outcome.1.1 outcome.2.1.1)
          (outcome.2.1.2, outcome.2.2)] ≤
      ((Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height tag) → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound (Fin (2 ^ height tag)) queries
        (Code.minDist (BlockCode.code domain m b : Set (Fin (2 ^ height tag) → Fin b → F)) - radius))
        (ColumnOpening.missBound (Fin (2 ^ height tag)) queries (radius + 1))) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss unifSpec (fun tag => Skeleton.perfect (height tag)))
        (StatefulCommitmentPrefix.program tag commit (fun root => SharedContinuation.program (selectQuery root) (fun query => game (respond root query) (next root query))))
        (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))) := by
  classical
  let continuation := fun root => SharedContinuation.program (selectQuery root)
    (fun query => game (respond root query) (next root query))
  apply StatefulCommitmentPrefix.event_bound (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (fun tag => Skeleton.perfect (height tag)) tag commit continuation
    (fun first last => AcceptedWrong enc dummy height tag (StatefulCommitmentPrefix.snapshot _ tag first)
      domain capacity radius (left last.1.1) (right last.1.1)
      (testResponse first.1 last.1.1) (structuredResponse first.1 last.1.1) (last.1.2, last.2))
    (fun first last => SharedMatrixSampling.ArithmeticBad domain capacity radius
      (word enc dummy height tag (StatefulCommitmentPrefix.snapshot _ tag first)) (left last.1.1) (right last.1.1)
        (testResponse first.1 last.1.1) (structuredResponse first.1 last.1.1) last.1.2.1) _
  · intro first
    let source := word (leftCount := leftCount) (b := b) enc dummy height tag
      (StatefulCommitmentPrefix.snapshot _ tag first)
    let : Fintype (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) := Fintype.ofFinite _
    let : SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) :=
      SampleableType.ofFintype _
    let : Fintype (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker :=
      Fintype.ofFinite _
    let : SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker :=
      SampleableType.ofFintype _
    apply SharedContinuation.later_event_le enc dummy (fun tag => Skeleton.perfect (height tag))
      (selectQuery first.1) (fun query => game (respond first.1 query) (next first.1 query))
      (CheckpointExecution.record _ first.2 tag first.1.1)
      (fun query outcome => SharedMatrixSampling.ArithmeticBad domain capacity radius source
        (left query) (right query) (testResponse first.1 query) (structuredResponse first.1 query) outcome.1.1)
    intro query initial
    exact SharedMatrixSampling.arithmetic_after_bound basis domain enough capacity radius source
      (left query) (right query) enc dummy (fun tag => Skeleton.perfect (height tag))
      (respond first.1 query) (testResponse first.1 query) (structuredResponse first.1 query)
      (next first.1 query) initial small
  · intro first last reached accepted
    obtain ⟨selected, selectedReached, opened, openedReached, equal⟩ :=
      (SharedContinuation.support_program enc dummy (fun tag => Skeleton.perfect (height tag))
        (selectQuery first.1) (fun query => game (respond first.1 query) (next first.1 query))
        (CheckpointExecution.record _ first.2 tag first.1.1) last).mp reached
    subst last
    have recorded := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun tag => Skeleton.perfect (height tag)) tag (StatefulCommitmentPrefix.snapshot _ tag first)
      (selectQuery first.1) (CheckpointExecution.record _ first.2 tag first.1.1)
      (StatefulCommitmentPrefix.snapshot_recorded _ tag first) selected selectedReached
    exact accepted_wrong_implies_failure enc dummy (StatefulCommitmentPrefix.snapshot _ tag first) domain capacity radius
      (left selected.1) (right selected.1) (respond first.1 selected.1) (next first.1 selected.1)
      (testResponse first.1 selected.1) (structuredResponse first.1 selected.1)
      selected.2 recorded opened openedReached accepted

end

end FormalProof4FHE.HasteBoots.AdaptiveMatrixOpening
