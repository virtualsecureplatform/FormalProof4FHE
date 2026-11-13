module

public import FormalProof4FHE.HasteBoots.InteractiveSampling
public import FormalProof4FHE.HasteBoots.RectangularBatchOpeningKernel

@[expose] public section

/-!
# Rectangular batch-opening arithmetic under the actual shared handler

Independent test, packing and code-symbol widths are retained throughout.
Private ideal test/draw sampling is interpreted by the existing cached hash
handler, with arbitrary shared-oracle prover activity between the two draws.
Its exact response-state law instantiates the stochastic fixed-word batch theorem.
Every original query is covered without a query-count or group-count union factor.
Any later shared-oracle continuation retains the same arithmetic bound.
Authentication loss is still a separate event to compose on that complete run;
production transcript freshness and physical-work coupling remain open.
-/

open OracleSpec OracleComp ProbabilityTheory BinaryTree Matrix

namespace FormalProof4FHE.HasteBoots.SharedRectangularBatchSampling

noncomputable section

variable {F Position Left Group Query Response Result Cfg Input Digest Payload : Type}
  [Field F] [Fintype F] [DecidableEq F]
  [Fintype Position] [DecidableEq Position] [Fintype Left]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] {m packingWidth codeWidth testWidth size queries : ℕ}

/-- The arithmetic failure event uses one fixed source, the earlier response
messages and every original ordered draw. No later column data enter it. -/
def ArithmeticBad (domain : Position ↪ F) (capacity : size ≤ m * codeWidth) (radius : ℕ)
    (word : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (groupOf : Query → Group)
    (left : Group → Left → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (right : Query → Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (testResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Fin testWidth → Fin size → F)
    (structuredResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Group → Fin packingWidth → Fin size → F)
    (sample : ((Fin testWidth → (Left × Fin packingWidth) → F) × Response) × (Fin queries → Position)) : Prop :=
  (∃ query, RectangularBatchOpeningKernel.finishMessage groupOf right (structuredResponse sample.1.1 sample.1.2) query ≠
    matrixEvaluation (left (groupOf query)) (right query) (RectangularMatrixOpeningKernel.extract domain capacity radius word)) ∧
  RectangularMatrixOpeningKernel.Checks (m := m) domain word sample.1.1 (testResponse sample.1.1 sample.1.2) sample.2 ∧
  ∀ test : RectangularBatchOpeningKernel.Test (Group := Group) (packingWidth := packingWidth),
    ColumnOpening.Agrees (StructuredOpening.combine (RectangularBatchOpeningKernel.weights left test) word)
      (BlockEncoder.encode domain (RowLayout.padded (m := m)
        (structuredResponse sample.1.1 sample.1.2 test.1 test.2))) sample.2

/-- The actual response interpreter may query the shared oracle, use private
coins, and record further roots; its entire resulting state is retained by the
kernel proof. No uniform or independent response law is assumed. -/
theorem arithmetic_bound [NeZero m] [NeZero codeWidth]
    (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * codeWidth) (radius : ℕ)
    (word : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (groupOf : Query → Group)
    (left : Group → Left → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (right : Query → Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (respond : (Fin testWidth → (Left × Fin packingWidth) → F) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (testResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Fin testWidth → Fin size → F)
    (structuredResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Group → Fin packingWidth → Fin size → F)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    [SampleableType (Fin testWidth → (Left × Fin packingWidth) → F)] [SampleableType ((Left × Fin packingWidth) → F)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F))) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (InteractiveSampling.program ($ᵗ (Fin testWidth → (Left × Fin packingWidth) → F)) respond
          ($ᵗ (Fin queries → Position)))).run state}[
            ArithmeticBad domain capacity radius word groupOf left right testResponse structuredResponse outcome.1] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) / Fintype.card F)^testWidth +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius))
        (ColumnOpening.missBound Position queries (radius + 1)) := by
  let respondM := fun matrix => (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (respond matrix)).run state
  have bound := RectangularBatchOpeningKernel.soundness_bound domain enough capacity radius testWidth queries word groupOf left right respondM
    (fun matrix response => testResponse matrix response.1)
    (fun matrix response => structuredResponse matrix response.1) large small
  have law : InteractiveSampling.retain <$>
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (InteractiveSampling.program ($ᵗ (Fin testWidth → (Left × Fin packingWidth) → F)) respond
          ($ᵗ (Fin queries → Position)))).run state =
        RectangularOpeningKernel.experiment (F := F) (Row := Left × Fin packingWidth) (Position := Position) testWidth queries respondM :=
    InteractiveSampling.retain_run_program enc dummy shape _ respond _ state
  rw [← law, prEvent_map] at bound
  exact bound

/-- All later actual queries remain in the execution while an earlier
arithmetic event keeps the same bound. This does not discard rejecting paths. -/
theorem arithmetic_after_bound [NeZero m] [NeZero codeWidth]
    (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * codeWidth) (radius : ℕ)
    (word : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (groupOf : Query → Group)
    (left : Group → Left → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (right : Query → Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (respond : (Fin testWidth → (Left × Fin packingWidth) → F) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (testResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Fin testWidth → Fin size → F)
    (structuredResponse : (Fin testWidth → (Left × Fin packingWidth) → F) → Response → Group → Fin packingWidth → Fin size → F)
    (next : (((Fin testWidth → (Left × Fin packingWidth) → F) × Response) × (Fin queries → Position)) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    [SampleableType (Fin testWidth → (Left × Fin packingWidth) → F)] [SampleableType ((Left × Fin packingWidth) → F)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F))) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (InteractiveSampling.complete ($ᵗ (Fin testWidth → (Left × Fin packingWidth) → F)) respond
          ($ᵗ (Fin queries → Position)) next)).run state}[
            ArithmeticBad domain capacity radius word groupOf left right testResponse structuredResponse outcome.1.1] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) / Fintype.card F)^testWidth +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) - radius))
        (ColumnOpening.missBound Position queries (radius + 1)) :=
  (InteractiveSampling.earlier_event_le enc dummy shape _ respond _ next state
    (ArithmeticBad domain capacity radius word groupOf left right testResponse structuredResponse)).trans
      (arithmetic_bound domain enough capacity radius word groupOf left right enc dummy shape respond
        testResponse structuredResponse state large small)

end

end FormalProof4FHE.HasteBoots.SharedRectangularBatchSampling
