module

public import FormalProof4FHE.HasteBoots.InteractiveSampling
public import FormalProof4FHE.HasteBoots.MatrixOpeningKernel

@[expose] public section

/-!
# Matrix-opening arithmetic under the actual shared handler

Private ideal test/draw sampling is interpreted by the existing cached hash
handler, with arbitrary shared-oracle prover activity between the two draws.
Its exact response-state law instantiates the stochastic fixed-word theorem.
Any later shared-oracle continuation retains the same arithmetic bound.
Authentication loss is still a separate event to compose on that complete run;
production transcript freshness and physical-work coupling remain open.
-/

open OracleSpec OracleComp ProbabilityTheory BinaryTree Matrix

namespace FormalProof4FHE.HasteBoots.SharedMatrixSampling

noncomputable section

variable {F K Position Left Response Result Cfg Input Digest Payload : Type}
  [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fintype Position] [DecidableEq Position] [Fintype Left]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] {m b size queries : ℕ}

/-- The arithmetic failure event uses one fixed source, the earlier response
messages and every original ordered draw. No later column data enter it. -/
def ArithmeticBad (domain : Position ↪ F) (capacity : size ≤ m * b) (radius : ℕ)
    (word : Position → (Left × Fin b) → Fin b → F)
    (left : Left → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (testResponse structuredResponse : (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    (sample : ((Fin b → (Left × Fin b) → F) × Response) × (Fin queries → Position)) : Prop :=
  MatrixResponse.finishMessage right (structuredResponse sample.1.1 sample.1.2) ≠
    matrixEvaluation left right (MatrixOpeningSecurity.extract domain capacity radius word) ∧
  MatrixOpeningSecurity.Checks (m := m) domain word sample.1.1 (testResponse sample.1.1 sample.1.2) sample.2 ∧
  MatrixOpeningSecurity.Checks (m := m) domain word (MatrixResponse.weights left)
    (structuredResponse sample.1.1 sample.1.2) sample.2

/-- The actual response interpreter may query the shared oracle, use private
coins, and record further roots; its entire resulting state is retained by the
kernel proof. No uniform or independent response law is assumed. -/
theorem arithmetic_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b) (radius : ℕ)
    (word : Position → (Left × Fin b) → Fin b → F)
    (left : Left → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (respond : (Fin b → (Left × Fin b) → F) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (testResponse structuredResponse : (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    [SampleableType (Fin b → (Left × Fin b) → F)] [SampleableType ((Left × Fin b) → K)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (InteractiveSampling.program ($ᵗ (Fin b → (Left × Fin b) → F)) respond
          ($ᵗ (Fin queries → Position)))).run state}[
            ArithmeticBad domain capacity radius word left right testResponse structuredResponse outcome.1] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius))
        (ColumnOpening.missBound Position queries (radius + 1)) := by
  let respondM := fun matrix => (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (respond matrix)).run state
  have bound := MatrixOpeningKernel.soundness_bound basis domain enough capacity radius queries word left right respondM
    (fun matrix response => testResponse matrix response.1)
    (fun matrix response => structuredResponse matrix response.1) small
  have law : InteractiveSampling.retain <$>
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (InteractiveSampling.program ($ᵗ (Fin b → (Left × Fin b) → F)) respond
          ($ᵗ (Fin queries → Position)))).run state =
        CommonSourceOpeningKernel.experiment (F := F) (Row := Left × Fin b) (Position := Position) b queries respondM :=
    InteractiveSampling.retain_run_program enc dummy shape _ respond _ state
  rw [← law, prEvent_map] at bound
  exact bound

/-- All later actual queries remain in the execution while an earlier
arithmetic event keeps the same bound. This does not discard rejecting paths. -/
theorem arithmetic_after_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b) (radius : ℕ)
    (word : Position → (Left × Fin b) → Fin b → F)
    (left : Left → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (respond : (Fin b → (Left × Fin b) → F) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (testResponse structuredResponse : (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    (next : (((Fin b → (Left × Fin b) → F) × Response) × (Fin queries → Position)) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    [SampleableType (Fin b → (Left × Fin b) → F)] [SampleableType ((Left × Fin b) → K)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (InteractiveSampling.complete ($ᵗ (Fin b → (Left × Fin b) → F)) respond
          ($ᵗ (Fin queries → Position)) next)).run state}[
            ArithmeticBad domain capacity radius word left right testResponse structuredResponse outcome.1.1] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius))
        (ColumnOpening.missBound Position queries (radius + 1)) :=
  (InteractiveSampling.earlier_event_le enc dummy shape _ respond _ next state
    (ArithmeticBad domain capacity radius word left right testResponse structuredResponse)).trans
      (arithmetic_bound basis domain enough capacity radius word left right enc dummy shape respond
        testResponse structuredResponse state small)

end

end FormalProof4FHE.HasteBoots.SharedMatrixSampling
