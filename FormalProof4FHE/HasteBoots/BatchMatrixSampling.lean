module

public import FormalProof4FHE.HasteBoots.SharedMatrixSampling
public import FormalProof4FHE.HasteBoots.JointMatrixOpening

@[expose] public section

/-!
# A batch of claims with one actual random test and column draw

Every value and query is fixed before the common random test. One wrong claim
can therefore be selected before that test; all accepted response/finish checks
imply its single-query arithmetic event. The same PCS arithmetic error covers
the entire batch, without a query-count union loss or independent per-query
sampling. Prover response work, shared columns and later native work remain one
actual cached execution. Native grouping, workers and availability compose
separately; this theorem does not assume batch commitment security.
-/

open OracleSpec OracleComp BinaryTree Matrix

namespace FormalProof4FHE.HasteBoots.BatchMatrixSampling

noncomputable section

variable {F K Position Left Claim Response Result Cfg Input Digest Payload : Type}
  [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fintype Position] [DecidableEq Position] [Fintype Left]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] {m b size queries : ℕ}

def error (domain : Position ↪ F) (radius : ℕ) : ENNReal :=
  (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
    Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
  max (ColumnOpening.missBound Position queries
    (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius))
    (ColumnOpening.missBound Position queries (radius + 1))

/-- All grouped responses are interpreted on one test/draw packet. Supplied
values are fixed before the random test, as in native `bind_many`. -/
def ArithmeticBad (domain : Position ↪ F) (capacity : size ≤ m * b) (radius : ℕ)
    (word : Position → (Left × Fin b) → Fin b → F)
    (left : Claim → Left → Matrix (Fin b) (Fin b) F)
    (right : Claim → Fin size → Matrix (Fin b) (Fin b) F) (values : Claim → Fin b → F)
    (testResponse : (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    (structuredResponse : Claim → (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    (sample : ((Fin b → (Left × Fin b) → F) × Response) × (Fin queries → Position)) : Prop :=
  (∃ claim, values claim ≠ matrixEvaluation (left claim) (right claim)
    (MatrixOpeningSecurity.extract domain capacity radius word)) ∧
  MatrixOpeningSecurity.Checks (m := m) domain word sample.1.1 (testResponse sample.1.1 sample.1.2) sample.2 ∧
  (∀ claim, MatrixOpeningSecurity.Checks (m := m) domain word (MatrixResponse.weights (left claim))
    (structuredResponse claim sample.1.1 sample.1.2) sample.2) ∧
  ∀ claim, MatrixResponse.finishMessage (right claim) (structuredResponse claim sample.1.1 sample.1.2) = values claim

/-- One selected false pre-test value suffices. The response distribution is
arbitrary shared work and may depend on every query and the whole random test. -/
theorem arithmetic_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b) (radius : ℕ)
    (word : Position → (Left × Fin b) → Fin b → F)
    (left : Claim → Left → Matrix (Fin b) (Fin b) F)
    (right : Claim → Fin size → Matrix (Fin b) (Fin b) F) (values : Claim → Fin b → F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (respond : (Fin b → (Left × Fin b) → F) → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (testResponse : (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    (structuredResponse : Claim → (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    [SampleableType (Fin b → (Left × Fin b) → F)] [SampleableType ((Left × Fin b) → K)]
    [SampleableType (Fin queries → Position)]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m : Set (Position → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (InteractiveSampling.program ($ᵗ (Fin b → (Left × Fin b) → F)) respond
        ($ᵗ (Fin queries → Position)))).run state}[
          ArithmeticBad domain capacity radius word left right values testResponse structuredResponse outcome.1] ≤
      error (K := K) (m := m) (b := b) (queries := queries) domain radius := by
  classical
  by_cases wrong : ∃ claim, values claim ≠ matrixEvaluation (left claim) (right claim)
      (MatrixOpeningSecurity.extract domain capacity radius word)
  · obtain ⟨claim, different⟩ := wrong
    let : Fintype (Matrix.rowSpan (BaseMatrixProximity.stack basis word)) := Fintype.ofFinite _
    let : SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word)) := SampleableType.ofFintype _
    let : Fintype (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker := Fintype.ofFinite _
    let : SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker :=
      SampleableType.ofFintype _
    have bound := SharedMatrixSampling.arithmetic_bound (queries := queries) basis domain enough capacity radius word (left claim) (right claim)
      enc dummy shape respond testResponse (structuredResponse claim) state small
    apply le_trans (prEvent_mono _ _ _ ?_) bound
    intro outcome accepted
    refine ⟨?_, accepted.2.1, accepted.2.2.1 claim⟩
    rw [accepted.2.2.2 claim]
    exact different
  · simp [ArithmeticBad, wrong, prEvent_norm]

/-- Later worker calls and cancellation retain this same one-batch bound on
the actual earlier packet. No column or query is sampled a second time. -/
theorem arithmetic_after_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b) (radius : ℕ)
    (word : Position → (Left × Fin b) → Fin b → F)
    (left : Claim → Left → Matrix (Fin b) (Fin b) F)
    (right : Claim → Fin size → Matrix (Fin b) (Fin b) F) (values : Claim → Fin b → F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (respond : (Fin b → (Left × Fin b) → F) → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (testResponse : (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    (structuredResponse : Claim → (Fin b → (Left × Fin b) → F) → Response → Fin b → Fin size → F)
    (next : (((Fin b → (Left × Fin b) → F) × Response) × (Fin queries → Position)) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    [SampleableType (Fin b → (Left × Fin b) → F)] [SampleableType ((Left × Fin b) → K)]
    [SampleableType (Fin queries → Position)]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m : Set (Position → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (InteractiveSampling.complete ($ᵗ (Fin b → (Left × Fin b) → F)) respond
        ($ᵗ (Fin queries → Position)) next)).run state}[
          ArithmeticBad domain capacity radius word left right values testResponse structuredResponse outcome.1.1] ≤
      error (K := K) (m := m) (b := b) (queries := queries) domain radius :=
  (SharedContinuation.earlier_event_le enc dummy shape _ next state
    (ArithmeticBad domain capacity radius word left right values testResponse structuredResponse)).trans
      (arithmetic_bound basis domain enough capacity radius word left right values enc dummy shape respond
        testResponse structuredResponse state small)

end

end FormalProof4FHE.HasteBoots.BatchMatrixSampling
