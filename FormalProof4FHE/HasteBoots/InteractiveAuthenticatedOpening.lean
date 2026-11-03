module

public import FormalProof4FHE.HasteBoots.SharedMatrixSampling
public import FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks
public import FormalProof4FHE.HasteBoots.CheckpointHistory

@[expose] public section

/-!
# Interactive authenticated matrix opening on one shared execution

A recorded root precedes the private uniform test. Arbitrary shared-oracle
response work follows, then a private uniform column vector, then arbitrary
further work producing typed columns. Native replay authentication, coverage,
both Boolean coordinate families and an incorrect finished value imply either
the arithmetic event or the root-wide availability event. Their probabilities
are bounded on this same complete execution by the PCS error plus its expected
accumulated hash charge. No independent authentication experiment is assumed.
This is the conditional private-coin interactive component. The empty-cache
commitment-prefix adapter is supplied by `CommittedMatrixOpening`. Production
Fiat--Shamir, concrete parameters and native Rust refinement remain open.
-/

open OracleSpec OracleComp ProbabilityTheory BinaryTree Matrix MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

noncomputable section

variable {F Input Digest Cfg Response : Type} [Field F] [DecidableEq F]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {leftCount b m size queries : ℕ}

abbrev TestMatrix (F : Type) (leftCount b : ℕ) := Fin b → (Fin leftCount × Fin b) → F
abbrev SampleData (F Response : Type) (leftCount b height queries : ℕ) :=
  (TestMatrix F leftCount b × Response) × (Fin queries → Fin (2 ^ height))
abbrev Columns (F Digest : Type) (leftCount b height : ℕ) :=
  List (NativeColumnLayout.Column F Digest height (leftCount * b) b)

/-- The one immutable common word used by arithmetic and authentication. -/
def word (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag) :
    Fin (2 ^ height tag) → (Fin leftCount × Fin b) → Fin b → F :=
  NativeColumnLayout.expandedWord
    (AuthenticatedColumnChecks.frozenWord enc dummy height tag checkpoint)

/-- Typed native authentication/coordinate acceptance with an incorrect
finished value. Replay conditions follow from completed interleaved workers. -/
def AcceptedWrong (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (domain : Fin (2 ^ height tag) ↪ F) (capacity : size ≤ m * b) (radius : ℕ)
    (left : Fin leftCount → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (testResponse structuredResponse : TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (outcome : (SampleData F Response leftCount b (height tag) queries × Columns F Digest leftCount b (height tag)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag))) : Prop :=
  let earlier := outcome.1.1
  let columns := outcome.1.2
  MatrixResponse.finishMessage right (structuredResponse earlier.1.1 earlier.1.2) ≠
    matrixEvaluation left right (MatrixOpeningSecurity.extract domain capacity radius (word enc dummy height tag checkpoint)) ∧
  NativeColumnLayout.Covers columns earlier.2 ∧
  (∀ column ∈ columns, ParallelColumnAvailability.Replays enc height
    (AuthenticatedColumnChecks.request height tag checkpoint.root column) outcome.2.hash.cache) ∧
  NativeColumnLayout.allCoordinates columns
    (NativeColumnLayout.flattenWeights earlier.1.1)
    (NativeColumnLayout.flattenWeights (MatrixResponse.weights left))
    (NativeColumnLayout.flattenResponse
      (MatrixOpeningSecurity.encodeMessages (m := m) domain (testResponse earlier.1.1 earlier.1.2)))
    (NativeColumnLayout.flattenResponse
      (MatrixOpeningSecurity.encodeMessages (m := m) domain (structuredResponse earlier.1.1 earlier.1.2))) = true

omit [SampleableType Digest] in
/-- Native checks interpreted in the final shared cache imply the arithmetic
checks on the frozen word, outside the single root-wide disagreement event.
No particular local execution or intermediate safety certificate is needed. -/
theorem final_checks_imply_failure
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (domain : Fin (2 ^ height tag) ↪ F) (capacity : size ≤ m * b) (radius : ℕ)
    (left : Fin leftCount → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (testResponse structuredResponse : TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (outcome : (SampleData F Response leftCount b (height tag) queries × Columns F Digest leftCount b (height tag)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (present : ⟨tag, checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints)
    (accepted : AcceptedWrong enc dummy height tag checkpoint domain capacity radius left right
      testResponse structuredResponse outcome) :
    SharedMatrixSampling.ArithmeticBad domain capacity radius (word enc dummy height tag checkpoint) left right
      testResponse structuredResponse outcome.1.1 ∨
    CheckpointAvailability.Disagreement enc dummy (fun tag => Skeleton.perfect (height tag)) outcome.2 := by
  classical
  by_cases availability : CheckpointAvailability.Disagreement enc dummy
      (fun tag => Skeleton.perfect (height tag)) outcome.2
  · exact Or.inr availability
  left
  obtain ⟨different, covered, replays, checked⟩ := accepted
  have noFailure : ¬ParallelColumnAvailability.Failure enc dummy height
      (AuthenticatedColumnChecks.requests height tag checkpoint.root outcome.1.2) outcome.2 :=
    fun failure => availability (ParallelColumnAvailability.failure_implies_disagreement enc dummy height _ outcome.2 failure)
  have both := AuthenticatedColumnChecks.matrix_pair_checks_of_authentication enc dummy height tag checkpoint
    outcome.2 present outcome.1.2 outcome.1.1.2 covered replays noFailure domain outcome.1.1.1.1
      (MatrixResponse.weights left) (testResponse outcome.1.1.1.1 outcome.1.1.1.2)
      (structuredResponse outcome.1.1.1.1 outcome.1.1.1.2) checked
  exact ⟨different, both.1, both.2⟩

section Game

variable {height : Cfg → ℕ} {tag : Cfg}
  [SampleableType (TestMatrix F leftCount b)] [SampleableType (Fin queries → Fin (2 ^ height tag))]

def game
    (respond : TestMatrix F leftCount b → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (next : SampleData F Response leftCount b (height tag) queries →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Columns F Digest leftCount b (height tag))) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest)
      (SampleData F Response leftCount b (height tag) queries × Columns F Digest leftCount b (height tag)) :=
  InteractiveSampling.complete ($ᵗ (TestMatrix F leftCount b)) respond
    ($ᵗ (Fin queries → Fin (2 ^ height tag))) next

/-- The native checks need only one availability exception to obtain both
arithmetic checks, and the original checkpoint remains recorded throughout. -/
theorem accepted_wrong_implies_failure
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (domain : Fin (2 ^ height tag) ↪ F) (capacity : size ≤ m * b) (radius : ℕ)
    (left : Fin leftCount → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (respond : TestMatrix F leftCount b → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (next : SampleData F Response leftCount b (height tag) queries →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Columns F Digest leftCount b (height tag)))
    (testResponse structuredResponse : TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (outcome : (SampleData F Response leftCount b (height tag) queries × Columns F Digest leftCount b (height tag)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun tag => Skeleton.perfect (height tag)))
        (game respond next)).run state))
    (accepted : AcceptedWrong enc dummy height tag checkpoint domain capacity radius left right
      testResponse structuredResponse outcome) :
    SharedMatrixSampling.ArithmeticBad domain capacity radius (word enc dummy height tag checkpoint) left right
      testResponse structuredResponse outcome.1.1 ∨
    CheckpointAvailability.Disagreement enc dummy (fun tag => Skeleton.perfect (height tag)) outcome.2 := by
  have present := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (fun tag => Skeleton.perfect (height tag)) tag checkpoint (game respond next) state recorded outcome supported
  exact final_checks_imply_failure enc dummy height tag checkpoint domain capacity radius left right
    testResponse structuredResponse outcome present accepted

variable {K : Type} [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [Fintype Digest]

/-- Interactive authenticated soundness: arithmetic error plus the expected
hash charge of exactly this complete shared-oracle program. Responses and later
work are unrestricted adaptive programs; no adversary query budget is assumed. -/
theorem soundness_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (domain : Fin (2 ^ height tag) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height tag)))
    (capacity : size ≤ m * b) (radius : ℕ)
    (left : Fin leftCount → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (respond : TestMatrix F leftCount b → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (next : SampleData F Response leftCount b (height tag) queries →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Columns F Digest leftCount b (height tag)))
    (testResponse structuredResponse : TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (safe : CheckpointCollision.Safe enc dummy (fun tag => Skeleton.perfect (height tag)) state)
    [SampleableType ((Fin leftCount × Fin b) → K)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis
      (word (leftCount := leftCount) (b := b) enc dummy height tag checkpoint)))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis
      (word (leftCount := leftCount) (b := b) enc dummy height tag checkpoint))).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height tag) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun tag => Skeleton.perfect (height tag)))
        (game respond next)).run state}[
      AcceptedWrong enc dummy height tag checkpoint domain capacity radius left right
        testResponse structuredResponse outcome] ≤
      ((Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height tag) → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound (Fin (2 ^ height tag)) queries
        (Code.minDist (BlockCode.code domain m b : Set (Fin (2 ^ height tag) → Fin b → F)) - radius))
        (ColumnOpening.missBound (Fin (2 ^ height tag)) queries (radius + 1))) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss unifSpec (fun tag => Skeleton.perfect (height tag))) (game respond next) state := by
  have arithmetic := SharedMatrixSampling.arithmetic_after_bound basis domain enough capacity radius
    (word enc dummy height tag checkpoint) left right enc dummy (fun tag => Skeleton.perfect (height tag))
      respond testResponse structuredResponse next state small
  have authentication := CheckpointAvailability.disagreement_le_charge (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (fun tag => Skeleton.perfect (height tag)) (game respond next) state safe
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    SharedMatrixSampling.ArithmeticBad domain capacity radius (word enc dummy height tag checkpoint) left right
      testResponse structuredResponse outcome.1.1 ∨
    CheckpointAvailability.Disagreement enc dummy (fun tag => Skeleton.perfect (height tag)) outcome.2) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic authentication)
  · intro outcome supported accepted
    exact accepted_wrong_implies_failure enc dummy checkpoint domain capacity radius left right respond next
      testResponse structuredResponse state recorded outcome supported accepted

end Game

end

end FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
