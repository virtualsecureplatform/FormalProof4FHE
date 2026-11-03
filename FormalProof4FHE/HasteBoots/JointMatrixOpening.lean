module

public import FormalProof4FHE.HasteBoots.SharedSequence
public import FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

@[expose] public section

/-!
# Joint arithmetic and authentication for sequential factor openings

Each factor has its own previously recorded root and fixed source. The native
factor loop is sequential, while each column phase may contain interleaved
workers. Steps carry arbitrary private memory. Arithmetic losses are summed;
all column checks use the final shared cache and one availability exception.
This homogeneous-layout component still uses private verifier coins. Adaptive
multi-root initialization, full stage orchestration, Fiat--Shamir and Rust
refinement remain separate obligations.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.JointMatrixOpening

noncomputable section

variable {F Factor Cfg Input Digest Response Memory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {leftCount b m size queries height : ℕ}

abbrev Data (F Digest Response : Type) (leftCount b height queries : ℕ) :=
  SampleData F Response leftCount b height queries × Columns F Digest leftCount b height

/-- Private memory returned by the column phase is carried into the next
factor. Projecting it out does not delete any actual oracle calls. -/
def step [SampleableType (TestMatrix F leftCount b)]
    [SampleableType (Fin queries → Fin (2 ^ height))]
    (respond : Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Columns F Digest leftCount b height × Memory))
    (factor : Factor) (memory : Memory) :
    OracleComp (SharedSequence.Shared Cfg Input Digest)
      (Data F Digest Response leftCount b height queries × Memory) :=
  (fun outcome => ((outcome.1, outcome.2.1), outcome.2.2)) <$>
    InteractiveSampling.complete ($ᵗ (TestMatrix F leftCount b)) (respond factor memory)
      ($ᵗ (Fin queries → Fin (2 ^ height))) (next factor memory)

/-- The frozen word is indexed by factor/root, never by its opening query. -/
def frozen (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (tag : Factor → Cfg)
    (checkpoint : ∀ factor, Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) (tag factor))
    (factor : Factor) : Fin (2 ^ height) → (Fin leftCount × Fin b) → Fin b → F :=
  word enc dummy (fun _ => height) (tag factor) (checkpoint factor)

/-- Any accepted incorrect factor, interpreting completed workers in the
final cache. This includes repeated factors and aliased root contexts. -/
def AnyAcceptedWrong (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (tag : Factor → Cfg)
    (checkpoint : ∀ factor, Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) (tag factor))
    (domain : Fin (2 ^ height) ↪ F) (capacity : size ≤ m * b) (radius : ℕ)
    (left : Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (testResponse structuredResponse : Factor → TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (outcome : (List (Factor × Data F Digest Response leftCount b height queries) × Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) : Prop :=
  ∃ entry ∈ outcome.1.1,
    AcceptedWrong enc dummy (fun _ => height) (tag entry.1) (checkpoint entry.1) domain capacity radius
      (left entry.1) (right entry.1) (testResponse entry.1) (structuredResponse entry.1) (entry.2, outcome.2)

variable {K : Type} [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]

/-- The arithmetic loss of one native semantic matrix opening. -/
def error (domain : Fin (2 ^ height) ↪ F) (radius : ℕ) : ENNReal :=
  (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
    Set (Fin (2 ^ height) → K)) : ENNReal) / (Fintype.card F ^ b) +
  max (ColumnOpening.missBound (Fin (2 ^ height)) queries
    (Code.minDist (BlockCode.code domain m b : Set (Fin (2 ^ height) → Fin b → F)) - radius))
    (ColumnOpening.missBound (Fin (2 ^ height)) queries (radius + 1))

variable [SampleableType (TestMatrix F leftCount b)]
  [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType ((Fin leftCount × Fin b) → K)]

/-- Each arithmetic loss is uniform over the actual incoming private memory
and shared cache. Row-span samplers are internal proof devices. -/
theorem step_arithmetic_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2 ^ height) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : size ≤ m * b) (radius : ℕ)
    (source : Fin (2 ^ height) → (Fin leftCount × Fin b) → Fin b → F)
    (left : Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (respond : Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Columns F Digest leftCount b height × Memory))
    (testResponse structuredResponse : Factor → TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (factor : Factor) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy (fun _ : Cfg => Skeleton.perfect height)) (step respond next factor memory)).run state}[
        SharedMatrixSampling.ArithmeticBad domain capacity radius source (left factor) (right factor)
          (testResponse factor) (structuredResponse factor) outcome.1.1.1] ≤
      error (K := K) (m := m) (b := b) (queries := queries) domain radius := by
  classical
  let : Fintype (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) := Fintype.ofFinite _
  let : SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis source)) := SampleableType.ofFintype _
  let : Fintype (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker :=
    Fintype.ofFinite _
  let : SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis source)).toAddMonoidHom.ker :=
    SampleableType.ofFintype _
  rw [step, simulateQ_map, StateT.run_map, prEvent_map]
  exact SharedMatrixSampling.arithmetic_after_bound basis domain enough capacity radius source
    (left factor) (right factor) enc dummy (fun _ : Cfg => Skeleton.perfect height)
    (respond factor memory) (testResponse factor) (structuredResponse factor) (next factor memory) state small

/-- Joint arithmetic error is independent of source availability and incoming
hash safety. This is the interface averaged over a multi-root commitment prefix. -/
theorem arithmetic_union_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2 ^ height) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : size ≤ m * b) (radius : ℕ)
    (source : Factor → Fin (2 ^ height) → (Fin leftCount × Fin b) → Fin b → F)
    (left : Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (respond : Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Columns F Digest leftCount b height × Memory))
    (testResponse structuredResponse : Factor → TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (indices : List Factor) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy (fun _ : Cfg => Skeleton.perfect height))
      (SharedSequence.program (step respond next) indices memory)).run state}[
        SharedSequence.AnyBad (fun factor data => SharedMatrixSampling.ArithmeticBad domain capacity radius
          (source factor) (left factor) (right factor) (testResponse factor) (structuredResponse factor) data.1)
          outcome.1.1] ≤
      (indices.map (fun _ => error (K := K) (m := m) (b := b) (queries := queries) domain radius)).sum :=
  SharedSequence.arithmetic_union_bound enc dummy (fun _ : Cfg => Skeleton.perfect height)
    (step respond next) _ _ indices (fun factor _ incoming initial =>
      step_arithmetic_bound basis enc dummy domain enough capacity radius (source factor) left right
        respond next testResponse structuredResponse factor incoming initial small) memory state

variable [Fintype Digest]

/-- Joint factor-opening loss: one arithmetic term for each attempted factor,
plus ONE hash charge for the whole sequential program. No per-factor hash
union, independent prover state or atomic column-worker premise is used. -/
theorem joint_soundness_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (tag : Factor → Cfg)
    (checkpoint : ∀ factor, Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) (tag factor))
    (domain : Fin (2 ^ height) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : size ≤ m * b) (radius : ℕ)
    (left : Factor → Fin leftCount → Matrix (Fin b) (Fin b) F)
    (right : Factor → Fin size → Matrix (Fin b) (Fin b) F)
    (respond : Factor → Memory → TestMatrix F leftCount b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response leftCount b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Columns F Digest leftCount b height × Memory))
    (testResponse structuredResponse : Factor → TestMatrix F leftCount b → Response → Fin b → Fin size → F)
    (indices : List Factor) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (recorded : ∀ factor, ⟨tag factor, checkpoint factor⟩ ∈ state.checkpoints.checkpoints)
    (safe : CheckpointCollision.Safe enc dummy (fun _ : Cfg => Skeleton.perfect height) state)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy (fun _ : Cfg => Skeleton.perfect height))
      (SharedSequence.program (step respond next) indices memory)).run state}[
        AnyAcceptedWrong enc dummy tag checkpoint domain capacity radius left right
          testResponse structuredResponse outcome] ≤
      (indices.map (fun _ => error (K := K) (m := m) (b := b) (queries := queries) domain radius)).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (SharedSequence.program (step respond next) indices memory) state := by
  let bad := fun factor (data : Data F Digest Response leftCount b height queries) =>
    SharedMatrixSampling.ArithmeticBad domain capacity radius (frozen enc dummy tag checkpoint factor)
      (left factor) (right factor) (testResponse factor) (structuredResponse factor) data.1
  have arithmetic := SharedSequence.arithmetic_union_bound enc dummy (fun _ : Cfg => Skeleton.perfect height)
    (step respond next) bad (fun _ => error (K := K) (m := m) (b := b) (queries := queries) domain radius)
    indices (fun factor _ incoming initial => step_arithmetic_bound basis enc dummy domain enough capacity radius
      (frozen enc dummy tag checkpoint factor) left right respond next testResponse structuredResponse
      factor incoming initial small) memory state
  have authentication := CheckpointAvailability.disagreement_le_charge (QueryImpl.ofLift unifSpec ProbComp)
    enc dummy (fun _ : Cfg => Skeleton.perfect height) (SharedSequence.program (step respond next) indices memory)
    state safe
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome => SharedSequence.AnyBad bad outcome.1.1 ∨
    CheckpointAvailability.Disagreement enc dummy (fun _ : Cfg => Skeleton.perfect height) outcome.2) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic authentication)
  · intro outcome supported accepted
    obtain ⟨entry, member, wrong⟩ := accepted
    have present := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun _ : Cfg => Skeleton.perfect height) (tag entry.1) (checkpoint entry.1)
      (SharedSequence.program (step respond next) indices memory) state (recorded entry.1) outcome supported
    obtain failed | unavailable := final_checks_imply_failure enc dummy (fun _ : Cfg => height)
      (tag entry.1) (checkpoint entry.1) domain capacity radius (left entry.1) (right entry.1)
      (testResponse entry.1) (structuredResponse entry.1) (entry.2, outcome.2) present wrong
    · exact Or.inl ⟨entry, member, failed⟩
    · exact Or.inr unavailable

end

end FormalProof4FHE.HasteBoots.JointMatrixOpening
