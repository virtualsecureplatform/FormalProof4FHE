module

public import FormalProof4FHE.HasteBoots.SharedChargedCompletion
public import FormalProof4FHE.HasteBoots.ByteLookupUnbounded

@[expose] public section

/-!
# Unbounded byte lookup with its actual continuation availability account

The complete raw byte sampler runs at the fixed incoming shared state before
an arbitrary trace-sensitive helper/native continuation. The charge is the
actual checkpoint/collision availability loss. The normalized limit retains
that account and its exact expected whole-prefix continuation charge. Work
before this incoming state and computational byte costs remain separate.
-/

open OracleSpec OracleComp BinaryTree MeasureTheory

namespace FormalProof4FHE.HasteBoots.ByteLookupChargedLimit

noncomputable section

variable {F K Cfg Input Digest Payload Later : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {p degree width size count : ℕ} [Module (ZMod p) K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] [Fintype Digest]

local instance (X : Type) : MeasurableSpace X := ⊤
local instance (X Y : Type) : MeasurableSpace (X × Y) := ⊤

omit [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] in
/-- Actual availability loss is zero on every ideal private primitive. -/
theorem private_zero (shape : Cfg → Skeleton) (query : unifSpec.Domain)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    CheckpointCollision.loss unifSpec shape (.inl query) state = 0 := by
  simp [CheckpointCollision.loss, CheckpointExecution.loss, CheckpointCollision.collisionLoss]

variable (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F) (repetitions : ℕ)
  (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
  (next : ByteLookupPairTyped.Sample p degree K repetitions →
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)

local notation "draws" => ByteLookupUnbounded.steps basis table repetitions
local notation "done" => ByteLookupUnbounded.complete (p := p) (degree := degree) (K := K) (repetitions := repetitions)
local notation "order" => ByteLookupUnbounded.grows basis table repetitions
local notation "hazard" => CheckpointCollision.loss unifSpec shape

/-- Genuine complete-observation measure with the actual final state/account. -/
def measure : Measure ((ByteLookupPairTyped.Sample p degree K repetitions × Option Later) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal) :=
  SharedChargedCompletion.measure enc dummy shape hazard (private_zero shape) next initial draws done order

local notation "law" => measure basis table repetitions enc dummy shape next initial

/-- Mean availability account equals the supremum of the actual finite
sampling-plus-continuation charges, with all native return flags retained. -/
theorem expected : (∫⁻ outcome, outcome.2.2 ∂law) =
    ⨆ n, ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) hazard
      (SharedCompletedContinuation.program (draws n) done next) initial :=
  SharedChargedCompletion.expected enc dummy shape hazard (private_zero shape) next initial draws done order

/-- Recording the account preserves the full uncharged complete execution law. -/
theorem erase_event (event : (ByteLookupPairTyped.Sample p degree K repetitions × Option Later) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    law {outcome | event (outcome.1, outcome.2.1)} =
      SharedCompletedContinuation.measure draws done order enc dummy shape next initial {outcome | event outcome} :=
  SharedChargedCompletion.erase_event enc dummy shape hazard (private_zero shape) next initial draws done order event

variable [Fintype K] [SampleableType K] [NeZero p]

/-- Almost-sure complete sampling gives a normalized execution/account law. -/
theorem probability (valid : 1 < p) (enough : size + 1 < Fintype.card K) : IsProbabilityMeasure law :=
  SharedChargedCompletion.probability enc dummy shape hazard (private_zero shape) next initial draws done order
    (ByteLookupUnbounded.completion_sup valid basis table enough repetitions)

/-- The repeated lookup bound survives real adaptive continuation work and
availability-account recording; it concerns the actual retained typed vector. -/
theorem lookup_bound {char : ℕ} [CharP K char] (valid : 1 < p)
    (sources : Fin count → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char) :
    law {outcome | outcome.1.1.values.elim False (LookupPairVector.AllPass sources table multiplicities)} ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  have erased := erase_event basis table repetitions enc dummy shape next initial
    (fun outcome => outcome.1.1.values.elim False (LookupPairVector.AllPass sources table multiplicities))
  have earlier : SharedCompletedContinuation.measure draws done order enc dummy shape next initial
      {outcome | outcome.1.1.values.elim False (LookupPairVector.AllPass sources table multiplicities)} =
      ByteLookupUnbounded.measure basis table repetitions
        {observed | observed.values.elim False (LookupPairVector.AllPass sources table multiplicities)} := by
    simpa only [ByteLookupUnbounded.measure] using SharedCompletedContinuation.earlier_marginal draws done order enc dummy shape next initial
      (fun observed => observed.values.elim False (LookupPairVector.AllPass sources table multiplicities))
  exact erased.trans_le (earlier.trans_le (ByteLookupUnbounded.lookup_bound valid basis sources table multiplicities enough bad small repetitions))

end

end FormalProof4FHE.HasteBoots.ByteLookupChargedLimit
