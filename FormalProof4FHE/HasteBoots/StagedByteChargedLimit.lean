module

public import FormalProof4FHE.HasteBoots.StagedByteFactor
public import FormalProof4FHE.HasteBoots.ByteLookupChargedLimit

@[expose] public section

/-!
# Expected account for the actual staged byte lookup program

The measure returns the original source, typed raw-byte/helper emission,
optional native result and actual final state/account. Source root recording
precedes sampling; helper root recording follows the real builder. The
expected account equals the supremum of the original staged-program charges,
using proved structural suspension behavior rather than a work certificate.
-/

open OracleSpec OracleComp BinaryTree MeasureTheory

namespace FormalProof4FHE.HasteBoots.StagedByteChargedLimit

noncomputable section

variable {F K Cfg Input Digest Payload First HelperMemory Later : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {p degree width size repetitions : ℕ} [Module (ZMod p) K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] [Fintype Digest]

local instance (X : Type) : MeasurableSpace X := ⊤
local instance (X Y : Type) : MeasurableSpace (X × Y) := ⊤

abbrev Second (p degree : ℕ) (K Digest HelperMemory : Type) [Zero K] (repetitions : ℕ) :=
  ByteLookupPairMiddle.Emission p degree K Digest HelperMemory repetitions

def pack {shape : Cfg → Skeleton}
    (outcome : (First × ByteLookupPairTyped.Sample p degree K repetitions ×
      Option (Option (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory) × Option Later)) ×
        CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal) :=
  (StagedByteFactor.project outcome.1, outcome.2)

variable (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
  (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
  (sourceRequests : First → List (Cfg × Digest))
  (requests : First → Second p degree K Digest HelperMemory repetitions → List (Cfg × Digest))
  (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
  (build : First → ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
  (next : First → Second p degree K Digest HelperMemory repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest) (Option Later))
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)

local notation "draws" => ByteLookupUnbounded.steps basis table repetitions
local notation "done" => ByteLookupUnbounded.complete (p := p) (degree := degree) (K := K) (repetitions := repetitions)
local notation "order" => ByteLookupUnbounded.grows basis table repetitions
local notation "hazard" => CheckpointCollision.loss unifSpec shape
local notation "original" => StagedByteFactor.before sourceRequests sourceCommit
local notation "continuation" => StagedByteFactor.tail requests build next
local notation "core" => ChargedPrefixCompletion.operational enc dummy shape hazard
  (ByteLookupChargedLimit.private_zero shape) original continuation initial draws done order

/-- Original staged return shape with raw partial traces and the full account. -/
def measure : Measure ((First × Second p degree K Digest HelperMemory repetitions × Option Later) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal) :=
  @Measure.map _ _ ⊤ ⊤ pack core

local notation "law" => measure basis table enc dummy shape sourceRequests requests sourceCommit build next initial

variable [Fintype K] [SampleableType K] [NeZero p]

/-- The full completed original-shape account law is normalized. -/
theorem probability (valid : 1 < p) (enough : size + 1 < Fintype.card K) : IsProbabilityMeasure law := by
  unfold measure
  apply (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr
  apply ChargedPrefixCompletion.operational_probability
  exact ByteLookupUnbounded.completion_sup valid basis table enough repetitions

/-- Structural suspension rules identify this mean with the actual original
staged program's charge supremum, including earlier source work exactly once. -/
theorem expected (valid : 1 < p) (enough : size + 1 < Fintype.card K)
    (requests_none : ∀ first observed, observed.values = none → requests first (observed, none) = [])
    (next_none : ∀ first observed, observed.values = none → next first (observed, none) = pure none) :
    (∫⁻ outcome, outcome.2.2 ∂law) =
      ⨆ n, ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) hazard
        (StagedCommitmentPrefix.program sourceRequests requests sourceCommit
          (fun first => ByteLookupPairMiddle.program basis table n n n repetitions (build first)) next) initial := by
  rw [measure, lintegral_map Measurable.of_discrete Measurable.of_discrete]
  change (∫⁻ outcome, outcome.2.2 ∂core) = _
  rw [ChargedPrefixCompletion.expected enc dummy shape hazard (ByteLookupChargedLimit.private_zero shape)
    original continuation initial draws done order (ByteLookupUnbounded.completion_sup valid basis table enough repetitions)]
  apply iSup_congr
  intro n
  exact (StagedByteFactor.charge basis table n n n enc dummy shape hazard sourceRequests requests sourceCommit build next
    requests_none next_none initial).symm

end

end FormalProof4FHE.HasteBoots.StagedByteChargedLimit
