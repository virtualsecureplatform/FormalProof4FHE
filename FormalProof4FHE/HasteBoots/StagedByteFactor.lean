module

public import FormalProof4FHE.HasteBoots.ByteLookupPairMiddle
public import FormalProof4FHE.HasteBoots.ChargedPrefixCompletion

@[expose] public section

/-!
# Exact source/helper/native query-program factorization

Source roots are recorded before private byte sampling. On completion, the
actual builder runs, its chosen helper roots are recorded, and the native
continuation sees the trusted stored sample. Suspension retains the partial
sample, records no helper root and runs no native fallback. Projection only
repackages returned observations and introduces no queries.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical

namespace FormalProof4FHE.HasteBoots.StagedByteFactor

noncomputable section

variable {F K Cfg Input Digest First HelperMemory Later : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {p degree width size repetitions : ℕ} [Module (ZMod p) K]

abbrev Second (p degree : ℕ) (K Digest HelperMemory : Type) [Zero K] (repetitions : ℕ) :=
  ByteLookupPairMiddle.Emission p degree K Digest HelperMemory repetitions

/-- The real original commitment and its root annotations precede all bytes. -/
def before (sourceRequests : First → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First) := do
  let first ← sourceCommit
  let _ ← RecordRoots.program (sourceRequests first)
  pure first

/-- The complete raw sample determines helper work and all later native work. -/
def tail
    (requests : First → Second p degree K Digest HelperMemory repetitions → List (Cfg × Digest))
    (build : First → ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (next : First → Second p degree K Digest HelperMemory repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest) (Option Later))
    (first : First) (observed : ByteLookupPairTyped.Sample p degree K repetitions) := do
  let helper ← ByteLookupPairMiddle.after (build first) observed
  let _ ← RecordRoots.program (requests first (observed, helper))
  let result ← next first (observed, helper)
  pure (helper, result)

/-- No default typed vector, helper root or native result is inserted. -/
def project (outcome : First × ByteLookupPairTyped.Sample p degree K repetitions ×
    Option (Option (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory) × Option Later)) :
    First × Second p degree K Digest HelperMemory repetitions × Option Later :=
  match outcome.2.2 with
  | none => (outcome.1, (outcome.2.1, none), none)
  | some last => (outcome.1, (outcome.2.1, last.1), last.2)

/-- Structural suspension behavior suffices for an equality of actual query
programs; no security or work certificate is supplied to this theorem. -/
theorem factor (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer : ℕ)
    (sourceRequests : First → List (Cfg × Digest))
    (requests : First → Second p degree K Digest HelperMemory repetitions → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (build : First → ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (next : First → Second p degree K Digest HelperMemory repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest) (Option Later))
    (requests_none : ∀ first observed, observed.values = none → requests first (observed, none) = [])
    (next_none : ∀ first observed, observed.values = none → next first (observed, none) = pure none) :
    project <$> ChargedPrefixCompletion.program
      (ByteLookupPairTyped.sample basis table hashDepth inner outer repetitions)
      (fun observed => observed.values ≠ none) (before sourceRequests sourceCommit) (tail requests build next) =
      StagedCommitmentPrefix.program sourceRequests requests sourceCommit
        (fun first => ByteLookupPairMiddle.program basis table hashDepth inner outer repetitions (build first)) next := by
  simp only [ChargedPrefixCompletion.program, before, SharedCompletedContinuation.program,
    StagedCommitmentPrefix.program, ByteLookupPairMiddle.program, SharedContinuation.program,
    map_bind, map_pure, bind_assoc, pure_bind]
  congr 1
  funext first
  congr 1
  funext recorded
  congr 1
  funext observed
  split_ifs with done
  · simp only [tail, map_bind, map_pure, bind_assoc, pure_bind, project]
  · have suspended : observed.values = none := by simpa only [not_not] using done
    simp [ByteLookupPairMiddle.after_none _ _ suspended, requests_none _ _ suspended,
      next_none _ _ suspended, RecordRoots.program, project]

variable {Payload : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Repackaging returned data adds no charge to the original staged program. -/
theorem charge (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer : ℕ)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (loss : (SharedSequence.Shared Cfg Input Digest).Domain →
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape → ENNReal)
    (sourceRequests : First → List (Cfg × Digest))
    (requests : First → Second p degree K Digest HelperMemory repetitions → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (build : First → ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (next : First → Second p degree K Digest HelperMemory repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest) (Option Later))
    (requests_none : ∀ first observed, observed.values = none → requests first (observed, none) = [])
    (next_none : ∀ first observed, observed.values = none → next first (observed, none) = pure none)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
      (StagedCommitmentPrefix.program sourceRequests requests sourceCommit
        (fun first => ByteLookupPairMiddle.program basis table hashDepth inner outer repetitions (build first)) next) initial =
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
        (ChargedPrefixCompletion.program (ByteLookupPairTyped.sample basis table hashDepth inner outer repetitions)
          (fun observed => observed.values ≠ none) (before sourceRequests sourceCommit) (tail requests build next)) initial := by
  rw [← factor basis table hashDepth inner outer sourceRequests requests sourceCommit build next requests_none next_none,
    ExpectedChargeComposition.map]

end

end FormalProof4FHE.HasteBoots.StagedByteFactor
