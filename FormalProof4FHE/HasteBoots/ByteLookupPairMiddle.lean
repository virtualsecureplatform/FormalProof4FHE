module

public import FormalProof4FHE.HasteBoots.ByteLookupPairTyped
public import FormalProof4FHE.HasteBoots.LookupPairVectorMiddle

@[expose] public section

/-!
# Byte-backed challenge vectors retained across helper construction

The helper builder receives the actual typed vector and complete raw traces.
It supplies only roots and opaque helper memory. The trusted completed view
attaches the stored vector; a suspended sample starts no helper work and has
no completed helper emission. All shared work remains in the real execution.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical

namespace FormalProof4FHE.HasteBoots.ByteLookupPairMiddle

noncomputable section

abbrev Emission (p degree : ℕ) (K Digest HelperMemory : Type) [Zero K] (repetitions : ℕ) :=
  ByteLookupPairTyped.Sample p degree K repetitions ×
    Option (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory)

/-- The trusted read-only view attaches the stored vector after helper work.
The builder never supplies the vector in this emitted verifier input. -/
def completed {p degree repetitions : ℕ} {K Digest HelperMemory : Type} [Zero K]
    (emission : Emission p degree K Digest HelperMemory repetitions) :
    Option (LookupPairVectorMiddle.Emission K Digest HelperMemory repetitions) :=
  match emission.1.values, emission.2 with
  | some values, some helper => some (helper.1, (values, helper.2))
  | _, _ => none

theorem completed_none {p degree repetitions : ℕ} {K Digest HelperMemory : Type} [Zero K]
    (emission : Emission p degree K Digest HelperMemory repetitions) (suspended : emission.1.values = none) :
    completed emission = none := by simp [completed, suspended]

/-- A completed helper emission contains exactly the stored typed vector. -/
theorem completed_values {p degree repetitions : ℕ} {K Digest HelperMemory : Type} [Zero K]
    (emission : Emission p degree K Digest HelperMemory repetitions)
    (helper : LookupPairVectorMiddle.Emission K Digest HelperMemory repetitions) (returned : completed emission = some helper) :
    emission.1.values = some helper.2.1 := by
  cases values : emission.1.values <;> cases roots : emission.2 <;> simp_all [completed]
  cases returned
  rfl

/-- The completed verifier input forgets to the original raw-byte values. -/
theorem completed_raw {p degree repetitions : ℕ} {K Digest HelperMemory : Type} [Zero K]
    (emission : Emission p degree K Digest HelperMemory repetitions)
    (helper : LookupPairVectorMiddle.Emission K Digest HelperMemory repetitions) (returned : completed emission = some helper) :
    emission.1.raw.values = some (ByteLookupPairTyped.forget helper.2.1) := by
  rw [← emission.1.consistent, completed_values emission helper returned]
  rfl

variable {F K Cfg Input Digest Payload HelperMemory Later : Type}
  [Field F] [Field K] [Algebra F K]
  {p degree width count size repetitions : ℕ} [Module (ZMod p) K] [DecidableEq K]

/-- Helper work starts only after all requested challenge pairs complete. -/
def after (build : ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (observed : ByteLookupPairTyped.Sample p degree K repetitions) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Option (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory)) :=
  match observed.values with
  | none => pure none
  | some values => some <$> build observed.raw values

omit [Module (ZMod p) K] [DecidableEq K] in
theorem after_none (build : ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (observed : ByteLookupPairTyped.Sample p degree K repetitions) (suspended : observed.values = none) :
    after build observed = pure none := by simp [after, suspended]

/-- The private byte program and all later helper queries use the same shared
execution. Both complete and partial raw observations are retained. -/
def program (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer repetitions : ℕ)
    (build : ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory)) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Emission p degree K Digest HelperMemory repetitions) :=
  SharedContinuation.program (PrivateSampling.embed Cfg Input Digest (ByteLookupPairTyped.sample basis table hashDepth inner outer repetitions)) (after build)

/-- No completed view means no later verifier execution and no fallback input.
The retained emission still records every byte spent before suspension. -/
def continueWith (next : LookupPairVectorMiddle.Emission K Digest HelperMemory repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Later)
    (emission : Emission p degree K Digest HelperMemory repetitions) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Option Later) :=
  match completed emission with
  | none => pure none
  | some helper => some <$> next helper

def helperRequests (requests : LookupPairVectorMiddle.Emission K Digest HelperMemory repetitions → List (Cfg × Digest))
    (emission : Emission p degree K Digest HelperMemory repetitions) : List (Cfg × Digest) :=
  (completed emission).elim [] requests

omit [Module (ZMod p) K] [DecidableEq K] in
/-- A suspended helper view executes no later verifier query. -/
theorem continueWith_none (next : LookupPairVectorMiddle.Emission K Digest HelperMemory repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Later)
    (emission : Emission p degree K Digest HelperMemory repetitions) (suspended : completed emission = none) :
    continueWith next emission = pure none := by simp [continueWith, suspended]

omit [Module (ZMod p) K] [DecidableEq K] in
/-- A suspended helper view records no invented helper root. -/
theorem helperRequests_none (requests : LookupPairVectorMiddle.Emission K Digest HelperMemory repetitions → List (Cfg × Digest))
    (emission : Emission p degree K Digest HelperMemory repetitions) (suspended : completed emission = none) :
    helperRequests requests emission = [] := by simp [helperRequests, suspended]

def AllPass (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (emission : Emission p degree K Digest HelperMemory repetitions) : Prop :=
  (completed emission).elim False (fun helper => LookupPairVector.AllPass sources table multiplicities helper.2.1)

omit [Module (ZMod p) K] [DecidableEq K] in
/-- Helper completion cannot create an all-pass event absent from the stored
sample. The statement also excludes any suspended optional vector. -/
theorem allPass_sampled (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (emission : Emission p degree K Digest HelperMemory repetitions) (passed : AllPass sources table multiplicities emission) :
    emission.1.values.elim False (LookupPairVector.AllPass sources table multiplicities) := by
  cases values : emission.1.values <;> cases roots : emission.2 <;> simp_all [AllPass, completed]

variable [Fintype K] [SampleableType K] [NeZero p]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Later helper work cannot increase the all-pass mass of the stored byte
vector, even if it inspects the full trace or makes adaptive shared hashes. -/
theorem retained_bound {char : ℕ} [CharP K char] (valid : 1 < p)
    (basis : Module.Basis (Fin degree) (ZMod p) K)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (enough : size + 1 < Fintype.card K) (bad : ∃ index, ∀ entry, sources index ≠ table entry) (small : count < char)
    (hashDepth inner outer repetitions : ℕ)
    (build : ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program basis table hashDepth inner outer repetitions build)).run state}[AllPass sources table multiplicities outcome.1] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest (ByteLookupPairTyped.sample basis table hashDepth inner outer repetitions)) (after build) state
    (fun observed => observed.values.elim False (LookupPairVector.AllPass sources table multiplicities))
  have sampled := ByteLookupPairTyped.finite_bound valid basis sources table multiplicities enough bad small hashDepth inner outer repetitions
  have bounded := retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_map] using sampled)
  apply (prEvent_mono _ _ _ (fun outcome passed => allPass_sampled sources table multiplicities outcome.1 passed)).trans bounded

/-- The original source tuples are fixed at their first recorded state before
sampling. All helper and later work remains in the actual staged execution. -/
theorem staged_bound {First Result : Type} {char : ℕ} [CharP K char] (valid : 1 < p)
    (basis : Module.Basis (Fin degree) (ZMod p) K)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest))
    (requests : First → Emission p degree K Digest HelperMemory repetitions → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (hashDepth inner outer : ℕ)
    (build : First → ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (next : First → Emission p degree K Digest HelperMemory repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (sources : First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Fin count → Fin width → F)
    (multiplicities : First → Fin size → K) (small : count < char)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy shape sourceRequests requests sourceCommit
      (fun first => program basis table hashDepth inner outer repetitions (build first)) next initial)}[
        (∃ index, ∀ entry, sources outcome.1 index ≠ table entry) ∧
        AllPass (sources outcome.1) table (multiplicities outcome.1.1) outcome.2.1.1] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  unfold StagedCommitmentPrefix.witness
  apply prEvent_bind_le_of_forall_le
  intro first
  by_cases bad : ∃ index, ∀ entry, sources first index ≠ table entry
  · have middle := retained_bound valid basis enc dummy shape (sources first) table (multiplicities first.1) enough bad small
      hashDepth inner outer repetitions (build first.1) (RecordRoots.state shape (sourceRequests first.1) first.2)
    have retained := prEvent_bind_le_prEvent_of_forall_eq_zero
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program basis table hashDepth inner outer repetitions (build first.1))).run (RecordRoots.state shape (sourceRequests first.1) first.2))
      (fun second => do
        let last ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (next first.1 second.1)).run (RecordRoots.state shape (requests first.1 second.1) second.2)
        pure (first, second, last))
      (fun second => AllPass (sources first) table (multiplicities first.1) second.1)
      (fun outcome => (∃ index, ∀ entry, sources outcome.1 index ≠ table entry) ∧
        AllPass (sources outcome.1) table (multiplicities outcome.1.1) outcome.2.1.1) ?_
    · exact retained.trans middle
    · intro second failed
      simp only [prEvent_norm]
      exact prEvent_eq_zero_of_forall_not _ _ (fun _ event => failed event.2)
  · apply prEvent_bind_le_of_forall_le
    intro second
    simp only [prEvent_norm]
    exact (prEvent_eq_zero_of_forall_not _ _ (fun _ event => bad event.1)).le.trans zero_le

end

end FormalProof4FHE.HasteBoots.ByteLookupPairMiddle
