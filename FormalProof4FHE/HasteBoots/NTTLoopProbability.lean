module
public import FormalProof4FHE.HasteBoots.NTTSequenceSoundness
public import FormalProof4FHE.HasteBoots.HadamardNTTProbability
@[expose] public section

/-! Original-owner NTT risks across the ordered child loop. Conditional stage
errors sum over the trusted possible attempts, while all child collision
alternatives are charged once on the actual short-circuit loop execution. -/
namespace FormalProof4FHE.HasteBoots.NTTLoopProbability
open OracleSpec OracleComp BinaryTree
open NTTSequence NTTSequenceSoundness
noncomputable section
variable {F Index Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k front suffix m queries height : ℕ}
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))] [SampleableType Digest]
variable (factory : Index → Memory → AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory
  b c r k front suffix m queries height)

def AnyRisk (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ)
    (trace : Trace (F := F) (Index := Index) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ entry ∈ trace.results,
    OwnedNTTSoundness.OriginalRisk (factory entry.1 entry.2.1) dummy capacity (radius entry.1) entry.2.2

/-- A common final collision event absorbs every earlier child exception.
No stage is restarted from empty and no hash charge is multiplied by loop size. -/
theorem original_risk_bound [Fintype Digest]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (indices : List Index) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ) (epsilon : Index → ENNReal)
    (conditional : ∀ index ∈ indices, ∀ memory initial,
      CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) initial →
      Pr{let child ← (MultiCommitmentPrefix.witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
        (CommittedJointMatrixOpening.requests (factory index memory).tag [false,true]) (factory index memory).commit
        (AuthenticatedNTT.continuation (factory index memory)) initial)}[
          LocalSafeRisk factory dummy capacity radius (index,(memory,child))] ≤ epsilon index)
    (memory : Memory) :
    Pr{let outcome ← (witness factory enc dummy indices memory
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      AnyRisk factory dummy capacity radius outcome.1] ≤ (indices.map epsilon).sum +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height)) (program factory indices memory)
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  have initial := CheckpointExecution.good_empty enc dummy (RecordedSourceCoherence.Shape Cfg height)
  have arithmetic := safe_union_bound factory enc dummy indices capacity radius epsilon conditional memory
    _ ⟨initial.1,fun _ => initial.2.2⟩
  have hash := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (RecordedSourceCoherence.Shape Cfg height) (program factory indices memory)
  rw [←project_witness factory enc dummy indices memory
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)),prEvent_map] at hash
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    AnySafeRisk factory dummy capacity radius outcome.1 ∨
      CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.2) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic hash)
  · intro outcome supported event
    obtain ⟨entry,member,risk⟩ := event
    by_cases bad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) entry.2.2.2.2
    · exact Or.inr (child_bad_persistent factory enc dummy indices memory _ outcome supported entry member bad)
    · exact Or.inl ⟨entry,member,risk,bad⟩

variable {K : Type} [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType F] [SampleableType (Fin r → F)] [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Instantiates the loop with the proved native NTT arithmetic/PCS bound.
The remaining per-index cap is numerical calibration, not a relation-truth flag. -/
theorem native_original_risk_bound [Fintype Digest] [NeZero m] [NeZero b]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (indices : List Index) (basis : Module.Basis (Fin b) F K)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (radius : Index → ℕ) (epsilon : Index → ENNReal)
    (encoding : ∀ index ∈ indices, ∀ memory, (factory index memory).encoding = enc)
    (small : ∀ index ∈ indices, ∀ memory, ((radius index : ℕ) : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (factory index memory).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ index ∈ indices, ∀ memory,
      HadamardNTTProbability.rate (K := K) (factory index memory) (radius index) ≤ epsilon index)
    (memory : Memory) :
    Pr{let outcome ← (witness factory enc dummy indices memory
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      AnyRisk factory dummy capacity radius outcome.1] ≤ (indices.map epsilon).sum +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height)) (program factory indices memory)
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  apply original_risk_bound factory enc dummy indices capacity radius epsilon _ memory
  intro index member incoming state audited
  have inherited : CheckpointExecution.Audited (factory index incoming).encoding dummy
      (RecordedSourceCoherence.Shape Cfg height) state := by
    rw [encoding index member incoming]
    exact audited
  have native := NTTConditionalSoundness.original_safe_bound (factory index incoming) basis dummy enough capacity
    (radius index) (small index member incoming) state inherited
  have bound := native.trans (calibrated index member incoming)
  simpa only [NTTConditionalSoundness.witness,LocalSafeRisk,encoding index member incoming] using bound

end
end FormalProof4FHE.HasteBoots.NTTLoopProbability
