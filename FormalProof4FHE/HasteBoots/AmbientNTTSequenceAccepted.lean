module
public import FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness
@[expose] public section

/-! Actual loop acceptance propagates to every retained native NTT child. -/
namespace FormalProof4FHE.HasteBoots.AmbientNTTSequenceAccepted
open OracleSpec OracleComp BinaryTree
open AmbientNTTSequence
noncomputable section
variable {F Index Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k front suffix m queries height : ℕ}
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))] [SampleableType Digest]
variable (factory : Index → Memory → AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory
  b c r k front suffix m queries height)
variable (heights : Cfg → ℕ)

abbrev Trace := ShortCircuitSequence.Outcome Index
  (Memory × Child heights (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
    (front := front) (queries := queries) (height := height)) Memory


/-- Acceptance is derived from the actual short-circuit loop, including the
case where a rejected head would have skipped the entire remaining suffix. -/
theorem accepted_children (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (indices : List Index) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : Trace heights (F := F) (Index := Index) (Input := Input) (Digest := Digest) (Cfg := Cfg)
      (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r)
      (k := k) (front := front) (queries := queries) (height := height) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (supported : outcome ∈ support (witness factory heights enc dummy indices memory initial))
    (passed : outcome.1.accepted = true) :
    ∀ entry ∈ outcome.1.results, AuthenticatedNTT.accepted entry.2.2.2.1 = true := by
  induction indices generalizing memory initial outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    intro entry member
    cases member
  | cons index rest ih =>
    simp only [witness,support_bind,Set.mem_iUnion] at supported
    obtain ⟨child,childSupported,remainder⟩ := supported
    by_cases head : AuthenticatedNTT.accepted child.2.1 = true
    · simp only [head,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨later,laterSupported,equal⟩ := remainder
      subst outcome
      intro entry member
      rcases List.mem_cons.mp member with first | tail
      · subst entry
        exact head
      · exact ih child.2.1.2.memory child.2.2 later laterSupported passed entry tail
    · simp [head] at remainder
      subst outcome
      cases passed

end
end FormalProof4FHE.HasteBoots.AmbientNTTSequenceAccepted
