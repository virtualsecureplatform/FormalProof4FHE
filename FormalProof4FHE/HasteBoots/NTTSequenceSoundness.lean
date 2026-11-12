module
public import FormalProof4FHE.HasteBoots.NTTSequence
@[expose] public section

/-! Uniform conditional original-source risks compose across the reached NTT
loop. Every stage starts from its predecessor's actual memory and shared state.
The local safe errors sum; a whole-loop collision charge is kept separate. -/
namespace FormalProof4FHE.HasteBoots.NTTSequenceSoundness
open OracleSpec OracleComp BinaryTree
open NTTSequence
noncomputable section
variable {F Index Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k front suffix m queries height : ℕ}
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))] [SampleableType Digest]
variable (factory : Index → Memory → AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory
  b c r k front suffix m queries height)

abbrev Trace := ShortCircuitSequence.Outcome Index
  (Memory × Child (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
    (front := front) (queries := queries) (height := height)) Memory

def LocalSafeRisk (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ)
    (entry : Index × Memory × Child (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height)) : Prop :=
  OwnedNTTSoundness.OriginalRisk (factory entry.1 entry.2.1) dummy capacity (radius entry.1) entry.2.2 ∧
    ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) entry.2.2.2.2

def AnySafeRisk (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ)
    (trace : Trace (F := F) (Index := Index) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ entry ∈ trace.results, LocalSafeRisk factory dummy capacity radius entry

/-- A child's inherited audit follows from its actual committed execution. -/
theorem child_audited (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (index : Index) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (child : Child (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (supported : child ∈ support (MultiCommitmentPrefix.witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests (factory index memory).tag [false,true]) (factory index memory).commit
      (AuthenticatedNTT.continuation (factory index memory)) initial)) :
    CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) child.2.2 := by
  have projected : ((child.1.1,child.2.1),child.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (RecordedSourceCoherence.Shape Cfg height)) (AuthenticatedNTT.program (factory index memory))).run initial) := by
    unfold AuthenticatedNTT.program
    rw [←MultiCommitmentPrefix.project_witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests (factory index memory).tag [false,true]) (factory index memory).commit
      (AuthenticatedNTT.continuation (factory index memory)) initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (RecordedSourceCoherence.Shape Cfg height) (AuthenticatedNTT.program (factory index memory)) initial audited _ projected

/-- Sum conditional local-safe risks over the trusted possible child list.
Later children are charged only through their reached actual incoming states. -/
theorem safe_union_bound
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (indices : List Index) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ) (epsilon : Index → ENNReal)
    (conditional : ∀ index ∈ indices, ∀ memory initial,
      CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) initial →
      Pr{let child ← (MultiCommitmentPrefix.witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
        (CommittedJointMatrixOpening.requests (factory index memory).tag [false,true]) (factory index memory).commit
        (AuthenticatedNTT.continuation (factory index memory)) initial)}[
          LocalSafeRisk factory dummy capacity radius (index,(memory,child))] ≤ epsilon index)
    (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (witness factory enc dummy indices memory initial)}[
      AnySafeRisk factory dummy capacity radius outcome.1] ≤ (indices.map epsilon).sum := by
  classical
  induction indices generalizing memory initial with
  | nil => simp [witness,AnySafeRisk,prEvent_norm]
  | cons index rest ih =>
    rw [witness]
    refine (prEvent_bind_le_prEvent_add_of_support (ε := (rest.map epsilon).sum) _ _
      (fun child => LocalSafeRisk factory dummy capacity radius (index,(memory,child))) _ ?_).trans ?_
    · intro child supported notHead
      have incoming := child_audited factory enc dummy index memory initial audited child supported
      by_cases passes : AuthenticatedNTT.accepted child.2.1 = true
      · simp only [passes,ite_true,prEvent_norm]
        have tail := ih (fun other member => conditional other (List.mem_cons_of_mem index member))
          child.2.1.2.memory child.2.2 incoming
        apply le_trans (prEvent_mono _ _ (fun outcome => AnySafeRisk factory dummy capacity radius outcome.1) ?_) tail
        intro outcome event
        obtain ⟨entry,member,risk⟩ := event
        rcases List.mem_cons.mp member with equal | later
        · subst entry
          exact False.elim (notHead risk)
        · exact ⟨entry,later,risk⟩
      · simp only [ite_eq_right passes,pure_bind,prEvent_pure]
        split_ifs with event
        · obtain ⟨entry,member,risk⟩ := event
          have equal := List.mem_singleton.mp member
          subst entry
          exact False.elim (notHead risk)
        · exact zero_le
    · simpa only [List.map_cons,List.sum_cons] using
        add_le_add (conditional index (List.mem_cons_self) memory initial audited) le_rfl


variable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
  (indices : List Index) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (outcome : Trace (F := F) (Index := Index) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (supported : outcome ∈ support (witness factory enc dummy indices memory initial))

include supported in
/-- Earlier collision/source-monitor failures persist through the exact loop. -/
theorem bad_persistent
    (bad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) initial) :
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.2 := by
  have projected : (erase outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (RecordedSourceCoherence.Shape Cfg height)) (program factory indices memory)).run initial) := by
    rw [←project_witness factory enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (RecordedSourceCoherence.Shape Cfg height) (program factory indices memory) initial bad _ projected

include supported in
/-- The final loop exception covers a bad state at ANY retained child end. -/
theorem child_bad_persistent
    (entry : Index × Memory × Child (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (member : entry ∈ outcome.1.results)
    (bad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) entry.2.2.2.2) :
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.2 := by
  induction indices generalizing memory initial outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    cases member
  | cons index rest ih =>
    simp only [witness,support_bind,Set.mem_iUnion] at supported
    obtain ⟨child,childSupported,remainder⟩ := supported
    by_cases passes : AuthenticatedNTT.accepted child.2.1 = true
    · simp only [passes,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨later,laterSupported,equal⟩ := remainder
      subst outcome
      rcases List.mem_cons.mp member with first | tail
      · subst entry
        exact bad_persistent factory enc dummy rest child.2.1.2.memory child.2.2 later laterSupported bad
      · exact ih child.2.1.2.memory child.2.2 later laterSupported tail
    · simp [passes] at remainder
      subst outcome
      have first := List.mem_singleton.mp member
      subst entry
      exact bad


include supported in
/-- An accepted loop attempted every trusted child, in exactly the supplied
order; skipped suffixes cannot be hidden by the retained analysis trace. -/
theorem accepted_indices (accepted : outcome.1.accepted = true) :
    outcome.1.results.map Prod.fst = indices := by
  have projected : (erase outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (RecordedSourceCoherence.Shape Cfg height)) (program factory indices memory)).run initial) := by
    rw [←project_witness factory enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  have covered := ShortCircuitSequence.accepted_indices enc dummy (RecordedSourceCoherence.Shape Cfg height)
    (step factory) indices memory initial (erase outcome.1,outcome.2) projected accepted
  simpa only [erase,List.map_map,Function.comp_def] using covered

end
end FormalProof4FHE.HasteBoots.NTTSequenceSoundness
