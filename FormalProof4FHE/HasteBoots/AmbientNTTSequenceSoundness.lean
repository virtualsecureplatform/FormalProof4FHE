module
public import FormalProof4FHE.HasteBoots.AmbientNTTSequence
@[expose] public section

/-! Uniform conditional original-source risks compose across the reached NTT
loop. Every stage starts from its predecessor's actual memory and shared state.
The local safe errors sum; a whole-loop collision charge is kept separate. -/
namespace FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness
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

def LocalSafeRisk (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ)
    (entry : Index × Memory × Child heights (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height)) : Prop :=
  AmbientNTT.OriginalRisk heights (factory entry.1 entry.2.1) dummy capacity (radius entry.1) entry.2.2 ∧
    ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) entry.2.2.2.2

def AnySafeRisk (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ)
    (trace : Trace heights (F := F) (Index := Index) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ entry ∈ trace.results, LocalSafeRisk factory heights dummy capacity radius entry

/-- A child's inherited audit follows from its actual committed execution. -/
theorem child_audited (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (index : Index) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial)
    (child : Child heights (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (supported : child ∈ support (MultiCommitmentPrefix.witness enc dummy (AmbientMatrixSource.Shape heights)
      (CommittedJointMatrixOpening.requests (factory index memory).tag [false,true]) (factory index memory).commit
      (AuthenticatedNTT.continuation (factory index memory)) initial)) :
    CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) child.2.2 := by
  have projected : ((child.1.1,child.2.1),child.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (AuthenticatedNTT.program (factory index memory))).run initial) := by
    unfold AuthenticatedNTT.program
    rw [←MultiCommitmentPrefix.project_witness enc dummy (AmbientMatrixSource.Shape heights)
      (CommittedJointMatrixOpening.requests (factory index memory).tag [false,true]) (factory index memory).commit
      (AuthenticatedNTT.continuation (factory index memory)) initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape heights) (AuthenticatedNTT.program (factory index memory)) initial audited _ projected

/-- Sum conditional local-safe risks over the trusted possible child list.
Later children are charged only through their reached actual incoming states. -/
theorem safe_union_bound
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (indices : List Index) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ) (epsilon : Index → ENNReal)
    (conditional : ∀ index ∈ indices, ∀ memory initial,
      CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial →
      Pr{let child ← (MultiCommitmentPrefix.witness enc dummy (AmbientMatrixSource.Shape heights)
        (CommittedJointMatrixOpening.requests (factory index memory).tag [false,true]) (factory index memory).commit
        (AuthenticatedNTT.continuation (factory index memory)) initial)}[
          LocalSafeRisk factory heights dummy capacity radius (index,(memory,child))] ≤ epsilon index)
    (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness factory heights enc dummy indices memory initial)}[
      AnySafeRisk factory heights dummy capacity radius outcome.1] ≤ (indices.map epsilon).sum := by
  classical
  induction indices generalizing memory initial with
  | nil => simp [witness,AnySafeRisk,prEvent_norm]
  | cons index rest ih =>
    rw [witness]
    refine (prEvent_bind_le_prEvent_add_of_support (ε := (rest.map epsilon).sum) _ _
      (fun child => LocalSafeRisk factory heights dummy capacity radius (index,(memory,child))) _ ?_).trans ?_
    · intro child supported notHead
      have incoming := child_audited factory heights enc dummy index memory initial audited child supported
      by_cases passes : AuthenticatedNTT.accepted child.2.1 = true
      · simp only [passes,ite_true,prEvent_norm]
        have tail := ih (fun other member => conditional other (List.mem_cons_of_mem index member))
          child.2.1.2.memory child.2.2 incoming
        apply le_trans (prEvent_mono _ _ (fun outcome => AnySafeRisk factory heights dummy capacity radius outcome.1) ?_) tail
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
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : Trace heights (F := F) (Index := Index) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (supported : outcome ∈ support (witness factory heights enc dummy indices memory initial))

include supported in
/-- Earlier collision/source-monitor failures persist through the exact loop. -/
theorem bad_persistent
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) initial) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2 := by
  have projected : (erase heights outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program factory indices memory)).run initial) := by
    rw [←project_witness factory heights enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape heights) (program factory indices memory) initial bad _ projected

include supported in
/-- The final loop exception covers a bad state at ANY retained child end. -/
theorem child_bad_persistent
    (entry : Index × Memory × Child heights (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (member : entry ∈ outcome.1.results)
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) entry.2.2.2.2) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2 := by
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
        exact bad_persistent factory heights enc dummy rest child.2.1.2.memory child.2.2 later laterSupported bad
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
  have projected : (erase heights outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program factory indices memory)).run initial) := by
    rw [←project_witness factory heights enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  have covered := ShortCircuitSequence.accepted_indices enc dummy (AmbientMatrixSource.Shape heights)
    (step factory) indices memory initial (erase heights outcome.1,outcome.2) projected accepted
  simpa only [erase,List.map_map,Function.comp_def] using covered


include supported in
/-- Each retained entry comes from its actual selected factory and an actual
incoming state; no independent child-from-empty support is required. -/
theorem retained_child_support
    (entry : Index × Memory × Child heights (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (member : entry ∈ outcome.1.results) :
    ∃ before, entry.2.2 ∈ support (MultiCommitmentPrefix.witness enc dummy (AmbientMatrixSource.Shape heights)
      (CommittedJointMatrixOpening.requests (factory entry.1 entry.2.1).tag [false,true])
      (factory entry.1 entry.2.1).commit (AuthenticatedNTT.continuation (factory entry.1 entry.2.1)) before) := by
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
        exact ⟨initial,childSupported⟩
      · exact ih child.2.1.2.memory child.2.2 later laterSupported tail
    · simp [passes] at remainder
      subst outcome
      have first := List.mem_singleton.mp member
      subst entry
      exact ⟨initial,childSupported⟩

include supported in
/-- All earlier helper/source owners persist through the complete loop. -/
theorem retains (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.checkpoints.checkpoints := by
  have actual : (erase heights outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program factory indices memory)).run initial) := by
    rw [←project_witness factory heights enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape heights) tag saved (program factory indices memory) initial recorded _ actual

include supported in
/-- The actual complete loop inherits the caller's audit, including on rejection. -/
theorem audited_witness (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) outcome.2 := by
  have actual : (erase heights outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program factory indices memory)).run initial) := by
    rw [←project_witness factory heights enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape heights) (program factory indices memory) initial audited _ actual

include supported in
/-- Every checkpoint recorded at a retained child's end remains available at
the loop's final state, even if a later child rejects. -/
theorem child_retains
    (entry : Index × Memory × Child heights (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (member : entry ∈ outcome.1.results) (tag : Cfg)
    (saved : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (recorded : ⟨tag,saved⟩ ∈ entry.2.2.2.2.checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ outcome.2.checkpoints.checkpoints := by
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
        exact retains factory heights enc dummy rest child.2.1.2.memory child.2.2 later laterSupported tag saved recorded
      · exact ih child.2.1.2.memory child.2.2 later laterSupported tail
    · simp [passes] at remainder
      subst outcome
      have first := List.mem_singleton.mp member
      subst entry
      exact recorded

/-- Original-source risks at retained child ends, before excluding failures. -/
def AnyOriginalRisk (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ)
    (trace : Trace heights (F := F) (Index := Index) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height)) : Prop :=
  ∃ entry ∈ trace.results, AmbientNTT.OriginalRisk heights (factory entry.1 entry.2.1) dummy capacity (radius entry.1) entry.2.2

/-- The loop's final clear state excludes every retained child's exception. -/
theorem original_safe_le_local (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (indices : List Index) (capacity : 2^suffix ≤ m*b) (radius : Index → ℕ) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    Pr{let outcome ← (witness factory heights enc dummy indices memory initial)}[
      AnyOriginalRisk factory heights dummy capacity radius outcome.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2] ≤
    Pr{let outcome ← (witness factory heights enc dummy indices memory initial)}[
      AnySafeRisk factory heights dummy capacity radius outcome.1] := by
  apply prEvent_mono_of_support
  intro actual actualSupported event
  obtain ⟨⟨entry,member,risk⟩,clear⟩ := event
  refine ⟨entry,member,risk,?_⟩
  intro bad
  exact clear (child_bad_persistent factory heights enc dummy indices memory initial actual actualSupported entry member bad)

variable {K : Type} [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType F] [SampleableType (Fin r → F)]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- Row/compression arithmetic and both PCS errors are derived at each
actually reached audited child, then summed once over the trusted index list. -/
theorem derived_original_safe_union_bound [NeZero m] [NeZero b]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin b) F K) (indices : List Index)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (radius : Index → ℕ) (epsilon : Index → ENNReal)
    (encoding : ∀ index memory, (factory index memory).encoding = enc)
    (geometry : ∀ index memory side, heights ((factory index memory).tag side) = height)
    (small : ∀ index memory, (radius index : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (factory index memory).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ index memory,
      ((((r : ENNReal)/Fintype.card F)^k) +
        (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
      (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) (factory index memory).domain (radius index) +
        JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) (factory index memory).domain (radius index)) ≤ epsilon index)
    (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (witness factory heights enc dummy indices memory initial)}[
      AnyOriginalRisk factory heights dummy capacity radius outcome.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2] ≤ (indices.map epsilon).sum := by
  refine (original_safe_le_local factory heights enc dummy indices capacity radius memory initial).trans
    (safe_union_bound factory heights enc dummy indices capacity radius epsilon ?_ memory initial audited)
  intro index _ before initial incoming
  have stageAudit : CheckpointExecution.Audited (factory index before).encoding dummy (AmbientMatrixSource.Shape heights) initial := by
    rw [encoding]
    exact incoming
  have bound := (AmbientNTT.original_safe_bound heights (factory index before) (geometry index before)
    basis dummy enough capacity (radius index) (small index before) initial stageAudit).trans (calibrated index before)
  simpa only [AmbientNTT.witness,LocalSafeRisk,encoding] using bound

end
end FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness
