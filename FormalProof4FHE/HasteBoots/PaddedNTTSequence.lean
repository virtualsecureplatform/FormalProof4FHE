module
public import FormalProof4FHE.HasteBoots.PaddedNTT
public import FormalProof4FHE.HasteBoots.ShortCircuitSequence
@[expose] public section

/-! Ordered padded NTT calls with per-call physical geometry. The scheduled
index and incoming private memory select the dependent result type; neither
is supplied by the prover. All calls share one execution history. -/
namespace FormalProof4FHE.HasteBoots.PaddedNTTSequence
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {F Index Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {heights : Cfg → ℕ} {b c r k : ℕ}

variable (factory : Index → Memory → PaddedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory heights b c r k)

/-- The caller selects one shared encoding without changing a source layout. -/
abbrev shared (enc : MerkleOracle.Encoding Input Digest (List F)) (index : Index) (memory : Memory) :=
  {factory index memory with encoding := enc}

abbrev Actual := Sigma (fun request : Index × Memory =>
  ((Bool → Digest) × CommitMemory) × PaddedNTT.ActualResult (factory request.1 request.2))
abbrev Child := Sigma (fun request : Index × Memory =>
  PaddedNTT.Prefix (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
    PaddedNTT.RunResult (factory request.1 request.2))
abbrev Trace := ShortCircuitSequence.Outcome Index (Child factory) Memory

variable [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)] [SampleableType Digest]
  [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^((factory index memory).code side).front) b)]
  [∀ index memory side, SampleableType (Fin ((factory index memory).code side).queries → Fin (2^heights ((factory index memory).tag side)))]

/-- Packing retains the actual factory argument, roots and returned memory. -/
def step (enc : MerkleOracle.Encoding Input Digest (List F)) (index : Index) (memory : Memory) := do
  let result ← PaddedNTT.program (shared factory enc index memory)
  pure (⟨⟨(index,memory),result⟩,result.2.2.memory,PaddedNTT.accepted (factory index memory) result.2⟩ :
    ShortCircuitSequence.StepResult (Actual factory) Memory)

def program (enc : MerkleOracle.Encoding Input Digest (List F)) (indices : List Index) (memory : Memory) :=
  ShortCircuitSequence.program (step factory enc) indices memory

/-- Retain every reached child's original root snapshot and final state. -/
def witness (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) :
    List Index → Memory → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights) →
      ProbComp (Trace factory × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  | [], memory, initial => pure (⟨[],memory,true⟩,initial)
  | index::rest, memory, initial => do
    let child ← PaddedNTT.witness (shared factory enc index memory) dummy initial
    let later ← if PaddedNTT.accepted (factory index memory) child.2.1 then
        witness enc dummy rest child.2.1.2.memory child.2.2
      else pure (⟨[],child.2.1.2.memory,false⟩,child.2.2)
    pure (⟨(index,⟨(index,memory),child⟩)::later.1.results,later.1.memory,later.1.accepted⟩,later.2)

def erase (trace : Trace factory) : ShortCircuitSequence.Outcome Index (Actual factory) Memory :=
  ⟨trace.results.map (fun entry => (entry.1,⟨entry.2.1,(entry.2.2.1.1,entry.2.2.2.1)⟩)),trace.memory,trace.accepted⟩

/-- Erasure changes only analysis data, including on failure or early return. -/
theorem project_witness (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (indices : List Index) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    (fun outcome => (erase factory outcome.1,outcome.2)) <$> witness factory enc dummy indices memory initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program factory enc indices memory)).run initial := by
  induction indices generalizing memory initial with
  | nil => rfl
  | cons index rest ih =>
    simp only [witness,program,ShortCircuitSequence.program,step,PaddedNTT.program,PaddedNTT.witness,
      MultiCommitmentPrefix.witness,MultiCommitmentPrefix.program,simulateQ_bind,StateT.run_bind,
      RecordRoots.run_program,map_bind,pure_bind,bind_assoc]
    congr 1
    funext first
    congr 1
    funext last
    split
    · simp only [map_bind,map_pure,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure]
      have tail := ih last.1.2.memory last.2
      unfold program at tail
      rw [←tail]
      simp only [bind_map_left,erase,List.map_cons]
    · simp only [map_pure,simulateQ_pure,StateT.run_pure,erase,List.map_cons,List.map_nil]

variable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
  (indices : List Index) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : Trace factory ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (supported : outcome ∈ support (witness factory enc dummy indices memory initial))

include supported in
/-- Earlier collision/source-monitor failures persist through the exact loop. -/
theorem bad_persistent
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) initial) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2 := by
  have projected : (erase factory outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program factory enc indices memory)).run initial) := by
    rw [←project_witness factory enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape heights) (program factory enc indices memory) initial bad _ projected

include supported in
/-- The final loop exception covers a bad state at ANY retained child end. -/
theorem child_bad_persistent
    (entry : Index × Child factory)
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
    by_cases passes : PaddedNTT.accepted (factory index memory) child.2.1 = true
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
  have projected : (erase factory outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program factory enc indices memory)).run initial) := by
    rw [←project_witness factory enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  have covered := ShortCircuitSequence.accepted_indices enc dummy (AmbientMatrixSource.Shape heights)
    (step factory enc) indices memory initial (erase factory outcome.1,outcome.2) projected accepted
  simpa only [erase,List.map_map,Function.comp_def] using covered


include supported in
/-- Each retained entry comes from its actual selected factory and an actual
incoming state; no independent child-from-empty support is required. -/
theorem retained_child_support
    (entry : Index × Child factory)
    (member : entry ∈ outcome.1.results) :
    ∃ before, entry.2.2 ∈ support (PaddedNTT.witness (shared factory enc entry.2.1.1 entry.2.1.2) dummy before) := by
  induction indices generalizing memory initial outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    cases member
  | cons index rest ih =>
    simp only [witness,support_bind,Set.mem_iUnion] at supported
    obtain ⟨child,childSupported,remainder⟩ := supported
    by_cases passes : PaddedNTT.accepted (factory index memory) child.2.1 = true
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
  have actual : (erase factory outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program factory enc indices memory)).run initial) := by
    rw [←project_witness factory enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape heights) tag saved (program factory enc indices memory) initial recorded _ actual

include supported in
/-- The actual complete loop inherits the caller's audit, including on rejection. -/
theorem audited_witness (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) outcome.2 := by
  have actual : (erase factory outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (AmbientMatrixSource.Shape heights)) (program factory enc indices memory)).run initial) := by
    rw [←project_witness factory enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape heights) (program factory enc indices memory) initial audited _ actual

include supported in
/-- Every checkpoint recorded at a retained child's end remains available at
the loop's final state, even if a later child rejects. -/
theorem child_retains
    (entry : Index × Child factory)
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
    by_cases passes : PaddedNTT.accepted (factory index memory) child.2.1 = true
    · simp only [passes,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨later,laterSupported,equal⟩ := remainder
      subst outcome
      rcases List.mem_cons.mp member with first | tail
      · subst entry
        exact retains factory enc dummy rest child.2.1.2.memory child.2.2 later laterSupported tag saved recorded
      · exact ih child.2.1.2.memory child.2.2 later laterSupported tail
    · simp [passes] at remainder
      subst outcome
      have first := List.mem_singleton.mp member
      subst entry
      exact recorded



include supported in
/-- The sigma tag is the scheduled index, never a prover-chosen tag. -/
theorem retained_index (entry : Index × Child factory) (member : entry ∈ outcome.1.results) :
    entry.2.1.1 = entry.1 := by
  induction indices generalizing memory initial outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    cases member
  | cons index rest ih =>
    simp only [witness,support_bind,Set.mem_iUnion] at supported
    obtain ⟨child,childSupported,remainder⟩ := supported
    by_cases passes : PaddedNTT.accepted (factory index memory) child.2.1 = true
    · simp only [passes,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨later,laterSupported,equal⟩ := remainder
      subst outcome
      rcases List.mem_cons.mp member with first | tail
      · subst entry
        rfl
      · exact ih child.2.1.2.memory child.2.2 later laterSupported tail
    · simp [passes] at remainder
      subst outcome
      have first := List.mem_singleton.mp member
      subst entry
      rfl

include supported in
/-- Overall acceptance implies actual computed acceptance at every retained call. -/
theorem accepted_children (passes : outcome.1.accepted = true)
    (entry : Index × Child factory) (member : entry ∈ outcome.1.results) :
    PaddedNTT.accepted (factory entry.2.1.1 entry.2.1.2) entry.2.2.2.1 = true := by
  induction indices generalizing memory initial outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    cases member
  | cons index rest ih =>
    simp only [witness,support_bind,Set.mem_iUnion] at supported
    obtain ⟨child,childSupported,remainder⟩ := supported
    by_cases head : PaddedNTT.accepted (factory index memory) child.2.1 = true
    · simp only [head,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨later,laterSupported,equal⟩ := remainder
      subst outcome
      rcases List.mem_cons.mp member with first | tail
      · subst entry
        exact head
      · exact ih child.2.1.2.memory child.2.2 later laterSupported passes tail
    · simp [head] at remainder
      subst outcome
      cases passes

end
end FormalProof4FHE.HasteBoots.PaddedNTTSequence
